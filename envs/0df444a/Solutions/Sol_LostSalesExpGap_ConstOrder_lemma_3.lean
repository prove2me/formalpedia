-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:07:21.836591+00:00
-- url     : https://prove2.me/submissions/ca4f86ec-d298-4e88-8ecd-26a3c26e3fc0

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_kingman_series
import Theorems.Thm_LostSalesExpGap_ConstOrder_vartheta_pos_gamma_lt_one

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapL3

open CappedBaseStock LostSalesExpGap.ConstOrder Filter Topology

lemma measurable_finiteInventory (x : ℝ) (m : ℕ) :
    Measurable (fun d : DemandPath => finiteInventory d x m) := by
  unfold finiteInventory
  apply Finset.measurable_range_sup''
  intro k _
  fun_prop

lemma finiteInventory_nonneg (d : DemandPath) (x : ℝ) (m : ℕ) : 0 ≤ finiteInventory d x m := by
  unfold finiteInventory
  exact le_trans (by simp) (Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (x - (d i : ℝ)))
    (Finset.mem_range.mpr (Nat.succ_pos m)))

lemma finiteInventory_le (d : DemandPath) (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    finiteInventory d x m ≤ m * x := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc ∑ i ∈ Finset.range k, (x - (d i : ℝ)) ≤ ∑ i ∈ Finset.range k, x :=
        Finset.sum_le_sum fun i _ => by have := NNReal.coe_nonneg (d i); linarith
    _ = k * x := by simp
    _ ≤ m * x := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hx

lemma walk_eq (r : ℝ≥0) (d : DemandPath) (k : ℕ) :
    LostSalesConstantOrder.LargeLeadTime.walk r d k = ∑ i ∈ Finset.range k, ((r : ℝ) - d i) := by
  unfold LostSalesConstantOrder.LargeLeadTime.walk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    push_cast
    linarith

lemma EIinf_eq_iSup (P : DemandLaw) (r : ℝ) (hr : 0 ≤ r) :
    EIinf P r = ⨆ m : ℕ, ENNReal.ofReal (EIL P r m) := by
  have hsup : ∀ d, LostSalesConstantOrder.LargeLeadTime.supWalk r.toNNReal d =
      ⨆ m : ℕ, ENNReal.ofReal (finiteInventory d r m) := by
    intro d
    unfold LostSalesConstantOrder.LargeLeadTime.supWalk
    apply le_antisymm
    · refine iSup_le fun k => le_iSup_of_le k (ENNReal.ofReal_le_ofReal ?_)
      rw [walk_eq, Real.coe_toNNReal _ hr]
      unfold finiteInventory
      exact Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (Finset.mem_range.mpr (Nat.lt_succ_self k))
    · refine iSup_le fun m => ?_
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := m))
        (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
      refine le_iSup_of_le k (le_of_eq ?_)
      unfold finiteInventory
      rw [hkeq, walk_eq, Real.coe_toNNReal _ hr]
  unfold EIinf
  simp_rw [hsup]
  rw [lintegral_iSup (f := fun m d => ENNReal.ofReal (finiteInventory d r m))
    (fun m => ENNReal.measurable_ofReal.comp (measurable_finiteInventory r m))]
  · congr 1; funext m
    unfold EIL
    have hint : Integrable (fun d => finiteInventory d r m) (demandPathLaw P) := by
      refine Integrable.of_bound (C := m * r)
        (measurable_finiteInventory r m).aestronglyMeasurable (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (finiteInventory_nonneg d r m)]
      exact finiteInventory_le d r hr m
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun d => finiteInventory_nonneg d r m)]
  · intro m n hmn d
    apply ENNReal.ofReal_le_ofReal
    unfold finiteInventory
    exact Finset.sup'_mono _ (Finset.range_mono (by omega)) _

/-- `E[exp(θ (N x − S_N))] = ψ(θ)^N` with `ψ(θ) = e^{θx} E[e^{−θD}]`. -/
lemma mgf_walk (P : DemandLaw) (x θ : ℝ) (hθ : 0 ≤ θ) (N : ℕ) :
    ∫ d, Real.exp (θ * ((N : ℝ) * x - ∑ i ∈ Finset.range N, (d i : ℝ))) ∂demandPathLaw P =
      (Real.exp (θ * x) * ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law) ^ N := by
  set μ := demandPathLaw P with hμ
  let X : ℕ → DemandPath → ℝ := fun i d => (d i : ℝ)
  have hXm : ∀ i, Measurable (X i) := fun i => by fun_prop
  have hind : iIndepFun X μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ (x : ℝ≥0) => (x : ℝ))
      (fun _ => by fun_prop)
  have hmgf1 : ∀ i (t : ℝ), mgf (X i) μ t = ∫ y : ℝ≥0, Real.exp (t * (y : ℝ)) ∂P.law := by
    intro i t
    simp only [mgf, X]
    have hmap : μ.map (fun d : DemandPath => d i) = P.law := by
      simp only [hμ, demandPathLaw]
      exact Measure.infinitePi_map_eval _ i
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable]
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hsum : mgf (∑ i ∈ Finset.range N, X i) μ (-θ) =
      (∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law) ^ N := by
    rw [hind.mgf_sum hXm]
    simp_rw [hmgf1]
    rw [Finset.prod_const, Finset.card_range]
  have hS : ∀ d, (∑ i ∈ Finset.range N, X i) d = ∑ i ∈ Finset.range N, (d i : ℝ) := by
    intro d; simp [X, Finset.sum_apply]
  have e1 : ∫ d, Real.exp (θ * ((N : ℝ) * x - ∑ i ∈ Finset.range N, (d i : ℝ))) ∂μ =
      Real.exp (θ * N * x) * mgf (∑ i ∈ Finset.range N, X i) μ (-θ) := by
    simp only [mgf]
    rw [← integral_const_mul]
    congr 1; funext d
    rw [hS, ← Real.exp_add]; congr 1; ring
  rw [e1, hsum, mul_pow, ← Real.exp_nat_mul]
  congr 2; ring

lemma pos_le_exp (x θ : ℝ) (hθ : 0 < θ) :
    max x 0 ≤ Real.exp (θ * x) / (Real.exp 1 * θ) := by
  have hpos : 0 < Real.exp 1 * θ := by positivity
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx]; positivity
  · rw [max_eq_left hx, le_div_iff₀ hpos]
    have h := Real.add_one_le_exp (θ * x - 1)
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)] at h
    nlinarith

/-- If `D < r` has positive probability, then `φ` attains its infimum on `[0, ∞)`. -/
lemma minimizer_exists (P : DemandLaw) (c : Parameters)
    (h : ¬ ∀ᵐ x : ℝ≥0 ∂P.law, rInf P c ≤ (x : ℝ)) : (phiMinimizers P c).Nonempty := by
  set r := rInf P c
  have hpos : P.law {x : ℝ≥0 | (x : ℝ) < r} ≠ 0 := by
    intro h0; apply h
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq, not_le] at hx ⊢; exact hx
  obtain ⟨ε, hε, hq⟩ : ∃ ε : ℝ, 0 < ε ∧ P.law {x : ℝ≥0 | (x : ℝ) ≤ r - ε} ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hpos
    have hU : {x : ℝ≥0 | (x : ℝ) < r} = ⋃ k : ℕ, {x : ℝ≥0 | (x : ℝ) ≤ r - 1 / ((k : ℝ) + 1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / (r - x))
        refine ⟨k, ?_⟩
        have h1 : 0 < r - x := by linarith
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have : 1 / ((k : ℝ) + 1) < r - x := by
          rw [div_lt_iff₀ hk1]
          rw [div_lt_iff₀ h1] at hk
          nlinarith
        linarith
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hU]
    exact measure_iUnion_null fun k => hcon _ (by positivity)
  set A : Set ℝ≥0 := {x : ℝ≥0 | (x : ℝ) ≤ r - ε}
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  set q := P.law.real A
  have hq0 : 0 < q := ENNReal.toReal_pos hq (measure_ne_top _ _)
  set I : ℝ → ℝ := fun θ => ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law
  have hphiI : ∀ θ, phi P c θ = Real.exp (θ * r) * I θ := fun θ => rfl
  -- lower bound
  have hlow : ∀ θ, 0 ≤ θ → q * Real.exp (θ * ε) ≤ phi P c θ := by
    intro θ hθ
    have hI : q * Real.exp (-θ * (r - ε)) ≤ I θ := by
      have hint : Integrable (fun y : ℝ≥0 => Real.exp (-θ * (y : ℝ))) P.law := by
        refine Integrable.of_bound (C := 1) (Measurable.aestronglyMeasurable (by fun_prop))
          (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        nlinarith [NNReal.coe_nonneg y]
      have := integral_mono ((integrable_const (Real.exp (-θ * (r - ε)))).indicator hAm) hint
        (fun y => by
          by_cases hy : y ∈ A
          · rw [Set.indicator_of_mem hy]
            apply Real.exp_le_exp.mpr
            have : (y : ℝ) ≤ r - ε := hy
            nlinarith
          · rw [Set.indicator_of_notMem hy]; exact (Real.exp_pos _).le)
      rw [integral_indicator_const _ hAm, smul_eq_mul] at this
      show q * Real.exp (-θ * (r - ε)) ≤ ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law
      linarith
    rw [hphiI]
    calc q * Real.exp (θ * ε) = Real.exp (θ * r) * (q * Real.exp (-θ * (r - ε))) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (θ * r) * I θ := mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
  -- a level beyond which `φ > 1`
  set Θ := (|Real.log q| + 1) / ε
  have hΘ : 0 < Θ := by positivity
  have hbig : ∀ θ, Θ ≤ θ → 1 < phi P c θ := by
    intro θ hθ
    have h1 : |Real.log q| + 1 ≤ θ * ε := by
      rw [div_le_iff₀ hε] at hθ; linarith
    have h2 : 1 < q * Real.exp (θ * ε) := by
      have : Real.exp (-Real.log q) < Real.exp (θ * ε) := by
        apply Real.exp_lt_exp.mpr
        have := neg_le_abs (Real.log q); linarith
      rw [Real.exp_neg, Real.exp_log hq0] at this
      rw [inv_lt_iff_one_lt_mul₀ hq0] at this
      linarith
    exact lt_of_lt_of_le h2 (hlow θ (le_trans hΘ.le hθ))
  -- continuity of `φ` on `[0, ∞)`
  have hIcont : ContinuousOn I (Set.Ici 0) := by
    apply continuousOn_of_dominated (bound := fun _ => 1)
    · intro θ _; exact Measurable.aestronglyMeasurable (by fun_prop)
    · intro θ hθ
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ θ := hθ
      nlinarith [NNReal.coe_nonneg y]
    · exact integrable_const 1
    · exact ae_of_all _ fun y => (by fun_prop : Continuous fun θ : ℝ => Real.exp (-θ * (y : ℝ))).continuousOn
  have hphicont : ContinuousOn (phi P c) (Set.Icc 0 Θ) := by
    have : ContinuousOn (fun θ => Real.exp (θ * r) * I θ) (Set.Ici 0) :=
      (by fun_prop : Continuous fun θ : ℝ => Real.exp (θ * r)).continuousOn.mul hIcont
    exact (this.mono Set.Icc_subset_Ici_self).congr fun θ _ => hphiI θ
  obtain ⟨θs, hθs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hΘ.le) hphicont
  have hphi0 : phi P c 0 = 1 := by simp [phi]
  have hglob : ∀ θ, 0 ≤ θ → phi P c θs ≤ phi P c θ := by
    intro θ hθ
    by_cases hθΘ : θ ≤ Θ
    · exact hmin ⟨hθ, hθΘ⟩
    · have h1 := hbig θ (le_of_not_ge hθΘ)
      have h2 : phi P c θs ≤ phi P c 0 := hmin ⟨le_rfl, hΘ.le⟩
      linarith
  have hphinn : ∀ θ : ℝ, 0 ≤ phi P c θ := fun θ =>
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hbdd : BddBelow (Set.range fun θ : Set.Ici (0 : ℝ) => phi P c θ) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact hphinn θ⟩
  refine ⟨θs, hθs.1, le_antisymm ?_ ?_⟩
  · exact le_ciInf fun θ => hglob θ θ.2
  · exact ciInf_le hbdd ⟨θs, hθs.1⟩

end LSExpGapL3

open LostSalesExpGap.ConstOrder LSExpGapL3 CappedBaseStock Filter Topology in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    (∀ r : ℝ, 0 ≤ r → r ≤ CappedBaseStock.mean P → ∀ m : ℕ, 1 ≤ m →
      EIL P r m = ∑ n ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ r : ℝ, 0 ≤ r → r < CappedBaseStock.mean P →
      EIinf P r = ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
        ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ))
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ m : ℕ, 1 ≤ m →
      EIinf P (rInf P c) ≤ ENNReal.ofReal (EIL P (rInf P c) m) +
        ENNReal.ofReal (((1 - gamma P c) * Real.exp 1 * ((m : ℝ) + 1))⁻¹ * varthetaInv P c *
          gamma P c ^ (m + 1))) := by
  obtain ⟨hK1, hK2⟩ := kingman_series P
  refine ⟨hK1, hK2, ?_⟩
  intro m hm
  obtain ⟨hγ0, hγ1, hϑpos⟩ := vartheta_pos_gamma_lt_one P c hP
  set μ := demandPathLaw P with hμ
  set r := rInf P c with hrdef
  set γ := gamma P c with hγdef
  set mean := CappedBaseStock.mean P
  have hmean : 0 < mean := P.positiveMean
  have hr0 : 0 ≤ r ∧ r ≤ mean := by
    simp only [hrdef, rInf]
    by_cases hne : (argminConst P c).Nonempty
    · obtain ⟨x, hx⟩ := hne
      exact ⟨le_csInf ⟨x, hx⟩ fun y hy => hy.1.1,
        le_trans (csInf_le ⟨0, fun y hy => hy.1.1⟩ hx) hx.1.2⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]; exact ⟨le_rfl, hmean.le⟩
  -- the Kingman terms
  let a : ℕ → ℝ := fun n =>
    ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0 ∂μ
  have ha0 : ∀ n, 0 ≤ a n := fun n => integral_nonneg fun _ => le_max_right _ _
  have hEIL : ∀ M, EIL P r M = ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1) * a n := by
    intro M
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · subst h0; simp [EIL, finiteInventory]
    · exact hK1 r hr0.1 hr0.2 M hpos
  have hEILnn : ∀ M, 0 ≤ EIL P r M := fun M => by
    rw [hEIL M]; exact Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (ha0 n)
  -- the exponential bound for each minimiser
  have hbound : ∀ θ ∈ phiMinimizers P c, ∀ n, a n ≤ γ ^ (n + 1) / (Real.exp 1 * θ) := by
    intro θ hθ n
    have hθpos : 0 < θ := by
      rcases hθ.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have := hθ.2
        rw [← h] at this
        simp [phi] at this
        rw [← hγdef] at this
        linarith
    set N := n + 1
    have hX : ∀ d : DemandPath, ((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) =
        (N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ) := by
      intro d; simp [N]
    have hint : Integrable (fun d : DemandPath =>
        Real.exp (θ * ((N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ)))) μ := by
      refine Integrable.of_bound (C := Real.exp (θ * ((N : ℝ) * r)))
        (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ ∑ i ∈ Finset.range N, (d i : ℝ) := by positivity
      nlinarith
    have hmaxint : Integrable (fun d : DemandPath =>
        max ((N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ)) 0) μ := by
      refine Integrable.of_bound (C := (N : ℝ) * r)
        (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have : 0 ≤ ∑ i ∈ Finset.range N, (d i : ℝ) := by positivity
      exact max_le (by linarith) (mul_nonneg (Nat.cast_nonneg N) hr0.1)
    have h1 : a n = ∫ d, max ((N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ)) 0 ∂μ := by
      simp only [a]; congr 1; funext d; rw [hX d]
    rw [h1]
    calc ∫ d, max ((N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ)) 0 ∂μ
        ≤ ∫ d, Real.exp (θ * ((N : ℝ) * r - ∑ i ∈ Finset.range N, (d i : ℝ))) /
            (Real.exp 1 * θ) ∂μ :=
          integral_mono hmaxint (hint.div_const _) (fun d => pos_le_exp _ θ hθpos)
      _ = (phi P c θ) ^ N / (Real.exp 1 * θ) := by
          rw [integral_div, mgf_walk P r θ hθpos.le N]; rfl
      _ = γ ^ (n + 1) / (Real.exp 1 * θ) := by rw [hθ.2]
  -- the tail bound for each minimiser
  set K := ((1 - γ) * Real.exp 1 * ((m : ℝ) + 1))⁻¹ * γ ^ (m + 1) with hK
  have h1γ : 0 < 1 - γ := by linarith
  have hK0 : 0 ≤ K := by positivity
  have htail : ∀ M, m ≤ M → ∀ θ ∈ phiMinimizers P c, (EIL P r M - EIL P r m) * θ ≤ K := by
    intro M hmM θ hθ
    have hθpos : 0 < θ := by
      rcases hθ.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have := hθ.2
        rw [← h] at this
        simp [phi] at this
        rw [← hγdef] at this
        linarith
    have hdiff : EIL P r M - EIL P r m =
        ∑ n ∈ Finset.Ico m M, 1 / ((n : ℝ) + 1) * a n := by
      rw [hEIL, hEIL, ← Finset.sum_range_add_sum_Ico _ hmM]; ring
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hterm : ∀ n ∈ Finset.Ico m M, 1 / ((n : ℝ) + 1) * a n ≤
        γ / (Real.exp 1 * θ * ((m : ℝ) + 1)) * γ ^ n := by
      intro n hn
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      have hb := hbound θ hθ n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      calc 1 / ((n : ℝ) + 1) * a n ≤ 1 / ((m : ℝ) + 1) * (γ ^ (n + 1) / (Real.exp 1 * θ)) := by
            apply mul_le_mul (one_div_le_one_div_of_le hm1 (by linarith)) hb (ha0 n)
              (by positivity)
        _ = γ / (Real.exp 1 * θ * ((m : ℝ) + 1)) * γ ^ n := by
            rw [pow_succ]; field_simp
    have hgeo := geom_sum_Ico_le_of_lt_one (m := m) (n := M) hγ0 hγ1
    rw [hdiff]
    calc (∑ n ∈ Finset.Ico m M, 1 / ((n : ℝ) + 1) * a n) * θ
        ≤ (∑ n ∈ Finset.Ico m M, γ / (Real.exp 1 * θ * ((m : ℝ) + 1)) * γ ^ n) * θ :=
          mul_le_mul_of_nonneg_right (Finset.sum_le_sum hterm) hθpos.le
      _ = γ / (Real.exp 1 * θ * ((m : ℝ) + 1)) * (∑ n ∈ Finset.Ico m M, γ ^ n) * θ := by
          rw [Finset.mul_sum]
      _ ≤ γ / (Real.exp 1 * θ * ((m : ℝ) + 1)) * (γ ^ m / (1 - γ)) * θ := by
          gcongr
      _ = K := by
          rw [hK, pow_succ]; field_simp
  -- the final real bound
  set B := ((1 - γ) * Real.exp 1 * ((m : ℝ) + 1))⁻¹ * varthetaInv P c * γ ^ (m + 1) with hB
  have hBK : B = K * varthetaInv P c := by rw [hB, hK]; ring
  have hϑi0 : 0 ≤ varthetaInv P c := by
    simp only [varthetaInv]
    split_ifs with hs
    · exact (inv_pos.mpr (hϑpos hs.1 hs.2)).le
    · exact le_rfl
  have hB0 : 0 ≤ B := by rw [hBK]; exact mul_nonneg hK0 hϑi0
  have hfinal : ∀ M, EIL P r M ≤ EIL P r m + B := by
    intro M
    rcases le_total M m with hMm | hmM
    · have : EIL P r M ≤ EIL P r m := by
        rw [hEIL, hEIL]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMm)
          (fun n _ _ => mul_nonneg (by positivity) (ha0 n))
      linarith
    · set X := EIL P r M - EIL P r m with hXdef
      have hX0 : 0 ≤ X := by
        rw [hXdef, hEIL, hEIL, ← Finset.sum_range_add_sum_Ico _ hmM]
        have : 0 ≤ ∑ n ∈ Finset.Ico m M, 1 / ((n : ℝ) + 1) * a n :=
          Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (ha0 n)
        linarith
      suffices X ≤ B by linarith
      rcases hX0.lt_or_eq with hXpos | hXz
      · -- `X > 0`: every minimiser is at most `K / X`
        have hle : ∀ θ ∈ phiMinimizers P c, θ ≤ K / X := by
          intro θ hθ
          rw [le_div_iff₀ hXpos, mul_comm]
          exact htail M hmM θ hθ
        by_cases hne : (phiMinimizers P c).Nonempty
        · have hbdd : BddAbove (phiMinimizers P c) := ⟨K / X, hle⟩
          have hϑ := hϑpos hne hbdd
          have hsup : sSup (phiMinimizers P c) ≤ K / X := csSup_le hne hle
          rw [hBK]
          simp only [varthetaInv, if_pos (And.intro hne hbdd)]
          rw [le_div_iff₀ hXpos] at hsup
          rw [← div_eq_mul_inv, le_div_iff₀ hϑ]
          linarith
        · -- no minimiser: `D ≥ r` a.s., so all Kingman terms vanish
          exfalso
          have hae : ∀ᵐ x : ℝ≥0 ∂P.law, r ≤ (x : ℝ) := by
            by_contra hcon
            exact hne (minimizer_exists P c hcon)
          have haeμ : ∀ᵐ d ∂μ, ∀ i, r ≤ (d i : ℝ) := by
            rw [ae_all_iff]
            intro i
            have hmap : μ.map (fun d : DemandPath => d i) = P.law := by
              rw [hμ, demandPathLaw]; exact Measure.infinitePi_map_eval _ i
            have hm : MeasurableSet {x : ℝ≥0 | r ≤ (x : ℝ)} :=
              measurableSet_le measurable_const (by fun_prop)
            rw [← hmap] at hae
            exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hae
          have hazero : ∀ n, a n = 0 := by
            intro n
            apply integral_eq_zero_of_ae
            filter_upwards [haeμ] with d hd
            simp only [Pi.zero_apply]
            apply max_eq_right
            have : ∑ _i ∈ Finset.range (n + 1), r ≤ ∑ i ∈ Finset.range (n + 1), (d i : ℝ) :=
              Finset.sum_le_sum fun i _ => hd i
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
            push_cast at this
            linarith
          have : X = 0 := by
            rw [hXdef, hEIL, hEIL]
            simp [hazero]
          linarith
      · rw [← hXz]; exact hB0
  rw [EIinf_eq_iSup P r hr0.1]
  refine iSup_le fun M => ?_
  rw [← ENNReal.ofReal_add (hEILnn m) hB0]
  exact ENNReal.ofReal_le_ofReal (hfinal M)
