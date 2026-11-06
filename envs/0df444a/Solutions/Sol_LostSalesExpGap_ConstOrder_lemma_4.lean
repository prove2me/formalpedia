-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:26:01.447616+00:00
-- url     : https://prove2.me/submissions/594856df-f6e6-434c-8944-477a0a14588a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_eq_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_2
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapL4

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

lemma finiteInventory_le (d : DemandPath) (x : ℝ) (m : ℕ) :
    finiteInventory d x m ≤ m * |x| := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc ∑ i ∈ Finset.range k, (x - (d i : ℝ)) ≤ ∑ i ∈ Finset.range k, |x| :=
        Finset.sum_le_sum fun i _ => by
          have := NNReal.coe_nonneg (d i); have := le_abs_self x; linarith
    _ = k * |x| := by simp
    _ ≤ m * |x| := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hk') (abs_nonneg x)

lemma finiteInventory_lip (d : DemandPath) (x y : ℝ) (m : ℕ) :
    finiteInventory d x m ≤ finiteInventory d y m + m * |x - y| := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : ∑ i ∈ Finset.range k, (x - (d i : ℝ)) =
      ∑ i ∈ Finset.range k, (y - (d i : ℝ)) + k * (x - y) := by
    rw [show (k : ℝ) * (x - y) = ∑ _i ∈ Finset.range k, (x - y) by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul], ← Finset.sum_add_distrib]
    congr 1; funext i; ring
  rw [h1]
  have h2 : (k : ℝ) * (x - y) ≤ m * |x - y| := by
    calc (k : ℝ) * (x - y) ≤ k * |x - y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg k)
      _ ≤ m * |x - y| := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') (abs_nonneg _)
  have h3 : ∑ i ∈ Finset.range k, (y - (d i : ℝ)) ≤ (Finset.range (m + 1)).sup' (by simp)
      (fun k => ∑ i ∈ Finset.range k, (y - (d i : ℝ))) :=
    Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (y - (d i : ℝ))) hk
  linarith

lemma integrable_finiteInventory (P : DemandLaw) (x : ℝ) (m : ℕ) :
    Integrable (fun d => finiteInventory d x m) (demandPathLaw P) := by
  refine Integrable.of_bound (C := m * |x|)
    (measurable_finiteInventory x m).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteInventory_nonneg d x m)]
  exact finiteInventory_le d x m

lemma continuous_EIL (P : DemandLaw) (m : ℕ) : Continuous (fun x => EIL P x m) := by
  apply LipschitzWith.continuous (K := ⟨m, Nat.cast_nonneg m⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  show |EIL P x m - EIL P y m| ≤ (m : ℝ) * |x - y|
  simp only [EIL]
  rw [← integral_sub (integrable_finiteInventory P x m) (integrable_finiteInventory P y m)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ d, |finiteInventory d x m - finiteInventory d y m| ∂demandPathLaw P
      ≤ ∫ _d, (m : ℝ) * |x - y| ∂demandPathLaw P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun d => abs_nonneg _)
          (integrable_const _) (ae_of_all _ fun d => ?_)
        rw [abs_le]
        have h1 := finiteInventory_lip d x y m
        have h2 := finiteInventory_lip d y x m
        rw [abs_sub_comm y x] at h2
        constructor <;> linarith
    _ = m * |x - y| := by simp

/-- `r_m` is itself a minimizer of `C_m` over `[0, E[D]]`. -/
lemma rL_mem (P : DemandLaw) (c : Parameters) (m : ℕ) : rL P c m ∈ argminCL P c m := by
  have hm : 0 < mean P := P.positiveMean
  have hcont : Continuous (fun x => CL P c x m) := by
    unfold CL
    exact ((continuous_const.mul (continuous_EIL P m)).add continuous_const).sub
      (continuous_const.mul continuous_id)
  obtain ⟨x, hx, hxmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := mean P)).exists_isMinOn
    (Set.nonempty_Icc.mpr hm.le) hcont.continuousOn
  have hne : (argminCL P c m).Nonempty := ⟨x, hx, fun r' hr' => hxmin hr'⟩
  have hclosed : IsClosed (argminCL P c m) := by
    have : argminCL P c m = Set.Icc 0 (mean P) ∩
        ⋂ r' ∈ Set.Icc 0 (mean P), {r | CL P c r m ≤ CL P c r' m} := by
      ext r; simp [argminCL]
    rw [this]
    refine isClosed_Icc.inter (isClosed_biInter fun r' _ => ?_)
    exact isClosed_le hcont continuous_const
  exact hclosed.csInf_mem hne ⟨0, fun y hy => hy.1.1⟩

end LSExpGapL4

open LostSalesExpGap.ConstOrder LSExpGapL4 CappedBaseStock Filter Topology in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ∀ m : ℕ, 1 ≤ m → rInf P c ≤ rL P c m := by
  intro m hm
  obtain ⟨_, _, hrmem, hrlt⟩ := best_constant_exists P c hP
  obtain ⟨hK1, hK2, _⟩ := lemma_3 P c hP
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set μ := demandPathLaw P with hμ
  set r := rInf P c
  set s := rL P c m
  set mean := CappedBaseStock.mean P
  have hmean : 0 < mean := P.positiveMean
  have hr0 : 0 ≤ r := hrmem.1.1
  have hsmem : s ∈ argminCL P c m := rL_mem P c m
  have hs0 : 0 ≤ s := hsmem.1.1
  by_contra hlt
  push_neg at hlt
  have hsm : s < mean := lt_trans hlt hrlt
  -- Kingman terms
  let b : ℝ → ℕ → ℝ := fun x n => (1 / ((n : ℝ) + 1)) *
    ∫ d, max (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0 ∂μ
  let a : ℝ → ℕ → ℝ≥0∞ := fun x n => ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
    ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) ∂μ
  have hfint : ∀ x, 0 ≤ x → ∀ n : ℕ, Integrable (fun d : DemandPath =>
      max (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0) μ := by
    intro x hx n
    refine Integrable.of_bound (C := ((n : ℝ) + 1) * x) ?_ (ae_of_all _ fun d => ?_)
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
    · have hS : 0 ≤ ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) (by positivity)
  have hb0 : ∀ x, 0 ≤ x → ∀ n, 0 ≤ b x n := fun x _ n =>
    mul_nonneg (by positivity) (integral_nonneg fun _ => le_max_right _ _)
  have hab : ∀ x, 0 ≤ x → ∀ n, a x n = ENNReal.ofReal (b x n) := by
    intro x hx n
    simp only [a, b]
    rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal (hfint x hx n)
      (ae_of_all _ fun _ => le_max_right _ _)]
    congr 2; funext d
    rcases le_total 0 (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have hEIinf : ∀ x, 0 ≤ x → x < mean → EIinf P x = ∑' n, a x n := fun x hx0 hxm => hK2 x hx0 hxm
  have hEIL : ∀ x, 0 ≤ x → x ≤ mean → EIL P x m = ∑ n ∈ Finset.range m, b x n :=
    fun x hx0 hxm => hK1 x hx0 hxm m hm
  -- finiteness of E[I^r_∞] and E[I^s_∞]
  have hE0 : EIinf P 0 = 0 := by
    rw [hEIinf 0 le_rfl hmean]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    have : (fun d : DemandPath => ENNReal.ofReal (((n : ℝ) + 1) * 0 -
        ∑ i ∈ Finset.range (n + 1), (d i : ℝ))) = fun _ => 0 := by
      funext d
      apply ENNReal.ofReal_of_nonpos
      have : 0 ≤ ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by positivity
      linarith
    show a 0 n = 0
    simp only [a]
    rw [this, lintegral_zero, mul_zero]
  have hfin0 : constCost P c 0 ≠ ⊤ := by
    rw [eq_3 P c 0 le_rfl hmean, hE0, mul_zero, zero_add]
    exact ENNReal.ofReal_ne_top
  have hfinr : constCost P c r ≠ ⊤ :=
    ne_top_of_le_ne_top hfin0 (hrmem.2 0 ⟨le_rfl, hmean.le⟩)
  have hEr : EIinf P r ≠ ⊤ := by
    intro htop
    rw [eq_3 P c r hr0 hrlt, htop, ENNReal.mul_top (by simp [hh]), top_add] at hfinr
    exact hfinr rfl
  have hmono_walk : ∀ d, LostSalesConstantOrder.LargeLeadTime.supWalk s.toNNReal d ≤
      LostSalesConstantOrder.LargeLeadTime.supWalk r.toNNReal d := by
    intro d
    unfold LostSalesConstantOrder.LargeLeadTime.supWalk
    refine iSup_mono fun k => ENNReal.ofReal_le_ofReal ?_
    unfold LostSalesConstantOrder.LargeLeadTime.walk
    have : (s.toNNReal : ℝ) ≤ (r.toNNReal : ℝ) := by
      rw [Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hr0]; exact hlt.le
    have := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (α := ℝ) k)
    linarith
  have hEs : EIinf P s ≠ ⊤ := ne_top_of_le_ne_top hEr (lintegral_mono hmono_walk)
  -- real summability of the Kingman terms
  have hsumm : ∀ x, 0 ≤ x → x < mean → EIinf P x ≠ ⊤ → Summable (b x) := by
    intro x hx0 hxm hfin
    rw [hEIinf x hx0 hxm] at hfin
    have := ENNReal.summable_toReal hfin
    refine this.congr fun n => ?_
    rw [hab x hx0 n, ENNReal.toReal_ofReal (hb0 x hx0 n)]
  have hreal : ∀ x, 0 ≤ x → x < mean → EIinf P x ≠ ⊤ →
      (EIinf P x).toReal = ∑' n, b x n := by
    intro x hx0 hxm hfin
    rw [hEIinf x hx0 hxm, ENNReal.tsum_toReal_eq]
    · congr 1; funext n; rw [hab x hx0 n, ENNReal.toReal_ofReal (hb0 x hx0 n)]
    · intro n; rw [hab x hx0 n]; exact ENNReal.ofReal_ne_top
  have hSr := hsumm r hr0 hrlt hEr
  have hSs := hsumm s hs0 hsm hEs
  -- optimality inequalities
  have hopt1 := hrmem.2 s ⟨hs0, hsm.le⟩
  rw [eq_3 P c r hr0 hrlt, eq_3 P c s hs0 hsm] at hopt1
  have hopt1' : c.h * (EIinf P r).toReal + c.p * (mean - r) ≤
      c.h * (EIinf P s).toReal + c.p * (mean - s) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEs,
      ENNReal.ofReal_ne_top⟩) hopt1
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEr) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEs) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le,
      ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by nlinarith)] at this
  have hopt2 := hsmem.2 r ⟨hr0, hrlt.le⟩
  simp only [CL] at hopt2
  -- tails
  have htail : ∑' n, b r (n + m) ≤ ∑' n, b s (n + m) := by
    have e1 := hSr.sum_add_tsum_nat_add m
    have e2 := hSs.sum_add_tsum_nat_add m
    rw [hreal r hr0 hrlt hEr] at hopt1'
    rw [hreal s hs0 hsm hEs] at hopt1'
    rw [hEIL r hr0 hrlt.le, hEIL s hs0 hsm.le] at hopt2
    rw [← e1, ← e2] at hopt1'
    nlinarith
  -- termwise comparison
  let A : ℕ → Set DemandPath := fun n =>
    {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * s}
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le (by fun_prop) (by fun_prop)
  have hterm : ∀ n, b s n + (r - s) * μ.real (A n) ≤ b r n := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpt : ∀ d, max (((n : ℝ) + 1) * s - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0 +
        ((n : ℝ) + 1) * (r - s) * (A n).indicator (fun _ => (1 : ℝ)) d ≤
        max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0 := by
      intro d
      simp only [A, Set.indicator, Set.mem_setOf_eq]
      split_ifs with hd
      · rw [max_eq_left (by linarith)]
        have : ((n : ℝ) + 1) * s - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) +
            ((n : ℝ) + 1) * (r - s) * 1 =
            ((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by ring
        rw [this]; exact le_max_left _ _
      · simp only [mul_zero, add_zero]
        exact max_le_max (by nlinarith) le_rfl
    have hind : Integrable ((A n).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator (hAm n)
    have := integral_mono ((hfint s hs0 n).add (hind.const_mul (((n : ℝ) + 1) * (r - s))))
      (hfint r hr0 n) hpt
    simp only [Pi.add_apply] at this
    rw [integral_add (hfint s hs0 n) (hind.const_mul _), integral_const_mul,
      integral_indicator_const _ (hAm n), smul_eq_mul, mul_one] at this
    simp only [b]
    have h1 : (1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * (r - s) * μ.real (A n)) =
        (r - s) * μ.real (A n) := by field_simp
    rw [← h1, ← mul_add]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- hence P(A m) = 0
  have hAzero : μ.real (A m) = 0 := by
    have hsum1 : Summable (fun n => (r - s) * μ.real (A (n + m))) :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (by linarith) measureReal_nonneg)
        (fun n => by have := hterm (n + m); have := hb0 s hs0 (n + m); linarith)
        ((summable_nat_add_iff m).mpr hSr)
    have h1 : ∑' n, b s (n + m) + ∑' n, (r - s) * μ.real (A (n + m)) ≤ ∑' n, b r (n + m) := by
      rw [← Summable.tsum_add ((summable_nat_add_iff m).mpr hSs) hsum1]
      exact Summable.tsum_le_tsum (fun n => hterm (n + m))
        (((summable_nat_add_iff m).mpr hSs).add hsum1) ((summable_nat_add_iff m).mpr hSr)
    have h2 : ∑' n, (r - s) * μ.real (A (n + m)) ≤ 0 := by linarith
    have h3 : (r - s) * μ.real (A (0 + m)) ≤ ∑' n, (r - s) * μ.real (A (n + m)) :=
      hsum1.le_tsum 0 (fun n _ => mul_nonneg (by linarith) measureReal_nonneg)
    have h4 : 0 ≤ μ.real (A m) := measureReal_nonneg
    simp only [zero_add] at h3
    have : (r - s) * μ.real (A m) ≤ 0 := by linarith
    nlinarith
  -- so P(D ≤ s) = 0
  set t : Set ℝ≥0 := {x | (x : ℝ) ≤ s}
  have htm : MeasurableSet t := measurableSet_le (by fun_prop) measurable_const
  have hlaw0 : P.law t = 0 := by
    have hsub : Set.pi (↑(Finset.range (m + 1))) (fun _ => t) ⊆ A m := by
      intro d hd
      simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range] at hd
      simp only [A, Set.mem_setOf_eq]
      calc ∑ i ∈ Finset.range (m + 1), (d i : ℝ) ≤ ∑ _i ∈ Finset.range (m + 1), s :=
            Finset.sum_le_sum fun i hi => hd i (Finset.mem_range.mp hi)
        _ = ((m : ℝ) + 1) * s := by simp
    have h0 : μ (A m) = 0 := by
      rw [← ofReal_measureReal (measure_ne_top _ _), hAzero, ENNReal.ofReal_zero]
    have h1 : Measure.infinitePi (fun _ : ℕ => P.law)
        (Set.pi (↑(Finset.range (m + 1))) (fun _ => t)) = 0 := measure_mono_null hsub h0
    rw [Measure.infinitePi_pi (μ := fun _ : ℕ => P.law) (s := Finset.range (m + 1))
      (t := fun _ => t) (fun _ _ => htm), Finset.prod_const, Finset.card_range] at h1
    exact pow_eq_zero_iff (Nat.succ_ne_zero m) |>.mp h1
  have hae : ∀ᵐ d ∂μ, ∀ i, s < (d i : ℝ) := by
    rw [ae_all_iff]
    intro i
    have hmap : μ.map (fun d : DemandPath => d i) = P.law := by
      rw [hμ, demandPathLaw]; exact Measure.infinitePi_map_eval _ i
    have : μ ((fun d : DemandPath => d i) ⁻¹' t) = 0 := by
      rw [← Measure.map_apply (measurable_pi_apply i) htm, hmap, hlaw0]
    rw [ae_iff]
    refine measure_mono_null (fun d hd => ?_) this
    simp only [Set.mem_setOf_eq, not_lt] at hd
    exact hd
  -- E[I^s_m] = 0 and E[I^s_∞] = 0
  have hEILs : EIL P s m = 0 := by
    unfold EIL
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with d hd
    apply le_antisymm _ (finiteInventory_nonneg d s m)
    unfold finiteInventory
    apply Finset.sup'_le
    intro k _
    exact Finset.sum_nonpos fun i _ => by linarith [hd i]
  have hEIs : EIinf P s = 0 := by
    unfold EIinf
    apply lintegral_eq_zero_of_ae_eq_zero ?_ |>.trans (by simp)
    filter_upwards [hae] with d hd
    simp only [Pi.zero_apply]
    unfold LostSalesConstantOrder.LargeLeadTime.supWalk
    apply ENNReal.iSup_eq_zero.mpr
    intro k
    apply ENNReal.ofReal_of_nonpos
    unfold LostSalesConstantOrder.LargeLeadTime.walk
    rw [Real.coe_toNNReal _ hs0]
    have : ∑ _i ∈ Finset.Icc 1 k, s ≤ ∑ i ∈ Finset.Icc 1 k, (d (i - 1) : ℝ) :=
      Finset.sum_le_sum fun i _ => (hd (i - 1)).le
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at this
    linarith
  -- C(π_s) = C_m(s) ≤ OPT ≤ C(π_r)
  let c' : Parameters := { c with L := m, leadTime_pos := hm }
  obtain ⟨hlow, -⟩ := lemma_2 P c' hP
  have hCLeq : CL P c' (rL P c' m) m = c.p * (mean - s) := by
    show CL P c s m = _
    simp only [CL, hEILs, mul_zero, zero_add]; ring
  have hOPT : OPT P c' ≤ constCost P c' r :=
    iInf_le (fun π => policyCost P c' π) (constOrderPolicy r.toNNReal)
  have hc'r : constCost P c' r = constCost P c r := by
    rw [eq_3 P c' r hr0 hrlt, eq_3 P c r hr0 hrlt]
  have hCs : constCost P c s = ENNReal.ofReal (c.p * (mean - s)) := by
    rw [eq_3 P c s hs0 hsm, hEIs, mul_zero, zero_add]
  have hsr : constCost P c s ≤ constCost P c r := by
    rw [hCs, ← hCLeq, ← hc'r]; exact hlow.trans hOPT
  have hsarg : s ∈ argminConst P c :=
    ⟨⟨hs0, hsm.le⟩, fun r' hr' => hsr.trans (hrmem.2 r' hr')⟩
  have : r ≤ s := csInf_le ⟨0, fun y hy => hy.1.1⟩ hsarg
  linarith
