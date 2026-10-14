-- Prove2me | solution 1 for MDPFinance.TerminalWealth.exponential_utility_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:00:52.313641+00:00
-- url     : https://prove2.me/submissions/d2ab3bea-509b-48dd-954e-a0444d5c92dd

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_ExpAuxiliary

open MeasureTheory ProbabilityTheory


namespace MDPFinance.TerminalWealth

section Minim
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def twNullSp (μ : Measure Ω) (R : Ω → Fin d → ℝ) : Submodule ℝ (Fin d → ℝ) where
  carrier := {a | ∀ᵐ ω ∂μ, ∑ k, a k * R ω k = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    filter_upwards [ha, hb] with ω h1 h2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Filter.Eventually.of_forall (fun ω => by simp)
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    filter_upwards [ha] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h, mul_zero]

lemma tw_sum_meas (R : Ω → Fin d → ℝ) (hR : Measurable R) (u : Fin d → ℝ) :
    Measurable (fun ω => ∑ k, u k * R ω k) := by
  fun_prop

lemma tw_phi_pos (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R) (u : Fin d → ℝ)
    (hu : u ∉ twNullSp μ R) :
    0 < ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := by
  have hm := tw_sum_meas R hR u
  have hint : Integrable (fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (measurable_const.min (hm.neg.max measurable_const)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := le_max_right (-(∑ k, u k * R ω k)) 0
        have : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one this
        linarith
      · exact min_le_left _ _
  have hnn : (0 : Ω → ℝ) ≤ fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0) :=
    fun ω => le_min zero_le_one (le_max_right _ _)
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsupp : Function.support (fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0)) =
      {ω | ∑ k, u k * R ω k < 0} := by
    ext ω
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      apply h
      rw [max_eq_right (by linarith), min_eq_right zero_le_one]
    · intro h h0
      rcases min_choice (1:ℝ) (max (-(∑ k, u k * R ω k)) 0) with h1 | h1
      · rw [h1] at h0; norm_num at h0
      · rw [h1, max_eq_left (by linarith)] at h0; linarith
  rw [hsupp]
  by_contra h0
  push_neg at h0
  have h0' : μ {ω | ∑ k, u k * R ω k < 0} = 0 := nonpos_iff_eq_zero.mp h0
  have hge : ∀ᵐ ω ∂μ, 0 ≤ ∑ k, u k * R ω k := by
    rw [ae_iff]; simpa using h0'
  have hpos : μ {ω | 0 < ∑ k, u k * R ω k} = 0 := by
    by_contra hp
    exact hNA ⟨u, hge, pos_iff_ne_zero.mpr hp⟩
  have hle : ∀ᵐ ω ∂μ, ∑ k, u k * R ω k ≤ 0 := by
    rw [ae_iff]; simpa using hpos
  apply hu
  show ∀ᵐ ω ∂μ, ∑ k, u k * R ω k = 0
  filter_upwards [hge, hle] with ω h1 h2
  linarith

lemma tw_phi_cont (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) :
    Continuous (fun u : Fin d → ℝ => ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ) := by
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro u
    exact (measurable_const.min ((tw_sum_meas R hR u).neg.max measurable_const)).aestronglyMeasurable
  · intro u
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_right (-(∑ k, u k * R ω k)) 0
      have : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one this
      linarith
    · exact min_le_left _ _
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    fun_prop

lemma tw_pointwise (t v : ℝ) (ht : 0 ≤ t) :
    t * min 1 (max (-v) 0) ≤ Real.exp (t * (-v)) := by
  have h1 : t * min 1 (max (-v) 0) ≤ t * max (-v) 0 :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) ht
  have h2 := Real.add_one_le_exp (t * (-v))
  have h3 := Real.exp_pos (t * (-v))
  rcases le_total (-v) 0 with h | h
  · rw [max_eq_right h] at h1 ⊢; linarith
  · rw [max_eq_left h] at h1 ⊢; linarith

lemma tw_bdd (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R) (C : Submodule ℝ (Fin d → ℝ))
    (hC : Disjoint (twNullSp μ R) C) (b : ℝ) (hb : b < 0) :
    ∃ ρ : ℝ, ∀ c ∈ C, (∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, c k * R ω k)) ∂μ) ≤ 1 →
      ‖c‖ ≤ ρ := by
  set S : Set (Fin d → ℝ) := (C : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1 with hS
  have hSc : IsCompact S := (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional C)
  have hnorm : ∀ c ∈ C, c ≠ 0 → ‖c‖⁻¹ • c ∈ S := by
    intro c hc hc0
    refine ⟨C.smul_mem _ hc, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc0)]
  rcases S.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, fun c hc _ => ?_⟩
    by_contra h
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact h le_rfl
    have := hnorm c hc hc0
    rw [hE] at this; exact this
  obtain ⟨u0, hu0S, hu0⟩ := hSc.exists_isMinOn hne (tw_phi_cont μ R hR).continuousOn
  set η := ∫ ω, min 1 (max (-(∑ k, u0 k * R ω k)) 0) ∂μ with hη
  have hηpos : 0 < η := by
    apply tw_phi_pos μ R hR hNA u0
    intro hmem
    have : u0 = 0 := (Submodule.disjoint_def.mp hC) u0 hmem hu0S.1
    have h1 := hu0S.2
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at h1
    norm_num at h1
  refine ⟨2 / ((-b) * η), fun c hc hf => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hpos' : 0 < (-b) * η := mul_pos (by linarith) hηpos
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlt
    have : 0 < 2 / ((-b) * η) := div_pos two_pos hpos'
    linarith
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  set u := ‖c‖⁻¹ • c with hu
  have huS := hnorm c hc hc0
  have hφu : η ≤ ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := hu0 huS
  have hsum : ∀ ω, ∑ k, c k * R ω k = ‖c‖ * ∑ k, u k * R ω k := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hu, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hmu := tw_sum_meas R hR u
  have hint : Integrable (fun ω => ((-b) * ‖c‖) * min 1 (max (-(∑ k, u k * R ω k)) 0)) μ := by
    refine (integrable_const ((-b) * ‖c‖)).mono' ?_ ?_
    · exact (measurable_const.mul (measurable_const.min (hmu.neg.max measurable_const))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have hnn : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one (le_max_right _ _)
      have hle1 : min 1 (max (-(∑ k, u k * R ω k)) 0) ≤ 1 := min_le_left _ _
      have hbc : 0 ≤ (-b) * ‖c‖ := mul_nonneg (by linarith) hcn.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbc hnn)]
      nlinarith
  have hlow : ENNReal.ofReal (∫ ω, ((-b) * ‖c‖) * min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, c k * R ω k)) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ω => mul_nonneg (mul_nonneg (by linarith) hcn.le)
        (le_min zero_le_one (le_max_right _ _))))]
    refine lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_)
    rw [hsum ω]
    have := tw_pointwise ((-b) * ‖c‖) (∑ k, u k * R ω k) (mul_nonneg (by linarith) hcn.le)
    convert this using 2
    ring
  rw [integral_const_mul] at hlow
  have hbig : 1 < (-b) * ‖c‖ * ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := by
    have h1 : 2 < (-b) * η * ‖c‖ := by
      rw [div_lt_iff₀ hpos'] at hlt; linarith
    have h2 : (-b) * η * ‖c‖ ≤ (-b) * ‖c‖ * ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := by
      have : 0 ≤ (-b) * ‖c‖ := mul_nonneg (by linarith) hcn.le
      nlinarith
    linarith
  have : (1 : ENNReal) < ENNReal.ofReal ((-b) * ‖c‖ * ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hbig
  exact absurd (lt_of_lt_of_le this (hlow.trans hf)) (lt_irrefl _)

lemma tw_lsc (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (b : ℝ) :
    LowerSemicontinuous (fun a : Fin d → ℝ =>
      ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, a k * R ω k)) ∂μ) := by
  have heq : (fun a : Fin d → ℝ => ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, a k * R ω k)) ∂μ) =
      fun a => ⨆ M : ℕ, ENNReal.ofReal
        (∫ ω, min (M : ℝ) (Real.exp (b * ∑ k, a k * R ω k)) ∂μ) := by
    funext a
    have hm : Measurable (fun ω => b * ∑ k, a k * R ω k) := (tw_sum_meas R hR a).const_mul b
    have hint : ∀ M : ℕ, Integrable (fun ω => min (M : ℝ) (Real.exp (b * ∑ k, a k * R ω k))) μ := by
      intro M
      refine (integrable_const (M : ℝ)).mono' ?_ ?_
      · exact (measurable_const.min (Real.measurable_exp.comp hm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg M) (Real.exp_pos _).le)]
        exact min_le_left _ _
    simp_rw [fun M : ℕ => ofReal_integral_eq_lintegral_ofReal (hint M)
      (Filter.Eventually.of_forall (fun ω => le_min (Nat.cast_nonneg M) (Real.exp_pos _).le))]
    rw [← lintegral_iSup]
    · congr 1
      funext ω
      apply le_antisymm
      · obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (b * ∑ k, a k * R ω k))
        refine le_trans ?_ (le_iSup _ M)
        rw [min_eq_right hM]
      · exact iSup_le (fun M => ENNReal.ofReal_le_ofReal (min_le_right _ _))
    · intro M
      exact (measurable_const.min (Real.measurable_exp.comp hm)).ennreal_ofReal
    · intro M N hMN ω
      exact ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hMN))
  rw [heq]
  refine lowerSemicontinuous_iSup (fun M => Continuous.lowerSemicontinuous ?_)
  refine ENNReal.continuous_ofReal.comp ?_
  refine continuous_of_dominated (bound := fun _ => (M : ℝ)) ?_ ?_ (integrable_const _) ?_
  · intro a
    exact (measurable_const.min (Real.measurable_exp.comp
      ((tw_sum_meas R hR a).const_mul b))).aestronglyMeasurable
  · intro a
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg M) (Real.exp_pos _).le)]
    exact min_le_left _ _
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    fun_prop

lemma tw_exists_min (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R) (b : ℝ) (hb : b < 0) :
    ∃ a : Fin d → ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, a k * R ω k)) ∂μ =
      ⨅ a : Fin d → ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, a k * R ω k)) ∂μ := by
  set f := fun a : Fin d → ℝ => ∫⁻ ω, ENNReal.ofReal (Real.exp (b * ∑ k, a k * R ω k)) ∂μ
    with hfdef
  obtain ⟨C, hC⟩ := (twNullSp μ R).exists_isCompl
  obtain ⟨ρ, hρ⟩ := tw_bdd μ R hR hNA C hC.disjoint b hb
  set K : Set (Fin d → ℝ) := (C : Set (Fin d → ℝ)) ∩ Metric.closedBall 0 (max ρ 0)
  have hK : IsCompact K :=
    (isCompact_closedBall 0 (max ρ 0)).inter_left (Submodule.closed_of_finiteDimensional C)
  have h0K : (0 : Fin d → ℝ) ∈ K := ⟨C.zero_mem, by simp⟩
  obtain ⟨a0, ha0K, ha0⟩ := (tw_lsc μ R hR b).lowerSemicontinuousOn K |>.exists_isMinOn
    ⟨0, h0K⟩ hK
  have hf0 : f 0 = 1 := by
    simp [f]
  refine ⟨a0, le_antisymm (le_iInf fun a => ?_) (iInf_le _ _)⟩
  have hmem : a ∈ twNullSp μ R ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.mp hmem
  have hfa : f a = f c := by
    simp only [f]
    apply lintegral_congr_ae
    filter_upwards [hl] with ω hω
    rw [← hlc]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hω, zero_add]
  show f a0 ≤ f a
  rw [hfa]
  by_cases hc1 : f c ≤ 1
  · have : c ∈ K := ⟨hc, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (hρ c hc hc1).trans (le_max_left _ _)⟩
    exact ha0 this
  · push_neg at hc1
    exact (ha0 h0K).trans (hf0.le.trans hc1.le)

end Minim

section Multi
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def twW (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) : ℕ → ℕ → ℝ → (ℕ → Fin d → ℝ) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, r => twW i π k (n + 1) ((1 + i (n + 1)) * (x + ∑ j, π n x j * r (n + 1) j)) r

lemma tw_tw_eq (M : TerminalWealthMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ) (x : ℝ)
    (ω : Ω) : M.terminalWealth π k n x ω = twW M.i π k n x (fun j => M.R j ω) := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih => rw [TerminalWealthMarket.terminalWealth, twW]; exact ih _ _

lemma twW_congr (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ) (x : ℝ)
    (r r' : ℕ → Fin d → ℝ) (h : ∀ j, n < j → j ≤ n + k → r j = r' j) :
    twW i π k n x r = twW i π k n x r' := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    rw [twW, twW, h (n + 1) (by omega) (by omega)]
    exact ih _ _ (fun j h1 h2 => h j (by omega) (by omega))

lemma twW_meas (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ)
    (hπ : ∀ j, n ≤ j → j < n + k → Measurable (π j)) :
    Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) => twW i π k n p.1 p.2) := by
  induction k generalizing n with
  | zero => exact measurable_fst
  | succ k ih =>
    have hπn : Measurable (π n) := hπ n le_rfl (by omega)
    have hT : Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) =>
        ((1 + i (n + 1)) * (p.1 + ∑ j, π n p.1 j * p.2 (n + 1) j), p.2)) := by
      fun_prop
    exact (ih (n + 1) (fun j h1 h2 => hπ j (by omega) (by omega))).comp hT

lemma tw_lintegral_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y μ) (H : α × β → ENNReal) (hH : Measurable H) :
    ∫⁻ ω, H (X ω, Y ω) ∂μ = ∫⁻ ω, ∫⁻ ω', H (X ω, Y ω') ∂μ ∂μ := by
  have h1 : ∫⁻ ω, H (X ω, Y ω) ∂μ = ∫⁻ p, H p ∂(μ.map (fun ω => (X ω, Y ω))) :=
    (lintegral_map hH (hX.prodMk hY)).symm
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
    lintegral_prod _ hH.aemeasurable, lintegral_map (hH.lintegral_prod_right') hX]
  congr 1
  funext ω
  exact lintegral_map (hH.comp measurable_prodMk_left) hY

noncomputable def twJ (M : TerminalWealthMarket Ω d) (γ : ℝ) (π : ℕ → ℝ → (Fin d → ℝ))
    (m : ℕ) (y : ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * M.terminalWealth π (M.N - m) m y ω)) ∂M.measIP

lemma twJ_decomp (M : TerminalWealthMarket Ω d) (γ : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (m : ℕ)
    (hm : m < M.N) (hπ : ∀ j, m ≤ j → j < M.N → Measurable (π j)) (y : ℝ) :
    twJ M γ π m y = ∫⁻ ω, twJ M γ π (m + 1)
      ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ∂M.measIP := by
  haveI := M.isProb
  set f : Fin M.N → Ω → (Fin d → ℝ) := fun j => M.R (j.val + 1) with hf
  have hfm : ∀ j, Measurable (f j) := fun j => M.hR_meas _ (by omega) (by omega)
  set S : Finset (Fin M.N) := {⟨m, hm⟩} with hS
  set T : Finset (Fin M.N) := Finset.univ.filter (fun j : Fin M.N => m < j.val) with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hS, Finset.mem_singleton] at ha
    rw [hT, Finset.mem_filter] at hb
    rw [ha] at hb
    exact lt_irrefl _ hb.2
  have hind := M.hR_indep.indepFun_finset S T hST hfm
  have hmS : (⟨m, hm⟩ : Fin M.N) ∈ S := Finset.mem_singleton_self _
  have hind2 := hind.comp (measurable_pi_apply (⟨⟨m, hm⟩, hmS⟩ : S)) measurable_id
  have hTmem : ∀ j : Fin M.N, m < j.val → j ∈ T := fun j hj => by
    rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
  let ext : (T → Fin d → ℝ) → (ℕ → Fin d → ℝ) := fun v j =>
    if h : j - 1 < M.N ∧ m < j - 1 then v ⟨⟨j - 1, h.1⟩, hTmem _ h.2⟩ else 0
  have hext_meas : Measurable ext := by
    refine measurable_pi_lambda _ (fun j => ?_)
    by_cases h : j - 1 < M.N ∧ m < j - 1
    · simp only [ext, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext, dif_neg h]; exact measurable_const
  set Y : Ω → (T → Fin d → ℝ) := fun ω (j : T) => f j ω with hY
  have hYm : Measurable Y := measurable_pi_lambda _ (fun j => hfm j)
  have hext : ∀ ω j, m + 1 < j → j ≤ M.N → ext (Y ω) j = M.R j ω := by
    intro ω j h1 h2
    have h : j - 1 < M.N ∧ m < j - 1 := ⟨by omega, by omega⟩
    simp only [ext, dif_pos h, hY, hf]
    congr 1; omega
  have hk : M.N - m = (M.N - (m + 1)) + 1 := by omega
  set k := M.N - (m + 1) with hkdef
  let H : (Fin d → ℝ) × (T → Fin d → ℝ) → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (-γ * twW M.i π k (m + 1)
      ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * p.1 j)) (ext p.2)))
  have hHm : Measurable H := by
    have h1 := twW_meas M.i π k (m + 1) (fun j h1 h2 => hπ j (by omega) (by omega))
    have h2 : Measurable (fun p : (Fin d → ℝ) × (T → Fin d → ℝ) =>
        ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * p.1 j), ext p.2)) := by
      refine Measurable.prodMk ?_ (hext_meas.comp measurable_snd)
      fun_prop
    exact (Real.measurable_exp.comp ((h1.comp h2).const_mul (-γ))).ennreal_ofReal
  have hX : Measurable (fun ω => (fun ω (i : S) => f i ω) ω ⟨⟨m, hm⟩, hmS⟩) :=
    (measurable_pi_apply _).comp (measurable_pi_lambda _ (fun j => hfm j))
  have key := tw_lintegral_indep M.measIP _ Y hX hYm hind2 H hHm
  unfold twJ
  rw [hk]
  have eL : ∀ ω, ENNReal.ofReal (Real.exp (-γ * M.terminalWealth π (k + 1) m y ω)) =
      H ((fun ω (i : S) => f i ω) ω ⟨⟨m, hm⟩, hmS⟩, Y ω) := by
    intro ω
    simp only [H]
    rw [tw_tw_eq, twW]
    congr 3
    apply twW_congr
    intro j h1 h2
    exact (hext ω j h1 (by omega)).symm
  simp_rw [eL]
  rw [key]
  congr 1
  funext ω
  have hMN : M.N - (m + 1) = k := rfl
  rw [hMN]
  congr 1
  funext ω'
  simp only [H]
  rw [tw_tw_eq]
  congr 3
  apply twW_congr
  intro j h1 h2
  exact hext ω' j h1 (by omega)

end Multi

section Final
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma tw_S0_pos (M : TerminalWealthMarket Ω d) (m : ℕ) (hm : m ≤ M.N) : 0 < M.S0 m := by
  unfold TerminalWealthMarket.S0
  exact Finset.prod_pos (fun j hj => M.hi_pos (j + 1) (by omega)
    (by rw [Finset.mem_range] at hj; omega))

lemma tw_c_succ (M : TerminalWealthMarket Ω d) (m : ℕ) (hm : m < M.N) :
    M.S0 M.N / M.S0 (m + 1) * (1 + M.i (m + 1)) = M.S0 M.N / M.S0 m := by
  have h1 : M.S0 (m + 1) = M.S0 m * (1 + M.i (m + 1)) := by
    unfold TerminalWealthMarket.S0; rw [Finset.prod_range_succ]
  have h2 := tw_S0_pos M m hm.le
  have h3 := M.hi_pos (m + 1) (by omega) (by omega)
  rw [h1]; field_simp

lemma tw_alg (μ : Measure Ω) (R1 : Ω → Fin d → ℝ) (hR1 : Measurable R1) (γ cm cm1 ip y : ℝ)
    (hc : cm1 * ip = cm) (a : Fin d → ℝ) (P : ENNReal) :
    ∫⁻ ω, P * ENNReal.ofReal (Real.exp (-γ * cm1 * (ip * (y + ∑ j, a j * R1 ω j)))) ∂μ =
      P * ENNReal.ofReal (Real.exp (-γ * cm * y)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * cm * ∑ j, a j * R1 ω j)) ∂μ := by
  have e : ∀ ω, P * ENNReal.ofReal (Real.exp (-γ * cm1 * (ip * (y + ∑ j, a j * R1 ω j)))) =
      P * ENNReal.ofReal (Real.exp (-γ * cm * y)) *
        ENNReal.ofReal (Real.exp (-γ * cm * ∑ j, a j * R1 ω j)) := by
    intro ω
    rw [mul_assoc P (ENNReal.ofReal _) (ENNReal.ofReal _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← hc]
    congr 3; ring
  simp_rw [e]
  rw [lintegral_const_mul]
  exact (Real.measurable_exp.comp ((tw_sum_meas R1 hR1 a).const_mul _)).ennreal_ofReal

noncomputable def twWk (M : TerminalWealthMarket Ω d) (γ : ℝ) (k : ℕ) : ENNReal :=
  ⨅ a : Fin d → ℝ, ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-γ * (M.S0 M.N / M.S0 k) * ∑ j, a j * M.R (k + 1) ω j)) ∂M.measIP

lemma twJ_N (M : TerminalWealthMarket Ω d) (γ : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (y : ℝ) :
    twJ M γ π M.N y = ENNReal.ofReal (Real.exp (-γ * y)) := by
  haveI := M.isProb
  unfold twJ
  rw [Nat.sub_self]
  simp [TerminalWealthMarket.terminalWealth]

lemma twJ_lower (M : TerminalWealthMarket Ω d) (γ : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ)
    (hπ : ∀ j, n ≤ j → j < M.N → Measurable (π j)) :
    ∀ t m, m + t = M.N → n ≤ m → ∀ y,
      (∏ k ∈ Finset.Ico m M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 m) * y)) ≤ twJ M γ π m y := by
  intro t
  induction t with
  | zero =>
    intro m hm _ y
    simp only [add_zero] at hm
    subst hm
    rw [twJ_N, Finset.Ico_self, Finset.prod_empty, one_mul,
      div_self (tw_S0_pos M _ le_rfl).ne', mul_one]
  | succ t ih =>
    intro m hm hnm y
    have hmN : m < M.N := by omega
    rw [twJ_decomp M γ π m hmN (fun j h1 h2 => hπ j (by omega) h2) y]
    have step : ∫⁻ ω, (∏ k ∈ Finset.Ico (m + 1) M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 (m + 1)) *
          ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)))) ∂M.measIP ≤
        ∫⁻ ω, twJ M γ π (m + 1)
          ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ∂M.measIP :=
      lintegral_mono (fun ω => ih (m + 1) (by omega) (by omega) _)
    rw [tw_alg M.measIP (M.R (m + 1)) (M.hR_meas _ (by omega) (by omega)) γ
      (M.S0 M.N / M.S0 m) _ _ y (tw_c_succ M m hmN)] at step
    refine le_trans ?_ step
    rw [Finset.prod_eq_prod_Ico_succ_bot hmN]
    have hw : twWk M γ m ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 m) *
        ∑ j, π m y j * M.R (m + 1) ω j)) ∂M.measIP := iInf_le _ (π m y)
    calc twWk M γ m * (∏ k ∈ Finset.Ico (m + 1) M.N, twWk M γ k) *
          ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 m) * y))
        = (∏ k ∈ Finset.Ico (m + 1) M.N, twWk M γ k) *
          ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 m) * y)) * twWk M γ m := by ring
      _ ≤ _ := mul_le_mul' le_rfl hw

lemma twJ_eq (M : TerminalWealthMarket Ω d) (γ : ℝ) (astar : ℕ → Fin d → ℝ)
    (hast : ∀ k, k < M.N → ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-γ * (M.S0 M.N / M.S0 k) * ∑ j, astar k j * M.R (k + 1) ω j)) ∂M.measIP =
        twWk M γ k) :
    ∀ t m, m + t = M.N → ∀ y,
      twJ M γ (fun k _ => astar k) m y = (∏ k ∈ Finset.Ico m M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 m) * y)) := by
  intro t
  induction t with
  | zero =>
    intro m hm y
    simp only [add_zero] at hm
    subst hm
    rw [twJ_N, Finset.Ico_self, Finset.prod_empty, one_mul,
      div_self (tw_S0_pos M _ le_rfl).ne', mul_one]
  | succ t ih =>
    intro m hm y
    have hmN : m < M.N := by omega
    rw [twJ_decomp M γ _ m hmN (fun j _ _ => measurable_const) y]
    simp_rw [ih (m + 1) (by omega)]
    rw [tw_alg M.measIP (M.R (m + 1)) (M.hR_meas _ (by omega) (by omega)) γ
      (M.S0 M.N / M.S0 m) _ _ y (tw_c_succ M m hmN), hast m hmN,
      Finset.prod_eq_prod_Ico_succ_bot hmN]
    ring

lemma tw_toENNReal (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_eq_right.mpr (by exact_mod_cast h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [sup_eq_left.mpr (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t),
      EReal.toReal_coe]

theorem exp_core (M : TerminalWealthMarket Ω d) (γ : ℝ) (hγ : 0 < γ) (hdomU : M.domU = Set.univ)
    (hU : ∀ x : ℝ, M.U x = -Real.exp (-γ * x) / γ) :
    (∀ n ≤ M.N, ∀ x : ℝ,
        M.V n x = ((((-1 / γ) * ∏ k ∈ Finset.Ico n M.N, M.vExp γ k) *
          Real.exp (-γ * (M.S0 M.N / M.S0 n) * x) : ℝ) : EReal)) ∧
      (∃ astar : ℕ → (Fin d → ℝ),
        (∀ n < M.N,
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) *
            ∑ k, astar n k * M.R (n + 1) ω k)) ∂M.measIP).toReal = M.vExp γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x : ℝ, fstar n x = astar n) ∧
          ∀ x : ℝ, M.Vpi fstar 0 x = M.V 0 x) := by
  haveI := M.isProb
  have hex : ∀ n, n < M.N → ∃ a : Fin d → ℝ, ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-γ * (M.S0 M.N / M.S0 n) * ∑ j, a j * M.R (n + 1) ω j)) ∂M.measIP =
        twWk M γ n := by
    intro n hn
    have hc := div_pos (tw_S0_pos M M.N le_rfl) (tw_S0_pos M n hn.le)
    exact tw_exists_min M.measIP (M.R (n + 1)) (M.hR_meas _ (by omega) (by omega))
      (M.hNA _ (by omega) (by omega)) (-γ * (M.S0 M.N / M.S0 n)) (by nlinarith)
  choose! astar hastar using hex
  have hwk_le : ∀ k, twWk M γ k ≤ 1 := by
    intro k
    refine iInf_le_of_le 0 ?_
    simp
  have hwk_eq : ∀ k, twWk M γ k = ENNReal.ofReal (M.vExp γ k) := by
    intro k
    change twWk M γ k = ENNReal.ofReal (twWk M γ k).toReal
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hwk_le k))]
  have hVpi : ∀ π n x, M.Vpi π n x =
      -((ENNReal.ofReal γ⁻¹ * twJ M γ π n x : ENNReal) : EReal) := by
    intro π n x
    unfold TerminalWealthMarket.Vpi erealIntegral twJ
    have e1 : ∀ ω, ((M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal = 0 := by
      intro ω
      rw [tw_toENNReal, hU]
      apply ENNReal.ofReal_of_nonpos
      have := Real.exp_pos (-γ * M.terminalWealth π (M.N - n) n x ω)
      have : 0 ≤ Real.exp (-γ * M.terminalWealth π (M.N - n) n x ω) / γ := by positivity
      rw [neg_div]; linarith
    have e2 : ∀ ω, (-(M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal =
        ENNReal.ofReal γ⁻¹ *
          ENNReal.ofReal (Real.exp (-γ * M.terminalWealth π (M.N - n) n x ω)) := by
      intro ω
      rw [← EReal.coe_neg, tw_toENNReal, hU, ← ENNReal.ofReal_mul (inv_nonneg.mpr hγ.le)]
      congr 1
      field_simp
    simp_rw [e1, e2]
    rw [lintegral_zero, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp
  set fstar : ℕ → ℝ → (Fin d → ℝ) := fun k _ => astar k with hfstar
  have hadm : ∀ n, M.IsAdmissible n fstar := by
    intro n k _ _
    refine ⟨fun x _ => ?_, measurable_const⟩
    show ∀ᵐ ω ∂M.measIP, _ ∈ M.domU
    rw [hdomU]
    exact Filter.Eventually.of_forall (fun ω => Set.mem_univ _)
  have hV : ∀ n ≤ M.N, ∀ x, M.V n x = -((ENNReal.ofReal γ⁻¹ *
      ((∏ k ∈ Finset.Ico n M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) * x))) : ENNReal) : EReal) ∧
      M.Vpi fstar n x = -((ENNReal.ofReal γ⁻¹ *
      ((∏ k ∈ Finset.Ico n M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) * x))) : ENNReal) : EReal) := by
    intro n hn x
    have hfs : M.Vpi fstar n x = -((ENNReal.ofReal γ⁻¹ *
        ((∏ k ∈ Finset.Ico n M.N, twWk M γ k) *
          ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) * x))) : ENNReal) : EReal) := by
      rw [hVpi, twJ_eq M γ astar hastar (M.N - n) n (by omega) x]
    refine ⟨le_antisymm ?_ ?_, hfs⟩
    · unfold TerminalWealthMarket.V
      refine iSup₂_le (fun π hπ => ?_)
      rw [hVpi, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact mul_le_mul' le_rfl (twJ_lower M γ π n (fun j h1 h2 => (hπ j h1 h2).2)
        (M.N - n) n (by omega) le_rfl x)
    · unfold TerminalWealthMarket.V
      rw [← hfs]
      exact le_iSup₂ (f := fun π (_ : π ∈ {π | M.IsAdmissible n π}) => M.Vpi π n x) fstar (hadm n)
  have hreal : ∀ n x, -((ENNReal.ofReal γ⁻¹ *
      ((∏ k ∈ Finset.Ico n M.N, twWk M γ k) *
        ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) * x))) : ENNReal) : EReal) =
      ((((-1 / γ) * ∏ k ∈ Finset.Ico n M.N, M.vExp γ k) *
          Real.exp (-γ * (M.S0 M.N / M.S0 n) * x) : ℝ) : EReal) := by
    intro n x
    have hv : ∀ k, 0 ≤ M.vExp γ k := fun k => ENNReal.toReal_nonneg
    have hp : 0 ≤ ∏ k ∈ Finset.Ico n M.N, M.vExp γ k :=
      Finset.prod_nonneg (fun k _ => hv k)
    simp_rw [hwk_eq]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => hv k),
      ← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hγ.le),
      EReal.coe_ennreal_ofReal, max_eq_left (by positivity), ← EReal.coe_neg]
    congr 1
    ring
  refine ⟨fun n hn x => by rw [(hV n hn x).1, hreal], astar, fun n hn => ?_, fstar, hadm 0,
    fun n _ x => rfl, fun x => by rw [(hV 0 (Nat.zero_le _) x).1, (hV 0 (Nat.zero_le _) x).2]⟩
  rw [hastar n hn]
  rfl

end Final

end MDPFinance.TerminalWealth

open MDPFinance.TerminalWealth


theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (γ : ℝ) (hγ : 0 < γ) (hdomU : M.domU = Set.univ)
    (hU : ∀ x : ℝ, M.U x = -Real.exp (-γ * x) / γ) :
    (∀ n ≤ M.N, ∀ x : ℝ,
        M.V n x = ((((-1 / γ) * ∏ k ∈ Finset.Ico n M.N, M.vExp γ k) *
          Real.exp (-γ * (M.S0 M.N / M.S0 n) * x) : ℝ) : EReal)) ∧
      (∃ astar : ℕ → (Fin d → ℝ),
        (∀ n < M.N,
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) *
            ∑ k, astar n k * M.R (n + 1) ω k)) ∂M.measIP).toReal = M.vExp γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x : ℝ, fstar n x = astar n) ∧
          ∀ x : ℝ, M.Vpi fstar 0 x = M.V 0 x) := by
  exact exp_core M γ hγ hdomU hU
