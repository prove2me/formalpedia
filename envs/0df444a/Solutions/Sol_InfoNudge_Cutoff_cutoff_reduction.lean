-- Prove2me | solution 1 for InfoNudge.Cutoff.cutoff_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:57:23.324999+00:00
-- url     : https://prove2.me/submissions/f3bdc7da-bd6d-418d-b550-18caf0e1ccf2

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory InfoNudge.Cutoff Filter Topology

namespace InfoNudgeSolP12

variable {M : Params}

lemma ta_th (hS : Standing M) : 0 < ta M ∧ ta M < 1 ∧ 0 < th M ∧ th M < ta M := by
  obtain ⟨hβ0, hβ1, hδ0, hδ1, hK, _, _⟩ := hS
  have hK0 : 0 < M.β * M.δ ^ 2 * M.C := by linarith
  have ta0 : 0 < ta M := by unfold ta; exact div_pos one_pos hK0
  have ta1 : ta M < 1 := by unfold ta; rw [div_lt_one hK0]; exact hK
  have hβδ : 0 < M.β * M.δ := mul_pos hβ0 hδ0
  have f0 : 0 < (1 + M.β * M.δ) / (1 + M.δ) := div_pos (by linarith) (by linarith)
  have f1 : (1 + M.β * M.δ) / (1 + M.δ) < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith
  refine ⟨ta0, ta1, ?_, ?_⟩
  · unfold th; exact mul_pos f0 ta0
  · unfold th
    calc (1 + M.β * M.δ) / (1 + M.δ) * ta M < 1 * ta M := mul_lt_mul_of_pos_right f1 ta0
      _ = ta M := one_mul _

lemma hprob (hS : Standing M) : IsProbabilityMeasure M.P := hS.2.2.2.2.2.1

lemma ae_mem (hS : Standing M) : ∀ᵐ θ ∂M.P, θ ∈ Set.Icc (0 : ℝ) 1 :=
  mem_ae_iff.mpr hS.2.2.2.2.2.2

lemma int_mech (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) : Integrable π M.P := by
  haveI := hprob hS
  exact Integrable.of_bound hπ.1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hπ.2 θ).1, (hπ.2 θ).2])

lemma int_id (hS : Standing M) : Integrable (fun θ : ℝ => θ) M.P := by
  haveI := hprob hS
  refine Integrable.of_bound measurable_id.aestronglyMeasurable 1 ?_
  filter_upwards [ae_mem hS] with θ hθ
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hθ.1, hθ.2]

lemma int_mul (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) :
    Integrable (fun θ => θ * π θ) M.P := by
  haveI := hprob hS
  refine Integrable.of_bound (measurable_id.mul hπ.1).aestronglyMeasurable 1 ?_
  filter_upwards [ae_mem hS] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg (hπ.2 θ).1]
  nlinarith [hθ.1, hθ.2, (hπ.2 θ).1, (hπ.2 θ).2]

/-- Linearity: integral of an affine combination of `1, θ, π, θπ, ψ, θψ`. -/
lemma int_lin (hS : Standing M) {π ψ : ℝ → ℝ} (hπ : IsMechanism π) (hψ : IsMechanism ψ)
    (a b c d e f : ℝ) :
    (∫ θ, (a + b * θ + c * π θ + d * (θ * π θ) + e * ψ θ + f * (θ * ψ θ)) ∂M.P) =
      a + b * (∫ θ, θ ∂M.P) + c * (∫ θ, π θ ∂M.P) + d * (∫ θ, θ * π θ ∂M.P)
        + e * (∫ θ, ψ θ ∂M.P) + f * (∫ θ, θ * ψ θ ∂M.P) := by
  haveI := hprob hS
  have h1 := int_id hS
  have h2 := int_mech hS hπ
  have h3 := int_mul hS hπ
  have h4 := int_mech hS hψ
  have h5 := int_mul hS hψ
  rw [integral_add, integral_add, integral_add, integral_add, integral_add]
  · simp only [integral_const_mul]; simp
    exact integral_const_mul b (fun θ => θ)
  all_goals first
    | exact integrable_const _
    | exact h1.const_mul _
    | exact h2.const_mul _
    | exact h3.const_mul _
    | exact h4.const_mul _
    | exact h5.const_mul _
    | exact (((((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)).add (h3.const_mul _)).add (h4.const_mul _))
    | exact ((((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)).add (h3.const_mul _))
    | exact (((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _))
    | exact ((integrable_const _).add (h1.const_mul _))


lemma F_cdf (hS : Standing M) (x : ℝ) : F M x = ProbabilityTheory.cdf M.P x := by
  haveI := hprob hS
  rw [ProbabilityTheory.cdf_eq_real]; rfl

lemma F_mono (hS : Standing M) : Monotone (F M) := by
  intro x y h; rw [F_cdf hS, F_cdf hS]; exact ProbabilityTheory.monotone_cdf _ h

lemma Fminus_eq (hS : Standing M) (x : ℝ) :
    Fminus M x = Function.leftLim (ProbabilityTheory.cdf M.P) x := by
  haveI := hprob hS
  have h := (ProbabilityTheory.cdf M.P).measure_Iio (ProbabilityTheory.tendsto_cdf_atBot (μ := M.P)) x
  rw [ProbabilityTheory.measure_cdf, sub_zero] at h
  have hnn : 0 ≤ Function.leftLim (ProbabilityTheory.cdf M.P) x :=
    le_trans (ProbabilityTheory.cdf_nonneg _ (x - 1))
      (Monotone.le_leftLim (ProbabilityTheory.monotone_cdf _) (by linarith))
  unfold Fminus
  rw [measureReal_def, h, ENNReal.toReal_ofReal hnn]

lemma F_neg (hS : Standing M) {x : ℝ} (hx : x < 0) : F M x = 0 := by
  have h0 : M.P (Set.Iic x) = 0 := by
    apply measure_mono_null _ hS.2.2.2.2.2.2
    intro y hy hy'; simp only [Set.mem_Iic] at hy; linarith [hy'.1]
  unfold F; rw [measureReal_def, h0]; rfl

lemma F_one (hS : Standing M) : F M 1 = 1 := by
  haveI := hprob hS
  have h0 : M.P (Set.Iic (1:ℝ))ᶜ = 0 := by
    apply measure_mono_null _ hS.2.2.2.2.2.2
    intro y hy hy'; simp only [Set.mem_compl_iff, Set.mem_Iic] at hy; linarith [hy'.2]
  rw [prob_compl_eq_zero_iff measurableSet_Iic] at h0
  unfold F; rw [measureReal_def, h0]; rfl

lemma Fminus_le_F (hS : Standing M) (x : ℝ) : Fminus M x ≤ F M x := by
  haveI := hprob hS
  unfold Fminus F
  exact measureReal_mono Set.Iio_subset_Iic_self

/-- The structure of the cutoff mechanism for `γ ∈ [0,1)`. -/
lemma tG_props (hS : Standing M) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    0 ≤ tGamma M γ ∧ tGamma M γ ≤ 1 ∧ Fminus M (tGamma M γ) ≤ γ ∧ γ ≤ F M (tGamma M γ) := by
  haveI := hprob hS
  set S := {θ : ℝ | γ < F M θ} with hSdef
  have h1S : (1:ℝ) ∈ S := by simp only [hSdef, Set.mem_setOf_eq, F_one hS]; exact h1
  have hne : S.Nonempty := ⟨1, h1S⟩
  have hlb : ∀ θ ∈ S, 0 ≤ θ := by
    intro θ hθ; by_contra hc; push_neg at hc
    simp only [hSdef, Set.mem_setOf_eq, F_neg hS hc] at hθ; linarith
  have hbdd : BddBelow S := ⟨0, hlb⟩
  have ht : tGamma M γ = sInf S := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht]; exact le_csInf hne hlb
  · rw [ht]; exact csInf_le hbdd h1S
  · rw [Fminus_eq hS]
    have hT := Monotone.tendsto_leftLim (ProbabilityTheory.monotone_cdf M.P) (tGamma M γ)
    apply le_of_tendsto hT
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [← F_cdf hS]
    by_contra hc; push_neg at hc
    have : sInf S ≤ x := csInf_le hbdd hc
    rw [← ht] at this; exact absurd hx (not_lt.mpr this)
  · by_contra hc; push_neg at hc
    rw [F_cdf hS] at hc
    have hcont := (ProbabilityTheory.cdf M.P).right_continuous (tGamma M γ)
    have hev := hcont.eventually (gt_mem_nhds hc)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have : sInf S < u := by rw [← ht]; exact hu
    obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hne this
    have hts : tGamma M γ ≤ s := by rw [ht]; exact csInf_le hbdd hsS
    have := hsub ⟨hts, hsu⟩
    simp only [Set.mem_setOf_eq] at this
    rw [← F_cdf hS] at this
    simp only [hSdef, Set.mem_setOf_eq] at hsS
    linarith


/-- The weight on the atom. -/
noncomputable def wt (M : Params) (γ : ℝ) : ℝ :=
  if F M (tGamma M γ) = Fminus M (tGamma M γ) then 1
  else (γ - Fminus M (tGamma M γ)) / (F M (tGamma M γ) - Fminus M (tGamma M γ))

lemma cut_eq {γ : ℝ} (h1 : γ < 1) :
    cutoffMech M γ = fun θ => Set.indicator (Set.Iio (tGamma M γ)) (fun _ => (1:ℝ)) θ +
      Set.indicator {tGamma M γ} (fun _ => wt M γ) θ := by
  funext θ
  unfold cutoffMech
  rw [if_neg (not_le.mpr h1)]
  simp only [Set.indicator, Set.mem_Iio, Set.mem_singleton_iff, wt]

lemma cut_props (hS : Standing M) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    (∀ θ, θ < tGamma M γ → cutoffMech M γ θ = 1) ∧
    (∀ θ, tGamma M γ < θ → cutoffMech M γ θ = 0) ∧
    IsMechanism (cutoffMech M γ) ∧ (∫ θ, cutoffMech M γ θ ∂M.P) = γ := by
  haveI := hprob hS
  obtain ⟨_, _, hFm, hF⟩ := tG_props hS h0 h1
  set t := tGamma M γ with htdef
  have hw : wt M γ ∈ Set.Icc (0:ℝ) 1 := by
    unfold wt; rw [← htdef]
    split_ifs with h
    · exact ⟨zero_le_one, le_rfl⟩
    · have hpos : 0 < F M t - Fminus M t := by
        have := Fminus_le_F hS t
        exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm h))
      constructor
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]; linarith
  rw [cut_eq h1, ← htdef]
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro θ hθ
    simp [Set.indicator, hθ, ne_of_lt hθ]
  · intro θ hθ
    simp [Set.indicator, not_lt.mpr hθ.le, ne_of_gt hθ]
  · exact (measurable_const.indicator measurableSet_Iio).add
      (measurable_const.indicator (measurableSet_singleton _))
  · intro θ
    by_cases ha : θ < t
    · simp [Set.indicator, ha, ne_of_lt ha]
    · by_cases hb : θ = t
      · subst hb; simpa [Set.indicator] using hw
      · simp [Set.indicator, ha, hb]
  · rw [integral_add, integral_indicator_const _ measurableSet_Iio,
      integral_indicator_const _ (measurableSet_singleton _)]
    · have hu : M.P.real (Set.Iic t) = M.P.real (Set.Iio t) + M.P.real {t} := by
        rw [← Set.Iio_union_right]
        exact measureReal_union (by simp) (measurableSet_singleton _)
      have hF' : F M t = M.P.real (Set.Iio t) + M.P.real {t} := hu
      have hFm' : Fminus M t = M.P.real (Set.Iio t) := rfl
      simp only [smul_eq_mul, mul_one]
      unfold wt; rw [← htdef]
      split_ifs with h
      · have : M.P.real {t} = 0 := by linarith
        rw [this]; linarith
      · have hpos : M.P.real {t} ≠ 0 := by intro h'; apply h; linarith
        rw [hF', hFm', show M.P.real (Set.Iio t) + M.P.real {t} - M.P.real (Set.Iio t) = M.P.real {t} by ring,
          mul_div_cancel₀ _ hpos]; ring
    · exact (integrable_const _).indicator measurableSet_Iio
    · exact (integrable_const _).indicator (measurableSet_singleton _)


/-- Supporting-line inequality for a threshold mechanism `ψ` with threshold `s`. -/
lemma thr_ineq (hS : Standing M) {s : ℝ} {π ψ : ℝ → ℝ} (hπ : IsMechanism π) (hψ : IsMechanism ψ)
    (hlt : ∀ θ, θ < s → ψ θ = 1) (hgt : ∀ θ, s < θ → ψ θ = 0) :
    s * ((∫ θ, π θ ∂M.P) - ∫ θ, ψ θ ∂M.P) ≤ (∫ θ, θ * π θ ∂M.P) - ∫ θ, θ * ψ θ ∂M.P := by
  have h := integral_nonneg (μ := M.P) (f := fun θ =>
    0 + 0 * θ + (-s) * π θ + 1 * (θ * π θ) + s * ψ θ + (-1) * (θ * ψ θ)) (fun θ => by
      have key : 0 + 0 * θ + (-s) * π θ + 1 * (θ * π θ) + s * ψ θ + (-1) * (θ * ψ θ)
          = (θ - s) * (π θ - ψ θ) := by ring
      simp only at key ⊢
      rw [key]
      rcases lt_trichotomy θ s with h | h | h
      · rw [hlt θ h]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [(hπ.2 θ).2])
      · rw [h]; simp
      · rw [hgt θ h]; exact mul_nonneg (by linarith) (by linarith [(hπ.2 θ).1]))
  rw [int_lin hS hπ hψ] at h
  linarith

lemma int_one_sub (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) :
    (∫ θ, (1 - π θ) ∂M.P) = 1 - ∫ θ, π θ ∂M.P := by
  have := int_lin hS hπ hπ 1 0 (-1) 0 0 0
  rw [show (fun θ => 1 + 0 * θ + (-1) * π θ + 0 * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)) =
    fun θ => 1 - π θ by funext θ; ring] at this
  rw [this]; ring

lemma int_th_one_sub (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) :
    (∫ θ, θ * (1 - π θ) ∂M.P) = (∫ θ, θ ∂M.P) - ∫ θ, θ * π θ ∂M.P := by
  have := int_lin hS hπ hπ 0 1 0 (-1) 0 0
  rw [show (fun θ => 0 + 1 * θ + 0 * π θ + (-1) * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)) =
    fun θ => θ * (1 - π θ) by funext θ; ring] at this
  rw [this]; ring

noncomputable def G (M : Params) (γ : ℝ) : ℝ := ∫ θ, θ * cutoffMech M γ θ ∂M.P

noncomputable def Dv (M : Params) (γ : ℝ) : ℝ := (∫ θ, θ ∂M.P) - ta M - G M γ + ta M * γ

lemma eq16_iff (hS : Standing M) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) : Eq16 M γ ↔ Dv M γ = 0 := by
  obtain ⟨_, _, hm, hint⟩ := cut_props hS h0 h1
  unfold Eq16 Dv G
  rw [int_one_sub hS hm, int_th_one_sub hS hm, hint]
  constructor <;> intro h <;> linarith

/-- Supporting line for `G`. -/
lemma G_supp (hS : Standing M) {γ γ' : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) (h0' : 0 ≤ γ') (h1' : γ' < 1) :
    tGamma M γ' * (γ - γ') ≤ G M γ - G M γ' := by
  obtain ⟨_, _, hm, hint⟩ := cut_props hS h0 h1
  obtain ⟨hlt', hgt', hm', hint'⟩ := cut_props hS h0' h1'
  have := thr_ineq hS hm hm' hlt' hgt'
  rw [hint, hint'] at this
  exact this

lemma Dv_lip (hS : Standing M) {γ γ' : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) (h0' : 0 ≤ γ') (h1' : γ' < 1) :
    |Dv M γ - Dv M γ'| ≤ |γ - γ'| := by
  have A := G_supp hS h0 h1 h0' h1'
  have B := G_supp hS h0' h1' h0 h1
  obtain ⟨t0, t1, _, _⟩ := tG_props hS h0 h1
  obtain ⟨t0', t1', _, _⟩ := tG_props hS h0' h1'
  obtain ⟨a0, a1, _, _⟩ := ta_th hS
  unfold Dv
  rcases le_total γ' γ with h | h
  · have d0 : 0 ≤ γ - γ' := by linarith
    rw [abs_of_nonneg d0, abs_le]
    have e1 : tGamma M γ * (γ - γ') ≤ γ - γ' := by nlinarith
    have e2 : 0 ≤ tGamma M γ' * (γ - γ') := mul_nonneg t0' d0
    have e3 : ta M * (γ - γ') ≤ γ - γ' := by nlinarith
    have e4 : 0 ≤ ta M * (γ - γ') := mul_nonneg a0.le d0
    constructor <;> nlinarith
  · have d0 : 0 ≤ γ' - γ := by linarith
    rw [abs_sub_comm γ γ', abs_of_nonneg d0, abs_le]
    have e1 : tGamma M γ' * (γ' - γ) ≤ γ' - γ := by nlinarith
    have e2 : 0 ≤ tGamma M γ * (γ' - γ) := mul_nonneg t0 d0
    have e3 : ta M * (γ' - γ) ≤ γ' - γ := by nlinarith
    have e4 : 0 ≤ ta M * (γ' - γ) := mul_nonneg a0.le d0
    constructor <;> nlinarith

lemma Dv_cont (hS : Standing M) {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) :
    ContinuousOn (Dv M) (Set.Icc a b) := by
  have : LipschitzOnWith 1 (Dv M) (Set.Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    exact Dv_lip hS (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hy.1]) (by linarith [hy.2])
  exact this.continuousOn


lemma int_lin_int (hS : Standing M) {π ψ : ℝ → ℝ} (hπ : IsMechanism π) (hψ : IsMechanism ψ)
    (a b c d e f : ℝ) :
    Integrable (fun θ => a + b * θ + c * π θ + d * (θ * π θ) + e * ψ θ + f * (θ * ψ θ)) M.P := by
  haveI := hprob hS
  exact (((((integrable_const a).add ((int_id hS).const_mul b)).add
    ((int_mech hS hπ).const_mul c)).add ((int_mul hS hπ).const_mul d)).add
    ((int_mech hS hψ).const_mul e)).add ((int_mul hS hψ).const_mul f)

lemma tG_lb (hS : Standing M) {γ : ℝ} (h1 : γ < 1) (s : ℝ) (hs : ∀ θ, γ < F M θ → s ≤ θ) :
    s ≤ tGamma M γ :=
  le_csInf ⟨1, by simp only [Set.mem_setOf_eq, F_one hS]; exact h1⟩ hs

lemma D_pos (hS : Standing M) (hA : Assumption1 M) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1)
    (ht : ta M ≤ tGamma M γ) : 0 < Dv M γ := by
  haveI := hprob hS
  obtain ⟨hlt, hgt, hm, hint⟩ := cut_props hS h0 h1
  set t := tGamma M γ with htdef
  rcases lt_or_eq_of_le ht with ht' | ht'
  · have h := integral_nonneg (μ := M.P) (f := fun θ =>
      (-t) + 1 * θ + t * cutoffMech M γ θ + (-1) * (θ * cutoffMech M γ θ) +
        0 * cutoffMech M γ θ + 0 * (θ * cutoffMech M γ θ)) (fun θ => by
        have key : (-t) + 1 * θ + t * cutoffMech M γ θ + (-1) * (θ * cutoffMech M γ θ) +
            0 * cutoffMech M γ θ + 0 * (θ * cutoffMech M γ θ)
            = (θ - t) * (1 - cutoffMech M γ θ) := by ring
        simp only at key ⊢
        rw [key]
        rcases lt_or_ge θ t with h | h
        · rw [hlt θ h]; simp
        · exact mul_nonneg (by linarith) (by linarith [(hm.2 θ).2]))
    rw [int_lin hS hm hm, hint] at h
    unfold Dv G
    have : 0 < (t - ta M) * (1 - γ) := mul_pos (by linarith) (by linarith)
    nlinarith
  · -- t = ta
    set h : ℝ → ℝ := Set.indicator (Set.Ioi (ta M)) (fun θ => θ - ta M) with hhdef
    have hhi : Integrable h M.P := ((int_id hS).sub (integrable_const _)).indicator measurableSet_Ioi
    have hnn : 0 ≤ h := by
      intro θ; simp only [hhdef, Set.indicator, Set.mem_Ioi, Pi.zero_apply]
      split_ifs with hc <;> linarith
    have hpos : 0 < ∫ θ, h θ ∂M.P := by
      rw [integral_pos_iff_support_of_nonneg hnn hhi]
      have hP : M.P (Set.Ioi (ta M)) ≠ 0 := by
        intro h0; have := hA.2; rw [measureReal_def, h0] at this; simp at this
      refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hP) (measure_mono ?_)
      intro θ hθ
      simp only [Function.mem_support, hhdef, Set.indicator, Set.mem_Ioi] at hθ ⊢
      rw [if_pos hθ]; intro hc; linarith
    have hle : (∫ θ, h θ ∂M.P) ≤ ∫ θ, ((-ta M) + 1 * θ + ta M * cutoffMech M γ θ +
        (-1) * (θ * cutoffMech M γ θ) + 0 * cutoffMech M γ θ + 0 * (θ * cutoffMech M γ θ)) ∂M.P := by
      apply integral_mono hhi (int_lin_int hS hm hm _ _ _ _ _ _)
      intro θ
      have key : (-ta M) + 1 * θ + ta M * cutoffMech M γ θ + (-1) * (θ * cutoffMech M γ θ) +
          0 * cutoffMech M γ θ + 0 * (θ * cutoffMech M γ θ)
          = (θ - t) * (1 - cutoffMech M γ θ) := by rw [ht']; ring
      simp only at key ⊢
      rw [key]
      simp only [hhdef, Set.indicator, Set.mem_Ioi]
      rcases lt_trichotomy θ t with hc | hc | hc
      · rw [if_neg (by linarith), hlt θ hc]; simp
      · rw [if_neg (by linarith), hc]; simp
      · rw [if_pos (by linarith), hgt θ hc, ht']; simp
    rw [int_lin hS hm hm, hint] at hle
    unfold Dv G
    linarith

noncomputable def piu (M : Params) : ℝ → ℝ := Set.indicator (Set.Iic (th M)) (fun _ => (1 : ℝ))

lemma piu_props (hS : Standing M) :
    IsMechanism (piu M) ∧ (∀ θ, θ < th M → piu M θ = 1) ∧ (∀ θ, th M < θ → piu M θ = 0) ∧
    (∫ θ, piu M θ ∂M.P) = F M (th M) ∧
    (∫ θ, (1 - piu M θ) ∂M.P) = M.P.real (Set.Ioi (th M)) ∧
    (∫ θ, θ * (1 - piu M θ) ∂M.P) = ∫ θ in Set.Ioi (th M), θ ∂M.P := by
  haveI := hprob hS
  have hm : IsMechanism (piu M) := by
    refine ⟨measurable_const.indicator measurableSet_Iic, fun θ => ?_⟩
    unfold piu; simp only [Set.indicator, Set.mem_Iic]
    split_ifs <;> simp
  have hint : (∫ θ, piu M θ ∂M.P) = F M (th M) := by
    unfold piu; rw [integral_indicator_const _ measurableSet_Iic]; simp; rfl
  refine ⟨hm, ?_, ?_, hint, ?_, ?_⟩
  · intro θ h; unfold piu; simp [Set.indicator, h.le]
  · intro θ h; unfold piu; simp [Set.indicator, not_le.mpr h]
  · rw [int_one_sub hS hm, hint, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; rfl
  · rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext θ
    unfold piu; simp only [Set.indicator, Set.mem_Iic, Set.mem_Ioi]
    by_cases h : θ ≤ th M
    · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_pos (not_le.mp h)]; ring

lemma lagr (ta th t γc m' g' G Eθ : ℝ) (h1 : th ≤ t) (h2 : t < ta) (h3 : th < ta)
    (heq : Eθ - G - ta * (1 - γc) = 0) (hE : 0 ≤ Eθ - g' - ta * (1 - m'))
    (hthr : t * (m' - γc) ≤ g' - G) : th * m' - g' ≤ th * γc - G := by
  have key : (ta - t) * ((th * m' - g') - (th * γc - G)) + (t - th) * (Eθ - g' - ta * (1 - m'))
      = (ta - th) * (t * (m' - γc) - (g' - G)) + (t - th) * (Eθ - G - ta * (1 - γc)) := by ring
  have A : (ta - th) * (t * (m' - γc) - (g' - G)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have B : 0 ≤ (t - th) * (Eθ - g' - ta * (1 - m')) := mul_nonneg (by linarith) hE
  rw [heq, mul_zero, add_zero] at key
  have C : (ta - t) * ((th * m' - g') - (th * γc - G)) ≤ 0 := by linarith
  have := (mul_nonpos_iff_pos_imp_nonpos.mp C).1 (by linarith)
  linarith


lemma zero_mech : IsMechanism (fun _ : ℝ => (0:ℝ)) :=
  ⟨measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩

lemma prop1 (hS : Standing M) (hA : Assumption1 M) (h15 : Cond15 M) :
    IsOptimal M (Set.indicator (Set.Iic (th M)) (fun _ => (1 : ℝ))) := by
  obtain ⟨hm, hlt, hgt, hint, h1s, hth⟩ := piu_props hS
  obtain ⟨a0, a1, b0, b1⟩ := ta_th hS
  change IsOptimal M (piu M)
  refine ⟨hm, ⟨Or.inr ?_, Or.inr ?_⟩, ?_⟩
  · have := thr_ineq hS zero_mech hm hlt hgt
    simp only [mul_zero, integral_zero, zero_sub] at this
    have hF : 0 < F M (th M) := hA.1
    rw [hint] at this ⊢
    nlinarith
  · rw [h1s, hth]; exact h15
  · intro π' hπ' _
    unfold objective
    have := thr_ineq hS hπ' hm hlt hgt
    linarith

lemma prop2 (hS : Standing M) (hA : Assumption1 M) (h15 : ¬ Cond15 M) :
    ∃ γc ∈ Set.Ioo (F M (th M)) 1,
        Eq16 M γc ∧ (∀ γ ∈ Set.Ico (0 : ℝ) 1, Eq16 M γ → γ = γc) ∧
        IsOptimal M (cutoffMech M γc) := by
  haveI := hprob hS
  have hlt15 : (∫ θ in Set.Ioi (th M), θ ∂M.P) < ta M * M.P.real (Set.Ioi (th M)) :=
    lt_of_not_ge h15
  obtain ⟨a0, a1, b0, b1⟩ := ta_th hS
  obtain ⟨hm, hlt, hgt, hint, h1s, hth⟩ := piu_props hS
  have hu0 : 0 < F M (th M) := hA.1
  have hF1 : F M (ta M) = 1 - M.P.real (Set.Ioi (ta M)) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; unfold F; ring
  have h11 : F M (ta M) < 1 := by rw [hF1]; linarith [hA.2]
  have hule : F M (th M) ≤ F M (ta M) := F_mono hS b1.le
  have hu1 : F M (th M) < 1 := lt_of_le_of_lt hule h11
  -- Dv at γu is negative
  have hDu : Dv M (F M (th M)) < 0 := by
    obtain ⟨hltu, hgtu, hmu, hintu⟩ := cut_props hS hu0.le hu1
    have e1 := thr_ineq hS hmu hm hlt hgt
    have e2 := thr_ineq hS hm hmu hltu hgtu
    rw [hintu, hint, sub_self, mul_zero] at e1 e2
    have h3 := int_th_one_sub hS hm
    have h4 := int_one_sub hS hm
    rw [hth] at h3; rw [h1s, hint] at h4
    unfold Dv G
    nlinarith
  have hD1 : 0 < Dv M (F M (ta M)) := by
    apply D_pos hS hA (le_trans hu0.le hule) h11
    apply tG_lb hS h11
    intro θ hθ; by_contra hc; push_neg at hc
    have := F_mono hS hc.le; linarith
  obtain ⟨γc, ⟨hc1, hc2⟩, hDc⟩ := intermediate_value_Icc hule (Dv_cont hS hu0.le h11)
    ⟨hDu.le, hD1.le⟩
  have hcu : F M (th M) < γc := lt_of_le_of_ne hc1 (by rintro rfl; linarith)
  have hc1' : γc < 1 := lt_of_le_of_lt hc2 h11
  have hc0 : 0 ≤ γc := by linarith
  -- zeros of Dv have threshold below ta
  have hzero_t : ∀ γ, 0 ≤ γ → γ < 1 → Dv M γ = 0 → tGamma M γ < ta M := by
    intro γ g0 g1 hD; by_contra hc; push_neg at hc
    have := D_pos hS hA g0 g1 hc; linarith
  have htc : tGamma M γc < ta M := hzero_t γc hc0 hc1' hDc
  have htc' : th M ≤ tGamma M γc := by
    apply tG_lb hS hc1'
    intro θ hθ; by_contra hc; push_neg at hc
    have := F_mono hS hc.le; linarith
  refine ⟨γc, ⟨hcu, hc1'⟩, (eq16_iff hS hc0 hc1').mpr hDc, ?_, ?_⟩
  · intro γ ⟨g0, g1⟩ hEq
    have hD := (eq16_iff hS g0 g1).mp hEq
    have htg := hzero_t γ g0 g1 hD
    have s1 := G_supp hS g0 g1 hc0 hc1'
    have s2 := G_supp hS hc0 hc1' g0 g1
    unfold Dv at hD hDc
    rcases lt_trichotomy γ γc with h | h | h
    · have : 0 < (ta M - tGamma M γc) * (γc - γ) := mul_pos (by linarith) (by linarith)
      nlinarith
    · exact h
    · have : 0 < (ta M - tGamma M γ) * (γ - γc) := mul_pos (by linarith) (by linarith)
      nlinarith
  · obtain ⟨hltc, hgtc, hmc, hintc⟩ := cut_props hS hc0 hc1'
    have hEq := (eq16_iff hS hc0 hc1').mpr hDc
    refine ⟨hmc, ⟨Or.inr ?_, Or.inr ?_⟩, ?_⟩
    · have := thr_ineq hS zero_mech hmc hltc hgtc
      simp only [mul_zero, integral_zero, zero_sub] at this
      rw [hintc] at this ⊢
      have : 0 < (ta M - tGamma M γc) * γc := mul_pos (by linarith) (by linarith)
      nlinarith
    · exact le_of_eq hEq.symm
    · intro π' hπ' hIC'
      have hE : 0 ≤ (∫ θ, θ ∂M.P) - (∫ θ, θ * π' θ ∂M.P) - ta M * (1 - ∫ θ, π' θ ∂M.P) := by
        rcases hIC'.2 with h | h
        · rw [int_one_sub hS hπ'] at h
          have hn := integral_nonneg_of_ae (μ := M.P) (f := fun θ =>
            (1 - ta M) + 1 * θ + (ta M - 1) * π' θ + (-1) * (θ * π' θ) + 0 * π' θ +
              0 * (θ * π' θ)) (by
            filter_upwards [ae_mem hS] with θ hθ
            have key : (1 - ta M) + 1 * θ + (ta M - 1) * π' θ + (-1) * (θ * π' θ) + 0 * π' θ +
              0 * (θ * π' θ) = (θ - ta M + 1) * (1 - π' θ) := by ring
            simp only [Pi.zero_apply]
            rw [key]
            exact mul_nonneg (by linarith [hθ.1]) (by linarith [(hπ'.2 θ).2]))
          rw [int_lin hS hπ' hπ'] at hn
          nlinarith
        · rw [int_one_sub hS hπ', int_th_one_sub hS hπ'] at h
          linarith
      have hthr := thr_ineq hS hπ' hmc hltc hgtc
      rw [hintc] at hthr
      unfold Dv G at hDc
      unfold objective
      rw [hintc]
      exact lagr (ta M) (th M) (tGamma M γc) γc _ _ _ _ htc' htc b1 (by linarith) hE hthr

end InfoNudgeSolP12

namespace InfoNudgeSolP12

variable {M : Params}

lemma mean_one_g (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) (h : (∫ θ, π θ ∂M.P) = 1) :
    (∫ θ, θ * π θ ∂M.P) = ∫ θ, θ ∂M.P := by
  have n1 := integral_nonneg_of_ae (μ := M.P) (f := fun θ =>
    0 + 1 * θ + 0 * π θ + (-1) * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)) (by
      filter_upwards [ae_mem hS] with θ hθ
      have key : 0 + 1 * θ + 0 * π θ + (-1) * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)
        = θ * (1 - π θ) := by ring
      simp only [Pi.zero_apply]; rw [key]
      exact mul_nonneg hθ.1 (by linarith [(hπ.2 θ).2]))
  have n2 := integral_nonneg_of_ae (μ := M.P) (f := fun θ =>
    1 + (-1) * θ + (-1) * π θ + 1 * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)) (by
      filter_upwards [ae_mem hS] with θ hθ
      have key : 1 + (-1) * θ + (-1) * π θ + 1 * (θ * π θ) + 0 * π θ + 0 * (θ * π θ)
        = (1 - θ) * (1 - π θ) := by ring
      simp only [Pi.zero_apply]; rw [key]
      exact mul_nonneg (by linarith [hθ.2]) (by linarith [(hπ.2 θ).2]))
  rw [int_lin hS hπ hπ] at n1 n2
  rw [h] at n2
  linarith

lemma cut_one {γ : ℝ} (h : 1 ≤ γ) : cutoffMech M γ = fun _ => 1 := by
  funext θ; simp [cutoffMech, h]

lemma one_mech : IsMechanism (fun _ : ℝ => (1:ℝ)) :=
  ⟨measurable_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩

lemma mean_bounds (hS : Standing M) {π : ℝ → ℝ} (hπ : IsMechanism π) :
    0 ≤ (∫ θ, π θ ∂M.P) ∧ (∫ θ, π θ ∂M.P) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun θ => (hπ.2 θ).1)
  · have := integral_nonneg (μ := M.P) (f := fun θ => 1 - π θ)
      (fun θ => by simp only [Pi.zero_apply]; linarith [(hπ.2 θ).2])
    rw [int_one_sub hS hπ] at this; linarith

lemma cutoff_red (hS : Standing M) (π : ℝ → ℝ) (γ : ℝ)
    (hπ : IsMechanism π) (hIC : IC M π) (hγ : (∫ θ, π θ ∂M.P) = γ) :
    IC M (cutoffMech M γ) ∧ objective M π ≤ objective M (cutoffMech M γ) := by
  haveI := hprob hS
  obtain ⟨g0, g1⟩ := mean_bounds hS hπ
  rw [hγ] at g0 g1
  rcases lt_or_eq_of_le g1 with hlt1 | heq1
  · obtain ⟨hlt, hgt, hm, hint⟩ := cut_props hS g0 hlt1
    have hthr := thr_ineq hS hπ hm hlt hgt
    rw [hint, hγ, sub_self, mul_zero] at hthr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases hIC.1 with h | h
      · left; rw [hint]; rw [hγ] at h; exact h
      · right; rw [hint]; rw [hγ] at h; linarith
    · right
      rw [int_one_sub hS hm, int_th_one_sub hS hm, hint]
      rcases hIC.2 with h | h
      · rw [int_one_sub hS hπ, hγ] at h; exfalso; linarith
      · rw [int_one_sub hS hπ, int_th_one_sub hS hπ, hγ] at h; linarith
    · unfold objective; rw [hint, hγ]; linarith
  · subst heq1
    rw [cut_one le_rfl]
    have hg := mean_one_g hS hπ hγ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · right
      rcases hIC.1 with h | h
      · rw [hγ] at h; exfalso; exact one_ne_zero h
      · rw [hγ, hg] at h; simp only [mul_one, integral_const, smul_eq_mul, probReal_univ]; linarith
    · left; simp
    · unfold objective; rw [hγ, hg]; simp

lemma lemma2 (hS : Standing M) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsMechanism (cutoffMech M γ) ∧ (∫ θ, cutoffMech M γ θ ∂M.P) = γ ∧
    ∀ π : ℝ → ℝ, IsMechanism π → (∫ θ, π θ ∂M.P) = γ →
      (∫ θ, θ * cutoffMech M γ θ ∂M.P) ≤ ∫ θ, θ * π θ ∂M.P ∧
      ((∫ θ, θ * π θ ∂M.P) = ∫ θ, θ * cutoffMech M γ θ ∂M.P ↔
        π =ᵐ[M.P] cutoffMech M γ) := by
  haveI := hprob hS
  rcases lt_or_eq_of_le hγ.2 with hlt1 | heq1
  · obtain ⟨hlt, hgt, hm, hint⟩ := cut_props hS hγ.1 hlt1
    refine ⟨hm, hint, fun π hπ hmean => ?_⟩
    have hthr := thr_ineq hS hπ hm hlt hgt
    rw [hint, hmean, sub_self, mul_zero] at hthr
    refine ⟨by linarith, ⟨fun heq => ?_, fun hae => integral_congr_ae ?_⟩⟩
    · set t := tGamma M γ with htdef
      set c := cutoffMech M γ with hcdef
      have hnn : 0 ≤ fun θ => 0 + 0 * θ + (-t) * π θ + 1 * (θ * π θ) + t * c θ + (-1) * (θ * c θ) := by
        intro θ
        have key : 0 + 0 * θ + (-t) * π θ + 1 * (θ * π θ) + t * c θ + (-1) * (θ * c θ)
            = (θ - t) * (π θ - c θ) := by ring
        simp only [Pi.zero_apply]; rw [key]
        rcases lt_trichotomy θ t with h | h | h
        · rw [hlt θ h]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [(hπ.2 θ).2])
        · rw [h]; simp
        · rw [hgt θ h]; exact mul_nonneg (by linarith) (by linarith [(hπ.2 θ).1])
      have hz : (∫ θ, (0 + 0 * θ + (-t) * π θ + 1 * (θ * π θ) + t * c θ + (-1) * (θ * c θ)) ∂M.P) = 0 := by
        rw [int_lin hS hπ hm, hint, hmean, heq]; ring
      have hae0 := (integral_eq_zero_iff_of_nonneg hnn (int_lin_int hS hπ hm _ _ _ _ _ _)).mp hz
      -- d := π - c vanishes a.e. off {t}
      have hd : (fun θ => π θ - c θ) =ᵐ[M.P] Set.indicator {t} (fun _ => π t - c t) := by
        filter_upwards [hae0] with θ hθ
        have key : 0 + 0 * θ + (-t) * π θ + 1 * (θ * π θ) + t * c θ + (-1) * (θ * c θ)
            = (θ - t) * (π θ - c θ) := by ring
        simp only [Pi.zero_apply] at hθ
        rw [key] at hθ
        by_cases h : θ = t
        · subst h; simp
        · rw [Set.indicator_of_notMem (by simpa using h)]
          rcases mul_eq_zero.mp hθ with h' | h'
          · exact absurd (by linarith) h
          · exact h'
      have hint0 : (∫ θ, (π θ - c θ) ∂M.P) = 0 := by
        rw [integral_sub (int_mech hS hπ) (int_mech hS hm), hint, hmean, sub_self]
      rw [integral_congr_ae hd, integral_indicator_const _ (measurableSet_singleton _),
        smul_eq_mul] at hint0
      have hd0 : (fun θ => π θ - c θ) =ᵐ[M.P] 0 := by
        rcases mul_eq_zero.mp hint0 with h | h
        · have hnull : M.P {t} = 0 := (measureReal_eq_zero_iff).mp h
          refine hd.trans ?_
          have : ∀ᵐ θ ∂M.P, θ ∉ ({t} : Set ℝ) := by
            rw [ae_iff]; simpa using hnull
          filter_upwards [this] with θ hθ
          rw [Set.indicator_of_notMem hθ]; rfl
        · refine hd.trans (Filter.Eventually.of_forall fun θ => ?_)
          simp [Set.indicator, h]
      filter_upwards [hd0] with θ hθ
      simp only [Pi.zero_apply] at hθ; linarith
    · filter_upwards [hae] with θ hθ; rw [hθ]
  · subst heq1
    rw [cut_one le_rfl]
    refine ⟨one_mech, by simp, fun π hπ hmean => ?_⟩
    have hg := mean_one_g hS hπ hmean
    simp only [mul_one]
    refine ⟨le_of_eq hg.symm, ⟨fun _ => ?_, fun _ => hg⟩⟩
    have hnn : 0 ≤ fun θ => 1 - π θ := fun θ => by simp only [Pi.zero_apply]; linarith [(hπ.2 θ).2]
    have hz : (∫ θ, (1 - π θ) ∂M.P) = 0 := by rw [int_one_sub hS hπ, hmean]; ring
    have := (integral_eq_zero_iff_of_nonneg hnn
      ((integrable_const _).sub (int_mech hS hπ))).mp hz
    filter_upwards [this] with θ hθ
    simp only [Pi.zero_apply] at hθ; linarith

end InfoNudgeSolP12

open InfoNudgeSolP12 in
theorem solution (M : Params) (hS : Standing M) (π : ℝ → ℝ) (γ : ℝ)
    (hπ : IsMechanism π) (hIC : IC M π) (hγ : (∫ θ, π θ ∂M.P) = γ) :
    IC M (cutoffMech M γ) ∧ objective M π ≤ objective M (cutoffMech M γ) :=
  cutoff_red hS π γ hπ hIC hγ
