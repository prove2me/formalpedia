-- Prove2me | solution 1 for MaxSpectralRisk.Duality.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:14:00.907795+00:00
-- url     : https://prove2.me/submissions/1ee149ea-5ed7-4a15-b7af-4bf7143c2fb3

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting
import Theorems.Thm_MongeKantorovichYao_transferencePlansOf_isTight
import Theorems.Thm_MaxSpectralRisk_Duality_lemma_1
import Theorems.Thm_MaxSpectralRisk_Duality_proposition_2

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRProp3Found

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The couplings, as a set of probability measures. -/
def Pset (μ : Measure X) (ν : Measure Y) : Set (ProbabilityMeasure (X × Y)) :=
  {π | (π : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν}

lemma Pset_isClosed (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsClosed (Pset μ ν) := by
  set μ' : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  set ν' : ProbabilityMeasure Y := ⟨ν, inferInstance⟩
  have h1 : IsClosed {π : ProbabilityMeasure (X × Y) |
      π.map continuous_fst.measurable.aemeasurable = μ'} :=
    isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const
  have h2 : IsClosed {π : ProbabilityMeasure (X × Y) |
      π.map continuous_snd.measurable.aemeasurable = ν'} :=
    isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const
  convert h1.inter h2 using 1
  ext π
  simp only [Pset, MongeKantorovichYao.transferencePlans, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨-, hfst, hsnd⟩
    constructor
    · apply Subtype.ext
      simpa [μ'] using hfst
    · apply Subtype.ext
      simpa [ν'] using hsnd
  · rintro ⟨hfst, hsnd⟩
    refine ⟨inferInstance, ?_, ?_⟩
    · have := congrArg (fun p : ProbabilityMeasure X => (p : Measure X)) hfst
      simpa [μ'] using this
    · have := congrArg (fun p : ProbabilityMeasure Y => (p : Measure Y)) hsnd
      simpa [ν'] using this

lemma Pset_isCompact (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCompact (Pset μ ν) := by
  have htight : IsTightMeasureSet
      {((π : ProbabilityMeasure (X × Y)) : Measure (X × Y)) | π ∈ Pset μ ν} := by
    have h := MongeKantorovichYao.transferencePlansOf_isTight {μ} {ν}
      (fun m hm => by rw [Set.mem_singleton_iff.1 hm]; infer_instance)
      (fun m hm => by rw [Set.mem_singleton_iff.1 hm]; infer_instance)
      isTightMeasureSet_singleton isTightMeasureSet_singleton
    refine h.subset ?_
    rintro _ ⟨π, hπ, rfl⟩
    exact ⟨inferInstance, by rw [hπ.2.1]; rfl, by rw [hπ.2.2]; rfl⟩
  have := isCompact_closure_of_isTightMeasureSet htight
  rwa [(Pset_isClosed μ ν).closure_eq] at this

lemma Pset_nonempty (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : (Pset μ ν).Nonempty :=
  ⟨⟨μ.prod ν, inferInstance⟩, (inferInstance : IsProbabilityMeasure (μ.prod ν)), by simp, by simp⟩

end MSRProp3Found

namespace MSRProp3Aux

lemma coe_add_iInf (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨅ i, f i = ⨅ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h : ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)
          ≤ ((-a : ℝ) : EReal) + ((a : EReal) + f i) := add_le_add le_rfl (iInf_le _ i)
        _ = f i := by rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
    calc ⨅ i, ((a : EReal) + f i)
        = (a : EReal) + (((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
      _ ≤ (a : EReal) + ⨅ i, f i := add_le_add le_rfl h

lemma coe_add_iSup (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨆ i, f i = ⨆ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · have h : ⨆ i, f i ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) := by
      refine iSup_le fun i => ?_
      calc f i = ((-a : ℝ) : EReal) + ((a : EReal) + f i) := by
            rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
        _ ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) :=
            add_le_add le_rfl (le_iSup (fun i => (a : EReal) + f i) i)
    calc (a : EReal) + ⨆ i, f i
        ≤ (a : EReal) + (((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i)) := add_le_add le_rfl h
      _ = ⨆ i, ((a : EReal) + f i) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup f i)

instance gam_finite (sig : SpectralFunction) : IsFiniteMeasure (gam sig) := by
  refine ⟨?_⟩
  unfold gam
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top

lemma gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ico

lemma Gam_ac_gam (sig : SpectralFunction) : Gam sig ≪ gam sig :=
  withDensity_absolutelyContinuous _ _

lemma gam_ac_Gam (sig : SpectralFunction) : gam sig ≪ Gam sig := by
  unfold Gam
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith [hu.2]

lemma Gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(Gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  (Gam_ac_gam sig).ae_le (gam_ae_Ico sig)

lemma int_Gam_iff (sig : SpectralFunction) (f : ℝ → ℝ) :
    Integrable f (Gam sig) ↔ Integrable (fun u => (1 - u) * f u) (gam sig) := by
  unfold Gam
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]

lemma integral_Gam (sig : SpectralFunction) (f : ℝ → ℝ) :
    ∫ u, f u ∂(Gam sig) = ∫ u, (1 - u) * f u ∂(gam sig) := by
  unfold Gam
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]

lemma int_Gam_of_int_gam (sig : SpectralFunction) {f : ℝ → ℝ} (hf : Integrable f (gam sig)) :
    Integrable f (Gam sig) := by
  rw [int_Gam_iff]
  refine Integrable.mono' hf.norm (by fun_prop) ?_
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u)]
  have : 1 - u ≤ 1 := by linarith [hu.1]
  have h0 : 0 ≤ |f u| := abs_nonneg _
  nlinarith

section Coupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma aerect_ae {μ : Measure X} {ν : Measure Y} {P : X → Y → Prop}
    (h : AERect μ ν P) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    ∀ᵐ p ∂π, P p.1 p.2 := by
  obtain ⟨N, hN, N', hN', hP⟩ := h
  have h1 : π (Prod.fst ⁻¹' toMeasurable μ N) = 0 := by
    rw [← Measure.map_apply measurable_fst (measurableSet_toMeasurable _ _), hπ.2.1,
      measure_toMeasurable, hN]
  have h2 : π (Prod.snd ⁻¹' toMeasurable ν N') = 0 := by
    rw [← Measure.map_apply measurable_snd (measurableSet_toMeasurable _ _), hπ.2.2,
      measure_toMeasurable, hN']
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with p hp1 hp2
  exact hP p.1 (fun h => hp1 (subset_toMeasurable _ _ h)) p.2
    (fun h => hp2 (subset_toMeasurable _ _ h))

lemma int_fst {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : X × Y => f p.1) π := by
  have : Integrable f (π.map Prod.fst) := by rw [hπ.2.1]; exact hf
  exact (integrable_map_measure this.1 measurable_fst.aemeasurable).1 this

lemma int_snd {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun p : X × Y => f p.2) π := by
  have : Integrable f (π.map Prod.snd) := by rw [hπ.2.2]; exact hf
  exact (integrable_map_measure this.1 measurable_snd.aemeasurable).1 this

end Coupling

section Main

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {sig : SpectralFunction} {L : X × Y → ℝ}

lemma L_meas (hA : Assumptions L μ ν) : Measurable L := hA.usc.measurable

lemma L_int (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) : Integrable L π := by
  obtain ⟨A, B, -, hAi, -, hBi, hub⟩ := hA.upper_bound
  obtain ⟨a, b, -, hai, -, hbi, hlb⟩ := hA.lower_bound
  refine Integrable.mono' (((int_fst hπ hai).add (int_snd hπ hbi)).abs.add
    ((int_fst hπ hAi).add (int_snd hπ hBi)).abs) (L_meas hA).aestronglyMeasurable ?_
  filter_upwards [aerect_ae hub hπ, aerect_ae hlb hπ] with p h1 h2
  simp only [Prod.mk.eta] at h1 h2
  rw [Real.norm_eq_abs]
  exact (abs_le_max_abs_abs h2 h1).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))

lemma C_int (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) (β : ℝ → ℝ)
    (hβ : Integrable β (gam sig)) :
    Integrable (fun p : X × Y => Cbeta sig L β p.1 p.2) π := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hL := L_int hA hπ
  set f : (X × Y) → ℝ → ℝ := fun p u => max (L p - β u) 0 with hfdef
  have hf : Integrable (Function.uncurry f) (π.prod (gam sig)) := by
    refine Integrable.mono' ((hL.comp_fst (gam sig)).norm.add ((hβ.comp_snd π).norm)) ?_ ?_
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
        ((hL.comp_fst (gam sig)).1.sub (hβ.comp_snd π).1)
    · refine ae_of_all _ fun q => ?_
      show ‖max (L q.1 - β q.2) 0‖ ≤ ‖L q.1‖ + ‖β q.2‖
      rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith [le_abs_self (L q.1), neg_abs_le (β q.2)])
        (by positivity)
  have hC : ∀ p : X × Y, Cbeta sig L β p.1 p.2 = ∫ u, f p u ∂(gam sig) := fun p => by
    simp only [Cbeta, Prod.mk.eta, hfdef]
  simp_rw [hC]
  exact hf.integral_prod_left

/-- Step (7) of the proof of Theorem 1 (Tonelli): for a coupling `π` and `β ∈ L¹(γσ)`,
`H(π, β) = ∫ β dΓσ + E_π[C^β]`. -/
lemma H_eq (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) (β : ℝ → ℝ)
    (hβ : Integrable β (gam sig)) :
    H sig L π β = (((∫ u, β u ∂(Gam sig)) + ∫ p, Cbeta sig L β p.1 p.2 ∂π : ℝ) : EReal) := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hL := L_int hA hπ
  set f : (X × Y) → ℝ → ℝ := fun p u => max (L p - β u) 0 with hfdef
  have hf : Integrable (Function.uncurry f) (π.prod (gam sig)) := by
    refine Integrable.mono' ((hL.comp_fst (gam sig)).norm.add ((hβ.comp_snd π).norm)) ?_ ?_
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
        ((hL.comp_fst (gam sig)).1.sub (hβ.comp_snd π).1)
    · refine ae_of_all _ fun q => ?_
      show ‖max (L q.1 - β q.2) 0‖ ≤ ‖L q.1‖ + ‖β q.2‖
      rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith [le_abs_self (L q.1), neg_abs_le (β q.2)])
        (by positivity)
  have hG : Integrable (fun u => ∫ p, f p u ∂π) (gam sig) := hf.integral_prod_right
  have hswap : ∫ p, ∫ u, f p u ∂(gam sig) ∂π = ∫ u, ∫ p, f p u ∂π ∂(gam sig) :=
    integral_integral_swap hf
  have hC : ∀ p : X × Y, Cbeta sig L β p.1 p.2 = ∫ u, f p u ∂(gam sig) := fun p => by
    simp only [Cbeta, Prod.mk.eta, hfdef]
  have hG' : Integrable (fun u => (1 - u)⁻¹ * ∫ p, f p u ∂π) (Gam sig) := by
    rw [int_Gam_iff]
    refine hG.congr ?_
    filter_upwards [gam_ae_Ico sig] with u hu
    have : (1 - u) ≠ 0 := by linarith [hu.2]
    field_simp
  have hGint : ∫ u, (1 - u)⁻¹ * ∫ p, f p u ∂π ∂(Gam sig) = ∫ u, ∫ p, f p u ∂π ∂(gam sig) := by
    rw [integral_Gam]
    apply integral_congr_ae
    filter_upwards [gam_ae_Ico sig] with u hu
    have : (1 - u) ≠ 0 := by linarith [hu.2]
    field_simp
  have hF : Integrable (fun u => β u + (1 - u)⁻¹ * ∫ p, f p u ∂π) (Gam sig) :=
    (int_Gam_of_int_gam sig hβ).add hG'
  unfold H extIntegral
  rw [if_pos hF]
  congr 1
  rw [integral_add (int_Gam_of_int_gam sig hβ) hG', hGint, ← hswap]
  simp only [hC]

end Main


lemma int_pos {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ}
    (hL : Integrable L π)
    (b : ℝ) : Integrable (fun p => max (L p - b) 0) π :=
  (hL.sub (integrable_const b)).pos_part

lemma g_convex {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ} (hL : Integrable L π)
    {α : ℝ} (hα : α < 1) : ConvexOn ℝ Set.univ (fun b => g α b π L) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  have key : ∫ p, max (L p - (a * x + b * y)) 0 ∂π ≤
      a * ∫ p, max (L p - x) 0 ∂π + b * ∫ p, max (L p - y) 0 ∂π := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((int_pos hL x).const_mul a) ((int_pos hL y).const_mul b)]
    refine integral_mono (int_pos hL _) (((int_pos hL x).const_mul a).add
      ((int_pos hL y).const_mul b)) fun p => ?_
    have e : L p - (a * x + b * y) = a * (L p - x) + b * (L p - y) := by
      linear_combination (-(L p)) * hab
    show max (L p - (a * x + b * y)) 0 ≤ a * max (L p - x) 0 + b * max (L p - y) 0
    rw [e]
    exact max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  simp only [g, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left key hc
  nlinarith

lemma Φcont {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π]
    {L : W → ℝ} (hL : Integrable L π) : Continuous (fun b => ∫ p, max (L p - b) 0 ∂π) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub (int_pos hL s) (int_pos hL t)]
  have := norm_integral_le_of_norm_le_const (μ := π)
    (f := fun p => max (L p - s) 0 - max (L p - t) 0) (C := |s - t|)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_abs (L p - s) (L p - t) 0
      rwa [show L p - s - (L p - t) = -(s - t) by ring, abs_neg] at this)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  simpa using this

end MSRProp3Aux

open MSRProp3Found MSRProp3Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    (∀ β : ℝ → ℝ, Integrable β (gam sig) →
      ∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
        H sig L π' β ≤ H sig L π β) ∧
    (∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
      (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π' β) ≤
        ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β) ∧
    (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)),
        ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β) =
      ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν,
        ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β := by
  classical
  set P := Pset μ ν with hPdef
  have hPc := Pset_isCompact μ ν
  have hPne := Pset_nonempty μ ν
  -- the real-valued objective
  set J : (ℝ → ℝ) → ProbabilityMeasure (X × Y) → ℝ := fun β π =>
    (∫ u, β u ∂(Gam sig)) + ∫ p, Cbeta sig L β p.1 p.2 ∂(π : Measure (X × Y)) with hJdef
  have hHJm : ∀ β, Integrable β (gam sig) → ∀ π (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν),
      H sig L π β = ((J β ⟨π, hπ.1⟩ : ℝ) : EReal) := fun β hβ π hπ => H_eq hA hπ β hβ
  -- upper semicontinuity on `P`
  have hJusc : ∀ β, Integrable β (gam sig) → UpperSemicontinuousOn (J β) P := by
    intro β hβ π hπ y hy
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨x, hx, hfreq⟩ := Filter.frequently_iff_seq_frequently.1 hcon
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hlim : Tendsto (x ∘ φ) atTop (𝓝[P] π) := hx.comp hφ.tendsto_atTop
    rw [tendsto_nhdsWithin_iff] at hlim
    obtain ⟨hlim1, hlim2⟩ := hlim
    obtain ⟨N, hN⟩ := eventually_atTop.1 hlim2
    set πs : ℕ → ProbabilityMeasure (X × Y) := fun n => x (φ (n + N)) with hπs
    have hlim' : Tendsto πs atTop (𝓝 π) := hlim1.comp (tendsto_add_atTop_nat N)
    have hP' : ∀ n, (πs n : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν :=
      fun n => hN (n + N) (by omega)
    have hls := (proposition_2 μ ν sig L hA).2.1 β hβ πs π hP' hπ hlim'
    rw [hHJm β hβ _ hπ] at hls
    have hge : (y : EReal) ≤ limsup (fun n => H sig L (πs n : Measure (X × Y)) β) atTop := by
      refine le_limsup_of_frequently_le (Frequently.of_forall fun n => ?_) (by isBoundedDefault)
      rw [hHJm β hβ _ (hP' n)]
      exact EReal.coe_le_coe_iff.2 (not_lt.1 (hφP (n + N)))
    have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hy) (hge.trans hls)
    exact lt_irrefl _ this
  refine ⟨?_, ?_, ?_⟩
  · -- (a) attainment of `max_π H(π, β)`
    intro β hβ
    obtain ⟨π0, hπ0, hmax⟩ := (hJusc β hβ).exists_isMaxOn hPne hPc
    refine ⟨π0, hπ0, fun π' hπ' => ?_⟩
    rw [hHJm β hβ _ hπ', hHJm β hβ _ hπ0]
    exact EReal.coe_le_coe_iff.2 (isMaxOn_iff.1 hmax ⟨π', hπ'.1⟩ hπ')
  · -- (b) attainment of `max_π inf_β H(π, β)`
    set Φ : ProbabilityMeasure (X × Y) → EReal := fun π =>
      ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), ((J β π : ℝ) : EReal) with hΦ
    have hΦusc : UpperSemicontinuousOn Φ P :=
      upperSemicontinuousOn_iInf fun β => upperSemicontinuousOn_iInf fun hβ =>
        continuous_coe_real_ereal.comp_upperSemicontinuousOn (hJusc β hβ)
          (fun a b h => EReal.coe_le_coe_iff.2 h)
    obtain ⟨π1, hπ1, hmax⟩ := hΦusc.exists_isMaxOn hPne hPc
    have hΦeq : ∀ π (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν),
        (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β) = Φ ⟨π, hπ.1⟩ := by
      intro π hπ
      exact iInf_congr fun β => iInf_congr fun hβ => hHJm β hβ π hπ
    refine ⟨π1, hπ1, fun π' hπ' => ?_⟩
    rw [hΦeq _ hπ', hΦeq _ hπ1]
    exact isMaxOn_iff.1 hmax ⟨π', hπ'.1⟩ hπ'
  · -- (c) the minimax equality
    apply le_antisymm
    swap
    · exact iSup₂_le fun π hπ => le_iInf₂ fun β hβ =>
        (iInf₂_le β hβ).trans (le_iSup₂ (f := fun π _ => H sig L π β) π hπ)
    by_contra hlt
    push Not at hlt
    obtain ⟨t, hSt, htT⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hcov : ∀ π ∈ P, ∃ β, Integrable β (gam sig) ∧ J β π < t := by
      intro π hπ
      have h1 : (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L (π : Measure (X × Y)) β)
          < t := lt_of_le_of_lt (le_iSup₂ (f := fun π _ =>
            ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β) (π : Measure (X × Y)) hπ) hSt
      obtain ⟨β, hβ'⟩ := iInf_lt_iff.1 h1
      obtain ⟨hβ, hβ''⟩ := iInf_lt_iff.1 hβ'
      rw [hHJm β hβ _ hπ] at hβ''
      exact ⟨β, hβ, EReal.coe_lt_coe_iff.1 hβ''⟩
    choose! bf hbfi hbft using hcov
    have hnbhd : ∀ π ∈ P, ∃ O : Set (ProbabilityMeasure (X × Y)), IsOpen O ∧ π ∈ O ∧
        ∀ π' ∈ O ∩ P, J (bf π) π' < t := by
      intro π hπ
      have := hJusc (bf π) (hbfi π hπ) π hπ t (hbft π hπ)
      obtain ⟨O, hO, hπO, hOsub⟩ := mem_nhdsWithin.1 this
      exact ⟨O, hO, hπO, fun π' hπ' => hOsub hπ'⟩
    choose! O hOopen hπO hOt using hnbhd
    obtain ⟨F, hF⟩ := hPc.elim_finite_subcover (fun π : P => O π) (fun π => hOopen π π.2)
      (fun π hπ => Set.mem_iUnion.2 ⟨⟨π, hπ⟩, hπO π hπ⟩)
    -- the finitely many `βᵢ`
    set κ := {i // i ∈ F}
    set bi : κ → ℝ → ℝ := fun k => bf k.1.1 with hbi
    have hbii : ∀ k : κ, Integrable (bi k) (gam sig) := fun k => hbfi _ k.1.2
    have hfin : ∀ π ∈ P, ∃ k : κ, J (bi k) π < t := by
      intro π hπ
      obtain ⟨i, hi⟩ := Set.mem_iUnion₂.1 (hF hπ)
      exact ⟨⟨i, hi.1⟩, hOt i.1 i.2 π ⟨hi.2, hπ⟩⟩
    -- the convex sets to separate
    set Jv : ProbabilityMeasure (X × Y) → κ → ℝ := fun π k => J (bi k) π
    set S' : Set (κ → ℝ) := {s | ∃ π ∈ P, ∀ k, s k ≤ Jv π k} with hS'
    set U : Set (κ → ℝ) := ⋂ k, {u | (t : ℝ) < u k} with hU
    have hUopen : IsOpen U := isOpen_iInter_of_finite fun k =>
      isOpen_lt continuous_const (continuous_apply k)
    have hUconv : Convex ℝ U := by
      intro u1 hu1 u2 hu2 a b ha hb hab
      simp only [hU, Set.mem_iInter, Set.mem_setOf_eq] at hu1 hu2 ⊢
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hu1 k
      have h2 := hu2 k
      rcases ha.eq_or_lt with ha0 | ha0
      · rw [← ha0] at hab ⊢; rw [show b = 1 by linarith]; linarith
      · have : 0 < a * (u1 k - t) := mul_pos ha0 (by linarith)
        have : 0 ≤ b * (u2 k - t) := mul_nonneg hb (by linarith)
        have e : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
        nlinarith
    -- mixtures of couplings
    have hmixP : ∀ π1 ∈ P, ∀ π2 ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∃ πm ∈ P, ∀ k, a * Jv π1 k + b * Jv π2 k = Jv πm k := by
      intro π1 h1 π2 h2 a b ha hb hab
      set m : Measure (X × Y) := ENNReal.ofReal a • (π1 : Measure (X × Y)) +
        ENNReal.ofReal b • (π2 : Measure (X × Y)) with hm
      have hab' : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
        rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
      haveI hmP : IsProbabilityMeasure m := by
        refine ⟨?_⟩
        simp only [hm, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        exact hab'
      have hmplan : m ∈ MongeKantorovichYao.transferencePlans μ ν := by
        refine ⟨hmP, ?_, ?_⟩
        · rw [hm, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
            h1.2.1, h2.2.1, ← add_smul, hab', one_smul]
        · rw [hm, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
            h1.2.2, h2.2.2, ← add_smul, hab', one_smul]
      refine ⟨⟨m, hmP⟩, hmplan, fun k => ?_⟩
      simp only [Jv, hJdef]
      have i1 := C_int hA h1 (bi k) (hbii k)
      have i2 := C_int hA h2 (bi k) (hbii k)
      show _ = (∫ u, bi k u ∂(Gam sig)) + ∫ p, Cbeta sig L (bi k) p.1 p.2 ∂m
      rw [hm, integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
        (i2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]
      linear_combination (∫ u, bi k u ∂(Gam sig)) * hab
    have hS'conv : Convex ℝ S' := by
      intro s1 hs1 s2 hs2 a b ha hb hab
      obtain ⟨π1, h1, hs1'⟩ := hs1
      obtain ⟨π2, h2, hs2'⟩ := hs2
      obtain ⟨πm, hm, hmJ⟩ := hmixP π1 h1 π2 h2 a b ha hb hab
      refine ⟨πm, hm, fun k => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hmJ k]
      have := hs1' k
      have := hs2' k
      nlinarith
    have hdisj : Disjoint U S' := by
      refine Set.disjoint_left.2 fun u hu hs => ?_
      obtain ⟨π, hπ, hsπ⟩ := hs
      obtain ⟨k, hk⟩ := hfin π hπ
      have h1 : (t : ℝ) < u k := Set.mem_iInter.1 hu k
      have h2 := hsπ k
      simp only [Jv] at h2
      linarith
    obtain ⟨f, c, hfU, hfS⟩ := geometric_hahn_banach_open hUconv hUopen hS'conv hdisj
    -- `f` in coordinates
    set w : κ → ℝ := fun k => f (Pi.single k 1) with hw
    have hf_apply : ∀ x : κ → ℝ, f x = ∑ k, x k * w k := by
      intro x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Pi.single k (x k) = x k • (Pi.single k (1 : ℝ) : κ → ℝ) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
    have hu0 : (fun _ => (t : ℝ) + 1) ∈ U := Set.mem_iInter.2 fun k => by
      show (t : ℝ) < t + 1; linarith
    have hw_nonpos : ∀ k, w k ≤ 0 := by
      intro k
      by_contra hk
      push Not at hk
      set r := (c - f (fun _ => (t : ℝ) + 1)) / w k + 1 with hr
      have hr0 : 0 < r := by
        have : 0 < c - f (fun _ => (t : ℝ) + 1) := by linarith [hfU _ hu0]
        rw [hr]; positivity
      have hmem : (fun _ => (t : ℝ) + 1) + r • (Pi.single k (1 : ℝ) : κ → ℝ) ∈ U := by
        refine Set.mem_iInter.2 fun j => ?_
        show (t : ℝ) < (((fun _ => (t : ℝ) + 1) + r • (Pi.single k (1 : ℝ) : κ → ℝ) : κ → ℝ) j)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hjk : j = k
        · subst hjk; simp; linarith
        · simp [Pi.single_apply, hjk]
      have h1 := hfU _ hmem
      rw [map_add, map_smul, smul_eq_mul] at h1
      have h2 : r * w k = (c - f (fun _ => (t : ℝ) + 1)) + w k := by
        rw [hr]; field_simp
      linarith
    set W := ∑ k, -w k with hW
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => by linarith [hw_nonpos k]
    obtain ⟨π0, hπ0⟩ := hPne
    have hS'ne : (fun k => Jv π0 k) ∈ S' := ⟨π0, hπ0, fun k => le_rfl⟩
    have hWpos : 0 < W := by
      rcases hW0.eq_or_lt with h | h
      · exfalso
        have hall : ∀ k ∈ Finset.univ, -w k = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by linarith [hw_nonpos k]).1 h.symm
        have hf0 : ∀ x, f x = 0 := fun x => by
          rw [hf_apply]
          exact Finset.sum_eq_zero fun k _ => by
            have := hall k (Finset.mem_univ k); rw [show w k = 0 by linarith, mul_zero]
        have := hfU _ hu0
        have := hfS _ hS'ne
        rw [hf0] at *
        linarith
      · exact h
    set lam : κ → ℝ := fun k => -w k / W with hlam
    have hlam0 : ∀ k, 0 ≤ lam k := fun k => div_nonneg (by linarith [hw_nonpos k]) hWpos.le
    have hlam1 : ∑ k, lam k = 1 := by
      simp only [hlam]
      rw [← Finset.sum_div, ← hW, div_self hWpos.ne']
    -- `∑ λₖ Jₖ(π) ≤ t` on `P`
    have hcomb : ∀ π ∈ P, ∑ k, lam k * Jv π k ≤ t := by
      intro π hπ
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have huε : (fun _ => (t : ℝ) + ε) ∈ U := Set.mem_iInter.2 fun k => by
        show (t : ℝ) < t + ε; linarith
      have h1 := hfU _ huε
      have h2 := hfS _ (⟨π, hπ, fun k => le_rfl⟩ : (fun k => Jv π k) ∈ S')
      rw [hf_apply] at h1 h2
      have e1 : ∑ k, (t + ε) * w k = -((t + ε) * W) := by
        rw [← Finset.mul_sum, hW, Finset.sum_neg_distrib]; ring
      have e2 : ∑ k, lam k * Jv π k = (∑ k, Jv π k * (-w k)) / W := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hlam]; ring
      have e3 : ∑ k, Jv π k * (-w k) = -(∑ k, Jv π k * w k) := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [e1] at h1
      rw [e2, e3, div_lt_iff₀ hWpos]
      linarith
    -- the averaged threshold function
    set βb : ℝ → ℝ := ∑ k, lam k • bi k with hβb
    have hβb_apply : ∀ u, βb u = ∑ k, lam k * bi k u := fun u => by
      rw [hβb, Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]
    have hβbi : Integrable βb (gam sig) :=
      integrable_finsetSum' _ fun k _ => (hbii k).smul (lam k)
    have hJb : ∀ π ∈ P, J βb π ≤ ∑ k, lam k * Jv π k := by
      intro π hπ
      haveI : IsProbabilityMeasure (π : Measure (X × Y)) := inferInstance
      simp only [Jv, hJdef]
      have hint1 : ∫ u, βb u ∂(Gam sig) = ∑ k, lam k * ∫ u, bi k u ∂(Gam sig) := by
        simp_rw [hβb_apply]
        rw [integral_finsetSum _ fun k _ => ((int_Gam_of_int_gam sig (hbii k)).const_mul _)]
        exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
      have hCpt : ∀ x y, Cbeta sig L βb x y ≤ ∑ k, lam k * Cbeta sig L (bi k) x y := by
        intro x y
        have hi : ∀ k, Integrable (fun u => max (L (x, y) - bi k u) 0) (gam sig) :=
          fun k => (lemma_1 μ ν sig L hA (bi k) (hbii k)).2.1 x y
        unfold Cbeta
        calc ∫ u, max (L (x, y) - βb u) 0 ∂(gam sig)
            ≤ ∫ u, ∑ k, lam k * max (L (x, y) - bi k u) 0 ∂(gam sig) := by
              refine integral_mono ((lemma_1 μ ν sig L hA βb hβbi).2.1 x y)
                (integrable_finsetSum _ fun k _ => (hi k).const_mul _) fun u => ?_
              have e : L (x, y) - βb u = ∑ k, lam k * (L (x, y) - bi k u) := by
                rw [hβb_apply]
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]
              show max (L (x, y) - βb u) 0 ≤ ∑ k, lam k * max (L (x, y) - bi k u) 0
              rw [e]
              exact max_le (Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_left (le_max_left _ _) (hlam0 k))
                (Finset.sum_nonneg fun k _ => mul_nonneg (hlam0 k) (le_max_right _ _))
          _ = ∑ k, lam k * ∫ u, max (L (x, y) - bi k u) 0 ∂(gam sig) := by
              rw [integral_finsetSum _ fun k _ => (hi k).const_mul _]
              exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
      have hint2 : ∫ p, Cbeta sig L βb p.1 p.2 ∂(π : Measure (X × Y)) ≤
          ∑ k, lam k * ∫ p, Cbeta sig L (bi k) p.1 p.2 ∂(π : Measure (X × Y)) := by
        simp_rw [← integral_const_mul]
        rw [← integral_finsetSum _ fun k _ => (C_int hA hπ (bi k) (hbii k)).const_mul _]
        refine integral_mono (C_int hA hπ βb hβbi)
          (integrable_finsetSum _ fun k _ => (C_int hA hπ (bi k) (hbii k)).const_mul _)
          fun p => ?_
        simp only [Finset.sum_apply]
        exact hCpt p.1 p.2
      show (∫ u, βb u ∂(Gam sig)) + ∫ p, Cbeta sig L βb p.1 p.2 ∂(π : Measure (X × Y)) ≤
        ∑ k, lam k * ((∫ u, bi k u ∂(Gam sig)) +
          ∫ p, Cbeta sig L (bi k) p.1 p.2 ∂(π : Measure (X × Y)))
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hint1]
      linarith
    -- conclusion
    have hT : (⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)),
        ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β) ≤ (t : EReal) := by
      refine (iInf₂_le βb hβbi).trans (iSup₂_le fun π hπ => ?_)
      rw [hHJm βb hβbi π hπ]
      exact EReal.coe_le_coe_iff.2 ((hJb ⟨π, hπ.1⟩ hπ).trans (hcomb ⟨π, hπ.1⟩ hπ))
    exact absurd (lt_of_lt_of_le htT hT) (lt_irrefl _)
