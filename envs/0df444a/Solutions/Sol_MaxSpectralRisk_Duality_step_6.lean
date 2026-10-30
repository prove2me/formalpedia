-- Prove2me | solution 1 for MaxSpectralRisk.Duality.step_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:19:59.915709+00:00
-- url     : https://prove2.me/submissions/7abf7188-3099-4c28-aebf-fcd66c2e13ab

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting
import Theorems.Thm_MongeKantorovichYao_transferencePlansOf_isTight
import Theorems.Thm_MongeKantorovichYao_monge_kantorovich_duality
import Theorems.Thm_MaxSpectralRisk_Duality_lemma_1
import Theorems.Thm_MaxSpectralRisk_Duality_proposition_3

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRStep6Approx

/-- A nonnegative lower semicontinuous function on a metrizable space is the pointwise increasing
limit of continuous functions `0 ≤ cₖ ≤ min(f, k)` (Lipschitz regularization). -/
lemma lsc_approx {Z : Type*} [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [Nonempty Z] {f : Z → ℝ} (hf : LowerSemicontinuous f) (hf0 : ∀ z, 0 ≤ f z) :
    ∃ c : ℕ → Z → ℝ, (∀ k, Continuous (c k)) ∧ (∀ k z, 0 ≤ c k z) ∧ (∀ k z, c k z ≤ k) ∧
      (∀ k z, c k z ≤ f z) ∧ (∀ z, Monotone (fun k => c k z)) ∧
      (∀ z, Tendsto (fun k => c k z) atTop (𝓝 (f z))) := by
  letI : MetricSpace Z := TopologicalSpace.metrizableSpaceMetric Z
  set T : ℕ → Z → Z → ℝ := fun k z w => min (f w) k + k * dist z w with hT
  have hT0 : ∀ k z w, 0 ≤ T k z w := fun k z w =>
    add_nonneg (le_min (hf0 w) (Nat.cast_nonneg k)) (mul_nonneg (Nat.cast_nonneg k) dist_nonneg)
  have hbdd : ∀ k z, BddBelow (Set.range (T k z)) := fun k z =>
    ⟨0, by rintro _ ⟨w, rfl⟩; exact hT0 k z w⟩
  refine ⟨fun k z => ⨅ w, T k z w, fun k => ?_, fun k z => le_ciInf fun w => hT0 k z w,
    fun k z => ?_, fun k z => ?_, fun z k k' hkk' => ?_, fun z => ?_⟩
  · -- Lipschitz, hence continuous
    have hlip : ∀ z z', (⨅ w, T k z w) ≤ (⨅ w, T k z' w) + (k : ℝ) * dist z z' := by
      intro z z'
      have : (⨅ w, T k z w) - k * dist z z' ≤ ⨅ w, T k z' w := by
        refine le_ciInf fun w => ?_
        have h1 := ciInf_le (hbdd k z) w
        have h2 : T k z w ≤ T k z' w + k * dist z z' := by
          simp only [hT]
          have := dist_triangle z z' w
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith [dist_comm z z']
        linarith
      linarith
    exact (LipschitzWith.of_le_add_mul (Real.toNNReal k) fun z z' => by
      rw [Real.coe_toNNReal _ (Nat.cast_nonneg k)]; exact hlip z z').continuous
  · refine (ciInf_le (hbdd k z) z).trans ?_
    simp only [hT, dist_self, mul_zero, add_zero]
    exact min_le_right _ _
  · refine (ciInf_le (hbdd k z) z).trans ?_
    simp only [hT, dist_self, mul_zero, add_zero]
    exact min_le_left _ _
  · refine le_ciInf fun w => (ciInf_le (hbdd k z) w).trans ?_
    simp only [hT]
    have hkk : (k : ℝ) ≤ k' := Nat.cast_le.2 hkk'
    exact add_le_add (min_le_min le_rfl hkk) (mul_le_mul_of_nonneg_right hkk dist_nonneg)
  · rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨a', haa', ha'⟩ := exists_between ha
      have hev := hf z a' ha'
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (|a'| + 1),
        tendsto_natCast_atTop_atTop.eventually_ge_atTop ((|a'| + 1) / r)] with k hk1 hk2
      have hkr : |a'| + 1 ≤ k * r := by rwa [div_le_iff₀ hr] at hk2
      refine lt_of_lt_of_le haa' (le_ciInf fun w => ?_)
      simp only [hT]
      by_cases hw : dist w z < r
      · have := hball hw
        have : a' ≤ min (f w) k := le_min this.le (by linarith [le_abs_self a'])
        have : 0 ≤ (k : ℝ) * dist z w := mul_nonneg (Nat.cast_nonneg k) dist_nonneg
        linarith
      · push Not at hw
        have h1 : (k : ℝ) * r ≤ k * dist z w :=
          mul_le_mul_of_nonneg_left (by rwa [dist_comm]) (Nat.cast_nonneg k)
        have h2 : 0 ≤ min (f w) k := le_min (hf0 w) (Nat.cast_nonneg k)
        linarith [le_abs_self a']
    · intro b hb
      refine Eventually.of_forall fun k => lt_of_le_of_lt ?_ hb
      refine (ciInf_le (hbdd k z) z).trans ?_
      simp only [hT, dist_self, mul_zero, add_zero]
      exact min_le_left _ _

end MSRStep6Approx

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

namespace MSRStep6Aux

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

end MSRStep6Aux

open MSRStep6Approx MSRProp3Found MSRStep6Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (β : ℝ → ℝ) (hβ : Integrable β (gam sig)) :
    (⨅ φψ ∈ PhiC sig L μ ν β, (((∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν : ℝ) : EReal)) =
      ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, ((∫ p, Cbeta sig L β p.1 p.2 ∂π : ℝ) : EReal) ∧
    ∃ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
      ∫ p, Cbeta sig L β p.1 p.2 ∂π' ≤ ∫ p, Cbeta sig L β p.1 p.2 ∂π := by
  classical
  set Cf : X × Y → ℝ := fun p => Cbeta sig L β p.1 p.2 with hCf
  -- attainment, from Proposition 3
  obtain ⟨πm, hπm, hmax⟩ := (proposition_3 μ ν sig L hA).1 β hβ
  have hmaxC : ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
      ∫ p, Cf p ∂π' ≤ ∫ p, Cf p ∂πm := by
    intro π' hπ'
    have := hmax π' hπ'
    rw [H_eq hA hπ' β hβ, H_eq hA hπm β hβ] at this
    have := EReal.coe_le_coe_iff.1 this
    linarith
  refine ⟨?_, πm, hπm, hmaxC⟩
  set V := ∫ p, Cf p ∂πm with hV
  have hR : (⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, ((∫ p, Cf p ∂π : ℝ) : EReal)) =
      (V : EReal) :=
    le_antisymm (iSup₂_le fun π hπ => EReal.coe_le_coe_iff.2 (hmaxC π hπ))
      (le_iSup₂_of_le πm hπm le_rfl)
  rw [hR]
  haveI : IsProbabilityMeasure πm := hπm.1
  apply le_antisymm
  · -- the duality-gap inequality
    have key : ∀ ε > 0, ∃ φψ ∈ PhiC sig L μ ν β,
        (∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν ≤ V + ε := by
      intro ε hε
      obtain ⟨A, B, hAlsc, hAi, hBlsc, hBi, hub⟩ := hA.upper_bound
      obtain ⟨hCusc, hCint_u, -, -⟩ := lemma_1 μ ν sig L hA β hβ
      set m := (gam sig).real Set.univ with hm
      have hm0 : 0 ≤ m := measureReal_nonneg
      set k0 := ∫ u, max (-β u) 0 ∂(gam sig) with hk0
      set A' : X → ℝ := fun x => m * max (A x) 0 + k0 with hA'
      set B' : Y → ℝ := fun y => m * max (B y) 0 with hB'
      have hA'i : Integrable A' μ := (hAi.pos_part.const_mul m).add (integrable_const k0)
      have hB'i : Integrable B' ν := hBi.pos_part.const_mul m
      have hA'l : LowerSemicontinuous A' :=
        (continuous_const.mul continuous_id |>.add continuous_const :
          Continuous fun t : ℝ => m * t + k0).comp_lowerSemicontinuous
          (hAlsc.sup lowerSemicontinuous_const)
          (fun a b hab => by
          show m * a + k0 ≤ m * b + k0
          nlinarith)
      have hB'l : LowerSemicontinuous B' :=
        (continuous_const.mul continuous_id :
          Continuous fun t : ℝ => m * t).comp_lowerSemicontinuous
          (hBlsc.sup lowerSemicontinuous_const)
          (fun a b hab => mul_le_mul_of_nonneg_left hab hm0)
      -- `C^β ≤ A' ⊕ B'` off a null rectangle
      have hCbd : AERect μ ν (fun x y => Cbeta sig L β x y ≤ A' x + B' y) := by
        obtain ⟨N, hN, N', hN', hP⟩ := hub
        refine ⟨N, hN, N', hN', fun x hx y hy => ?_⟩
        have hxy := hP x hx y hy
        have hneg : Integrable (fun u => max (-β u) 0) (gam sig) := hβ.neg.pos_part
        calc Cbeta sig L β x y ≤ ∫ u, (max (A x + B y) 0 + max (-β u) 0) ∂(gam sig) :=
              integral_mono (hCint_u x y) ((integrable_const _).add hneg) fun u =>
                max_le (by linarith [le_max_left (A x + B y) 0, le_max_left (-β u) 0])
                  (add_nonneg (le_max_right _ _) (le_max_right _ _))
          _ = m * max (A x + B y) 0 + k0 := by
              rw [integral_add (integrable_const _) hneg, integral_const, smul_eq_mul]
          _ ≤ A' x + B' y := by
              have : max (A x + B y) 0 ≤ max (A x) 0 + max (B y) 0 :=
                max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
                  (add_nonneg (le_max_right _ _) (le_max_right _ _))
              simp only [hA', hB']
              nlinarith
      set Kc := ∫ x, A' x ∂μ + ∫ y, B' y ∂ν with hKc
      -- the nonnegative lsc cost `c' = (A' ⊕ B' - C)₊`
      set cp : X × Y → ℝ := fun p => max (A' p.1 + B' p.2 - Cf p) 0 with hcp
      have hcp_lsc : LowerSemicontinuous cp := by
        have h1 : LowerSemicontinuous (fun p : X × Y => -Cf p) :=
          continuous_neg.comp_upperSemicontinuous_antitone hCusc (fun a b hab => neg_le_neg hab)
        have h2 : LowerSemicontinuous (fun p : X × Y => A' p.1 + B' p.2 + -Cf p) :=
          ((hA'l.comp continuous_fst).add (hB'l.comp continuous_snd)).add h1
        have h3 := (continuous_id.max continuous_const :
          Continuous fun t : ℝ => max t 0).comp_lowerSemicontinuous h2
          (fun a b hab => max_le_max hab le_rfl)
        have e : cp = (fun t : ℝ => max t 0) ∘ (fun p : X × Y => A' p.1 + B' p.2 + -Cf p) := by
          funext p; simp only [hcp, Function.comp, sub_eq_add_neg]
        rw [e]; exact h3
      have hcp0 : ∀ p, 0 ≤ cp p := fun p => le_max_right _ _
      have hcp_ae : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν,
          cp =ᵐ[π] fun p => A' p.1 + B' p.2 - Cf p := by
        intro π hπ
        filter_upwards [aerect_ae hCbd hπ] with p hp
        simp only [hcp]
        rw [max_eq_left (by simp only [hCf]; linarith)]
      have hDi : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν,
          Integrable (fun p => A' p.1 + B' p.2 - Cf p) π := by
        intro π hπ
        haveI : IsProbabilityMeasure π := hπ.1
        exact ((int_fst hπ hA'i).add (int_snd hπ hB'i)).sub (C_int hA hπ β hβ)
      have hcpi : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν, Integrable cp π :=
        fun π hπ => (hDi π hπ).congr (hcp_ae π hπ).symm
      have hcp_int : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν,
          ∫ p, cp p ∂π = Kc - ∫ p, Cf p ∂π := by
        intro π hπ
        haveI : IsProbabilityMeasure π := hπ.1
        rw [integral_congr_ae (hcp_ae π hπ), integral_sub _ (C_int hA hπ β hβ),
          integral_add (int_fst hπ hA'i) (int_snd hπ hB'i)]
        · have e1 : ∫ p, A' p.1 ∂π = ∫ x, A' x ∂μ := by
            rw [← hπ.2.1, integral_map measurable_fst.aemeasurable
              (by rw [hπ.2.1]; exact hA'i.1)]
          have e2 : ∫ p, B' p.2 ∂π = ∫ y, B' y ∂ν := by
            rw [← hπ.2.2, integral_map measurable_snd.aemeasurable
              (by rw [hπ.2.2]; exact hB'i.1)]
          rw [e1, e2]
        · exact (int_fst hπ hA'i).add (int_snd hπ hB'i)
      -- continuous approximations
      haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
      haveI : Nonempty Y := nonempty_of_isProbabilityMeasure ν
      obtain ⟨c, hcc, hc0, hck, hcle, hcmono, hclim⟩ := lsc_approx hcp_lsc hcp0
      set cb : ℕ → BoundedContinuousFunction (X × Y) ℝ := fun k =>
        BoundedContinuousFunction.mkOfBound ⟨c k, hcc k⟩ k (fun x y => by
          simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
          constructor <;> linarith [hc0 k x, hc0 k y, hck k x, hck k y]) with hcb
      have hcb_apply : ∀ k p, cb k p = c k p := fun k p => rfl
      have hcki : ∀ k (π : Measure (X × Y)) [IsProbabilityMeasure π], Integrable (c k) π :=
        fun k π _ => (cb k).integrable π
      -- Step 1: a uniform lower bound for one `k`, by compactness of the couplings
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ π ∈ Pset μ ν,
          Kc - V - ε / 2 ≤ ∫ p, c k p ∂(π : Measure (X × Y)) := by
        by_contra hcon
        push Not at hcon
        set Kk : ℕ → Set (ProbabilityMeasure (X × Y)) := fun k =>
          Pset μ ν ∩ {π | ∫ p, cb k p ∂(π : Measure (X × Y)) ≤ Kc - V - ε / 2} with hKk
        have hKcl : ∀ k, IsClosed (Kk k) := fun k =>
          (Pset_isClosed μ ν).inter (isClosed_le
            (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (cb k))
            continuous_const)
        have hKne : ∀ k, (Kk k).Nonempty := by
          intro k
          obtain ⟨π, hπ, hlt⟩ := hcon k
          exact ⟨π, hπ, hlt.le⟩
        have hKsub : ∀ k, Kk (k + 1) ⊆ Kk k := by
          intro k π ⟨hπ, hle⟩
          have hle' : ∫ p, cb (k + 1) p ∂(π : Measure (X × Y)) ≤ Kc - V - ε / 2 := hle
          refine ⟨hπ, show ∫ p, cb k p ∂(π : Measure (X × Y)) ≤ Kc - V - ε / 2 from
            le_trans ?_ hle'⟩
          exact integral_mono (hcki k _) (hcki (k + 1) _) fun p =>
            hcmono p (Nat.le_succ k)
        have hK0 : IsCompact (Kk 0) :=
          (Pset_isCompact μ ν).of_isClosed_subset (hKcl 0) Set.inter_subset_left
        obtain ⟨πs, hπs⟩ :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Kk hKsub hKne hK0 hKcl
        have hπsK : ∀ k, πs ∈ Kk k := Set.mem_iInter.1 hπs
        have hπsP : (πs : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν :=
          (hπsK 0).1
        have hconv : Tendsto (fun k => ∫ p, c k p ∂(πs : Measure (X × Y))) atTop
            (𝓝 (∫ p, cp p ∂(πs : Measure (X × Y)))) :=
          tendsto_integral_of_dominated_convergence cp (fun k => (hcc k).aestronglyMeasurable)
            (hcpi _ hπsP) (fun k => ae_of_all _ fun p => by
              rw [Real.norm_of_nonneg (hc0 k p)]; exact hcle k p)
            (ae_of_all _ fun p => hclim p)
        have hle : ∫ p, cp p ∂(πs : Measure (X × Y)) ≤ Kc - V - ε / 2 :=
          le_of_tendsto' hconv fun k => (hπsK k).2
        rw [hcp_int _ hπsP] at hle
        have := hmaxC _ hπsP
        linarith
      -- Step 2: Kantorovich duality for the continuous cost `cₖ`
      have hMK := (MongeKantorovichYao.monge_kantorovich_duality μ ν (c k) (hcc k) (hc0 k)).2
      set r := Kc - V - ε / 2 with hr
      have hlow : (r : EReal) ≤ ((⨅ π ∈ MongeKantorovichYao.transferencePlans μ ν,
          ∫⁻ p, ENNReal.ofReal (c k p) ∂π : ENNReal) : EReal) := by
        have : ENNReal.ofReal r ≤ ⨅ π ∈ MongeKantorovichYao.transferencePlans μ ν,
            ∫⁻ p, ENNReal.ofReal (c k p) ∂π := by
          refine le_iInf₂ fun π hπ => ?_
          haveI : IsProbabilityMeasure π := hπ.1
          rw [← ofReal_integral_eq_lintegral_ofReal (hcki k π) (ae_of_all _ (hc0 k))]
          exact ENNReal.ofReal_le_ofReal (hk ⟨π, hπ.1⟩ hπ)
        calc (r : EReal) ≤ ((max r 0 : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (le_max_left _ _)
          _ = ((ENNReal.ofReal r : ENNReal) : EReal) := EReal.coe_ennreal_ofReal.symm
          _ ≤ _ := EReal.coe_ennreal_le_coe_ennreal_iff.2 this
      rw [hMK] at hlow
      have hlt : ((r - ε / 2 : ℝ) : EReal) < _ :=
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hlow
      obtain ⟨ψ, h1⟩ := lt_iSup_iff.1 hlt
      obtain ⟨φ, h2⟩ := lt_iSup_iff.1 h1
      obtain ⟨hfeas, h3⟩ := lt_iSup_iff.1 h2
      have h3' := EReal.coe_lt_coe_iff.1 h3
      -- Step 3: the dual pair `(A' - ψ, B' - φ)`
      have hmem : ((fun x => A' x - ψ x), (fun y => B' y - φ y)) ∈ PhiC sig L μ ν β := by
        refine ⟨hA'i.sub (ψ.integrable μ), hB'i.sub (φ.integrable ν), ?_⟩
        obtain ⟨N, hN, N', hN', hP⟩ := hCbd
        refine ⟨N, hN, N', hN', fun x hx y hy => ?_⟩
        have hb := hP x hx y hy
        have hf := hfeas x y
        have hc := hcle k (x, y)
        simp only [hcp, hCf] at hc
        rw [max_eq_left (by linarith)] at hc
        show Cbeta sig L β x y ≤ (A' x - ψ x) + (B' y - φ y)
        linarith
      have hval : (∫ x, (fun x => A' x - ψ x) x ∂μ) + ∫ y, (fun y => B' y - φ y) y ∂ν =
          Kc - ((∫ x, ψ x ∂μ) + ∫ y, φ y ∂ν) := by
        simp only
        rw [integral_sub hA'i (ψ.integrable μ), integral_sub hB'i (φ.integrable ν), hKc]
        ring
      exact ⟨_, hmem, by rw [hval]; linarith⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    obtain ⟨φψ, hmem, hle⟩ := key (r - V) (by have := EReal.coe_lt_coe_iff.1 hr1; linarith)
    have h := iInf₂_le (f := fun φψ (_ : φψ ∈ PhiC sig L μ ν β) =>
      (((∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν : ℝ) : EReal)) φψ hmem
    have h' : (((∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν : ℝ) : EReal) ≤ r :=
      EReal.coe_le_coe_iff.2 (by linarith)
    exact absurd (lt_of_lt_of_le hr2 (h.trans h')) (lt_irrefl _)
  · -- weak duality
    refine le_iInf₂ fun φψ hφψ => ?_
    obtain ⟨hφ, hψ, hrect⟩ := hφψ
    have hφπ := int_fst hπm hφ
    have hψπ := int_snd hπm hψ
    have h2 : ∫ p, Cf p ∂πm ≤ ∫ p, (φψ.1 p.1 + φψ.2 p.2) ∂πm :=
      integral_mono_ae (C_int hA hπm β hβ) (hφπ.add hψπ) (aerect_ae hrect hπm)
    have h3 : ∫ p, (φψ.1 p.1 + φψ.2 p.2) ∂πm = (∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν := by
      rw [integral_add hφπ hψπ]
      have e1 : ∫ p, φψ.1 p.1 ∂πm = ∫ x, φψ.1 x ∂μ := by
        rw [← hπm.2.1, integral_map measurable_fst.aemeasurable (by rw [hπm.2.1]; exact hφ.1)]
      have e2 : ∫ p, φψ.2 p.2 ∂πm = ∫ y, φψ.2 y ∂ν := by
        rw [← hπm.2.2, integral_map measurable_snd.aemeasurable (by rw [hπm.2.2]; exact hψ.1)]
      rw [e1, e2]
    exact EReal.coe_le_coe_iff.2 (by linarith)
