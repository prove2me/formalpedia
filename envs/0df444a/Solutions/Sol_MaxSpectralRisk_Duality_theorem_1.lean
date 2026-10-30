-- Prove2me | solution 1 for MaxSpectralRisk.Duality.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:36:41.433524+00:00
-- url     : https://prove2.me/submissions/97e8abcd-017a-4b18-b0e9-4bdc1469f357

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting
import Theorems.Thm_MaxSpectralRisk_Duality_step_6
import Theorems.Thm_MaxSpectralRisk_Duality_proposition_3
import Theorems.Thm_MaxSpectralRisk_Duality_lemma_4
import Theorems.Thm_MaxSpectralRisk_Duality_es_representation
import Theorems.Thm_MaxSpectralRisk_Duality_eq_2

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRThm1Aux

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

lemma K_eq_inf (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    K sig L π = ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β := by
  obtain ⟨-, -, -, h4⟩ := lemma_4 μ ν sig L hA π hπ
  apply le_antisymm
  · refine le_iInf₂ fun β hβ => ?_
    have hβ'm : Measurable (hβ.1.mk β) := hβ.1.stronglyMeasurable_mk.measurable
    have hae' : β =ᵐ[Gam sig] hβ.1.mk β := (Gam_ac_gam sig).ae_le hβ.1.ae_eq_mk
    have : H sig L π β = extIntegral (fun u => g u (hβ.1.mk β u) π L) (Gam sig) := by
      unfold H extIntegral g
      have hcongr : (fun u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π) =ᵐ[Gam sig]
          (fun u => hβ.1.mk β u + (1 - u)⁻¹ * ∫ p, max (L p - hβ.1.mk β u) 0 ∂π) := by
        filter_upwards [hae'] with u hu
        rw [hu]
      rw [integrable_congr hcongr, integral_congr_ae hcongr]
    rw [this]
    unfold K
    exact iInf₂_le (f := fun (β : ℝ → ℝ) (_ : Measurable β) =>
      extIntegral (fun u => g u (β u) π L) (Gam sig)) _ hβ'm
  · rw [h4]
    refine le_iInf₂ fun β hβ => ?_
    have hac := gam_ac_Gam sig
    have hβγ : MemLp β ⊤ (gam sig) := by
      refine ⟨hβ.1.mono_ac hac, ?_⟩
      have h2 := hβ.2
      rw [eLpNorm_exponent_top] at h2 ⊢
      exact lt_of_le_of_lt (eLpNormEssSup_mono_measure _ hac) h2
    exact iInf₂_le_of_le β (hβγ.integrable le_top) le_rfl

lemma specRisk_eq_K (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    ((specRisk sig π L : ℝ) : EReal) = K sig L π := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hLm := L_meas hA
  have hL := L_int hA hπ
  obtain ⟨-, hK2, -, -⟩ := lemma_4 μ ν sig L hA π hπ
  obtain ⟨hint, hrep⟩ := es_representation sig π L hLm hL
  obtain ⟨-, hES0, -, -⟩ := eq_2 π L hLm hL
  rw [hK2, hrep]
  congr 1
  have hIco : (Gam sig).restrict (Set.Ico 0 1) = Gam sig :=
    Measure.restrict_eq_self_of_ae_mem (Gam_ae_Ico sig)
  have h1 : ∫ u, ES u π L ∂(Gam sig) = ∫ u in Set.Ico (0 : ℝ) 1, ES u π L ∂(Gam sig) := by
    rw [hIco]
  rw [h1, ← Set.Ioo_insert_left zero_lt_one, Set.insert_eq,
    setIntegral_union (Set.disjoint_singleton_left.2 (fun h => (lt_irrefl _ h.1)))
      measurableSet_Ioo hint.integrableOn hint.integrableOn,
    integral_singleton, hES0, smul_eq_mul]

end Main

end MSRThm1Aux

open MSRThm1Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    V sig L μ ν = D sig L μ ν := by
  have hP3 := (proposition_3 μ ν sig L hA).2.2
  have hV : V sig L μ ν = ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν,
      ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)), H sig L π β := by
    unfold V
    refine iSup_congr fun π => iSup_congr fun hπ => ?_
    rw [specRisk_eq_K hA hπ, K_eq_inf hA hπ]
  have hD : D sig L μ ν = ⨅ (β : ℝ → ℝ) (_ : Integrable β (gam sig)),
      ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β := by
    unfold D
    refine iInf_congr fun β => iInf_congr fun hβ => ?_
    have h6 := (step_6 μ ν sig L hA β hβ).1
    calc (⨅ φψ ∈ PhiC sig L μ ν β,
          (((∫ u, β u ∂(Gam sig)) + (∫ x, φψ.1 x ∂μ) + (∫ y, φψ.2 y ∂ν) : ℝ) : EReal))
        = ((∫ u, β u ∂(Gam sig) : ℝ) : EReal) + ⨅ φψ ∈ PhiC sig L μ ν β,
            ((((∫ x, φψ.1 x ∂μ) + ∫ y, φψ.2 y ∂ν) : ℝ) : EReal) := by
          rw [coe_add_iInf]
          refine iInf_congr fun φψ => ?_
          rw [coe_add_iInf]
          refine iInf_congr fun _ => ?_
          rw [add_assoc, EReal.coe_add]
      _ = ((∫ u, β u ∂(Gam sig) : ℝ) : EReal) + ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν,
            ((∫ p, Cbeta sig L β p.1 p.2 ∂π : ℝ) : EReal) := by rw [h6]
      _ = ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν, H sig L π β := by
          rw [coe_add_iSup]
          refine iSup_congr fun π => ?_
          rw [coe_add_iSup]
          refine iSup_congr fun hπ => ?_
          rw [H_eq hA hπ β hβ, EReal.coe_add]
  rw [hV, hD, hP3]
