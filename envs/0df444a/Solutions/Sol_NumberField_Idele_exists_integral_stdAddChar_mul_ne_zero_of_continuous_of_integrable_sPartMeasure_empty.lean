-- Prove2me | solution 1 for NumberField.Idele.exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a3fafe4a-5c57-597d-a459-605b98d754e8

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Theorems.Thm_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
import Theorems.Thm_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Classical ENNReal NNReal
open MeasureTheory NumberField IsDedekindDomain NumberField.InfinitePlace

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace ArchTorus

variable (K : Type) [Field K] [NumberField K]

abbrev R : Type := InfiniteAdeleRing K

abbrev M : Type := mixedEmbedding.mixedSpace K

abbrev e : R K ≃+* M K := InfiniteAdeleRing.ringEquiv_mixedSpace K

theorem e_apply_fst (x : R K) (w : {w : InfinitePlace K // w.IsReal}) :
    (e K x).1 w = Completion.extensionEmbeddingOfIsReal w.2 (x w.1) := rfl

theorem e_apply_snd (x : R K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (e K x).2 w = Completion.extensionEmbedding w.1 (x w.1) := rfl

abbrev Rpi : Type := (v : InfinitePlace K) → v.Completion

def ePi : Rpi K ≃+* M K := e K

theorem ePi_apply (x : Rpi K) : ePi K x = e K x := rfl

theorem norm_ePi (x : Rpi K) : ‖ePi K x‖ = ‖x‖ := by
  have h1 : ∀ w : {w : InfinitePlace K // w.IsReal}, ‖(ePi K x).1 w‖ = ‖x w.1‖ := fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) (x w.1)
  have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex}, ‖(ePi K x).2 w‖ = ‖x w.1‖ := fun w =>
    (Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) (x w.1)
  apply le_antisymm
  · rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg (norm_nonneg _),
      pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    exact ⟨fun w => (h1 w).le.trans (norm_le_pi_norm x w.1), fun w => (h2 w).le.trans (norm_le_pi_norm x w.1)⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro w
    by_cases hw : w.IsReal
    · calc ‖x w‖ = ‖(ePi K x).1 ⟨w, hw⟩‖ := (h1 ⟨w, hw⟩).symm
        _ ≤ ‖(ePi K x).1‖ := norm_le_pi_norm _ _
        _ ≤ ‖ePi K x‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
      calc ‖x w‖ = ‖(ePi K x).2 ⟨w, hw'⟩‖ := (h2 ⟨w, hw'⟩).symm
        _ ≤ ‖(ePi K x).2‖ := norm_le_pi_norm _ _
        _ ≤ ‖ePi K x‖ := by rw [Prod.norm_def]; exact le_max_right _ _

theorem isometry_ePi : Isometry (ePi K) :=
  AddMonoidHomClass.isometry_of_norm (ePi K) (norm_ePi K)

def eIso : Rpi K ≃ᵢ M K := ⟨(ePi K).toEquiv, isometry_ePi K⟩

theorem continuous_e : Continuous (e K) := (isometry_ePi K).continuous

theorem continuous_e_symm : Continuous (e K).symm := (eIso K).symm.continuous

def inlHom : R K →* AdeleRing (𝓞 K) K where
  toFun y := (y, 1)
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (mul_one 1).symm

def archIdele : (R K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (inlHom K)

theorem archIdele_val (x : (R K)ˣ) : ((archIdele K x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((x : R K), 1) := rfl

def fstUnit : (AdeleRing (𝓞 K) K)ˣ →* (R K)ˣ := Units.map (MonoidHom.fst (R K) (FiniteAdeleRing (𝓞 K) K))

theorem fstUnit_val (a : (AdeleRing (𝓞 K) K)ˣ) : ((fstUnit K a : (R K)ˣ) : R K) = (a : AdeleRing (𝓞 K) K).1 := rfl

theorem archIdele_fstUnit {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    archIdele K (fstUnit K a) = a :=
  Units.ext (Prod.ext rfl ha.symm)

def sec (z : M K) : (AdeleRing (𝓞 K) K)ˣ :=
  if hz : IsUnit ((e K).symm z) then archIdele K hz.unit else 1

theorem sec_of_isUnit {z : M K} (hz : IsUnit ((e K).symm z)) : sec K z = archIdele K hz.unit := dif_pos hz

theorem sec_e_fst {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    sec K (e K (a : AdeleRing (𝓞 K) K).1) = a := by
  have hu : IsUnit ((e K).symm (e K (a : AdeleRing (𝓞 K) K).1)) := by
    rw [RingEquiv.symm_apply_apply]; exact ⟨fstUnit K a, rfl⟩
  rw [sec_of_isUnit K hu]
  apply Units.ext
  rw [archIdele_val]
  refine Prod.ext ?_ ?_
  · exact (IsUnit.unit_spec hu).trans (RingEquiv.symm_apply_apply _ _)
  · exact ha.symm

def U : Set (M K) := {z | IsUnit z}

theorem isUnit_e_symm_iff (z : M K) : IsUnit ((e K).symm z) ↔ IsUnit z := by
  constructor
  · intro h
    have h' := h.map (e K)
    rwa [RingEquiv.apply_symm_apply] at h'
  · intro h; exact h.map (e K).symm

theorem mem_U_iff (z : M K) : z ∈ U K ↔ (∀ w, z.1 w ≠ 0) ∧ ∀ w, z.2 w ≠ 0 := by
  show IsUnit z ↔ _
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  exact and_congr (forall_congr' fun w => isUnit_iff_ne_zero) (forall_congr' fun w => isUnit_iff_ne_zero)

theorem isOpen_U : IsOpen (U K) := by
  have hU : U K = (⋂ w, {z : M K | z.1 w ≠ 0}) ∩ ⋂ w, {z : M K | z.2 w ≠ 0} := by
    ext z
    rw [mem_U_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iInter]
    rfl
  rw [hU]
  exact (isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const).inter
    (isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)

theorem volume_compl_U : volume (U K)ᶜ = 0 := by
  have hsub : (U K)ᶜ ⊆ (⋃ w, {z : M K | z.1 w = 0}) ∪ ⋃ w, {z : M K | z.2 w = 0} := by
    intro z hz
    rw [Set.mem_compl_iff, mem_U_iff, not_and_or, not_forall, not_forall] at hz
    rcases hz with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w, not_not.mp hw⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨w, not_not.mp hw⟩)
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun w => ?_)
    (measure_iUnion_null fun w => ?_))
  · let L : M K →ₗ[ℝ] ℝ := (LinearMap.proj w).comp (LinearMap.fst ℝ _ _)
    have hS : ((LinearMap.ker L : Submodule ℝ (M K)) : Set (M K)) = {z : M K | z.1 w = 0} := by
      ext z
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_setOf_eq]
      rfl
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have h1 : (1 : M K) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at h1
      exact one_ne_zero h1
    rw [← hS]
    exact Measure.addHaar_submodule volume _ hne
  · let L : M K →ₗ[ℝ] ℂ := (LinearMap.proj w).comp (LinearMap.snd ℝ _ _)
    have hS : ((LinearMap.ker L : Submodule ℝ (M K)) : Set (M K)) = {z : M K | z.2 w = 0} := by
      ext z
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_setOf_eq]
      rfl
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have h1 : (1 : M K) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at h1
      exact one_ne_zero h1
    rw [← hS]
    exact Measure.addHaar_submodule volume _ hne

theorem ae_mem_U : ∀ᵐ z ∂(volume : Measure (M K)), z ∈ U K := by
  rw [ae_iff]
  exact volume_compl_U K

theorem val_inv_apply (u : (R K)ˣ) (w : InfinitePlace K) :
    ((u⁻¹ : (R K)ˣ) : R K) w = (((u : (R K)ˣ) : R K) w)⁻¹ := by
  have h : ((u⁻¹ : (R K)ˣ) : R K) w * ((u : (R K)ˣ) : R K) w = 1 := by
    have := congrArg (fun f : R K => f w) u.inv_val
    exact this
  exact eq_inv_of_mul_eq_one_left h

theorem e_symm_apply_ne_zero {z : M K} (hz : z ∈ U K) (w : InfinitePlace K) : (e K).symm z w ≠ 0 := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  exact (Pi.isUnit_iff.mp hu w).ne_zero

theorem sec_val_of_mem {z : M K} (hz : z ∈ U K) :
    ((sec K z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((e K).symm z, 1) := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  rw [sec_of_isUnit K hu, archIdele_val, IsUnit.unit_spec]

theorem sec_inv_val_of_mem {z : M K} (hz : z ∈ U K) :
    (((sec K z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((fun w => ((e K).symm z w)⁻¹ : R K), 1) := by
  have hu : IsUnit ((e K).symm z) := (isUnit_e_symm_iff K z).mpr hz
  rw [sec_of_isUnit K hu, ← map_inv, archIdele_val]
  refine Prod.ext (funext fun w => ?_) rfl
  show ((hu.unit⁻¹ : (R K)ˣ) : R K) w = ((e K).symm z w)⁻¹
  rw [val_inv_apply, IsUnit.unit_spec]

theorem continuousOn_sec : ContinuousOn (sec K) (U K) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous fun x : U K => (((e K).symm x.1, 1) : AdeleRing (𝓞 K) K) :=
      ((continuous_e_symm K).comp continuous_subtype_val).prodMk continuous_const
    exact hc.congr fun x => (sec_val_of_mem K x.2).symm
  · have hc : Continuous fun x : U K => (((fun w => ((e K).symm x.1 w)⁻¹ : R K), 1) : AdeleRing (𝓞 K) K) := by
      refine Continuous.prodMk ?_ continuous_const
      refine continuous_pi fun w => ?_
      have hc : ContinuousOn (fun z : M K => ((e K).symm z w)⁻¹) (U K) :=
        (((continuous_apply w).comp (continuous_e_symm K)).continuousOn).inv₀
          fun z hz => e_symm_apply_ne_zero K hz w
      exact continuousOn_iff_continuous_restrict.mp hc
    exact hc.congr fun x => (sec_inv_val_of_mem K x.2).symm

def dens (z : M K) : ℝ := (∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2

theorem continuous_dens : Continuous (dens K) := by
  unfold dens
  fun_prop

theorem dens_pos {z : M K} (hz : z ∈ U K) : 0 < dens K z := by
  rw [mem_U_iff] at hz
  unfold dens
  exact mul_pos (Finset.prod_pos fun w _ => abs_pos.mpr (hz.1 w))
    (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (hz.2 w)) 2)

def densInv (z : M K) : ℝ≥0 := Real.toNNReal (dens K z)⁻¹

theorem measurable_densInv : Measurable (densInv K) :=
  ((continuous_dens K).measurable.inv).real_toNNReal

theorem densInv_eq {z : M K} (hz : z ∈ U K) :
    ((densInv K z : ℝ≥0) : ℝ≥0∞) = (ENNReal.ofReal (dens K z))⁻¹ := by
  rw [← ENNReal.ofReal_inv_of_pos (dens_pos K hz)]
  rfl

theorem withDensity_eq :
    (volume : Measure (M K)).withDensity (fun z => (ENNReal.ofReal (dens K z))⁻¹) =
      (volume : Measure (M K)).withDensity (fun z => ((densInv K z : ℝ≥0) : ℝ≥0∞)) :=
  withDensity_congr_ae ((ae_mem_U K).mono fun _ hz => (densInv_eq K hz).symm)

theorem withDensity_eq' :
    ((volume : Measure (M K)).withDensity fun z => (ENNReal.ofReal ((∏ w, |z.1 w|) * ∏ w, ‖z.2 w‖ ^ 2))⁻¹) =
      (volume : Measure (M K)).withDensity (fun z => ((densInv K z : ℝ≥0) : ℝ≥0∞)) :=
  withDensity_eq K

theorem continuousOn_densInv : ContinuousOn (fun z => ((densInv K z : ℝ≥0) : ℝ)) (U K) := by
  have : ContinuousOn (fun z => (dens K z)⁻¹) (U K) :=
    (continuous_dens K).continuousOn.inv₀ fun z hz => (dens_pos K hz).ne'
  exact NNReal.continuous_coe.comp_continuousOn (continuous_real_toNNReal.comp_continuousOn this)

theorem ae_snd_eq_one :
    ∀ᵐ a : (AdeleRing (𝓞 K) K)ˣ ∂(Idele.sPartMeasure K ∅), ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := by
  have hcont : Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :=
    continuous_snd.comp Units.continuous_val
  have hs : MeasurableSet {a : (AdeleRing (𝓞 K) K)ˣ | ((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1} :=
    (isClosed_eq hcont continuous_const).measurableSet
  rw [Idele.sPartMeasure, ae_map_iff (Idele.measurable_partAt K ∅).aemeasurable hs]
  refine Filter.Eventually.of_forall fun a => ?_
  exact RestrictedProduct.ext _ _ fun v => Idele.partAt_snd_of_not_mem K ∅ a (Finset.notMem_empty v)

end ArchTorus

end

open ArchTorus in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (h : (AdeleRing (𝓞 K) K)ˣ → ℂ) (_hc : Continuous h)
    (_hint : Integrable h (NumberField.Idele.sPartMeasure K ∅))
    (_hne : ∃ t₀ : (AdeleRing (𝓞 K) K)ˣ, ((t₀ : AdeleRing (𝓞 K) K)).2 = 1 ∧ h t₀ ≠ 0) :
    ∃ u : InfiniteAdeleRing K,
      ∫ t, NumberField.StandardAddChar.stdAddChar K ((((t : AdeleRing (𝓞 K) K)).1 * u, 0)) * h t
          ∂(NumberField.Idele.sPartMeasure K ∅) ≠ 0 := by
  obtain ⟨t₀, ht₀, hne⟩ := _hne
  obtain ⟨C, hC0, hCtop, hmap⟩ :=
    NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity K

  set ν : Measure (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.sPartMeasure K ∅ with hν
  set π : (AdeleRing (𝓞 K) K)ˣ → M K := fun a =>
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1 with hπ
  have hπc : Continuous π := (continuous_e K).comp (continuous_fst.comp Units.continuous_val)
  have hπm : AEMeasurable π ν := hπc.measurable.aemeasurable
  set H : M K → ℂ := fun z => h (sec K z) with hH
  set G : M K → ℂ := fun z => (((densInv K z : ℝ≥0) : ℝ) : ℂ) * H z with hG
  have hHπ : ∀ᵐ a ∂ν, H (π a) = h a :=
    (ae_snd_eq_one K).mono fun a ha => by
      show h (sec K (e K ((a : AdeleRing (𝓞 K) K)).1)) = h a
      rw [sec_e_fst K ha]

  have hvolU : (volume : Measure (M K)).restrict (U K) = volume := Measure.restrict_eq_self_of_ae_mem (ae_mem_U K)
  have hHcont : ContinuousOn H (U K) := _hc.comp_continuousOn (continuousOn_sec K)
  have hHm : AEStronglyMeasurable H (volume : Measure (M K)) := by
    rw [← hvolU]; exact hHcont.aestronglyMeasurable (isOpen_U K).measurableSet
  have hHm' : AEStronglyMeasurable H (Measure.map π ν) := by
    rw [hmap, withDensity_eq' K]
    exact (hHm.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure C

  have hFc : ∀ v : M K, Continuous fun z : M K => ((Real.fourierChar (Algebra.traceForm ℝ (M K) z v) : Circle) : ℂ) := by
    intro v
    have hl : Continuous fun z : M K => Algebra.traceForm ℝ (M K) z v :=
      ((Algebra.traceForm ℝ (M K)).flip v).continuous_of_finiteDimensional
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hl)

  have key : ∀ u : InfiniteAdeleRing K,
      ∫ t, NumberField.StandardAddChar.stdAddChar K ((((t : AdeleRing (𝓞 K) K)).1 * u, 0)) * h t ∂ν
        = ((C.toReal : ℝ) : ℂ) *
          ∫ z, ((Real.fourierChar (Algebra.traceForm ℝ (M K) z (e K u)) : Circle) : ℂ) * G z ∂volume := by
    intro u
    set F : M K → ℂ := fun z => ((Real.fourierChar (Algebra.traceForm ℝ (M K) z (e K u)) : Circle) : ℂ) * H z
      with hF
    have hFm : AEStronglyMeasurable F (Measure.map π ν) := ((hFc (e K u)).aestronglyMeasurable).mul hHm'
    have h1 : ∀ᵐ t : (AdeleRing (𝓞 K) K)ˣ ∂ν,
        NumberField.StandardAddChar.stdAddChar K
            ((((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * u, 0)) * h t = F (π t) := by
      refine hHπ.mono fun t ht => ?_
      show _ = ((Real.fourierChar (Algebra.traceForm ℝ (M K) (e K ((t : AdeleRing (𝓞 K) K)).1) (e K u)) :
        Circle) : ℂ) * H (π t)
      rw [ht, NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace, map_mul,
        ← Algebra.traceForm_apply]
    rw [integral_congr_ae h1, ← integral_map hπm hFm, hmap, withDensity_eq' K, integral_smul_measure,
      integral_withDensity_eq_integral_smul (measurable_densInv K), Complex.real_smul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (densInv K z) • F z = ((Real.fourierChar (Algebra.traceForm ℝ (M K) z (e K u)) : Circle) : ℂ) * G z
    rw [NNReal.smul_def, Complex.real_smul, hF, hG]
    ring

  have hBnd : (Algebra.traceForm ℝ (M K)).Nondegenerate :=
    NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate K
  have hGcont : ContinuousOn G (U K) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_densInv K)).mul hHcont
  have hHint : Integrable H (Measure.map π ν) :=
    (integrable_map_measure hHm' hπm).mpr (_hint.congr (hHπ.mono fun a ha => ha.symm))
  have hGint : Integrable G (volume : Measure (M K)) := by
    rw [hmap, withDensity_eq' K] at hHint
    have h2 := (integrable_withDensity_iff_integrable_smul (measurable_densInv K)).mp
      ((integrable_smul_measure hC0 hCtop).mp hHint)
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show (densInv K z) • H z = G z
    rw [NNReal.smul_def, Complex.real_smul]
  have hz₀ : π t₀ ∈ U K := by
    show IsUnit (e K ((t₀ : AdeleRing (𝓞 K) K)).1)
    exact (fstUnit K t₀).isUnit.map (e K)
  have hG0 : G (π t₀) ≠ 0 := by
    show (((densInv K (π t₀) : ℝ≥0) : ℝ) : ℂ) * h (sec K (e K ((t₀ : AdeleRing (𝓞 K) K)).1)) ≠ 0
    rw [sec_e_fst K ht₀]
    refine mul_ne_zero ?_ hne
    rw [Ne, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]
    exact (Real.toNNReal_pos.mpr (inv_pos.mpr (dens_pos K hz₀))).ne'
  obtain ⟨u', hu'⟩ := MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
    (volume : Measure (M K)) (Algebra.traceForm ℝ (M K)) hBnd G hGint (U K) (isOpen_U K) hGcont (π t₀) hz₀ hG0
  refine ⟨(e K).symm u', ?_⟩
  rw [key, RingEquiv.apply_symm_apply]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hC0, hCtop⟩)) hu'

end S_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
end P2MW
export P2MW.S_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty (solution)
