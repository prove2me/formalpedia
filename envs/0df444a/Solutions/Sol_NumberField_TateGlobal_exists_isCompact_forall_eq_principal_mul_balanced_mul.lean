-- Prove2me | solution 1 for NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e344bc51-e692-543b-8dc3-c887b4fa34e8

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal Classical

namespace B2aDilation

variable (F : Type) [Field F] [NumberField F]

theorem extensionEmbedding_eq_ofReal_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    Completion.extensionEmbedding w x = ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) := by
  have h1 : Continuous fun x : w.Completion => Completion.extensionEmbedding w x :=
    (Completion.isometry_extensionEmbedding w).continuous
  have h2 : Continuous fun x : w.Completion => ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  refine NumberField.InfinitePlace.Completion.induction_on _
    (p := fun x : w.Completion =>
      Completion.extensionEmbedding w x = ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ))
    x (isClosed_eq h1 h2) fun y => ?_
  rw [Completion.extensionEmbedding_coe, Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_apply]

noncomputable def coordOf (w : InfinitePlace F) (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (Completion.ringEquivRealOfIsReal hw).symm r
  else (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (r : ℂ)

theorem extensionEmbedding_coordOf (w : InfinitePlace F) (r : ℝ) :
    Completion.extensionEmbedding w (coordOf F w r) = (r : ℂ) := by
  by_cases hw : w.IsReal
  · rw [coordOf, dif_pos hw, extensionEmbedding_eq_ofReal_of_isReal F hw]
    exact congrArg (fun s : ℝ => (s : ℂ)) ((Completion.ringEquivRealOfIsReal hw).apply_symm_apply r)
  · rw [coordOf, dif_neg hw]
    exact (Completion.ringEquivComplexOfIsComplex _).apply_symm_apply (r : ℂ)

theorem norm_eq_of_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖x‖ = ‖Completion.extensionEmbedding w x‖ := by
  have := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  exact this.symm

theorem norm_coordOf (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) : ‖coordOf F w r‖ = r := by
  rw [norm_eq_of_extensionEmbedding, extensionEmbedding_coordOf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem coordOf_ne_zero (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) : coordOf F w r ≠ 0 := by
  intro h
  have := norm_coordOf F w r hr
  rw [h, norm_zero] at this
  exact hr.ne this

noncomputable def dil (r : ℝ) (hr : 0 < r) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (MulEquiv.piUnits.symm fun w : InfinitePlace F => Units.mk0 (coordOf F w r) (coordOf_ne_zero F w r hr))

theorem dil_fst (r : ℝ) (hr : 0 < r) (w : InfinitePlace F) : ((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = coordOf F w r := rfl

theorem dil_snd (r : ℝ) (hr : 0 < r) : ((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

theorem distribHaarChar_dil (r : ℝ) (hr : 0 < r) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (dil F r hr) : ℝ) = r ^ Module.finrank ℚ F := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ‖((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [dil_snd]
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v‖ = 1
    rw [show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v = 1 from rfl, norm_one]
  rw [finprod_eq_one_of_forall_eq_one h2, mul_one]
  simp_rw [dil_fst, norm_coordOf F _ r hr]
  rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]

end B2aDilation

open B2aDilation in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ U : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U ∧ (∀ u ∈ U, ((α u : ℝˣ) : ℝ) = 1) ∧
      ∀ y : (AdeleRing (𝓞 F) F)ˣ, ∃ (η : Fˣ) (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ),
        u ∈ U ∧ 0 < r ∧
        y = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * u ∧
        (z : AdeleRing (𝓞 F) F).2 = 1 ∧
        (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) ∧
        ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F := by
  intro α
  have hα : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) := fun x => rfl
  have hαn : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := fun x => rfl
  obtain ⟨K, hKc, hK1, hKrep⟩ := NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul F
  refine ⟨K, hKc, fun u hu => ?_, fun y => ?_⟩
  · rw [hαn]
    exact (NumberField.TateGlobal.mem_normOneIdeles_iff u).mp (hK1 hu)

  set n : ℕ := Module.finrank ℚ F with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hy0 : 0 < ((α y : ℝˣ) : ℝ) := by rw [hα]; exact_mod_cast distribHaarChar_pos
  set r : ℝ := ((α y : ℝˣ) : ℝ) ^ ((n : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hy0 _
  have hrn : r ^ n = ((α y : ℝˣ) : ℝ) := by rw [hr, Real.rpow_inv_natCast_pow hy0.le hn0]
  set z := dil F r hr0 with hz
  have hαz : ((α z : ℝˣ) : ℝ) = r ^ n := by rw [hα, hz, distribHaarChar_dil]

  have hx : y * z⁻¹ ∈ NumberField.TateGlobal.normOneIdeles F := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, ← hαn, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      hαz, hrn, mul_inv_cancel₀ hy0.ne']
  obtain ⟨η, κ, hκ, hxeq⟩ := hKrep _ hx
  refine ⟨η, z, κ, r, hκ, hr0, ?_, dil_snd F r hr0, fun w => ?_, hαz⟩
  · calc y = (y * z⁻¹) * z := by rw [inv_mul_cancel_right]
      _ = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * κ * z := by rw [hxeq]; rfl
      _ = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * κ := by rw [mul_assoc, mul_comm κ z, ← mul_assoc]
  · rw [hz, dil_fst, extensionEmbedding_coordOf]

end S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul (solution)
