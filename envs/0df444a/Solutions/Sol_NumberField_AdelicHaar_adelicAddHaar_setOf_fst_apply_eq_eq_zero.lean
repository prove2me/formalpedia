-- Prove2me | solution 1 for NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb6bf813-d1f6-585b-8a0c-d39f084efd9c

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace NULLW

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem norm_two : ‖(2 : w.Completion)‖ = 2 := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (2 : w.Completion)
  rw [← h, map_ofNat]; norm_num

private theorem two_ne : (2 : w.Completion) ≠ 0 := by
  intro h; have := norm_two F w; rw [h, norm_zero] at this; norm_num at this

private def aAd : AdeleRing (𝓞 F) F := (Function.update 1 w 2, 1)
private def aInv : AdeleRing (𝓞 F) F := (Function.update 1 w 2⁻¹, 1)

private theorem aAd_fst_self : (aAd F w).1 w = 2 := by simp [aAd]
private theorem aAd_fst_of_ne {w' : InfinitePlace F} (h : w' ≠ w) : (aAd F w).1 w' = 1 := by simp [aAd, h]
private theorem aInv_fst_self : (aInv F w).1 w = 2⁻¹ := by simp [aInv]
private theorem aInv_fst_of_ne {w' : InfinitePlace F} (h : w' ≠ w) : (aInv F w).1 w' = 1 := by simp [aInv, h]

private theorem aAd_mul_aInv : aAd F w * aInv F w = 1 := by
  refine Prod.ext (funext fun w' => ?_) (by change (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1; rw [mul_one])
  change (aAd F w).1 w' * (aInv F w).1 w' = 1
  by_cases h : w' = w
  · subst h; rw [aAd_fst_self, aInv_fst_self, mul_inv_cancel₀ (two_ne F w')]
  · rw [aAd_fst_of_ne F w h, aInv_fst_of_ne F w h, mul_one]

private def aU : (AdeleRing (𝓞 F) F)ˣ := ⟨aAd F w, aInv F w, aAd_mul_aInv F w, by rw [mul_comm]; exact aAd_mul_aInv F w⟩

private theorem distribHaarChar_aU : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : ℝ) = 2 ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  change (∏ w' : InfinitePlace F, ‖(aAd F w).1 w'‖ ^ w'.mult) * ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(1 : FiniteAdeleRing (𝓞 F) F) u‖ = _
  rw [finprod_eq_one_of_forall_eq_one fun u => by change ‖(1 : u.adicCompletion F)‖ = 1; exact norm_one, mul_one]
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [aAd_fst_of_ne F w hw', norm_one, one_pow]) (fun h => absurd (Finset.mem_univ w) h),
    aAd_fst_self, norm_two]

private theorem smul_eq_self_of_mem {x : AdeleRing (𝓞 F) F} (hx : x.1 w = 0) :
    ((aU F w : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x = x := by
  change aAd F w * x = x
  refine Prod.ext (funext fun w' => ?_) (by change (1 : FiniteAdeleRing (𝓞 F) F) * x.2 = x.2; rw [one_mul])
  change (aAd F w).1 w' * x.1 w' = x.1 w'
  by_cases h : w' = w
  · subst h; rw [hx, mul_zero]
  · rw [aAd_fst_of_ne F w h, one_mul]

private theorem smul_inter (C : Set (AdeleRing (𝓞 F) F)) :
    (aU F w) • ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) = {x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((aU F w : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • x ∈ _
    rw [smul_eq_self_of_mem F w hx.1]; exact hx
  · intro hy
    exact ⟨y, hy, smul_eq_self_of_mem F w hy.1⟩

private theorem piece_null (C : Set (AdeleRing (𝓞 F) F)) (hfin : adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) ≠ ⊤) :
    adelicAddHaar (𝓞 F) F ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C) = 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar Measure.addHaar; infer_instance
  have h := distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (aU F w) ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ C)
  rw [smul_inter] at h
  by_contra hne
  have hδ : ((distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : NNReal) : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hne hfin).mp (h.trans (one_mul _).symm)
    exact_mod_cast this
  have hδ' : (distribHaarChar (AdeleRing (𝓞 F) F) (aU F w) : ℝ) = 1 := by exact_mod_cast hδ
  rw [distribHaarChar_aU] at hδ'
  have : (1 : ℝ) < 2 ^ w.mult := one_lt_pow₀ (by norm_num) (InfinitePlace.mult_pos).ne'
  exact this.ne' hδ'

private theorem null_zero : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = 0} = 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hcov : {x : AdeleRing (𝓞 F) F | x.1 w = 0} = ⋃ n, ({x : AdeleRing (𝓞 F) F | x.1 w = 0} ∩ compactCovering (AdeleRing (𝓞 F) F) n) := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  rw [hcov]
  refine measure_iUnion_null fun n => piece_null F w _ ?_
  exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (isCompact_compactCovering _ n).measure_lt_top).ne

theorem main (c : w.Completion) : adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = c} = 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  set y : AdeleRing (𝓞 F) F := (Function.update 0 w c, 0) with hy
  have hset : {x : AdeleRing (𝓞 F) F | x.1 w = c} = (fun x => -y + x) ⁻¹' {x : AdeleRing (𝓞 F) F | x.1 w = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    change x.1 w = c ↔ -((Function.update (0 : InfiniteAdeleRing F) w c) w) + x.1 w = 0
    rw [Function.update_self]
    constructor
    · intro h; rw [h, neg_add_cancel]
    · intro h; exact (neg_add_eq_zero.mp h).symm
  rw [hset, measure_preimage_add]
  exact null_zero F w

end NULLW

end

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (c : w.Completion) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.1 w = c} = 0 :=
  NULLW.main F w c

end S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero
end P2MW
export P2MW.S_NumberField_AdelicHaar_adelicAddHaar_setOf_fst_apply_eq_eq_zero (solution)
