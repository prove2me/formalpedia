-- Prove2me | solution 1 for ModularCurve.ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/39d19fe0-db7b-5157-ae46-92ffad714c4d

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective Polynomial IntermediateField"

namespace CuspsLegsE4

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem map_eval₂_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    g (Φ.eval₂ (aeval (R := ℤ) a).toRingHom b) = Φ.eval₂ (aeval (R := ℤ) (g a)).toRingHom (g b) := by
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval₂_aeval_jqModC_jqNModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqModC K)).toRingHom (jqNModC K ℓ) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℚ)).toRingHom (jqNModC ℚ ℓ) = 0 := by
    rw [jqNModC_rat, jqModC_rat]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℤ)).toRingHom (jqNModC ℤ ℓ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem eval₂_aeval_jqNModC_jqModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqNModC K ℓ)).toRingHom (jqModC K) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ ℓ)).toRingHom (jqModC ℚ) = 0 := by
    rw [jqNModC_rat, jqModC_rat, hsym (jqN ℓ) jq]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ ℓ)).toRingHom (jqModC ℤ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem isIntegral_adjoin_of_eval₂_eq_zero (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a b : ↥F)
    (h : Φ.eval₂ (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom (b : LaurentSeries K) = 0) :
    IsIntegral (Algebra.adjoin K ({a} : Set ↥F)) b := by
  refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom _) ⟨a, Algebra.self_mem_adjoin_singleton K _⟩),
    hΦ.map _, ?_⟩
  apply (algebraMap ↥F (LaurentSeries K)).injective
  have hcomp : (algebraMap ↥F (LaurentSeries K)).comp
      ((algebraMap _ ↥F).comp
        (Polynomial.eval₂RingHom (Int.castRingHom _)
          (⟨a, Algebra.self_mem_adjoin_singleton K _⟩ : ↥(Algebra.adjoin K ({a} : Set ↥F))))) =
      (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X]
    rfl
  rw [eval₂_map, hom_eval₂, hcomp, map_zero]
  exact h

end CuspsLegsE4

open CuspsLegsE4 in
theorem solution
    (K : Type) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.ord (heckeAlphaC K N ℓ (jGeomGen K N)) < 0 ↔ y.ord (heckeBetaC K N ℓ (jGeomGen K N)) < 0 := by
  obtain ⟨data, hsym⟩ := ModularCurve.exists_modularPolynomialData_evalSymm ℓ
  set a : ↥(charLDegeneracyRoof K N ℓ) := heckeAlphaC K N ℓ (jGeomGen K N) with ha
  set b : ↥(charLDegeneracyRoof K N ℓ) := heckeBetaC K N ℓ (jGeomGen K N) with hb
  have hac : (a : LaurentSeries K) = jqModC K := by rw [ha, coe_heckeAlphaC]; rfl
  have hbc : (b : LaurentSeries K) = jqNModC K ℓ := by rw [hb, coe_heckeBetaC]; rfl
  have ha0 : a ≠ 0 := by
    intro h
    have h1 : (a : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hac] at h1
    exact jqModC_ne_zero_of_nontrivial K h1
  have hb0 : b ≠ 0 := by
    intro h
    have h1 : (b : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hbc] at h1
    apply jqModC_ne_zero_of_nontrivial K
    apply qExpand_injective ℓ
    rw [map_zero]
    exact h1

  have hba : IsIntegral (Algebra.adjoin K ({a} : Set ↥(charLDegeneracyRoof K N ℓ))) b :=
    isIntegral_adjoin_of_eval₂_eq_zero K _ data.Φ data.monic a b
      (by rw [hac, hbc]; exact eval₂_aeval_jqModC_jqNModC_eq_zero K ℓ data)
  have hab : IsIntegral (Algebra.adjoin K ({b} : Set ↥(charLDegeneracyRoof K N ℓ))) a :=
    isIntegral_adjoin_of_eval₂_eq_zero K _ data.Φ data.monic b a
      (by rw [hac, hbc]; exact eval₂_aeval_jqNModC_jqModC_eq_zero K ℓ data hsym)

  rw [← not_le, ← not_le, not_iff_not, ← Place.mem_iff_ord_nonneg y ha0, ← Place.mem_iff_ord_nonneg y hb0]
  exact ⟨fun h => y.mem_toValuationSubring_of_isIntegral_adjoin h hba,
    fun h => y.mem_toValuationSubring_of_isIntegral_adjoin h hab⟩

end S_ModularCurve_ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg
end P2MW
export P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_neg_iff_ord_heckeBetaC_jGeomGen_neg (solution)
