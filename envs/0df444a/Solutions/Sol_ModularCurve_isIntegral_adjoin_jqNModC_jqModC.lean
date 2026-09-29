-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_jqNModC_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7dcf3471-bd2d-5145-83e9-e65f4a6fc0f7

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jqNModC_jqModC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jqNModC_rat coeffMap_jqModC coeffMap_jqNModC jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem jqNModC_mem jq jqN ModularPolynomialData coeffMap coeffMap_coeff EvalSymm exists_modularPolynomialData_evalSymm"
p2m_open "ModularCurve~coeffMap_injective"

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

theorem eval₂_aeval_jqNModC_jqModC_eq_zero (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularPolynomialData p) (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqNModC K p)).toRingHom (jqModC K) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ p)).toRingHom (jqModC ℚ) = 0 := by
    rw [jqNModC_rat, jqModC_rat, hsym (jqN p) jq]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ p)).toRingHom (jqModC ℤ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem isIntegral_adjoin_jqNModC_jqModC_of_modularPolynomialData (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularPolynomialData p) (hsym : EvalSymm data.Φ) :
    IsIntegral (Algebra.adjoin K ({(⟨jqNModC K p, jqNModC_mem K p⟩ : ↥(modularFunctionFieldC K p))} :
        Set ↥(modularFunctionFieldC K p)))
      (⟨jqModC K, jqModC_mem K p⟩ : ↥(modularFunctionFieldC K p)) := by

  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom _)
      ⟨⟨jqNModC K p, jqNModC_mem K p⟩, Algebra.self_mem_adjoin_singleton K _⟩),
    data.monic.map _, ?_⟩

  apply (algebraMap ↥(modularFunctionFieldC K p) (LaurentSeries K)).injective
  have hcomp : (algebraMap ↥(modularFunctionFieldC K p) (LaurentSeries K)).comp
      ((algebraMap _ ↥(modularFunctionFieldC K p)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom _)
          (⟨⟨jqNModC K p, jqNModC_mem K p⟩, Algebra.self_mem_adjoin_singleton K _⟩ :
            ↥(Algebra.adjoin K ({(⟨jqNModC K p, jqNModC_mem K p⟩ : ↥(modularFunctionFieldC K p))} :
              Set ↥(modularFunctionFieldC K p)))))) =
      (aeval (R := ℤ) (jqNModC K p)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X]
    rfl
  rw [eval₂_map, hom_eval₂, hcomp, map_zero]
  exact eval₂_aeval_jqNModC_jqModC_eq_zero K p data hsym

private theorem solution_impl (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] :
    IsIntegral (Algebra.adjoin K ({(⟨jqNModC K p, jqNModC_mem K p⟩ : ↥(modularFunctionFieldC K p))} :
        Set ↥(modularFunctionFieldC K p)))
      (⟨jqModC K, jqModC_mem K p⟩ : ↥(modularFunctionFieldC K p)) := by
  obtain ⟨data, hsym⟩ := exists_modularPolynomialData_evalSymm p
  exact isIntegral_adjoin_jqNModC_jqModC_of_modularPolynomialData K p data hsym

end ModularCurve

theorem solution (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] :
    IsIntegral
      (Algebra.adjoin K
        ({(⟨ModularCurve.jqNModC K p, ModularCurve.jqNModC_mem K p⟩ :
            ↥(ModularCurve.modularFunctionFieldC K p))} :
          Set ↥(ModularCurve.modularFunctionFieldC K p)))
      (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K p⟩ :
        ↥(ModularCurve.modularFunctionFieldC K p)) :=
  ModularCurve.solution_impl K p

end S_ModularCurve_isIntegral_adjoin_jqNModC_jqModC
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_jqNModC_jqModC (solution)
