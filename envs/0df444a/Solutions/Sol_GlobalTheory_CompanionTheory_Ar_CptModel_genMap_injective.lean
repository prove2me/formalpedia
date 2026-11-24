-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.genMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:18.914132+00:00
-- url     : https://prove2.me/submissions/f3a00f0d-95ca-4c66-a7da-b645de6e1862

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_toStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_exists_frac
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isUnit_toStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [Field K]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution (φ : R →+* K) (hφ : Function.Injective φ) (p : Cpt (pt φ)) :
    Function.Injective (genMap (pt φ) p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
  have h1 := (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  rw [hx, zero_mul, genMap_toStalk] at h1
  have ha : a = 0 := hφ (by rw [← h1, map_zero])
  rw [ha, map_zero] at h
  exact (isUnit_toStalk p.1 hs).mul_left_eq_zero.mp h
end GlobalTheory.CompanionTheory.Ar.CptModel
