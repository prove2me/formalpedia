-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.mem_regAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:04.131119+00:00
-- url     : https://prove2.me/submissions/da3bb0c0-bc45-42a8-a932-f9e73ba097b8

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
theorem _root_.solution (φ : R →+* K) (p : Cpt (pt φ)) (c : K) :
    c ∈ regAt (pt φ) p ↔ ∃ a s : R, s ∉ p.1.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  have hne : ∀ s : R, s ∉ p.1.asIdeal → φ s ≠ 0 := fun s hs => by
    rw [← genMap_toStalk φ p]
    exact ((isUnit_toStalk p.1 hs).map (genMap (pt φ) p)).ne_zero
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
    refine ⟨a, s, hs, hne s hs, ?_⟩
    rw [← genMap_toStalk φ p, ← genMap_toStalk φ p]
    exact (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  · rintro ⟨a, s, hs, h0, h⟩
    obtain ⟨v, hv⟩ := (isUnit_toStalk p.1 hs).exists_right_inv
    refine ⟨tS p.1 a * v, ?_⟩
    have e : φ s * genMap (pt φ) p v = 1 := by
      rw [← genMap_toStalk φ p]
      exact (map_mul (genMap (pt φ) p) _ _).symm.trans
        ((congrArg (genMap (pt φ) p) hv).trans (map_one _))
    refine (map_mul (genMap (pt φ) p) _ _).trans ?_
    rw [genMap_toStalk, ← h, mul_assoc, e, mul_one]
end GlobalTheory.CompanionTheory.Ar.CptModel
