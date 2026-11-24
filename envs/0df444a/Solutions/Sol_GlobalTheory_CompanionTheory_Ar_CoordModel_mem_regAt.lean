-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.mem_regAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:50.586275+00:00
-- url     : https://prove2.me/submissions/62e67372-a672-426d-ab13-00d6e513d2e7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_isLoc
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_genMap_toSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution (p : Cpt (gen A Ω)) (a : Ω) :
    a ∈ regAt (gen A Ω) p ↔ ∃ r s : A, s ∉ (pr A p.1).asIdeal ∧ a * algebraMap A Ω s = algebraMap A Ω r := by
  letI := (toSt A p.1).toAlgebra
  haveI := isLoc A p.1
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj ((pr A p.1).asIdeal).primeCompl t
    refine ⟨r, s, s.2, ?_⟩
    rw [← genMap_toSt A Ω p, ← genMap_toSt A Ω p, ← map_mul]
    exact congrArg _ h
  · rintro ⟨r, s, hs, h⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units ((Spec (CommRingCat.of A)).presheaf.stalk p.1)
      (⟨s, hs⟩ : ((pr A p.1).asIdeal).primeCompl)
    refine ⟨toSt A p.1 r * ↑u⁻¹, ?_⟩
    have e : genMap (gen A Ω) p u = algebraMap A Ω s := by
      rw [hu]; exact genMap_toSt A Ω p s
    have e2 : genMap (gen A Ω) p u * genMap (gen A Ω) p ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [map_mul, genMap_toSt, ← h, ← e, mul_assoc, e2, mul_one]
end GlobalTheory.CompanionTheory.Ar.CoordModel
