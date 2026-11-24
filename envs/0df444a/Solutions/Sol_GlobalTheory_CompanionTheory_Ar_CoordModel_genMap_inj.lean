-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.genMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:25.919887+00:00
-- url     : https://prove2.me/submissions/2542581f-7bf0-4b51-bb7a-ed2d90b1b47c

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
variable [IsDomain A] [IsFractionRing A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution (p : Cpt (gen A Ω)) : Function.Injective (genMap (gen A Ω) p) := by
  letI := (toSt A p.1).toAlgebra
  haveI := isLoc A p.1
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj ((pr A p.1).asIdeal).primeCompl t
  have h' := congrArg (genMap (gen A Ω) p) h
  rw [map_mul, ht, zero_mul] at h'
  have : algebraMap A Ω r = 0 := by rw [← genMap_toSt A Ω p]; exact h'.symm
  have hr : r = 0 := by simpa using this
  subst hr
  simp only [map_zero] at h
  exact (IsLocalization.map_units _ s).mul_left_eq_zero.1 h
end GlobalTheory.CompanionTheory.Ar.CoordModel
