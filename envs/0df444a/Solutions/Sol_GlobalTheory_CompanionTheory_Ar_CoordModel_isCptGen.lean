-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.isCptGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:21.49589+00:00
-- url     : https://prove2.me/submissions/f93f0d81-c101-4027-8e95-4170dfc31916

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_mem_regAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_genPt_asIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_genMap_inj

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
theorem _root_.solution : IsCptGen (gen A Ω) := by
  refine ⟨?_, genMap_inj A Ω⟩
  have e : genMap (gen A Ω) ⟨genPt (gen A Ω), specializes_rfl⟩ = (Scheme.stalkClosedPointTo (gen A Ω)).hom := by
    unfold genMap
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
    rfl
  have hb : Function.Bijective (genMap (gen A Ω) ⟨genPt (gen A Ω), specializes_rfl⟩) := by
    refine ⟨genMap_inj A Ω _, fun a => ?_⟩
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    refine (mem_regAt A Ω ⟨genPt (gen A Ω), specializes_rfl⟩ _).2 ⟨r, s, ?_, ?_⟩
    · change s ∉ (pr A (genPt (gen A Ω))).asIdeal
      rw [genPt_asIdeal]; simpa using nonZeroDivisors.ne_zero hs
    · have : algebraMap A Ω s ≠ 0 := by simpa using nonZeroDivisors.ne_zero hs
      field_simp
  rw [e] at hb
  exact hb
end GlobalTheory.CompanionTheory.Ar.CoordModel
