-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitRep.hform_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:02.255046+00:00
-- url     : https://prove2.me/submissions/e9d962d6-f391-4fd7-a492-5097ed415f32

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.UnitRep
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.SW.UnitRep
