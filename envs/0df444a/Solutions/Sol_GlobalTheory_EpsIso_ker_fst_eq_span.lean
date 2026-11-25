-- Prove2me | solution 1 for GlobalTheory.EpsIso.ker_fst_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:17:33.274588+00:00
-- url     : https://prove2.me/submissions/59cc64b6-7c2f-4d1b-99ba-ffd8d0b6a8ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso
namespace GlobalTheory.EpsIso
theorem _root_.solution (K : Type) [Field K] :
    RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h0 : x.fst = 0 := hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext
    · simp [h0]
    · simp
  · rintro ⟨y, rfl⟩
    show (DualNumber.eps * y).fst = 0
    simp
end GlobalTheory.EpsIso
