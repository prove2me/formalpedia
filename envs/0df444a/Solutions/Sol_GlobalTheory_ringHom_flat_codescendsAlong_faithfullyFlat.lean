-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_codescendsAlong_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:44.430794+00:00
-- url     : https://prove2.me/submissions/3a19ad27-b1cc-4507-9273-50683ca5b7ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    RingHom.CodescendsAlong.{0} RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S
end GlobalTheory
