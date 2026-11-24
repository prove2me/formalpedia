-- Prove2me | solution 1 for GlobalTheory.MulEtaleDvr.pullback_map_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:04.925798+00:00
-- url     : https://prove2.me/submissions/c11a5bf7-8a3a-4ad7-b488-84f2f0d9d50d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Theorems.Thm_GlobalTheory_MulEtaleDvr_mulN_eq_pow

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
open GlobalTheory.MulEtaleDvr
variable {S : Scheme.{0}}
namespace GlobalTheory.MulEtaleDvr
theorem _root_.solution {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _
end GlobalTheory.MulEtaleDvr
