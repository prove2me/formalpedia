-- Prove2me | solution 1 for GlobalTheory.Cartier.secMaps_genSec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:38.221853+00:00
-- url     : https://prove2.me/submissions/9f1a87f2-7d80-4320-b4c9-342d1b766035

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution {A B : LB X} (w : LB.Iso A B) (a : A.Gen) (ha : a.IsGen) (b : B.Gen)
    (hb : b.IsGen) :
    SecMaps w ⟨fun i => (a.s i).val, fun i j => congrArg Units.val (ha i j)⟩
      ⟨fun i => (b.s i).val, fun i j => congrArg Units.val (hb i j)⟩ ↔ LB.Gen.Maps w a b :=
  forall_congr' fun _ => ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
end GlobalTheory.Cartier
