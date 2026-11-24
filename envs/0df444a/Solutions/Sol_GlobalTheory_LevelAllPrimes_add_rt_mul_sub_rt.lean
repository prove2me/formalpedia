-- Prove2me | solution 1 for GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:53.930028+00:00
-- url     : https://prove2.me/submissions/47147135-b07e-4f18-a7e0-38a01d5c177e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelGoodAtAllPrimesAndIdx

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelAllPrimes
open GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LevelAllPrimes
namespace _root_.GlobalTheory.LevelAllPrimes
theorem _root_.solution (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    ((c : 𝓞 E) + H.rt) * (c - H.rt) = ((c ^ 2 + H.d : ℕ) : 𝓞 E) := by
  push_cast
  linear_combination (-1 : 𝓞 E) * H.rt_sq
end _root_.GlobalTheory.LevelAllPrimes
end GlobalTheory.LevelAllPrimes
