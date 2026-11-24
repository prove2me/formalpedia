-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.graded_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:51:53.95906+00:00
-- url     : https://prove2.me/submissions/bf9b97d6-ada8-49f7-b197-3667c2aa7368

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Theorems.Thm_GlobalTheory_SS_LinCore_aeval_intertwine
import Theorems.Thm_GlobalTheory_SS_LinCore_graded_comm

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]
namespace GlobalTheory.SS.LinCore
theorem _root_.solution (T Φ : Module.End 𝕜 V) (q : ℕ) (hq : q ≠ 0) (hT : IsNilpotent T)
    (h : Φ * (T + 1) = (T + 1) ^ q * Φ) (i : ℕ) (c : ℚ) (p : ℚ[X]) (x : V)
    (hx : (T ^ (i + 1)) x = 0) :
    aeval (c • Φ) p ((T ^ i) x) = (T ^ i) (aeval ((c * (q : ℚ) ^ i) • Φ) p x) := by
  refine aeval_intertwine _ _ (T ^ i) (LinearMap.ker (T ^ (i + 1))) ?_ ?_ p x hx
  · intro y hy
    have := (graded_comm T Φ q hq hT h i y hy).1
    simp [LinearMap.map_smul_of_tower, this]
  · intro y hy
    have := (graded_comm T Φ q hq hT h i y hy).2
    simp only [LinearMap.smul_apply, LinearMap.map_smul_of_tower, this, mul_smul]
end GlobalTheory.SS.LinCore
