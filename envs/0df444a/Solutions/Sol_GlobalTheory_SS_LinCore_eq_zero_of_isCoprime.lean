-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.eq_zero_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:12.299129+00:00
-- url     : https://prove2.me/submissions/ae60c577-3716-4e53-bd0f-25b63615a76d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic

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
theorem _root_.solution (f : Module.End 𝕜 V) {a b : ℚ[X]} (h : IsCoprime a b) {y : V}
    (ha : aeval f a y = 0) (hb : aeval f b y = 0) : y = 0 := by
  obtain ⟨c, d, hcd⟩ := h
  have := congrArg (fun p => aeval f p y) hcd
  simpa [Module.End.mul_apply, ha, hb] using this.symm
end GlobalTheory.SS.LinCore
