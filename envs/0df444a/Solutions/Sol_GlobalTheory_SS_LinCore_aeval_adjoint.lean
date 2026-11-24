-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.aeval_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:59.127809+00:00
-- url     : https://prove2.me/submissions/f498803d-3b62-4c0d-9b97-7d3e4df4a2bc

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
theorem _root_.solution (B : LinearMap.BilinForm 𝕜 V) (f g : Module.End 𝕜 V)
    (h : ∀ x y, B (f x) y = B x (g y)) (p : ℚ[X]) (x y : V) :
    B (aeval f p x) y = B x (aeval g p y) := by
  have hp : ∀ n : ℕ, ∀ x y, B ((f ^ n) x) y = B x ((g ^ n) y) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ', pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smul_of_tower, hp]
end GlobalTheory.SS.LinCore
