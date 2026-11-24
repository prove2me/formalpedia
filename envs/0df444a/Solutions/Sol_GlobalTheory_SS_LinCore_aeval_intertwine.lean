-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.aeval_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:59.95182+00:00
-- url     : https://prove2.me/submissions/edb3f519-25e2-4254-aa0c-40611e4dfd2b

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
theorem _root_.solution (f g L : Module.End 𝕜 V) (K : Submodule 𝕜 V)
    (hK : ∀ x ∈ K, g x ∈ K) (hL : ∀ x ∈ K, f (L x) = L (g x)) (p : ℚ[X]) :
    ∀ x ∈ K, aeval f p (L x) = L (aeval g p x) := by
  have hp : ∀ n : ℕ, ∀ x ∈ K, (f ^ n) (L x) = L ((g ^ n) x) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hL x hx, ih _ (hK x hx)]
  intro x hx
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smul_of_tower, hp _ x hx]
end GlobalTheory.SS.LinCore
