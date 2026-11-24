-- Prove2me | solution 1 for GlobalTheory.ThetaFn.ex_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:17.852012+00:00
-- url     : https://prove2.me/submissions/238f9bf3-dd93-4059-b262-81f1e8c61570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u)
namespace GlobalTheory.ThetaFn
theorem _root_.solution (k : ℕ) (z : Fin g → ℂ) : u.ex ((k : ℂ) • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul, ex_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]
end GlobalTheory.ThetaFn
