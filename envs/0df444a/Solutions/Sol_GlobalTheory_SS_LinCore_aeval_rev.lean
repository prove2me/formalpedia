-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.aeval_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:00.756515+00:00
-- url     : https://prove2.me/submissions/2b96f86e-e050-4f7d-b280-4fe868cac955

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
namespace GlobalTheory.SS.LinCore
theorem _root_.solution {A : Type} [Ring A] [Algebra ℚ A] (u v : A) (h : u * v = 1) (R : ℚ[X]) :
    aeval u (∑ i ∈ Finset.range (R.natDegree + 1), C (R.coeff i) * X ^ (R.natDegree - i))
      = u ^ R.natDegree * aeval v R := by
  have hp : ∀ i : ℕ, u ^ i * v ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_succ', _root_.mul_assoc, ← _root_.mul_assoc u, h, _root_.one_mul, ih]
  rw [aeval_eq_sum_range v, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : u ^ R.natDegree = u ^ (R.natDegree - i) * u ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [map_mul, aeval_C, map_pow, aeval_X, mul_smul_comm, this, _root_.mul_assoc, hp, _root_.mul_one,
    Algebra.smul_def]
end GlobalTheory.SS.LinCore
