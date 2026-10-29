-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_ld_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:49:36.0429+00:00
-- url     : https://prove2.me/submissions/2e1f394e-ad17-42da-888d-e94cb9e526b5

-- Generated proof for MIPStarRE.QPBT.exists_ld_soundness.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_codewords_le_evaluated_add
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_heteroKron_le_one
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le
import Theorems.Thm_MIPStarRE_QPBT_directLdPointPair_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_directPolynomialAgreement_avg_le_mdq
import Theorems.Thm_MIPStarRE_QPBT_error_and_collision_le_deltaLd
import Theorems.Thm_MIPStarRE_QPBT_exists_direct_ld_soundness
import Theorems.Thm_MIPStarRE_QPBT_ldStrategyToDirect_isProjective
import Theorems.Thm_MIPStarRE_QPBT_ldStrategyToDirect_pointPair_compression
import Theorems.Thm_MIPStarRE_QPBT_ldStrategyToDirect_pointPolynomial_compression
import Theorems.Thm_MIPStarRE_QPBT_ldStrategyToDirect_polynomialPoint_compression
import Theorems.Thm_MIPStarRE_QPBT_ldStrategyToDirect_value_eq
import Theorems.Thm_MIPStarRE_QPBT_one_le_deltaLd_of_one_le_error
import Theorems.Thm_MIPStarRE_QPBT_ten_sqrt_deltaLd_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Soundness.lean. -/
/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Absorbing the error bound from the low individual degree theorem

The specializations below combine three inputs: polynomial-tuple conclusions
whose error is built from `mainFormalError`, the error bound of
`thm:main-formal` at the auxiliary sampling parameter; the absorption
`exists_directLdTransportConstants` of that error into `deltaLd`; and the
coarse bound `consistencyDefect_heteroKron_le_one`, which closes both the
regime `1 ≤ ε` and the regime where the transport argument exceeds one, in
each of which `deltaLd` is already at least one. -/

/-- Formalization-only scalar step: a quantity dominated by an argument that
is itself at most one is dominated by the square root of that argument.

Support for the transport of `lem:ld-soundness`, blueprint
`ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem le_sqrt_of_le_of_le_one {x T : ℝ} (hxT : x ≤ T) (hT : T ≤ 1) :
    x ≤ Real.sqrt T := by
  rcases le_or_gt x 0 with hx | hx
  · exact le_trans hx (Real.sqrt_nonneg T)
  · have hx2 : x ^ 2 ≤ T := by nlinarith
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx.le).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hx2











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/PointAgreement.lean. -/
/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The point-agreement branch of the directly indexed game -/











/-! ## Transport through the correlated seed-residue dilation -/





/-- The two point readouts of a projective seed-indexed strategy of value at
least `1 - ε` are consistent up to `9 ε` on a uniformly random point.

The correlated seed-residue dilation has the same value, and its point
measurements are the block-diagonal amplifications of the original ones, so
the estimate transports back verbatim.  Blueprint
`ch13_qpbt_test.tex:137-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
theorem ldPointPair_consistencyDefect_le
    (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L)) (hS : S.IsProjective)
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron
          (((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
            (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1
          (((S.B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
            (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a)) S.ψ ≤ 9 * ε := by
  rw [← _root_.MIPStarRE.QPBT.ldStrategyToDirect_pointPair_compression L S]
  refine _root_.MIPStarRE.QPBT.directLdPointPair_consistencyDefect_le L.toDirectLdParams
    (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S) (_root_.MIPStarRE.QPBT.ldStrategyToDirect_isProjective L S hS) ε ?_
  rw [_root_.MIPStarRE.QPBT.ldStrategyToDirect_value_eq]
  exact hwin

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/LowDegreeGameTheorems.lean. -/
/-!
# Quantum soundness of the seed-indexed low-degree game

The general simultaneity reduction for the directly indexed game is transported
through the correlated seed dilation. Point consistency survives compression
exactly; global polynomial consistency is recovered by point agreement and
Schwartz--Zippel, with the square-root loss absorbed into `deltaLd`.

## References

* `arXiv:2001.04383v3, Section 7.1, Theorem 7.8`
* `arXiv:1904.05870v3, Theorem 4.43 and its proof`
* Blueprint `lem:ld-soundness`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- Distinct polynomial tuples collide only where one of their distinct
coordinates collides. This formalization auxiliary for `lem:ld-soundness`
therefore has the same Schwartz--Zippel bound for every simultaneity parameter. -/
theorem polyTupleAgreement_avg_le_mdq (L : _root_.MIPStarRE.QPBT.LdParams)
    (g g' : _root_.MIPStarRE.QPBT.PolyTuple L) (hne : g ≠ g') :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u => if _root_.MIPStarRE.QPBT.evalPolyTupleAt u g = _root_.MIPStarRE.QPBT.evalPolyTupleAt u g' then
          (1 : ℝ) else 0) ≤
      ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun u => ?_)
    (_root_.MIPStarRE.QPBT.directPolynomialAgreement_avg_le_mdq L.toDirectLdParams (g i) (g' i) hi)
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' (congrFun h i))
  · norm_num
  · exact le_rfl



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/-!
# Quantum soundness of the seed-indexed low-degree game

The general simultaneity reduction for the directly indexed game is transported
through the correlated seed dilation. Point consistency survives compression
exactly; global polynomial consistency is recovered by point agreement and
Schwartz--Zippel, with the square-root loss absorbed into `deltaLd`.

## References

* `arXiv:2001.04383v3, Section 7.1, Theorem 7.8`
* `arXiv:1904.05870v3, Theorem 4.43 and its proof`
* Blueprint `lem:ld-soundness`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

set_option maxHeartbeats 1000000 in

theorem solution :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : _root_.MIPStarRE.QPBT.LdParams) (ε : ℝ), 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιA, ∃ GB : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιB,
            _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
                (fun u outcome =>
                  _root_.MIPStarRE.QPBT.heteroKron
                    (((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
                      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome) 1)
                (fun u outcome =>
                  _root_.MIPStarRE.QPBT.heteroKron 1
                    ((GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome))
                S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε L.q L.m L.d L.k ∧
            _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
                (fun u outcome =>
                  _root_.MIPStarRE.QPBT.heteroKron
                    ((GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome) 1)
                (fun u outcome =>
                  _root_.MIPStarRE.QPBT.heteroKron 1
                    (((S.B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
                      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome))
                S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε L.q L.m L.d L.k ∧
            _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
                (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
                S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε L.q L.m L.d L.k := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hs⟩ := _root_.MIPStarRE.QPBT.exists_direct_ld_soundness
  refine ⟨10 * a, b / 2, by linarith, by positivity, by linarith, ?_⟩
  intro L ε hε S hS hwin
  let D := L.toDirectLdParams
  let E := _root_.MIPStarRE.QPBT.deltaLd a b ε L.q L.m L.d L.k
  let F := _root_.MIPStarRE.QPBT.deltaLd (10 * a) (b / 2) ε L.q L.m L.d L.k
  obtain ⟨GA₀, GB₀, h1, h2, _⟩ := hs D ε hε (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S)
    (_root_.MIPStarRE.QPBT.ldStrategyToDirect_isProjective L S hS)
    (by simpa only [_root_.MIPStarRE.QPBT.ldStrategyToDirect_value_eq] using hwin)
  let GA : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιA := _root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L GA₀
  let GB : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιB := _root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L GB₀
  have c1 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        (((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
          (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome)) S.ψ ≤ E := by
    rw [show GB = _root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L GB₀ from rfl,
      ← _root_.MIPStarRE.QPBT.ldStrategyToDirect_pointPolynomial_compression L S GB₀]
    exact h1
  have c2 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        (((S.B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
          (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome)) S.ψ ≤ E := by
    rw [show GA = _root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L GA₀ from rfl,
      ← _root_.MIPStarRE.QPBT.ldStrategyToDirect_polynomialPoint_compression L S GA₀]
    exact h2
  have c3 := _root_.MIPStarRE.QPBT.ldPointPair_consistencyDefect_le L S hS ε hwin
  have ctrans : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) :=
    _root_.MIPStarRE.QPBT.consistencyDefect_trans_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
      (fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
        (GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)))
      (fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
        ((S.B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)))
      (fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
        ((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)))
      (fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
        (GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)))
      S.ψ E (9 * ε) E (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.ψ_norm c2 c3 c1
  have ccode : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    have hstep := _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ : Unit => GA) (fun _ : Unit => GB) S.ψ
      (fun g u => _root_.MIPStarRE.QPBT.evalPolyTupleAt u g) ((L.m : ℝ) * L.d / L.q)
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.ψ_norm (by positivity)
      (fun g g' hne => _root_.MIPStarRE.QPBT.polyTupleAgreement_avg_le_mdq L g g' hne)
    have hprod : ∀ (A B : Unit × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) →
        (Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L) → _root_.LIDT.MIPStarRE.Quantum.Op (S.ιA × S.ιB)),
        _root_.MIPStarRE.QPBT.consistencyDefect
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))) A B S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
          (fun u => A ((), u)) (fun u => B ((), u)) S.ψ := by
      intro A B
      unfold _root_.MIPStarRE.QPBT.consistencyDefect
      rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod,
        _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
      simp
    rw [hprod] at hstep
    exact hstep.trans (by linarith)
  have hsqrt : 10 * Real.sqrt E ≤ F := _root_.MIPStarRE.QPBT.ten_sqrt_deltaLd_le D ha hε.le
  have hEnn : 0 ≤ E := by dsimp [E, _root_.MIPStarRE.QPBT.deltaLd]; positivity
  have hbound {X α : Type} [Fintype X] [DecidableEq X] [Nonempty X]
      [Fintype α] [DecidableEq α]
      (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α S.ιA)
      (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α S.ιB)
      (hc : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x o => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect o) 1)
        (fun x o => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect o)) S.ψ ≤
        E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q) :
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x o => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect o) 1)
        (fun x o => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect o)) S.ψ ≤ F := by
    have hone := _root_.MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) A B S.ψ S.ψ_norm
    by_cases hε1 : ε ≤ 1
    · by_cases hE1 : E ≤ 1
      · obtain ⟨he, hm⟩ := _root_.MIPStarRE.QPBT.error_and_collision_le_deltaLd D ha hb1 hε hε1
        change ε ≤ E at he
        change (L.m : ℝ) * L.d / L.q ≤ E at hm
        have hEs : E ≤ Real.sqrt E := _root_.MIPStarRE.QPBT.le_sqrt_of_le_of_le_one le_rfl hE1
        have hroot : Real.sqrt (9 * ε + E) ≤ 4 * Real.sqrt E := by
          apply (Real.sqrt_le_iff).mpr
          refine ⟨by positivity, ?_⟩
          nlinarith [Real.sq_sqrt hEnn]
        exact hc.trans (by linarith)
      · have hEs : 1 ≤ Real.sqrt E := by
          simpa using Real.sqrt_le_sqrt (not_le.mp hE1).le
        exact hone.trans (by linarith)
    · exact hone.trans (_root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error (by linarith) (by positivity)
        (not_le.mp hε1).le L.hm L.hd L.hk)
  have hrem : 0 ≤ 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    positivity
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · apply hbound
      (fun u => (S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L))
      (fun u => GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u))
    exact c1.trans (by linarith)
  · apply hbound (fun u => GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u))
      (fun u => (S.B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L))
    exact c2.trans (by linarith)
  · exact hbound (fun _ : Unit => GA) (fun _ : Unit => GB) ccode
