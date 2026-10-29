-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:48.655953+00:00
-- url     : https://prove2.me/submissions/95bf7959-1dd5-44f9-9a08-08e562ca59f6

-- Generated proof for MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Averages
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Consistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_uniform_fixed_le_card_mul_prod
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_cardRatio_mul_avgOver_filter
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pairWConsistency_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_anticommProb_eq
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono
import Theorems.Thm_MIPStarRE_QPBT_rejectionMass_eq_one_sub_value

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Basis
end MIPStarRE.QPBT.Basis
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Algebra/FieldBasis.lean. -/
/-!
# Finite-field bases and the fixed binary representation

The Pauli basis test uses fields of size `2^k` for odd `k`, together with a
chosen self-dual normal basis over `ZMod 2`.  This file constructs such bases
and records the resulting fixed field model for later proofs.

## References

The declarations correspond to blueprint `def:admissible-size`,
`def:dual-self-dual-normal-basis`, `def:subfields-kappa`, `def:subfield-trace`,
and `def:binary-representation`.
Their paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502,653-728`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT



/-- An admissible field size is at least two, its binary exponent being odd
and therefore positive.  This is a property of blueprint
`def:admissible-size`, paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
theorem IsAdmissibleSize.two_le {q : ℕ} (hq : _root_.MIPStarRE.QPBT.IsAdmissibleSize q) : 2 ≤ q := by
  obtain ⟨k, hk, hqk⟩ := hq
  obtain ⟨j, hj⟩ := hk
  rw [hqk, hj]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)







/- The characteristic-two self-dual normal-basis construction is carried out
in the group algebra of the finite Galois group.  The transition from a normal
basis to its trace dual is a symmetric unit; odd cardinality makes its square
root unique and symmetric. -/











/-!
The paper fixes the field representation and self-dual normal basis once for
each admissible field size.  We expose that choice through a single global
selector rather than carrying a potentially different model in every game
parameter record.  Existence is a named stage-4.3 proof obligation; the
selector itself is the resulting noncomputable choice.
-/






















end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/





















/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/














/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  unfold _root_.MIPStarRE.QPBT.outcomeWeight _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ










/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b
    · exact le_rfl














end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Consistency.lean. -/
/-!
# Exact consistency winning implication

This module proves the exact same-question consistency bound for the two
players' Pauli-test measurements.

## References

The strategy consistency theorem proves item 1
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications





/-- Unequal answers to the same sampled question are rejected on its self-loop.
This is the rejection event used for item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`. -/
theorem loopMismatch_le_rejection {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (t : _root_.MIPStarRE.QPBT.PauliType) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
        (t, _root_.MIPStarRE.QPBT.pauliCL P t z) (t, _root_.MIPStarRE.QPBT.pauliCL P t z) (fun A B => A ≠ B) ≤
      _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge t) z := by
  unfold _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt _root_.MIPStarRE.QPBT.WinImplications.pauliSourceQuestions _root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge
  dsimp
  apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
  intro A B hne
  simp only [_root_.MIPStarRE.QPBT.pauliWinPredicate, Bool.and_eq_true, ↓reduceIte,
    Bool.if_false_right, Bool.decide_and, Bool.decide_eq_true,
    Bool.and_eq_false_imp, decide_eq_false_iff_not, and_imp]
  intro _ _
  exact hne






end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

















/-- Uniform Pauli seeds have the uniform shared-tuple marginal. -/
theorem avgOver_pauliTuple_uniform (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (f : _root_.MIPStarRE.QPBT.PauliTuple P → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (fun z => f (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) f := by
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P) f





/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (ht : _root_.MIPStarRE.QPBT.pauliCL P t = _root_.MIPStarRE.QPBT.pauliSharedProjection) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P t z = _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfTuple P
      (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) := by
  rw [ht]
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> rfl






































































end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/Anticommuting.lean. -/
/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section















/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/



/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliScalar (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
  @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel





/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by
  have hK := card_pauliScalar P
  simp [_root_.MIPStarRE.QPBT.PauliTuple, Fintype.card_prod, hK]



/-- The anticommuting and commuting events partition the tuple space.
Blueprint `fact:omega-anticomm-prob`. -/
private theorem card_comm_add_card_anticomm (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsCommuting P)).card
      + (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card
      = Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) := by
  classical
  have hfil : (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P))
      = Finset.univ.filter (fun ω : _root_.MIPStarRE.QPBT.PauliTuple P => ¬ (@_root_.MIPStarRE.QPBT.IsCommuting P ω)) := by
    refine Finset.filter_congr ?_
    intro ω _
    simp [_root_.MIPStarRE.QPBT.IsAnticommuting, _root_.MIPStarRE.QPBT.IsCommuting]
  rw [hfil, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not _

/-- Formalization-only auxiliary: the tuple space is nonempty and finite.
Blueprint `fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple_pos (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    0 < Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) := by
  have hq : 0 < P.q := lt_of_lt_of_le (by norm_num) P.hq.two_le
  rw [card_pauliTuple P]
  exact Nat.mul_pos (pow_pos hq _) (Nat.mul_pos (pow_pos hq _) (Nat.mul_pos hq hq))

/-! ### The exact anticommuting probability -/



/-- A tuple is commuting with the probability complementary to the
anticommuting one. This is the complementarity clause of
blueprint `fact:omega-anticomm-prob`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_eq_one_sub_anticommProb (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    _root_.MIPStarRE.QPBT.commProb P = 1 - _root_.MIPStarRE.QPBT.anticommProb P := by
  have hpos : (0 : ℝ) < (Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) : ℝ) := by
    exact_mod_cast card_pauliTuple_pos P
  have hsum : ((Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsCommuting P)).card : ℝ)
      + ((Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card : ℝ)
      = (Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) : ℝ) := by
    exact_mod_cast card_comm_add_card_anticomm P
  rw [_root_.MIPStarRE.QPBT.commProb, _root_.MIPStarRE.QPBT.anticommProb, eq_sub_iff_add_eq, ← add_div, hsum,
    div_self hpos.ne']

/-- Formalization-only auxiliary: the base `1 - q^{-1}` of the exact
anticommuting probability lies in the unit interval. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem base_mem_unit_interval (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hinv : (P.q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
  constructor <;> linarith

/-- The commuting event has probability at least one half. This is the
complementary bound in blueprint
`fact:omega-anticomm-prob`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_ge_half (P : _root_.MIPStarRE.QPBT.AdmissibleParams) : 1 / 2 ≤ _root_.MIPStarRE.QPBT.commProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hle : (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) ≤ 1 := pow_le_one₀ h0 h1
  rw [_root_.MIPStarRE.QPBT.commProb_eq_one_sub_anticommProb, _root_.MIPStarRE.QPBT.anticommProb_eq]
  linarith





/-! ### Conditional uniform distributions -/









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Averages.lean. -/
/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

scoped instance pauliEdgeNonempty : Nonempty _root_.MIPStarRE.QPBT.PauliEdge := _root_.MIPStarRE.QPBT.pauliEdge_nonempty









/-- Conditioning on the commuting event costs at most its reciprocal lower bound. -/
theorem avgOver_comm_le_two_mul_gated (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (f : _root_.MIPStarRE.QPBT.PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) f ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P))
        (fun ω => if _root_.MIPStarRE.QPBT.IsCommuting ω then f ω else 0) := by
  have hnonempty : (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsCommuting P)).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [_root_.MIPStarRE.QPBT.IsCommuting, _root_.MIPStarRE.QPBT.gammaValue, _root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace, dotProduct]
  have heq := _root_.MIPStarRE.QPBT.WinImplications.cardRatio_mul_avgOver_filter (@_root_.MIPStarRE.QPBT.IsCommuting P) hnonempty f
  change _root_.MIPStarRE.QPBT.commProb P * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) f = _ at heq
  have havg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) f :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.MIPStarRE.QPBT.commTupleDist P) f hf
  nlinarith [_root_.MIPStarRE.QPBT.commProb_ge_half P]









/-- Rejection mass at every fixed edge and seed is nonnegative. -/
theorem pauliRejectionAt_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (e : _root_.MIPStarRE.QPBT.PauliEdge) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    0 ≤ _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S e z := by
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg S _ _ _

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) :
    _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
      _root_.MIPStarRE.QPBT.outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  simpa only [_root_.MIPStarRE.QPBT.outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    _root_.MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S

/-- Winning bounds the global rejection average. -/
theorem pauliRejectionAverage_le_error {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
        (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) ≤ ε := by
  have havg : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
      (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) =
      1 - S.toStrategy.value := by
    rw [← _root_.MIPStarRE.QPBT.WinImplications.rejectionEventAverage_eq_one_sub_value S.toStrategy]
    unfold _root_.MIPStarRE.QPBT.pauliBasisTest _root_.MIPStarRE.QPBT.pauliQuestionDistribution
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith [S.win]

/-- Fixing one verifier edge costs at most the cardinality of the finite edge graph. -/
theorem fixedEdgeRejection_le_error {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (e : _root_.MIPStarRE.QPBT.PauliEdge) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy e) ≤
      (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy e) ≤
        (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
            (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) := by
      exact _root_.MIPStarRE.QPBT.WinImplications.avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt_nonneg S.toStrategy edge z) e
    _ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAverage_le_error S)
        (Nat.cast_nonneg _)


end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  classical
  rw [_root_.MIPStarRE.QPBT.WinImplications.pairWConsistency_eq_mismatch]
  calc
    _ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
        if _root_.MIPStarRE.QPBT.IsCommuting ω then
          _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A ≠
              _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply _root_.MIPStarRE.QPBT.WinImplications.avgOver_comm_le_two_mul_gated
      intro ω
      exact _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge (.pairW W))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← _root_.MIPStarRE.QPBT.WinImplications.avgOver_pauliTuple_uniform]
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro z
      have hs : _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          ((.pairW W), _root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)
          ((.pairW W), _root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)
          (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A ≠
            _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero B) ≤
          _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge (.pairW W)) z := by
        refine le_trans ?_ (_root_.MIPStarRE.QPBT.WinImplications.loopMismatch_le_rejection S (.pairW W) z)
        apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
        intro A B hne hAB
        exact hne (by rw [hAB])
      rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.pairW W) rfl] at hs
      by_cases hcomm : _root_.MIPStarRE.QPBT.IsCommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        simpa [_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit, _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWQuestion] using hs
      · simp only [if_neg hcomm]
        exact _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.WinImplications.fixedEdgeRejection_le_error S _)
        (by norm_num)
