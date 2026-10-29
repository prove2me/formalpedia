-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_arbitrary_strategy_raw_isometry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:57:45.57998+00:00
-- url     : https://prove2.me/submissions/def8c3ba-0334-42f4-b3e6-61aa248f9f1f

-- Generated proof for MIPStarRE.QPBT.exists_arbitrary_strategy_raw_isometry_bounds.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_RawOperatorTransfer
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_deltaQld_mono
import Theorems.Thm_MIPStarRE_QPBT_exists_arbitrary_strategy_isometry_bounds
import Theorems.Thm_MIPStarRE_QPBT_raw_pauli_operator_distanceA_le_completed
import Theorems.Thm_MIPStarRE_QPBT_raw_pauli_operator_distanceB_le_completed
import Theorems.Thm_MIPStarRE_QPBT_scale_deltaQld_le
import Theorems.Thm_MIPStarRE_QPBT_three_add_six_sq_deltaQld_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Strategy
end MIPStarRE.QPBT.Strategy

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

























end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/EpsReduction.lean. -/
/-!
# Extending Pauli soundness bounds from `ε ≤ 1` to the full error domain

The Pauli basis test soundness statement quantifies over every error parameter
`0 ≤ ε`, while the extraction and isometry arguments that establish it are
carried out for `0 ≤ ε ≤ 1`.  This module supplies the two Lean-only facts that
bridge the two domains.

## Main results

* `deltaQld_mono_epsilon` — the error scale `deltaQld` is monotone in `ε`
  on `0 ≤ ε`; only the `ε ^ b` summand depends on `ε`.
* `pauli_isometry_bounds_extend_epsilon` — the soundness conclusion for every
  `ε` in `[0, 1]` implies the same conclusion for every `0 ≤ ε`, at the same
  universal constants `a` and `b`.

For `1 ≤ ε` the success hypothesis `1 - ε ≤ S.value` carries no information:
it already follows from `Strategy.value_nonneg` applied at `ε = 1`.  The
`ε ≤ 1` result is therefore instantiated at `ε = 1` and its conclusion pushed
up to the larger `ε` by monotonicity of `deltaQld`.  No trivial witness and no
uniform numeric bound are involved.

## References

These are formalization-only support results for blueprint `thm:pauli`, whose
statement is at paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
and whose isometry step is proved at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.  The
source states the theorem for every `ε ≥ 0` and argues the substantive case
`ε ≤ 1`; the reduction recorded here is the bookkeeping that the source leaves
implicit.  It adds no hypothesis to `thm:pauli` and changes no constant.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- The Pauli-test error scale `deltaQld` is monotone in the error parameter `ε`
on `0 ≤ ε`.  Only the summand `ε ^ b` depends on `ε`, and the prefactor
`a * (m * d) ^ a` is nonnegative, so the bound follows from monotonicity of
`Real.rpow` in its base.

Unlike `deltaQld_mono`, which adjusts the universal constants `a` and `b` and is
therefore restricted to `ε ≤ 1`, this lemma keeps `a` and `b` fixed and holds on
the whole domain `0 ≤ ε` of blueprint `thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
theorem deltaQld_mono_epsilon {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b ε ε' : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hε0 : 0 ≤ ε) (hle : ε ≤ ε') :
    _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε' P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by linarith
  unfold _root_.MIPStarRE.QPBT.deltaQld
  simp only [Real.rpow_eq_pow]
  have hεb : ε ^ b ≤ ε' ^ b := Real.rpow_le_rpow hε0 hle hb.le
  have hpre : 0 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hmd0 a)
  exact mul_le_mul_of_nonneg_left (by linarith) hpre



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/ScalarAbsorption.lean. -/
/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The Pauli soundness error is nonnegative whenever its prefactor and its
error argument are. The remaining two summands of the error bracket are
`rpow`s of nonnegative bases, so no admissibility hypothesis is needed. -/
theorem deltaQld_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon : ℝ}
    (ha : 0 ≤ a) (hepsilon : 0 ≤ epsilon) :
    0 ≤ _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q := by
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := Real.rpow_nonneg hepsilon b
  have h2 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold _root_.MIPStarRE.QPBT.deltaQld
  simp only [Real.rpow_eq_pow]
  exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hdegree0 a)) (by linarith)





end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/RejectionBounds.lean. -/
/-! # Probability bounds for the directly indexed low-degree game

This module records two elementary probability bounds needed when a caller caps an
assembled direct-game rejection estimate by one. The results are formalization-only
support: they do not bound any individual game branch or prove a passing-value theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#333
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

namespace Strategy

/-- Every tensor-product strategy has nonnegative value. -/
theorem value_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : 0 ≤ S.value := by
  unfold _root_.MIPStarRE.QPBT.Strategy.value
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg
  intro questions
  apply Finset.sum_nonneg
  intro answerA _
  apply Finset.sum_nonneg
  intro answerB _
  split
  · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S questions.1 questions.2 answerA answerB
  · exact le_rfl

end Strategy



end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/RawOperatorTransfer.lean. -/
/-!
# Final raw Pauli-effect soundness bounds

This module absorbs the completed-to-raw transfer loss into the Pauli
soundness error and exposes the fixed explicit baseline and existential
source-facing bounds. The operator transfer itself is implemented in
`MIPStarRE.QPBT.Test.Soundness.RawOperatorTransferCore`.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section



private theorem epsilon_le_deltaQld {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hmd
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hpref : 1 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd ha0)
  have hεpow : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
  have hq := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold _root_.MIPStarRE.QPBT.deltaQld
  simp only [Real.rpow_eq_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpref)
    (add_nonneg (add_nonneg (Real.rpow_nonneg hε0 b) hq) htwo)]

private theorem raw_pauli_error_absorb {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q +
        4 * _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ^ 2 +
        4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε ≤
      _root_.MIPStarRE.QPBT.deltaQld (rawPauliTransferFactor * (21 * a ^ 2)) b ε P.m P.d P.q := by
  let d := _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q
  let K := rawPauliTransferFactor
  have hd : 0 ≤ d := _root_.MIPStarRE.QPBT.deltaQld_nonneg (zero_le_one.trans ha) hε0
  have hεd : ε ≤ d := epsilon_le_deltaQld ha hb hb1 hε0 hε1
  have hK : 1 ≤ K := by
    dsimp only [K, rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card _root_.MIPStarRE.QPBT.PauliEdge := Nat.cast_nonneg _
    linarith
  have hbase : 3 * d + 6 * d ^ 2 ≤
      _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    _root_.MIPStarRE.QPBT.three_add_six_sq_deltaQld_le ha hb hε0 hε1
  calc
    2 * d + 4 * d ^ 2 + 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε ≤
        (2 + 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card _root_.MIPStarRE.QPBT.PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard (sub_nonneg.mpr hεd)]
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card _root_.MIPStarRE.QPBT.PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard hd, mul_nonneg hcard (sq_nonneg d), sq_nonneg d]
    _ ≤ K * _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hK)
    _ ≤ _root_.MIPStarRE.QPBT.deltaQld (K * (21 * a ^ 2)) b ε P.m P.d P.q := by
      exact _root_.MIPStarRE.QPBT.scale_deltaQld_le (by nlinarith [sq_nonneg a]) hε0 hK





end

end MIPStarRE.QPBT

/-!
# Final raw Pauli-effect soundness bounds

This module absorbs the completed-to-raw transfer loss into the Pauli
soundness error and exposes the fixed explicit baseline and existential
source-facing bounds. The operator transfer itself is implemented in
`MIPStarRE.QPBT.Test.Soundness.RawOperatorTransferCore`.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution :
    ∃ A b : ℝ, 1 ≤ A ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S,
            ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤
                _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hcompleted⟩ := _root_.MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds
  let A := rawPauliTransferFactor * (21 * a ^ 2)
  have hfactor : 1 ≤ rawPauliTransferFactor := by
    dsimp only [rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card _root_.MIPStarRE.QPBT.PauliEdge := Nat.cast_nonneg _
    linarith
  have h21 : 1 ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ rawPauliTransferFactor * (21 * a ^ 2) :=
        mul_le_mul hfactor h21 zero_le_one (zero_le_one.trans hfactor)
  have ha21 : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have h21A : 21 * a ^ 2 ≤ A := by
    dsimp only [A]
    exact le_mul_of_one_le_left (by positivity) hfactor
  have haA : a ≤ A := ha21.trans h21A
  have hsmall : ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S,
          ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤
              _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q ∧
          (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
            _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q) ∧
          (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
            _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q) := by
    intro P ε hε0 hε1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      hcompleted P ε hε0 hε1 S hwin
    let d := _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε ≤
          _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q := by
      dsimp only [d, A]
      exact raw_pauli_error_absorb ha hb hb1 hε0 hε1
    have hmono : d ≤ _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q := by
      dsimp only [d]
      exact _root_.MIPStarRE.QPBT.deltaQld_mono ha haA le_rfl hb hε0 hε1
    refine ⟨w, hstate.trans hmono, ?_, ?_⟩
    · intro W
      calc
        _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W ≤
            2 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S w W + 4 * d ^ 2 +
              4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε :=
          _root_.MIPStarRE.QPBT.raw_pauli_operator_distanceA_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
          linarith [hcompletedA W]
        _ ≤ _ := habsorb
    · intro W
      calc
        _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P S w W ≤
            2 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S w W + 4 * d ^ 2 +
              4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε :=
          _root_.MIPStarRE.QPBT.raw_pauli_operator_distanceB_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
          linarith [hcompletedB W]
        _ ≤ _ := habsorb
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact hsmall P ε hε0 hε1 S hwin
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : _root_.MIPStarRE.QPBT.deltaQld A b 1 P.m P.d P.q ≤
        _root_.MIPStarRE.QPBT.deltaQld A b ε P.m P.d P.q :=
      _root_.MIPStarRE.QPBT.deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩
