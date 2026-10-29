-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_seedFiber_compress_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:24.324062+00:00
-- url     : https://prove2.me/submissions/1d478ca5-8c3e-44b0-8826-a695621b987b

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_seedFiber_compress_left.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Algebra/Pauli.lean. -/
/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]























/-- Conjugated form of `inv_sqrt_natCast_mul_self`: the normalizing amplitude
`(√n)⁻¹` is real, so pairing it with its conjugate again gives `n⁻¹`.  This
formalization-only auxiliary is the form in which the identity occurs in Born
amplitudes, where the bra side carries the conjugate. -/
theorem inv_sqrt_natCast_mul_conj (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ by simp]
  exact _root_.MIPStarRE.QPBT.inv_sqrt_natCast_mul_self n

























































end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/SeedFiber.lean. -/
/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Projective block measurements -/













/-! ## The correlated residue state -/









/-! ## From the seed-indexed game to the direct game -/













/-- Coordinate formula for the correlated residue lift. -/
theorem seedFiberLiftedState_apply
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    (i : S.ιA) (j : S.ιB)
    (r s : Fin (L.q / L.m)) :
    _root_.MIPStarRE.QPBT.seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then
        S.ψ (i, j) * (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹
      else 0 := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [_root_.MIPStarRE.QPBT.seedFiberLiftedState, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, _root_.MIPStarRE.QPBT.seedResidueAncilla,
    _root_.MIPStarRE.QPBT.eprState, _root_.MIPStarRE.QPBT.prodShuffle]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Consistency/Compression.lean. -/
/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Seed-fiber identities -/











private theorem correlatedState_compress_left
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (iotaA × block)) (B : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm phi
        (_root_.MIPStarRE.QPBT.heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.averageDiagonalBlock A) B) := by
  classical
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker _root_.MIPStarRE.QPBT.averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (B j j' * (A (i, r) (i', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (B j j' *
                ((Fintype.card block : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [_root_.MIPStarRE.QPBT.inv_sqrt_natCast_mul_conj (Fintype.card block)]
  ring



/-- Compressing Alice's ancillary register preserves every correlation against
an operator on Bob's original carrier. -/
theorem seedFiberLiftedState_compress_left
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιA × Fin (L.q / L.m))) (B : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L)
        (_root_.MIPStarRE.QPBT.heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.averageDiagonalBlock A) B) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_left S.ψ (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L)
  intro i j r s
  exact _root_.MIPStarRE.QPBT.seedFiberLiftedState_apply S L i j r s











end

end MIPStarRE.QPBT

/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Seed-fiber identities -/

theorem solution
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A : X → alpha → _root_.LIDT.MIPStarRE.Quantum.Op (S.ιA × Fin (L.q / L.m)))
    (B : X → alpha → _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L) =
      _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.averageDiagonalBlock (A x a)) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (B x a)) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.LIDT.MIPStarRE.LDT.avgOver
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm,
    _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact _root_.MIPStarRE.QPBT.seedFiberLiftedState_compress_left S L (A x a) (B x b)
