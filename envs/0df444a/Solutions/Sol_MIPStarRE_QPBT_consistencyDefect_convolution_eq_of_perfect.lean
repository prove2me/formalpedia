-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:02.509996+00:00
-- url     : https://prove2.me/submissions/5bc8d931-c23a-4567-9c31-67be0a38b0f2

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect.
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_State
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_inner_prodShuffle_vecTensor_heteroKron

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ

























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

/- Source helpers from QPBT/Games/DistanceTheorems/TensorConsistency.lean. -/
/-! # Consistency under independent additive convolution

Adding the outcomes of an independently perfectly correlated ancillary measurement
pair preserves the consistency defect. The four register types are independent;
`prodShuffle` places the two registers of each player next to one another.

These are formalization-only auxiliary identities. Perfect ancillary correlation
is a hypothesis of the generic result, to be proved for the Pauli measurements
before applying it to the expanded point construction.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-438`,
  the expanded state and the convolution formula for expanded point effects.
- The same paper, `lem:qld-construct-the-paulis`.
- Blueprint `def:expanded-state` and `def:expanded-point-measurement`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#266; the ideal-point specialization is the separate issue
  Dengnifer/MIPStarRE-QPBT-bak#267.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

section Factorization

variable {ιA ιB κA κB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]



/-- For positive ancillary effects, the real joint expectation factors on the
shuffled tensor state. No normalization or positivity of `A` and `B` is needed. -/
theorem stateQForm_prodShuffle_vecTensor_heteroKron
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) {R : _root_.LIDT.MIPStarRE.Quantum.Op κA} {T : _root_.LIDT.MIPStarRE.Quantum.Op κB}
    (hR : 0 ≤ R) (hT : 0 ≤ T) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor ψ φ))
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A R) (_root_.MIPStarRE.QPBT.heteroKron B T)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm φ (_root_.MIPStarRE.QPBT.heteroKron R T) := by
  have hnonneg := (Matrix.nonneg_iff_posSemidef.mp
    (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg hR hT)).dotProduct_mulVec_nonneg φ.ofLp
  have him : (inner ℂ φ (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron R T) φ)).im = 0 := by
    simpa only [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, _root_.MIPStarRE.QPBT.heteroKron] using
      (Complex.nonneg_iff.mp hnonneg).2.symm
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.inner_prodShuffle_vecTensor_heteroKron, Complex.mul_re,
    him, mul_zero, sub_zero]

end Factorization

/-- An additive convolution of effect families can be indexed by the ancillary
answer alone. This is the finite-fiber form of the expanded point construction. -/
theorem sum_add_fiber_heteroKron {G ι κ : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup G]
    (A : G → _root_.LIDT.MIPStarRE.Quantum.Op ι) (R : G → _root_.LIDT.MIPStarRE.Quantum.Op κ) (z : G) :
    (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
      _root_.MIPStarRE.QPBT.heteroKron (A p.1) (R p.2)) =
      ∑ c : G, _root_.MIPStarRE.QPBT.heteroKron (A (z - c)) (R c) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← eq_sub_iff_add_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Averaging a common additive shift preserves the off-diagonal mass of any
weight function. The ancillary joint weights are supported on the diagonal
and have total diagonal mass one. -/
private theorem sum_convolution_off_diagonal_eq {G : Type*}
    [Fintype G] [DecidableEq G] [AddCommGroup G]
    (p q : G → G → ℝ) (hzero : ∀ c d, c ≠ d → q c d = 0)
    (hdiag : ∑ c : G, q c c = 1) :
    (∑ z : G, ∑ w : G, if z = w then 0 else
      ∑ c : G, ∑ d : G, p (z - c) (w - d) * q c d) =
      ∑ a : G, ∑ b : G, if a = b then 0 else p a b := by
  have hinner (z w c : G) :
      (∑ d : G, p (z - c) (w - d) * q c d) =
        p (z - c) (w - c) * q c c := by
    apply Finset.sum_eq_single c
    · intro d _ hdc
      rw [hzero c d hdc.symm, mul_zero]
    · simp
  have hshift (c : G) :
      (∑ z : G, ∑ w : G, if z = w then 0 else p (z - c) (w - c)) =
        ∑ a : G, ∑ b : G, if a = b then 0 else p a b := by
    refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun z => ?_
    refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun w => ?_
    change (if z = w then 0 else p (z - c) (w - c)) =
      if z - c = w - c then 0 else p (z - c) (w - c)
    simp only [sub_left_inj]
  simp_rw [hinner]
  calc
    (∑ z : G, ∑ w : G, if z = w then 0 else
        ∑ c : G, p (z - c) (w - c) * q c c) =
        ∑ z : G, ∑ w : G, ∑ c : G,
          (if z = w then 0 else p (z - c) (w - c)) * q c c := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      by_cases hzw : z = w <;> simp [hzw]
    _ = ∑ c : G, (∑ z : G, ∑ w : G,
        if z = w then 0 else p (z - c) (w - c)) * q c c := by
      simp_rw [Finset.sum_mul]
      conv_lhs =>
        arg 2
        ext z
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hshift]
      rw [← Finset.mul_sum, hdiag, mul_one]



end MIPStarRE.QPBT

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

/-! # Consistency under independent additive convolution

Adding the outcomes of an independently perfectly correlated ancillary measurement
pair preserves the consistency defect. The four register types are independent;
`prodShuffle` places the two registers of each player next to one another.

These are formalization-only auxiliary identities. Perfect ancillary correlation
is a hypothesis of the generic result, to be proved for the Pauli measurements
before applying it to the expanded point construction.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-438`,
  the expanded state and the convolution formula for expanded point effects.
- The same paper, `lem:qld-construct-the-paulis`.
- Blueprint `def:expanded-state` and `def:expanded-point-measurement`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#266; the ideal-point specialization is the separate issue
  Dengnifer/MIPStarRE-QPBT-bak#267.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {ιA ιB κA κB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

theorem solution
    {X G ιA ιB κA κB : Type*}
    [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G] [AddCommGroup G]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement G ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement G ιB)
    (R : X → _root_.LIDT.MIPStarRE.Quantum.Measurement G κA) (T : X → _root_.LIDT.MIPStarRE.Quantum.Measurement G κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (hφ : ‖φ‖ = 1)
    (hperfect : ∀ x, (∑ c : G, ∑ d : G, if c = d then 0 else
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm φ (_root_.MIPStarRE.QPBT.heteroKron ((R x).effect c) ((T x).effect d))) = 0) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x z => _root_.MIPStarRE.QPBT.heteroKron
          (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
            _root_.MIPStarRE.QPBT.heteroKron ((A x).effect p.1) ((R x).effect p.2)) 1)
        (fun x z => _root_.MIPStarRE.QPBT.heteroKron 1
          (∑ p ∈ Finset.univ.filter (fun p : G × G => p.1 + p.2 = z),
            _root_.MIPStarRE.QPBT.heteroKron ((B x).effect p.1) ((T x).effect p.2)))
        (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor ψ φ)) =
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect b)) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm, _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  let q : G → G → ℝ := fun c d =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm φ (_root_.MIPStarRE.QPBT.heteroKron ((R x).effect c) ((T x).effect d))
  have hnonneg (c d : G) : 0 ≤ q c d :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg φ (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((R x).pos c) ((T x).pos d))
  have hoff (c d : G) : 0 ≤ (if c = d then 0 else q c d) := by
    split_ifs
    · exact le_rfl
    · exact hnonneg c d
  have hzero (c d : G) (hcd : c ≠ d) : q c d = 0 := by
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => Finset.sum_nonneg (fun d _ => hoff c d))).mp (hperfect x)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => hoff c d)).mp (hrow c (Finset.mem_univ c)) d (Finset.mem_univ d)
    simpa only [if_neg hcd] using hterm
  have hdiag : ∑ c : G, q c c = 1 := by
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (R x))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (T x)) φ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
      _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq, hperfect x, hφ, one_pow] at h
    dsimp only [q]
    linarith
  have hfactor (a b c d : G) := _root_.MIPStarRE.QPBT.stateQForm_prodShuffle_vecTensor_heteroKron ψ φ
    ((A x).effect a) ((B x).effect b) ((R x).pos c) ((T x).pos d)
  simp_rw [_root_.MIPStarRE.QPBT.sum_add_fiber_heteroKron, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left,
    _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, hfactor]
  exact sum_convolution_off_diagonal_eq
    (fun a b => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) ((B x).effect b)))
    q hzero hdiag
