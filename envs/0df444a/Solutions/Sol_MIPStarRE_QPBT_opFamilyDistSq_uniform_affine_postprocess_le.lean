-- Prove2me | solution 1 for MIPStarRE.QPBT.opFamilyDistSq_uniform_affine_postprocess_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:56.853453+00:00
-- url     : https://prove2.me/submissions/18725c67-5fcf-4687-8d2d-ff3aec273c1c

-- Generated proof for MIPStarRE.QPBT.opFamilyDistSq_uniform_affine_postprocess_le.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_affine_collision_average

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

/- Source helpers from QPBT/Combining/PointsDataProcessing.lean. -/
/-!
# Averaged affine coarse-graining of complete operator families

Uniform scalar coefficients give collision probability `1 / card K` for
distinct pairs over a finite field. Expanding the squared state-dependent
distance therefore proves contraction when the two operator families have
the same total operator. The placement lemmas apply this identity to the
complete point measurements and to both ordered measurement products.

## References

This is the finite-dimensional calculation used for the coarse-graining in
`lem:qld-4-12`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1018`.
The operator-family contraction is a formalization-only auxiliary lemma.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section





private theorem sum_fiber_norm_sq_eq_pair_sum
    {Γ R ι : Type*} [Fintype Γ] [Fintype R] [DecidableEq R]
    [Fintype ι] [DecidableEq ι]
    (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
      ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
  classical
  calc
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
        ∑ r : R, ∑ g ∈ Finset.univ.filter (fun g => f g = r),
          ∑ g' ∈ Finset.univ.filter (fun g' => f g' = r),
            (inner ℂ (v g) (v g')).re := by
              apply Finset.sum_congr rfl
              intro r _
              simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum]
              apply Finset.sum_congr rfl
              intro g _
              apply Finset.sum_congr rfl
              intro g' _
              exact inner_re_symm _ _
    _ = ∑ r : R, ∑ g : Γ, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro g _
          by_cases hg : f g = r
          · rw [if_pos hg, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro g' _
            by_cases hg' : f g' = r <;> simp [hg, hg']
          · simp [hg]
    _ = ∑ g : Γ, ∑ r : R, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ g : Γ, ∑ g' : Γ, ∑ r : R,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          rw [Finset.sum_comm]
    _ = ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          apply Finset.sum_congr rfl
          intro g' _
          by_cases hgg' : f g = f g'
          · rw [if_pos hgg', Fintype.sum_eq_single (f g)]
            · simp [hgg']
            · intro r hr
              simp [Ne.symm hr]
          · rw [if_neg hgg']
            apply Finset.sum_eq_zero
            intro r _
            simp only [ite_eq_right_iff]
            intro h
            exact (hgg' (h.1.trans h.2.symm)).elim

private theorem avg_affine_fiber_norm_sq_le
    {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (v : K × K → EuclideanSpace ℂ ι) (hsum : ∑ p, v p = 0) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) ≤
      ∑ p, ‖v p‖ ^ 2 := by
  classical
  let w : (K × K) → (K × K) → ℝ := fun p p' => (inner ℂ (v p) (v p')).re
  let qinv : ℝ := (Fintype.card K : ℝ)⁻¹
  have hall : (∑ p, ∑ p', w p p') = 0 := by
    have h := sum_fiber_norm_sq_eq_pair_sum (fun _ : K × K => ()) v
    simpa [w, hsum] using h.symm
  have hdiag : (∑ p, w p p) = ∑ p, ‖v p‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    exact (@norm_sq_eq_re_inner ℂ _ _ _ _ (v p)).symm
  have hnonneg : 0 ≤ ∑ p, ‖v p‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hqinv : 0 ≤ qinv := by positivity
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
          ∑ p, ∑ p', if
            coefficients.1 * p.1 + coefficients.2 * p.2 =
              coefficients.1 * p'.1 + coefficients.2 * p'.2 then w p p' else 0) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro coefficients
            exact sum_fiber_norm_sq_eq_pair_sum _ v
    _ = ∑ p, ∑ p', _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
          if coefficients.1 * p.1 + coefficients.2 * p.2 =
              coefficients.1 * p'.1 + coefficients.2 * p'.2 then w p p' else 0) := by
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
            apply Finset.sum_congr rfl
            intro p _
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
    _ = ∑ p, ∑ p', if p = p' then w p p' else qinv * w p p' := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro p' _
            calc
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
                  if coefficients.1 * p.1 + coefficients.2 * p.2 =
                      coefficients.1 * p'.1 + coefficients.2 * p'.2 then
                    w p p' else 0) =
                  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
                    (if coefficients.1 * p.1 + coefficients.2 * p.2 =
                        coefficients.1 * p'.1 + coefficients.2 * p'.2 then
                      (1 : ℝ) else 0) * w p p') := by
                        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                        intro coefficients
                        split <;> simp_all
              _ = (if p = p' then 1 else qinv) * w p p' := by
                    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_mul_const, _root_.MIPStarRE.QPBT.affine_collision_average]
              _ = if p = p' then w p p' else qinv * w p p' := by
                    split <;> simp_all
    _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by
          calc
            (∑ p, ∑ p', if p = p' then w p p' else qinv * w p p') =
                qinv * (∑ p, ∑ p', w p p') + (1 - qinv) * ∑ p, w p p := by
                  rw [Finset.mul_sum, Finset.mul_sum]
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro p _
                  calc
                    (∑ p', if p = p' then w p p' else qinv * w p p') =
                        ∑ p', (qinv * w p p' +
                          if p = p' then (1 - qinv) * w p p' else 0) := by
                            apply Finset.sum_congr rfl
                            intro p' _
                            by_cases h : p = p' <;> simp [h]
                            ring
                    _ = qinv * ∑ p', w p p' + (1 - qinv) * w p p := by
                          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                          congr 1
                          rw [Fintype.sum_eq_single p]
                          · simp
                          · intro p' hp'
                            simp [Ne.symm hp']
            _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by rw [hall, hdiag]; ring
    _ ≤ ∑ p, ‖v p‖ ^ 2 := by nlinarith











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean. -/
/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  The reflections
of the source are the binary observables of the rest of the development, so this
file uses `MIPStarRE.QPBT.IsBinaryObservable` and its algebra, defined in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`, rather than a second predicate of
its own.  Two operators are compared through the norm of the difference of their
actions on a fixed state, the relation `NormCloseOn` below.  That relation is the
unsquared Euclidean distance between `M ψ` and `N ψ`; it is *not* the
state-dependent distance `≈_δ` of the source, which bounds the squared quantity
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩` and is formalized in this development by `opDistSq`.
The comparison is symmetric, satisfies the triangle inequality, and is unchanged
by multiplication on the left by an isometric operator; `NormCloseOn.opDistSq_le`
converts it into the source's relation.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/



/-! ## The state-dependent norm -/

section StateNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι]





/-- Formalization-only: acting by a finite sum of operators is the sum of the
actions. -/
theorem applyOperatorToState_sum {γ : Type} [Fintype γ]
    (M : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (∑ c, M c) ψ = ∑ c, _root_.MIPStarRE.QPBT.applyOperatorToState (M c) ψ := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]





end StateNorm

/-! ## Reflections

The *reflections* of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:228-250`, are the self-adjoint involutions attached to
two-outcome projective measurements, which are exactly the binary observables
`MIPStarRE.QPBT.IsBinaryObservable` of
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.  The Magic Square rigidity
argument therefore uses that predicate and its algebra directly:
`IsBinaryObservable.one`, `IsBinaryObservable.mul`,
`IsBinaryObservable.isometry`, `isBinaryObservable_heteroKron_one` and
`isBinaryObservable_one_heteroKron`. -/



/-! ## Closeness in the state-dependent norm -/





/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/



end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Averaged affine coarse-graining of complete operator families

Uniform scalar coefficients give collision probability `1 / card K` for
distinct pairs over a finite field. Expanding the squared state-dependent
distance therefore proves contraction when the two operator families have
the same total operator. The placement lemmas apply this identity to the
complete point measurements and to both ordered measurement products.

## References

This is the finite-dimensional calculation used for the coarse-graining in
`lem:qld-4-12`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1018`.
The operator-family contraction is a formalization-only auxiliary lemma.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution
    {X K ι : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (A B : X → K × K → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι)
    (hsum : ∀ x, ∑ p, A x p = ∑ p, B x p) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × (K × K)))
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), A question.1 p)
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), B question.1 p)
        ψ ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) A B ψ := by
  classical
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × (K × K))) (fun question =>
        ∑ c : K,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            ((∑ p ∈ Finset.univ.filter (fun p =>
                question.2.1 * p.1 + question.2.2 * p.2 = c), A question.1 p) -
              ∑ p ∈ Finset.univ.filter (fun p =>
                question.2.1 * p.1 + question.2.2 * p.2 = c), B question.1 p) ψ‖ ^ 2) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
            ∑ c : K,
              ‖_root_.MIPStarRE.QPBT.applyOperatorToState
                ((∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                  ∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2)) := by
          simpa only using (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := X) (β := K × K)
            (fun x coefficients =>
              ∑ c : K,
                ‖_root_.MIPStarRE.QPBT.applyOperatorToState
                  ((∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                    ∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2))
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x =>
        ∑ p, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x p - B x p) ψ‖ ^ 2) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro x
      let v : K × K → EuclideanSpace ℂ ι := fun p =>
        _root_.MIPStarRE.QPBT.applyOperatorToState (A x p - B x p) ψ
      have hvsum : ∑ p, v p = 0 := by
        simp only [v]
        calc
          (∑ p, _root_.MIPStarRE.QPBT.applyOperatorToState (A x p - B x p) ψ) =
              _root_.MIPStarRE.QPBT.applyOperatorToState (∑ p, (A x p - B x p)) ψ :=
                (_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sum
                  (fun p => A x p - B x p) ψ).symm
          _ = 0 := by
            rw [Finset.sum_sub_distrib, hsum x, sub_self]
            simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
      calc
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
            ∑ c : K,
              ‖_root_.MIPStarRE.QPBT.applyOperatorToState
                ((∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                  ∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2) =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
              ∑ c : K,
                ‖∑ p ∈ Finset.univ.filter (fun p =>
                  coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) := by
                  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                  intro coefficients
                  apply Finset.sum_congr rfl
                  intro c _
                  congr 2
                  simp only [v, _root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply,
                    map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]
        _ ≤ ∑ p, ‖v p‖ ^ 2 := avg_affine_fiber_norm_sq_le v hvsum
        _ = ∑ p, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x p - B x p) ψ‖ ^ 2 := rfl
