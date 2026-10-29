-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.point_mismatch_le_ordered_error
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:53:00.210501+00:00
-- url     : https://prove2.me/submissions/3a26ca09-0666-492e-bac8-6bc6d028ed65

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.point_mismatch_le_ordered_error.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_avg_wrong_ordered_norm_sq_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/- Source helpers from QPBT/Combining/PolynomialImageBounds.lean. -/
/-!
# Indicator-weighted ordered products

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#513.

Only the dependency chain needed for these estimates is exposed; supporting
lemmas remain private.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]











































omit [DecidableEq ι] in
/-- The squared-norm triangle inequality retains each outcome's state vector.
This norm-to-residual step is shared with the
wrong-variable argument in `eq:qld-g-prime-xpt-bound`; support for blueprint
`lem:qld-4-7`. No normalization is assumed. -/
theorem sum_mass_le_residual_add_image {Γ : Type*} (s : Finset Γ)
    (ψ A : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
      2 * ∑ g ∈ s, ‖ψ g - A g‖ ^ 2 + 2 * ∑ g ∈ s, ‖A g‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun g _ => ?_
  have htriangle := norm_add_le (ψ g - A g) (A g)
  rw [sub_add_cancel] at htriangle
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖ψ g - A g‖ - ‖A g‖)]



end PolynomialImageBounds

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/



















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h



/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg











/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Retained point mismatch from ordered estimates

The incorrect point projection is the outer factor of the ordered product.
The scalar collision identity then bounds its average image norm without an
outcome-count factor. All vectors remain unnormalized.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

theorem solution (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        ‖ψ - _root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) +
      4 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  have hpoint (v : Fin 2 → F) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) ψ‖ ^ 2 ≤
        2 * ‖ψ - _root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 +
        2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((1 - X.effect r) *
          _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 := by
    let T := _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)
    have h := _root_.MIPStarRE.QPBT.PolynomialImageBounds.sum_mass_le_residual_add_image (Finset.univ : Finset Unit)
      (fun _ => _root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) ψ)
      (fun _ => _root_.MIPStarRE.QPBT.applyOperatorToState ((1 - X.effect r) * T) ψ)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    have hcontract :
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) ψ -
          _root_.MIPStarRE.QPBT.applyOperatorToState ((1 - X.effect r) * T) ψ‖ ≤
        ‖ψ - _root_.MIPStarRE.QPBT.applyOperatorToState T ψ‖ := by
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
      have heq : _root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) ψ -
          _root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) (_root_.MIPStarRE.QPBT.applyOperatorToState T ψ) =
          _root_.MIPStarRE.QPBT.applyOperatorToState (1 - X.effect r) (ψ - _root_.MIPStarRE.QPBT.applyOperatorToState T ψ) := by
        simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub]
      rw [heq]
      exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcontract 2)
        (by norm_num)) le_rfl)
  have h := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) _ _ hpoint
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul] at h
  have hm := _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_wrong_ordered_norm_sq_le X Z hX hZ r t ψ
  linarith
