-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.chain_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:57.251544+00:00
-- url     : https://prove2.me/submissions/a6d7158b-5cc0-496e-ae0e-d17a80109789

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.chain_bounds.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_Combining_Points_Sandwich
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le

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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/-!
# Closeness estimates for the combined point measurements

Given projective measurements `Q^{x,z}` on each player's expanded local space
that are close to the sandwich POVMs on the placements where they were
constructed, this file assembles the three conclusions of `lem:qld-4-10` on
every pair of opposite placements by the triangle inequality along
`Q ≈ R ≈ M^Z M^X ≈ M^X M^Z` and the cross-placement consistency of the
ordered products.  It also records the bound `4` on the averaged squared
state-dependent distance of two families satisfying `∑ a, (A a)ᴴ * A a ≤ 1`
and `∑ a, (B a)ᴴ * B a ≤ 1` at every question, used when the test error
exceeds one, and the elementary estimate collapsing the error terms `ε`,
`√ε`, and `(ε + √ε)^{1/4}` into a single power `ε^{1/8}` when `ε ≤ 1`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`
(self-consistency and consistency with `M̂` in the proof of `lem:qld-4-10`),
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:803-960`; the route
is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The trivial bound -/









/-! ## The chain of closeness estimates -/

open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (Q : (side : _root_.MIPStarRE.QPBT.PlayerSide) → _root_.MIPStarRE.QPBT.PointPair P →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) (S.ExpandedLocalSpace side))
    (η C₁ C₂ C₃ : ℝ)
    (hQR : ∀ p : _root_.MIPStarRE.QPBT.Placement, _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ η)
    (h₁ : ∀ p : _root_.MIPStarRE.QPBT.Placement, _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
        S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat ≤ C₁ * Real.sqrt ε)
    (h₂ : ∀ p : _root_.MIPStarRE.QPBT.Placement, _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat ≤ C₂ * Real.sqrt ε)
    (h₃ : ∀ p₁ p₂ : _root_.MIPStarRE.QPBT.Placement, p₁.IsOpposite p₂ →
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p₁
          ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ C₃ * ε)
    (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1))
        S.psiHat ≤ 4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) +
          2 * (C₂ * Real.sqrt ε) ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
          S.place p₁ ((Q p₁.side xz).effect ab))
        (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab))
        S.psiHat ≤ 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) +
          4 * (C₂ * Real.sqrt ε) := by
  -- `R_1 ≈ M^X M^Z` on the opposite placement
  have hRXZ := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
    _ _ _ S.psiHat _ _ (h₁ p₁) (h₃ p₁ p₂ hopp)
  -- `Q_1 ≈ M^X M^Z` on the opposite placement
  have hQXZ := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
    _ _ _ S.psiHat _ _ (hQR p₁) hRXZ
  -- `Q_1 ≈ M^Z M^X` on the opposite placement
  have hQZX := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
    _ _ _ S.psiHat _ _ hQXZ (h₂ p₂)
  -- `M^Z M^X ≈ Q_2` on the opposite placement
  have hZXQ : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p₂
        ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab))
      S.psiHat ≤ 2 * η + 2 * (C₁ * Real.sqrt ε) := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    exact _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      _ _ _ S.psiHat _ _ (hQR p₂) (h₁ p₂)
  have hQQ := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
    _ _ _ S.psiHat _ _ hQZX hZXQ
  refine ⟨by linarith, by linarith, by linarith⟩
