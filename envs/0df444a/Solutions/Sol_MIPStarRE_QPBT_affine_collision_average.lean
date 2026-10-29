-- Prove2me | solution 1 for MIPStarRE.QPBT.affine_collision_average
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.453526+00:00
-- url     : https://prove2.me/submissions/e50f5e43-dcd0-4cf7-aa2b-fde3aaccfb72

-- Generated proof for MIPStarRE.QPBT.affine_collision_average.
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
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

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

private theorem avgOver_uniform_eq_indicator {K : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K] (x : K) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun y => if y = x then (1 : ℝ) else 0) =
      (Fintype.card K : ℝ)⁻¹ := by
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
  simp

















end

end MIPStarRE.QPBT

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

theorem solution {K : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    (p p' : K × K) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
      if coefficients.1 * p.1 + coefficients.2 * p.2 =
          coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  classical
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (K × K)) (fun coefficients =>
        if coefficients.1 * p.1 + coefficients.2 * p.2 =
            coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun alpha =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
            if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
              (1 : ℝ) else 0)) := by
                simpa only using
                  (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := K) (β := K) (fun alpha beta =>
                    if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                      (1 : ℝ) else 0))
    _ = if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
      by_cases hp : p = p'
      · subst p'
        simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
      · rw [if_neg hp]
        by_cases hfirst : p.1 = p'.1
        · have hsecond : p.2 ≠ p'.2 := by
            intro h
            exact hp (Prod.ext hfirst h)
          have hdiff : p.2 - p'.2 ≠ 0 := sub_ne_zero.mpr hsecond
          calc
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun alpha =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
              if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                (1 : ℝ) else 0)) =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun _ =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
                if beta = 0 then (1 : ℝ) else 0)) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro alpha
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro beta
              congr 1
              apply propext
              constructor
              · intro h
                rw [hfirst] at h
                have : beta * (p.2 - p'.2) = 0 := by
                  linear_combination h
                exact (mul_eq_zero.mp this).resolve_right hdiff
              · intro h
                subst beta
                simp [hfirst]
            _ = _ := by rw [avgOver_uniform_eq_indicator, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
        · have hdiff : p.1 - p'.1 ≠ 0 := sub_ne_zero.mpr hfirst
          calc
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun alpha =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
              if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                (1 : ℝ) else 0)) =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun alpha =>
                if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                  (1 : ℝ) else 0)) := by
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_comm]
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro beta
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro alpha
              congr 1
              apply propext
              exact calc
                alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 ↔
                    alpha * (p.1 - p'.1) = beta * (p'.2 - p.2) := by
                      constructor <;> intro h <;> linear_combination h
                _ ↔ alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) :=
                  (eq_div_iff hdiff).symm
            _ = _ := by
              calc
                _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun beta =>
                    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun alpha =>
                      if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                        (1 : ℝ) else 0)) =
                    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K)
                      (fun _ => (Fintype.card K : ℝ)⁻¹) := by
                        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                        intro beta
                        exact avgOver_uniform_eq_indicator _
                _ = _ := _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _
