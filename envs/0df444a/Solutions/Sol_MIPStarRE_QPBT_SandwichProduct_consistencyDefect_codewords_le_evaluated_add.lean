-- Prove2me | solution 1 for MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:56:25.467979+00:00
-- url     : https://prove2.me/submissions/a8c5d2a6-87df-4b36-a820-0820f7d2690d

-- Generated proof for MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add.
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_placed_eq_avg_point
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_point_codeword_defect_le_avg_evaluated_add

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.QPBT.SandwichProduct

set_option maxHeartbeats 600000 in
-- The proof rearranges question, evaluation, and two outcome sums.

theorem solution
    {X Y Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (eval : Γ → Y → R) (ε : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x g => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect g) 1)
        (fun x g => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect g)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod μ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y))
        (fun xy r => _root_.MIPStarRE.QPBT.heteroKron
          (((A xy.1).postprocess (fun g => eval g xy.2)).effect r) 1)
        (fun xy r => _root_.MIPStarRE.QPBT.heteroKron 1
          (((B xy.1).postprocess (fun g => eval g xy.2)).effect r)) ψ + ε := by
  classical
  let w : X → Γ → Γ → ℝ := fun x g g' =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect g) ((B x).effect g'))
  have hpoint (x : X) :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
          ∑ r : R, ∑ r' : R, if r = r' then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (_root_.MIPStarRE.QPBT.heteroKron
                (((A x).postprocess (fun g => eval g y)).effect r)
                (((B x).postprocess (fun g => eval g y)).effect r'))) + ε := by
    exact _root_.MIPStarRE.QPBT.SandwichProduct.point_codeword_defect_le_avg_evaluated_add
      (A x) (B x) ψ eval ε hψ hε hcollision
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point μ A B]
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point
    (_root_.MIPStarRE.QPBT.Distribution.prod μ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y))
    (fun xy => (A xy.1).postprocess (fun g => eval g xy.2))
    (fun xy => (B xy.1).postprocess (fun g => eval g xy.2))]
  change _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
      ∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤ _
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                (_root_.MIPStarRE.QPBT.heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r'))) + ε) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      exact hpoint
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                (_root_.MIPStarRE.QPBT.heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r')))) +
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun _ => ε) := _root_.LIDT.MIPStarRE.LDT.avgOver_add _ _ _
    _ = _ := by rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ]
