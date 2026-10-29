-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:13:59.553675+00:00
-- url     : https://prove2.me/submissions/606f4ddf-5642-4953-9b6d-6770f2956e7e

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_isProbability.
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Operations on finite distributions

Finite distributions support products, convex mixtures, dependent binds,
normalized restrictions, and push-forwards.  Uniform laws are preserved by
bijections and balanced maps, their product projections are uniform, and
dependent uniform sampling agrees with push-forward from a product.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution {α β : Type*}
    [DecidableEq α] [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).IsProbability := by
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability, _root_.LIDT.MIPStarRE.LDT.Distribution.totalWeight,
    _root_.MIPStarRE.QPBT.Distribution.prod]
  calc
    (∑ p ∈ μ.support.product ν.support, μ.weight p.1 * ν.weight p.2) =
        ∑ a ∈ μ.support, ∑ b ∈ ν.support, μ.weight a * ν.weight b := by
      exact Finset.sum_product' μ.support ν.support
        (fun a b => μ.weight a * ν.weight b)
    _ =
        ∑ a ∈ μ.support, μ.weight a * ∑ b ∈ ν.support, ν.weight b := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.mul_sum ν.support (fun b => ν.weight b) (μ.weight a)).symm
    _ = ∑ a ∈ μ.support, μ.weight a := by
      rw [hν.weight_sum_eq_one]
      simp
    _ = 1 := hμ.weight_sum_eq_one
