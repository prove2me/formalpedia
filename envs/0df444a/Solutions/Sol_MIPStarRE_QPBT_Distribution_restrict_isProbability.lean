-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.restrict_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.698528+00:00
-- url     : https://prove2.me/submissions/00013dd6-b6dc-456e-b593-122ea956d87f

-- Generated proof for MIPStarRE.QPBT.Distribution.restrict_isProbability.
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

theorem solution {α : Type*} [DecidableEq α]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) :
    (_root_.MIPStarRE.QPBT.Distribution.restrict μ p hpos).IsProbability := by
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability, _root_.LIDT.MIPStarRE.LDT.Distribution.totalWeight,
    _root_.MIPStarRE.QPBT.Distribution.restrict]
  calc
    (∑ a ∈ μ.support.filter p,
        if p a then μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b else 0) =
        ∑ a ∈ μ.support.filter p,
          μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_pos (Finset.mem_filter.mp ha).2]
    _ = (∑ a ∈ μ.support.filter p, μ.weight a) /
        ∑ b ∈ μ.support.filter p, μ.weight b := by
      rw [Finset.sum_div]
    _ = 1 := div_self hpos.ne'
