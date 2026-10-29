-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_const
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.45734+00:00
-- url     : https://prove2.me/submissions/3442cc25-98aa-40fe-af8e-63d15a3102b7

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_const.
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

















/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/





















/-! ## Elementary rewriting of finite distributions -/







/-! ## Reindexing a dependent mixture -/

theorem solution {α β : Type*} [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (hμ : μ.IsProbability) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β) :
    _root_.MIPStarRE.QPBT.Distribution.bind μ (fun _ => ν) = ν := by
  have hne : μ.support.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcard
    have hempty : μ.support = ∅ := by
      rw [← Finset.card_eq_zero]
      omega
    have h1 := hμ.weight_sum_eq_one
    rw [hempty] at h1
    simp at h1
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun _ => ν.support) = ν.support
    ext b
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨a, -, hb⟩
      exact hb
    · intro hb
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, hb⟩
  · funext b
    change (∑ a ∈ μ.support, μ.weight a * ν.weight b) = ν.weight b
    rw [← Finset.sum_mul, hμ.weight_sum_eq_one, one_mul]
