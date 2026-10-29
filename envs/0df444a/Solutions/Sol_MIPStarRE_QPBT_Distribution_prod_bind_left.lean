-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_bind_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:08.800592+00:00
-- url     : https://prove2.me/submissions/9ddb44bb-002a-4b10-9e56-0dbb4fbcad77

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_bind_left.
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







/-! ## Associativity of dependent mixtures -/



/-! ## Products with an independent factor -/

theorem solution {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : α → _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (ρ : _root_.LIDT.MIPStarRE.LDT.Distribution γ) :
    _root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.Distribution.bind μ ν) ρ =
      _root_.MIPStarRE.QPBT.Distribution.bind μ (fun a => _root_.MIPStarRE.QPBT.Distribution.prod (ν a) ρ) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.biUnion (fun a => (ν a).support)) ×ˢ ρ.support =
      μ.support.biUnion (fun a => (ν a).support ×ˢ ρ.support)
    ext w
    simp only [Finset.mem_product, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨a, ha, hb⟩, hc⟩
      exact ⟨a, ha, hb, hc⟩
    · rintro ⟨a, ha, hb, hc⟩
      exact ⟨⟨a, ha, hb⟩, hc⟩
  · funext w
    change (∑ a ∈ μ.support, μ.weight a * (ν a).weight w.1) * ρ.weight w.2 =
      ∑ a ∈ μ.support, μ.weight a * ((ν a).weight w.1 * ρ.weight w.2)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _
