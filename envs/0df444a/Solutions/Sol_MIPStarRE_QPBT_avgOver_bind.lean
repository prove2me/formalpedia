-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_bind
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:09.032622+00:00
-- url     : https://prove2.me/submissions/b24bcf1c-5c77-4155-8f73-c16e9dca821a

-- Generated proof for MIPStarRE.QPBT.avgOver_bind.
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



/-! ## The equal two-term mixture as a uniform dependent mixture -/



/-! ## Averages of the distribution operations -/

theorem solution {α β : Type*} [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : α → _root_.LIDT.MIPStarRE.LDT.Distribution β) (f : β → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.bind μ ν) f =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun a => _root_.LIDT.MIPStarRE.LDT.avgOver (ν a) f) := by
  classical
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver
  have h1 : ∀ b : β, (∑ a ∈ μ.support, μ.weight a * (ν a).weight b) * f b =
      ∑ a ∈ μ.support, μ.weight a * ((ν a).weight b * f b) := by
    intro b
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  change (∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
    (∑ a ∈ μ.support, μ.weight a * (ν a).weight b) * f b) = _
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_sum]
  congr 1
  refine (Finset.sum_subset ?_ ?_).symm
  · intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
  · intro b _ hb
    rw [(ν a).outsideSupport b hb, zero_mul]
