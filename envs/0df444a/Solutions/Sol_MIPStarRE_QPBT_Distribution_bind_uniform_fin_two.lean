-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_uniform_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:09.153897+00:00
-- url     : https://prove2.me/submissions/0db574af-59bb-4dba-8919-5d919473ea31

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_uniform_fin_two.
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

theorem solution {α : Type*} [DecidableEq α]
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α) :
    _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2)) ![μ, ν] =
      _root_.MIPStarRE.QPBT.Distribution.mix (1 / 2) (by norm_num) (by norm_num) μ ν := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset (Fin 2)).biUnion
        (fun i => (![μ, ν] i).support) = μ.support ∪ ν.support
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · funext a
    change (∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2)).weight i * (![μ, ν] i).weight a) =
      1 / 2 * μ.weight a + (1 - 1 / 2) * ν.weight a
    rw [Fin.sum_univ_two, _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply,
      _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply, Fintype.card_fin]
    norm_num
