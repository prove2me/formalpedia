-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.309927+00:00
-- url     : https://prove2.me/submissions/8e32e3d9-cc6e-46b1-a83c-310e067d97a0

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_isProbability.
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
import Definitions.Def_QPBT_QPBT_Upstream

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

theorem solution {α β : Type*} [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : α → _root_.LIDT.MIPStarRE.LDT.Distribution β) (hμ : μ.IsProbability)
    (hν : ∀ a ∈ μ.support, (ν a).IsProbability) :
    (_root_.MIPStarRE.QPBT.Distribution.bind μ ν).IsProbability := by
  classical
  have hν_union (a : α) (ha : a ∈ μ.support) :
      ∑ b ∈ μ.support.biUnion (fun a => (ν a).support), (ν a).weight b = 1 := by
    apply (hν a ha).weight_sum_eq_one_of_subset
    intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability, _root_.LIDT.MIPStarRE.LDT.Distribution.totalWeight,
    _root_.MIPStarRE.QPBT.Distribution.bind]
  rw [Finset.sum_comm]
  calc
    (∑ a ∈ μ.support,
        ∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
          μ.weight a * (ν a).weight b) =
        ∑ a ∈ μ.support,
          μ.weight a *
            ∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
              (ν a).weight b := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.mul_sum _ (fun b => (ν a).weight b) (μ.weight a)).symm
    _ = ∑ a ∈ μ.support, μ.weight a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hν_union a ha]
      simp
    _ = 1 := hμ.weight_sum_eq_one
