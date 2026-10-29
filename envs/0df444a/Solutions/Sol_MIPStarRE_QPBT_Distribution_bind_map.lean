-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_map
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.510406+00:00
-- url     : https://prove2.me/submissions/138e8da9-e84d-43f5-99d6-6ee4cfb4302b

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_map.
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

theorem solution {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : α → _root_.LIDT.MIPStarRE.LDT.Distribution β) (f : β → γ) :
    (_root_.MIPStarRE.QPBT.Distribution.bind μ ν).map f =
      _root_.MIPStarRE.QPBT.Distribution.bind μ (fun a => (ν a).map f) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.biUnion fun a => (ν a).support).image f =
      μ.support.biUnion fun a => (ν a).support.image f
    ext c
    constructor
    · intro hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨a, ha, hb'⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem f hb'⟩
    · intro hc
      obtain ⟨a, ha, hc'⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc'
      exact Finset.mem_image.mpr ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩, rfl⟩
  · funext c
    change (∑ b ∈ (μ.support.biUnion fun a => (ν a).support).filter
          (fun b => f b = c),
        ∑ a ∈ μ.support, μ.weight a * (ν a).weight b) =
      ∑ a ∈ μ.support, μ.weight a *
        ∑ b ∈ (ν a).support.filter (fun b => f b = c), (ν a).weight b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨a, ha, hb1⟩, hb2⟩
    · intro b hb hbnot
      have hfb : f b = c := (Finset.mem_filter.mp hb).2
      have hnot : b ∉ (ν a).support := fun hmem =>
        hbnot (Finset.mem_filter.mpr ⟨hmem, hfb⟩)
      rw [(ν a).outsideSupport b hnot, mul_zero]
