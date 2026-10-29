-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.406038+00:00
-- url     : https://prove2.me/submissions/7e31e666-1c34-4eab-bfc9-0ac2556f6d47

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_map_left.
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

theorem solution {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (f : α → β) (ν : β → _root_.LIDT.MIPStarRE.LDT.Distribution γ) :
    _root_.MIPStarRE.QPBT.Distribution.bind (μ.map f) ν =
      _root_.MIPStarRE.QPBT.Distribution.bind μ (fun a => ν (f a)) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.image f).biUnion (fun b => (ν b).support) =
      μ.support.biUnion (fun a => (ν (f a)).support)
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨b, ⟨a, ha, rfl⟩, hc⟩
      exact ⟨a, ha, hc⟩
    · rintro ⟨a, ha, hc⟩
      exact ⟨f a, ⟨a, ha, rfl⟩, hc⟩
  · funext c
    change (∑ b ∈ μ.support.image f, (μ.map f).weight b * (ν b).weight c) =
      ∑ a ∈ μ.support, μ.weight a * (ν (f a)).weight c
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := μ.support) (t := μ.support.image f) (g := f)
      (fun a ha => Finset.mem_image_of_mem f ha)
      (fun a => μ.weight a * (ν (f a)).weight c)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_weight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
