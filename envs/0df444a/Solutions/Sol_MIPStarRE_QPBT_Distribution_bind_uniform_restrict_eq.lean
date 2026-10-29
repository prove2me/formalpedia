-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.bind_uniform_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.420349+00:00
-- url     : https://prove2.me/submissions/25dbd15c-6d36-4f3d-a4ce-2300550406c0

-- Generated proof for MIPStarRE.QPBT.Distribution.bind_uniform_restrict_eq.
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

theorem solution {α ι : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (p : ι → α → Prop) [∀ i, DecidablePred (p i)]
    (hpos : ∀ i, 0 < ∑ a ∈ μ.support.filter (p i), μ.weight a)
    (hmass : ∀ i, ∑ a ∈ μ.support.filter (p i), μ.weight a =
      1 / (Fintype.card ι : ℝ))
    (hunique : ∀ a, ∃! i, p i a) :
    _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι)
        (fun i => _root_.MIPStarRE.QPBT.Distribution.restrict μ (p i) (hpos i)) = μ := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset ι).biUnion
      (fun i => μ.support.filter (p i)) = μ.support
    ext a
    constructor
    · intro ha
      obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp hai).1
    · intro ha
      obtain ⟨i, hi, -⟩ := hunique a
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  · funext a
    change (∑ i ∈ (Finset.univ : Finset ι), (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι).weight i *
      (_root_.MIPStarRE.QPBT.Distribution.restrict μ (p i) (hpos i)).weight a) = μ.weight a
    have hterm : ∀ i : ι, (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι).weight i *
        (_root_.MIPStarRE.QPBT.Distribution.restrict μ (p i) (hpos i)).weight a =
        if p i a then μ.weight a else 0 := by
      intro i
      rw [_root_.MIPStarRE.QPBT.uniformDistribution_weight_apply]
      by_cases h : p i a
      · have hw : (_root_.MIPStarRE.QPBT.Distribution.restrict μ (p i) (hpos i)).weight a =
            μ.weight a / (1 / (Fintype.card ι : ℝ)) := by
          simp only [_root_.MIPStarRE.QPBT.Distribution.restrict, if_pos h, hmass i]
        rw [hw, if_pos h]
        field_simp
      · have hw : (_root_.MIPStarRE.QPBT.Distribution.restrict μ (p i) (hpos i)).weight a = 0 := by
          simp only [_root_.MIPStarRE.QPBT.Distribution.restrict, if_neg h]
        rw [hw, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    obtain ⟨i₀, hi₀, huniq⟩ := hunique a
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos hi₀]
    · intro i _ hne
      exact if_neg fun hi => hne (huniq i hi)
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem
