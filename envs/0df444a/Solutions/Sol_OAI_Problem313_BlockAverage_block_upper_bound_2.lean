-- Prove2me | solution 2 for OAI.Problem313.BlockAverage.block_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:42:49.444643+00:00
-- url     : https://prove2.me/submissions/ba05d4b8-e4bf-4dd0-9d85-f75ecb09b0db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockAverage.lean:L61-L91
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BlockAverage.block_upper_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative

-- ---- from OAI.Combinatorics.SharpThreshold.BlockAverage ----
namespace OAI

universe u v w

noncomputable section

namespace Problem313.BlockAverage

open scoped BigOperators

/-- Exchange the average over blocks with a sum over objects detected by a block. -/
theorem weighted_incidence_sum
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) =
      ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : P b s <;> simp [h]

/-- Pointwise block bounds average to a global bound using the incidence
probability of each coordinate. No normalization assumption is required. -/
theorem block_upper_bound
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (a d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤ a * d * ∑ i, I i := by
  calc
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤
        ∑ b, μ b * (a * ∑ i, if E b i then I i else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hblock b) (hμ b)
    _ = a * ∑ b, μ b * ∑ i, if E b i then I i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = a * ∑ i, (∑ b, if E b i then μ b else 0) * I i := by
      rw [weighted_incidence_sum]
    _ ≤ a * ∑ i, d * I i := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hincidence i) (hI i)
    _ = a * d * ∑ i, I i := by rw [← Finset.mul_sum]; ring

end Problem313.BlockAverage

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BlockAverage
open scoped BigOperators


theorem solution.{u,v,w} : type_of% @_root_.OAI.Problem313.BlockAverage.block_upper_bound.{u,v,w} := @_root_.OAI.Problem313.BlockAverage.block_upper_bound.{u,v,w}
