-- Prove2me | solution 2 for OAI.Problem313.BlockAverage.capture_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:41:24.517091+00:00
-- url     : https://prove2.me/submissions/09f95d17-8923-48ba-98ac-7d7e7d388f19

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockAverage.lean:L40-L59
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BlockAverage.capture_lower_bound. The node keeps its source
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

/-- Nonnegative block weights give nonnegative incidence probabilities. -/
theorem incidence_sum_nonneg
    {β : Type v} [Fintype β] (μ : β → ℝ) (P : β → Prop)
    [DecidablePred P] (hμ : ∀ b, 0 ≤ μ b) :
    0 ≤ ∑ b, if P b then μ b else 0 := by
  apply Finset.sum_nonneg
  intro b hb
  split_ifs
  · exact hμ b
  · exact le_rfl

/-- A collection of nonnegative masses detected with probability at least `c`
contributes at least `c` times its total mass to the average detected mass. -/
theorem capture_lower_bound
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] (low : Finset α) (c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0) :
    c * ∑ s ∈ low, w s ≤ ∑ b, μ b * ∑ s, if P b s then w s else 0 := by
  rw [weighted_incidence_sum, Finset.mul_sum]
  calc
    ∑ s ∈ low, c * w s ≤
        ∑ s ∈ low, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_right (hcapture s hs) (hw s)
    _ ≤ ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      intro s hs hnot
      exact mul_nonneg (incidence_sum_nonneg μ (fun b => P b s) hμ) (hw s)

end Problem313.BlockAverage

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BlockAverage
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.BlockAverage.capture_lower_bound.{u,v} := @_root_.OAI.Problem313.BlockAverage.capture_lower_bound.{u,v}
