-- Prove2me | solution 1 for OAI.Problem313.BlockAverage.capture_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:19.788626+00:00
-- url     : https://prove2.me/submissions/ab571261-5012-4c3a-861d-bd2b3a9daaf8

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

open OAI OAI.Problem313
universe u v w
open scoped BigOperators


theorem solution
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] (low : Finset α) (c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0) :
    c * ∑ s ∈ low, w s ≤ ∑ b, μ b * ∑ s, if P b s then w s else 0 := by
  have h1 : (∑ b, μ b * ∑ s, if P b s then w s else 0) = ∑ s, w s * ∑ b, if P b s then μ b else 0 := by
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
  rw [h1, Finset.mul_sum]
  calc ∑ s ∈ low, c * w s ≤ ∑ s ∈ low, w s * ∑ b, if P b s then μ b else 0 :=
        Finset.sum_le_sum (fun s hs => by nlinarith [hcapture s hs, hw s])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => mul_nonneg (hw s) (Finset.sum_nonneg (fun b _ => by split_ifs <;> simp [hμ b])))

