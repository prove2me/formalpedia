-- Prove2me | solution 1 for OAI.Problem313.BlockAverage.block_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:27.738452+00:00
-- url     : https://prove2.me/submissions/b78bc1cb-7646-4497-996c-c119ea0e6d62

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
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (a d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤ a * d * ∑ i, I i := by
  calc (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤ ∑ b, μ b * (a * ∑ i, if E b i then I i else 0) :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hblock b) (hμ b))
    _ = a * ∑ i, I i * ∑ b, if E b i then μ b else 0 := by
      simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
    _ ≤ a * ∑ i, I i * d := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hincidence i) (hI i))) ha
    _ = a * d * ∑ i, I i := by rw [← Finset.sum_mul]; ring

