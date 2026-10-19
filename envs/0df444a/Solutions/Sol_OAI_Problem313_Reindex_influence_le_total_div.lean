-- Prove2me | solution 1 for OAI.Problem313.Reindex.influence_le_total_div
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:17:25.217718+00:00
-- url     : https://prove2.me/submissions/37a80db7-66bd-435e-b03b-9ce1c6e1e988

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/InfluenceReindex.lean:L81-L102
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.Reindex.influence_le_total_div. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.InfluenceReindex ----
namespace OAI

universe u v

noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

theorem weight_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem influence_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) : 0 ≤ influence p f i := by
  classical
  unfold influence
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp0 hp1 x
  · exact le_rfl

/-- An orbit of at least `m` equally influential coordinates bounds each influence. -/
theorem influence_le_total_div [Fintype ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) (i : ι)
    (S : Finset ι) {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (heq : ∀ j ∈ S, influence p f j = influence p f i) :
    influence p f i ≤ (∑ j, influence p f j) / m := by
  classical
  have hi := influence_nonneg hp0 hp1 f i
  have hS : (S.card : ℝ) * influence p f i = ∑ j ∈ S, influence p f j := by
    calc
      (S.card : ℝ) * influence p f i = ∑ _j ∈ S, influence p f i := by simp
      _ = ∑ j ∈ S, influence p f j := Finset.sum_congr rfl (fun j hj => (heq j hj).symm)
  have hsum : (∑ j ∈ S, influence p f j) ≤ ∑ j, influence p f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j hj hjS
    exact influence_nonneg hp0 hp1 f j
  apply (le_div_iff₀ hm).2
  calc
    influence p f i * m = m * influence p f i := mul_comm _ _
    _ ≤ (S.card : ℝ) * influence p f i := mul_le_mul_of_nonneg_right hcard hi
    _ = ∑ j ∈ S, influence p f j := hS
    _ ≤ ∑ j, influence p f j := hsum

end Reindex
end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.Reindex


theorem solution.{u} : type_of% @_root_.OAI.Problem313.Reindex.influence_le_total_div.{u} := @_root_.OAI.Problem313.Reindex.influence_le_total_div.{u}
