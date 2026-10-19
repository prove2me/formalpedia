-- Prove2me | solution 1 for OAI.MatchingSmoothing.card_colorings_mul_factorials
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:54:12.501978+00:00
-- url     : https://prove2.me/submissions/14f0433d-cfc2-43c8-b289-9a1fd8002ec4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean:L67-L85
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.card_colorings_mul_factorials. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts

-- ---- from OAI.Combinatorics.MatchingPSD.ColoringCounts ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

lemma card_colorings_mul_factorials [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) *
      (∏ b, (histogram f b).factorial) = (Fintype.card α).factorial := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  have hf (g : Colorings α β (histogram f)) :
      Fintype.card {σ // F σ = g} = ∏ b, (histogram f b).factorial := by
    let e₁ : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
      Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
    rw [Fintype.card_congr e₁, Fintype.card_congr (fiberPermEquiv f g.1),
      Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
    exact congrArg Nat.factorial (congrFun g.2 b)
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Fintype.card_sigma, Fintype.card_perm] at he
  simpa only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] using he

variable {H : Type u_5} [Fintype H] [DecidableEq H]

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.card_colorings_mul_factorials := @_root_.OAI.MatchingSmoothing.card_colorings_mul_factorials
