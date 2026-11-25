-- Prove2me | solution 1 for GlobalTheory.Kempf.exists_mem_map_toInter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:17.824929+00:00
-- url     : https://prove2.me/submissions/e91b99b2-49c1-472c-91ca-a982fa646134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_shortExact_map_interSheaf
import Theorems.Thm_GlobalTheory_Kempf_exists_isBasis_lift
import Theorems.Thm_P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
import Theorems.Thm_GlobalTheory_SheafLES_sections_surjective_of_subsingleton
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
import Theorems.Thm_P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES
namespace GlobalTheory.Kempf
theorem _root_.solution {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (V : Opens X) (n : ℕ)
    (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ q, 0 < q → q < n + 1 → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F (n + 1) V) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧
      map.{w} ((toInter AddCommGrpCat.{u} W).app F) (n + 1) V α = 0 := by
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    obtain ⟨β, rfl⟩ := δ_surjective_of_subsingleton.{w} hS 0 V
      (Flasque.subsingleton_H'_of_isFlasque _ 0 V) α
    obtain ⟨s, rfl⟩ := (equivZero _ V).symm.surjective β
    obtain ⟨W, hW, hxW, hWV, t, ht⟩ := exists_isBasis_lift hS h𝔅 s hx
    exact ⟨W, hW, hxW, hWV, map_toInter_δ_eq_zero hS s t ht⟩
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    obtain ⟨β, rfl⟩ := δ_surjective_of_subsingleton.{w} hS (n + 1) V
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) V) α
    obtain ⟨W, hW, hxW, hWV, hβ⟩ := ih (Flasque.injectiveShortComplex F).X₃
      (fun q hq hqn B hB ↦ subsingleton₃.{w} hS q B
        (Flasque.subsingleton_H'_of_isFlasque_of_pos _ hq B)
        (hF (q + 1) q.succ_pos (by omega) B hB)) β
    have hT := shortExact_map_interSheaf hS h𝔅 hinf
      (fun B hB ↦ sections_surjective_of_subsingleton.{w} hS B (hF 1 one_pos (by omega) B hB)) hW
    refine ⟨W, hW, hxW, hWV, ?_⟩
    refine (δ_naturality hS hT
      ((Flasque.injectiveShortComplex F).mapNatTrans (toInter AddCommGrpCat.{u} W))
      (n + 1) V β).trans ?_
    exact (congrArg (δ hT (n + 1) V) hβ).trans (map_zero _)
end GlobalTheory.Kempf
