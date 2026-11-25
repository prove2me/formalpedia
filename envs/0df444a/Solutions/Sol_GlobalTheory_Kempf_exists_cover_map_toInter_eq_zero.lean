-- Prove2me | solution 1 for GlobalTheory.Kempf.exists_cover_map_toInter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:15.020431+00:00
-- url     : https://prove2.me/submissions/0d469789-174e-48c7-ae28-c5202bd4a9ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_exists_mem_map_toInter_eq_zero

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
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (F : X.Sheaf AddCommGrpCat.{u}) (V : Opens X)
    {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ q, 0 < q → q < n → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F n V) :
    ∃ 𝔘 ⊆ 𝔅, sSup 𝔘 = V ∧
      ∀ W ∈ 𝔘, map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine ⟨{W | W ∈ 𝔅 ∧ W ≤ V ∧ map.{w} ((toInter AddCommGrpCat.{u} W).app F) (n + 1) V α = 0},
    fun _ h ↦ h.1, le_antisymm (sSup_le fun _ h ↦ h.2.1) fun x hx ↦ ?_, fun _ h ↦ h.2.2⟩
  obtain ⟨W, hW, hxW, hWV, h⟩ := exists_mem_map_toInter_eq_zero h𝔅 hinf V n F hF α hx
  exact Opens.mem_sSup.2 ⟨W, ⟨hW, hWV, h⟩, hxW⟩
end GlobalTheory.Kempf
