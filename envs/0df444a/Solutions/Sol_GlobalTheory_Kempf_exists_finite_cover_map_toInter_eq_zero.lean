-- Prove2me | solution 1 for GlobalTheory.Kempf.exists_finite_cover_map_toInter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:31.190397+00:00
-- url     : https://prove2.me/submissions/40997920-117a-4abf-bcc6-9ab0eb71d8d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_exists_cover_map_toInter_eq_zero

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
    (hV : IsCompact (V : Set X)) {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ q, 0 < q → q < n → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F n V) :
    ∃ 𝔘 ⊆ 𝔅, 𝔘.Finite ∧ sSup 𝔘 = V ∧
      ∀ W ∈ 𝔘, map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0 := by
  obtain ⟨𝔘, h𝔘, hsup, h0⟩ := exists_cover_map_toInter_eq_zero h𝔅 hinf F V hn hF α
  obtain ⟨𝔙, h𝔙, hfin, hcov⟩ := hV.elim_finite_subcover_image (b := 𝔘)
    (c := fun W : Opens X ↦ (W : Set X)) (fun W _ ↦ W.isOpen) fun x hx ↦ by
      obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.1 (hsup.ge hx)
      exact Set.mem_biUnion hW hxW
  refine ⟨𝔙, h𝔙.trans h𝔘, hfin, le_antisymm ((sSup_le_sSup h𝔙).trans hsup.le) fun x hx ↦ ?_,
    fun W hW ↦ h0 W (h𝔙 hW)⟩
  obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hcov hx)
  exact Opens.mem_sSup.2 ⟨W, hW, hxW⟩
end GlobalTheory.Kempf
