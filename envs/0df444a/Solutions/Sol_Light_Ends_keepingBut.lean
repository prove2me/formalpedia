-- Prove2me | solution 1 for Light.Ends.keepingBut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:27:23.658623+00:00
-- url     : https://prove2.me/submissions/ad24c152-3eb8-446d-b68a-ea5646ed9cf6

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Theorems.Thm_Light_Ends_keeping
public import Theorems.Thm_Light_Ends_mono
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (xs : List ℕ) (hxs : s.assigns ⊆ xs := by simp) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ xs, σ'.loc y = σ.loc y :=
  h.keeping.mono le_rfl fun _ hq => ⟨hq.1, fun y hy => hq.2 y fun hmem => hy (hxs hmem)⟩
end Ends
end Light
