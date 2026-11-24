-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:59.055795+00:00
-- url     : https://prove2.me/submissions/71f2519e-4ed2-4e57-871f-726a1491c928

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Alt_sq_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h : Alt c) (L : AddSubgroup W) (hL : L ≤ h.perp L) :
    ∃ A : AddSubgroup W, L ≤ A ∧ A ≤ h.perp A ∧ h.perp A ≤ A := by
  obtain ⟨A, hLA, hA, hmax⟩ := zorn_le_nonempty₀ {A : AddSubgroup W | A ≤ h.perp A} (fun s hs hch y hy => by
    refine ⟨sSup s, fun a ha b hb => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨P, hP, ha⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 ha
    obtain ⟨Q, hQ, hb⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hb
    obtain ⟨R, hR, h1, h2⟩ := hch.directedOn P hP Q hQ
    exact hs hR (h1 ha) b (h2 hb)) L hL
  refine ⟨A, hLA, hA, fun x hx => ?_⟩
  have h1 : AddSubgroup.closure (insert x (A : Set W)) ≤ h.perp (insert x (A : Set W)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro a (rfl | ha) b (rfl | hb)
    · rw [h.self, one_pow]
    · exact hx b hb
    · exact h.sq_swap (hx a ha)
    · exact hA ha b hb
  have h2 : AddSubgroup.closure (insert x (A : Set W)) ≤ h.perp (AddSubgroup.closure (insert x (A : Set W))) :=
    (AddSubgroup.closure_le _).2 fun a ha b hb => h.sq_swap (h1 hb a ha)
  exact hmax h2 (fun a ha => AddSubgroup.subset_closure (Or.inr ha)) (AddSubgroup.subset_closure (Or.inl rfl))
end GlobalTheory.Published.SvN
