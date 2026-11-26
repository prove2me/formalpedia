-- Prove2me | solution 1 for HajnalSzemeredi.mem_palette_of_reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:44.354122+00:00
-- url     : https://prove2.me/submissions/50ffca00-0f5f-4730-b9e5-1f8cde9b568f

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Definitions.Def_HajnalSzemeredi_Reach
public import Definitions.Def_HajnalSzemeredi_Shift
public import Theorems.Thm_HajnalSzemeredi_mem_cls
attribute [local simp] HajnalSzemeredi.mem_cls



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {c : V → ℕ} (hc : Into S c P)
    {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → Mov G S c a b) {j lo : ℕ}
    (h : ReflTransGen R j lo) (hj : j ≠ lo) : j ∈ P := by
  rcases h.cases_head with h | ⟨k, hjk, -⟩
  · exact absurd h hj
  · obtain ⟨v, hv, -⟩ := hR _ _ hjk
    rw [mem_cls] at hv
    exact hv.2 ▸ hc v hv.1
end HajnalSzemeredi
