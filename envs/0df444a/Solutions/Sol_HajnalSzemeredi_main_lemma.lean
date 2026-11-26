-- Prove2me | solution 1 for HajnalSzemeredi.main_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:52.558682+00:00
-- url     : https://prove2.me/submissions/1aa6a586-763a-4739-8c74-cb21581ddfac

module
public import Definitions.Def_HajnalSzemeredi_Cases
public import Definitions.Def_HajnalSzemeredi_Main
public import Theorems.Thm_HajnalSzemeredi_bminus
public import Theorems.Thm_HajnalSzemeredi_CountHyp_lemma_2_3
public import Theorems.Thm_HajnalSzemeredi_Ctx_countHyp
public import Theorems.Thm_HajnalSzemeredi_Ctx_exists_TU
public import Theorems.Thm_HajnalSzemeredi_Ctx_hi_mem_B
public import Theorems.Thm_HajnalSzemeredi_case1
public import Theorems.Thm_HajnalSzemeredi_case2
public import Theorems.Thm_HajnalSzemeredi_shift_of_acc


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {r s lo : ℕ}
    (IH : ∀ S' ⊆ S, edgeCount G S' < edgeCount G S → ∀ (P' : Finset ℕ) (r' : ℕ),
      P'.card = r' + 1 → S'.card = s * (r' + 1) → DegLe G S' r' → ∃ c, IsEq G S' P' c s)
    (hdeg : DegLe G S r) (hP : P.card = r + 1) :
    ∀ (c : V → ℕ) (hi : ℕ), IsNear G S P c s lo hi → ∃ c', IsEq G S P c' s := by
  intro c hi hc
  induction hk : P.card - (acc G S P c lo).card using Nat.strong_induction_on
    generalizing c hi with
  | _ k ih =>
  by_cases hacc : hi ∈ acc G S P c lo
  · exact shift_of_acc hc (mem_filter.mp hacc).2
  have h : Ctx G S P c r s lo hi := ⟨hc, hdeg, hP, hacc⟩
  obtain ⟨U, hU, hne, hterm, hP2⟩ := h.exists_TU
  have hch := h.countHyp hU hne hP2
  obtain ⟨z, hzS, hzT, ⟨y₀, hy₀⟩, hcase⟩ := hch.lemma_2_3
  -- la coloración `g` de `B \ {y}` por la hipótesis de inducción primaria
  have getg : ∀ y ∈ part S c (P \ acc G S P c lo), ∃ g, IsEq G
      ((part S c (P \ acc G S P c lo)).erase y) (P \ acc G S P c lo) g s := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := bminus h hch hy
    exact IH _ h1 h2 _ _ (Nat.succ_pred_eq_of_pos (card_pos.mpr ⟨hi, h.hi_mem_B⟩)).symm h3 h4
  have memB : ∀ y ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z,
      y ∈ part S c (P \ acc G S P c lo) := fun y hy => (mem_filter.mp hy).1
  by_cases hmov : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X
  · obtain ⟨g, hg⟩ := getg y₀ (memB y₀ hy₀)
    exact case1 h hterm hzS hzT hy₀ hmov hg
  · rcases hcase with hX | ⟨y₁, hy₁, y₂, hy₂, hne12, hnadj⟩
    · exact absurd hX hmov
    · push Not at hmov
      obtain ⟨g, hg⟩ := getg y₁ (memB y₁ hy₁)
      obtain ⟨c', hi', hnear, hlt⟩ :=
        case2 h hterm hzS hzT (fun X hX hXz => hmov X hX hXz) hy₁ hy₂ hne12 hnadj hg
      have hle : (acc G S P c' lo).card ≤ P.card := card_le_card (filter_subset _ _)
      exact ih _ (by omega) c' hi' hnear rfl
end HajnalSzemeredi
