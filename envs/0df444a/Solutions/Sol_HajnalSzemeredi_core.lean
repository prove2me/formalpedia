-- Prove2me | solution 1 for HajnalSzemeredi.core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:27.446282+00:00
-- url     : https://prove2.me/submissions/7b887494-1c45-431c-ba38-28e3bd361198

module
public import Definitions.Def_HajnalSzemeredi_Cases
public import Definitions.Def_HajnalSzemeredi_Main
public import Theorems.Thm_HajnalSzemeredi_main_lemma
public import Theorems.Thm_HajnalSzemeredi_exists_equipartition
public import Theorems.Thm_HajnalSzemeredi_card_cls_update_old
public import Theorems.Thm_HajnalSzemeredi_card_cls_update_self
public import Theorems.Thm_HajnalSzemeredi_cls_update_other
public import Theorems.Thm_HajnalSzemeredi_into_update
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
public import Theorems.Thm_HajnalSzemeredi_proper_update
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution (n : ℕ) : ∀ (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (r s : ℕ),
    edgeCount G S = n → P.card = r + 1 → S.card = s * (r + 1) → DegLe G S r →
    ∃ c, IsEq G S P c s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G S P r s hn hP hS hdeg
  by_cases h0 : n = 0
  · -- sin aristas: cualquier equipartición sirve
    obtain ⟨c, hc, hcard⟩ := exists_equipartition P s S (by rw [hS, hP])
    refine ⟨c, fun v hv w hw hadj => ?_, hc, hcard⟩
    exfalso
    have : (v, w) ∈ S.offDiag.filter fun p => G.Adj p.1 p.2 :=
      mem_filter.mpr ⟨mem_offDiag.mpr ⟨hv, hw, hadj.ne⟩, hadj⟩
    rw [edgeCount, h0] at hn
    rw [card_eq_zero.mp hn] at this
    exact notMem_empty _ this
  -- hay una arista `xy`
  obtain ⟨⟨x, y⟩, hxy⟩ : (S.offDiag.filter fun p => G.Adj p.1 p.2).Nonempty := by
    rw [← card_pos]; unfold edgeCount at hn; omega
  obtain ⟨hxyS, hadj⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy, -⟩ := mem_offDiag.mp hxyS
  obtain ⟨G', hG'⟩ : ∃ G' : SimpleGraph V, ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ s(x, y) :=
    ⟨{ Adj := fun a b => G.Adj a b ∧ s(a, b) ≠ s(x, y)
       symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
       loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }, fun _ _ => Iff.rfl⟩
  have hG'le : ∀ a b, G'.Adj a b → G.Adj a b := fun a b h => ((hG' a b).mp h).1
  have hG'adj : ∀ a b, G.Adj a b → s(a, b) ≠ s(x, y) → G'.Adj a b :=
    fun a b hab hne => (hG' a b).mpr ⟨hab, hne⟩
  -- menos aristas en `G'`
  have hlt : edgeCount G' S < edgeCount G S := by
    apply card_lt_card
    refine ⟨fun p hp => ?_, fun hsub => ?_⟩
    · obtain ⟨hp, hpadj⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hp, hG'le _ _ hpadj⟩
    · have := (mem_filter.mp (hsub hxy)).2
      exact ((hG' x y).mp this).2 rfl
  have hdeg' : DegLe G' S r := fun v hv =>
    le_trans (card_le_card fun w hw =>
      mem_nbr.mpr ⟨(mem_nbr.mp hw).1, hG'le _ _ (mem_nbr.mp hw).2⟩) (hdeg v hv)
  obtain ⟨f₀, hf₀⟩ := ih _ (hn ▸ hlt) G' S P r s rfl hP hS hdeg'
  -- hipótesis de inducción para subconjuntos (mismo grafo `G`)
  have IH : ∀ S' ⊆ S, edgeCount G S' < edgeCount G S → ∀ (P' : Finset ℕ) (r' : ℕ),
      P'.card = r' + 1 → S'.card = s * (r' + 1) → DegLe G S' r' → ∃ c, IsEq G S' P' c s :=
    fun S' _ hS' P' r' hP' hcard hdeg'' => ih _ (hn ▸ hS') G S' P' r' s rfl hP' hcard hdeg''
  by_cases hcol : f₀ x = f₀ y
  · -- `x` e `y` en la misma clase: mover `x` a una clase sin vecinos de `x`
    -- vecinos de `x` en colores distintos de `f₀ x`: a lo más `r - 1`
    set N := (nbr G S x).filter fun w => f₀ w ≠ f₀ x
    have hN : N.card + 1 ≤ r := by
      have hsub : insert y N ⊆ nbr G S x := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact mem_nbr.mpr ⟨hy, hadj⟩
        · exact (mem_filter.mp hw).1
      have hyN : y ∉ N := fun h => (mem_filter.mp h).2 hcol.symm
      have := card_le_card hsub
      rw [card_insert_of_notMem hyN] at this
      exact le_trans this (hdeg x hx)
    have hfree : ∃ j ∈ P.erase (f₀ x), ∀ w ∈ N, f₀ w ≠ j := by
      by_contra hno
      push Not at hno
      have hsub : P.erase (f₀ x) ⊆ N.image f₀ := by
        intro j hj
        obtain ⟨w, hw, hwj⟩ := hno j hj
        exact mem_image.mpr ⟨w, hw, hwj⟩
      have h1 := le_trans (card_le_card hsub) card_image_le
      rw [card_erase_of_mem (hf₀.into x hx), hP] at h1
      omega
    obtain ⟨j, hjP, hjfree⟩ := hfree
    obtain ⟨hjx, hjP⟩ := mem_erase.mp hjP
    have hmov : Movable G S f₀ x j := by
      intro w hw hxw
      rw [mem_cls] at hw
      exact hjfree w (mem_filter.mpr ⟨mem_nbr.mpr ⟨hw.1, hxw⟩, hw.2 ▸ hjx⟩) hw.2
    have hcx : f₀ x ≠ j := Ne.symm hjx
    have hproper : Proper G S (Function.update f₀ x j) := by
      have hp' : Proper G' S (Function.update f₀ x j) :=
        proper_update hf₀.proper fun w hw hxw => hmov w hw (hG'le _ _ hxw)
      intro a ha b hb hab
      by_cases he : s(a, b) = s(x, y)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hab' : a ≠ b := hab.ne
          simp only [Function.update_self, Function.update_of_ne hab'.symm]
          rw [← hcol]; exact Ne.symm hcx
        · have hab' : a ≠ b := hab.ne
          simp only [Function.update_self, Function.update_of_ne hab']
          rw [← hcol]; exact hcx
      · exact hp' a ha b hb (hG'adj a b hab he)
    have hs1 : (cls S f₀ (f₀ x)).card = s := hf₀.card _ (hf₀.into x hx)
    have hnear : IsNear G S P (Function.update f₀ x j) s (f₀ x) j := by
      refine ⟨hproper, into_update hf₀.into hjP, hf₀.into x hx, hjP, hcx, ?_, ?_, ?_⟩
      · have h1 : (cls S (Function.update f₀ x j) (f₀ x)).card + 1 = (cls S f₀ (f₀ x)).card :=
          card_cls_update_old hx hcx
        omega
      · rw [card_cls_update_self hx hcx, hf₀.card j hjP]
      · intro i hi hix hij
        rw [cls_update_other hij hix, hf₀.card i hi]
    exact main_lemma IH hdeg hP _ j hnear
  · -- `f₀` ya es propia para `G`
    refine ⟨f₀, fun a ha b hb hab => ?_, hf₀.into, hf₀.card⟩
    by_cases he : s(a, b) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcol
      · exact Ne.symm hcol
    · exact hf₀.proper a ha b hb (hG'adj a b hab he)
end HajnalSzemeredi
