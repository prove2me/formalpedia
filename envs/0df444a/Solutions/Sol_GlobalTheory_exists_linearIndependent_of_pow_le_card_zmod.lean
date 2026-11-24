-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_of_pow_le_card_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:51.351301+00:00
-- url     : https://prove2.me/submissions/782f6175-3e8f-4037-a775-d44a3d8e1969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hs : (Z.image w).card = Z.card := Finset.card_image_of_injOn hinj
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)
  have hbfin : b.Finite := (Finset.finite_toSet _).subset hbs
  haveI : Fintype b := hbfin.fintype
  have hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y := by
    intro y hy
    have hy' : y ∈ Submodule.span (ZMod l) b := by
      rw [hspan]; exact Submodule.subset_span (by exact_mod_cast hy)
    rw [← Subtype.range_coe (s := b)] at hy'
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'
  have hle : (Z.image w).card ≤ l ^ Fintype.card b := by
    have h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨f, hf⟩ := hrange y hy
      exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩
    calc _ ≤ _ := h3
      _ ≤ (Finset.univ : Finset (b → ZMod l)).card := Finset.card_image_le
      _ = l ^ Fintype.card b := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have hhb : h ≤ Fintype.card b := by
    have : l ^ h ≤ l ^ Fintype.card b := hcard.trans (hs ▸ hle)
    exact (Nat.pow_le_pow_iff_right hl1).1 this
  let e : Fin h ↪ b := (Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding
  have hpre : ∀ c : b, ∃ i ∈ Z, w i = c := fun c => Finset.mem_image.1 (hbs c.2)
  choose g hgZ hgw using hpre
  refine ⟨fun a => g (e a), fun a => hgZ _, ?_⟩
  have hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q)) := hli.comp e e.injective
  convert hli' using 1
  funext a
  exact hgw (e a)
end GlobalTheory
