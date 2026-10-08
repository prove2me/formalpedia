-- Prove2me | solution 1 for GilmoreGomoryTSP.Bottleneck.lemma_8_count
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:57:47.078071+00:00
-- url     : https://prove2.me/submissions/e39be2c9-617f-4f6b-95e5-cfd96459f99e

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model
set_option backward.isDefEq.respectTransparency false

open GilmoreGomoryTSP.Bottleneck

open Classical in
theorem solution {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    (Finset.univ.filter (fun i => Cond22a φ ψ q i)).card =
      (Finset.univ.filter (fun j => Cond22b φ ψ q j)).card := by
  classical
  let e := ψ.trans φ.symm
  let p := fun i : Fin (n + 1) => (i : ℕ) ≤ q
  let r := fun i : Fin (n + 1) => (e i : ℕ) ≤ q
  have he : (Finset.univ.filter p).card = (Finset.univ.filter r).card := by
    apply Finset.card_bij (fun i _ => e.symm i)
    · simp [p, r]
    · intro a ha b hb hab
      exact e.symm.injective hab
    · intro b hb
      refine ⟨e b, ?_, by simp⟩
      simpa [p, r] using hb
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) r
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter r) p
  have hc : (Finset.univ.filter p |>.filter r) = (Finset.univ.filter r |>.filter p) := by
    ext i
    simp [and_comm]
  rw [hc] at h1
  have hh : (Finset.univ.filter p |>.filter (fun i => ¬ r i)).card =
      (Finset.univ.filter r |>.filter (fun i => ¬ p i)).card := by omega
  have ha : (Finset.univ.filter p |>.filter (fun i => ¬ r i)) =
      Finset.univ.filter (fun i => Cond22a φ ψ q i) := by
    ext i
    simp +instances [p, r, e, Cond22a]
  have hb : (Finset.univ.filter r |>.filter (fun i => ¬ p i)) =
      Finset.univ.filter (fun i => Cond22b φ ψ q i) := by
    ext i
    simp +instances [p, r, e, Cond22b]
  rw [ha, hb] at hh
  exact hh

#print axioms solution
