-- Prove2me | solution 1 for GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:38.750357+00:00
-- url     : https://prove2.me/submissions/ee21b39e-80cf-466e-9d11-d06798ecf3e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InfimumSupPowerIdeal
namespace GlobalTheory.InfimumSupPowerIdeal
theorem _root_.solution (C : Type) [CommRing C] (J : Ideal C) (hJ : IsAdicComplete J C)
    (u : ℕ → Ideal C) (hu : ∀ e : ℕ, u e = u (e + 1) ⊔ J ^ (e + 1)) (e : ℕ) :
    (⨅ l : ℕ, u l) ⊔ J ^ (e + 1) = u e := by

  have hsm : ∀ m : ℕ, (J ^ m • ⊤ : Submodule C C) = J ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

  have hanti : Antitone u := antitone_nat_of_succ_le fun k => by
    rw [hu k]; exact le_sup_left
  have hJle : ∀ k, J ^ (k + 1) ≤ u k := fun k => by
    rw [hu k]; exact le_sup_right
  apply le_antisymm
  · exact sup_le (iInf_le u e) (hJle e)
  · intro x hx

    have step : ∀ (k : ℕ) (a : u k), ∃ b : u (k + 1), (a : C) - b ∈ J ^ (k + 1) := by
      intro k a
      have ha : (a : C) ∈ u (k + 1) ⊔ J ^ (k + 1) := by rw [← hu k]; exact a.2
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 ha
      refine ⟨⟨b, hb⟩, ?_⟩
      have : (a : C) - b = c := by rw [← hbc]; ring
      rw [this]; exact hc
    choose g hg using step
    let s : ∀ n : ℕ, u (e + n) := fun n =>
      Nat.rec (motive := fun n => ↥(u (e + n))) ⟨x, hx⟩ (fun n a => g (e + n) a) n
    have hs0 : (s 0 : C) = x := rfl
    have hss : ∀ n, (s n : C) - s (n + 1) ∈ J ^ (e + n + 1) := fun n => hg (e + n) (s n)
    have hchain : ∀ m n, m ≤ n → (s m : C) - s n ∈ J ^ (e + m + 1) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have h1 : (s n : C) - s (n + 1) ∈ J ^ (e + m + 1) :=
          Ideal.pow_le_pow_right (by omega) (hss n)
        have hsum : (s m : C) - s (n + 1) = ((s m : C) - s n) + ((s n : C) - s (n + 1)) := by ring
        rw [hsum]; exact add_mem ih h1

    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun n => (s n : C)) (by
      intro m n hmn
      rw [hsm, SModEq.sub_mem]
      exact Ideal.pow_le_pow_right (by omega) (hchain m n hmn))
    have hL' : ∀ n, (s n : C) - L ∈ J ^ n := fun n => by
      have h := hL n
      rw [hsm, SModEq.sub_mem] at h
      exact h

    have hLu : L ∈ ⨅ l, u l := by
      rw [Submodule.mem_iInf]
      intro l
      have h1 : (s (l + 1) : C) ∈ u l := hanti (by omega : l ≤ e + (l + 1)) (s (l + 1)).2
      have h2 : (s (l + 1) : C) - L ∈ u l := hJle l (hL' (l + 1))
      have h3 := Submodule.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3

    have hxL : x - L ∈ J ^ (e + 1) := by
      have h1 : (s 0 : C) - s (e + 1) ∈ J ^ (e + 1) := by simpa using hchain 0 (e + 1) (by omega)
      have hsum : x - L = ((s 0 : C) - s (e + 1)) + ((s (e + 1) : C) - L) := by rw [hs0]; ring
      rw [hsum]; exact add_mem h1 (hL' (e + 1))
    exact Submodule.mem_sup.2 ⟨L, hLu, x - L, hxL, by ring⟩
end GlobalTheory.InfimumSupPowerIdeal
