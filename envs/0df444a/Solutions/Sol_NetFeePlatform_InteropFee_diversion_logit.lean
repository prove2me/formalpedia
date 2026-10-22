-- Prove2me | solution 1 for NetFeePlatform.InteropFee.diversion_logit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:27:05.014279+00:00
-- url     : https://prove2.me/submissions/ab546355-ad72-4e8f-9617-2e48382dc1c0

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
set_option autoImplicit false

theorem solution {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (t : Fin J → ℝ) (j : Fin J) :
    NetFeePlatform.Competition.diversion w t j = (∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) /
        (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) ∧
      HasDerivAt (fun s => ∑ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w (Function.update t j s) k)
        (NetFeePlatform.Competition.diversion w t j * (NetFeePlatform.Competition.demand w t j * (1 - NetFeePlatform.Competition.demand w t j))) (t j) := by
  set S : ℝ := ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  have hsplit : ∀ u : Fin J → ℝ, ∑ k, Real.exp (-u k) = Real.exp (-u j) + ∑ k ∈ Finset.univ.erase j, Real.exp (-u k) := by
    intro u
    exact (Finset.add_sum_erase Finset.univ (fun k => Real.exp (-u k)) (Finset.mem_univ j)).symm
  have hwS : 0 < w + S := by
    rcases hJ with h | h
    · linarith
    · have hne : (Finset.univ.erase j).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j)]
        simp; omega
      have : 0 < S := Finset.sum_pos (fun k _ => Real.exp_pos _) hne
      linarith
  have hD : w + ∑ k, Real.exp (-t k) = Real.exp (-t j) + (w + S) := by
    rw [hsplit t]; ring
  have hDpos : 0 < Real.exp (-t j) + (w + S) := by
    have := Real.exp_pos (-t j); linarith
  have hdem : ∀ k, NetFeePlatform.Competition.demand w t k = Real.exp (-t k) / (Real.exp (-t j) + (w + S)) := by
    intro k; unfold NetFeePlatform.Competition.demand; rw [hD]
  have h1 : 1 - Real.exp (-t j) / (Real.exp (-t j) + (w + S)) = (w + S) / (Real.exp (-t j) + (w + S)) := by
    rw [eq_div_iff hDpos.ne', sub_mul, div_mul_cancel₀ _ hDpos.ne']; ring
  have hdiv : NetFeePlatform.Competition.diversion w t j = S / (w + S) := by
    unfold NetFeePlatform.Competition.diversion
    simp only [hdem, ← Finset.sum_div]
    rw [← hS, h1]
    exact div_div_div_cancel_right₀ hDpos.ne' S (w + S)
  refine ⟨hdiv, ?_⟩
  have hfun : (fun s => ∑ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w (Function.update t j s) k)
      = fun s => S / (Real.exp (-s) + (w + S)) := by
    funext s
    have h1 : ∀ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w (Function.update t j s) k
        = Real.exp (-t k) / (Real.exp (-s) + (w + S)) := by
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      unfold NetFeePlatform.Competition.demand
      rw [Function.update_of_ne hkj, hsplit]
      rw [Function.update_self]
      have : ∑ m ∈ Finset.univ.erase j, Real.exp (-Function.update t j s m) = S := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Function.update_of_ne (Finset.mem_erase.mp hm).1]
      rw [this]; ring_nf
    rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  rw [hfun, hdiv, hdem j]
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s) + (w + S)) (-Real.exp (-t j)) (t j) := by
    have := ((Real.hasDerivAt_exp (-t j)).comp (t j) (hasDerivAt_neg (t j))).add_const (w + S)
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => S / (Real.exp (-s) + (w + S)))
      ((0 * (Real.exp (-t j) + (w + S)) - S * -Real.exp (-t j)) / (Real.exp (-t j) + (w + S)) ^ 2) (t j) :=
    (hasDerivAt_const (t j) S).div hd hDpos.ne'
  refine h2.congr_deriv ?_
  rw [h1]
  field_simp
  ring
