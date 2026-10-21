-- Prove2me | solution 1 for NetFeePlatform.Competition.proposition_1_logit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:26:16.774163+00:00
-- url     : https://prove2.me/submissions/516733d5-a623-456d-85b8-b51a3eaebb71

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
set_option autoImplicit false
open NetFeePlatform.Competition

open Finset in
theorem aux_sum {J : ℕ} (t : Fin J → ℝ) (j : Fin J) (s : ℝ) :
    ∑ k, Real.exp (-(Function.update t j s k)) =
      Real.exp (-s) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem logit_deriv_aux {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (t : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun s => demand w (Function.update t j s) j)
      (-(demand w t j * (1 - demand w t j))) (t j) := by
  set C : ℝ := w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
      Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    linarith
  have hf : (fun s => demand w (Function.update t j s) j) = fun s => Real.exp (-s) / (Real.exp (-s) + C) := by
    funext s
    unfold demand
    rw [aux_sum]
    simp only [Function.update_self]
    rw [hC]; ring_nf
  rw [hf]
  have hD : ∀ s, 0 < Real.exp (-s) + C := fun s => by have := Real.exp_pos (-s); linarith
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-(t j))) (t j) := by
    have := ((hasDerivAt_id (t j)).neg).exp
    have this : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-(t j)) * -1) (t j) := this
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s) + C) (-Real.exp (-(t j))) (t j) := h1.add_const C
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s) / (Real.exp (-s) + C))
      ((-Real.exp (-t j) * (Real.exp (-t j) + C) - Real.exp (-t j) * -Real.exp (-t j)) / (Real.exp (-t j) + C) ^ 2) (t j) :=
    h1.div h2 (hD (t j)).ne'
  refine h3.congr_deriv ?_
  have hdem : demand w t j = Real.exp (-t j) / (Real.exp (-t j) + C) := by
    unfold demand
    have := aux_sum t j (t j)
    rw [Function.update_eq_self] at this
    rw [this, hC]; ring_nf
  rw [hdem]
  have := (hD (t j)).ne'
  field_simp
  ring

theorem solution {J : ℕ} (w c γ : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (t : Fin J → ℝ) (ht : IsEquilibrium w c γ 0 t) :
    ∀ j, t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j := by
  intro j
  have hn := logit_deriv_aux w hw t j
  have hsplit : ∑ k, Real.exp (-t k) = Real.exp (-t j) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hC : 0 < w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
    have h0 : 0 ≤ ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
      Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    rcases hJ with h | h
    · linarith
    · have hne : (Finset.univ.erase j).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j)]
        simp
        omega
      have : 0 < ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
        Finset.sum_pos (fun k _ => Real.exp_pos _) hne
      linarith
  have hD : 0 < w + ∑ k, Real.exp (-t k) := by
    rw [hsplit]; have := Real.exp_pos (-t j); linarith
  have hn0 : 0 < demand w t j := by unfold demand; positivity
  have hn1 : 0 < 1 - demand w t j := by
    unfold demand
    rw [sub_pos, div_lt_one hD, hsplit]
    linarith
  set n := demand w t j with hnn
  have hf : (fun s => profit w c γ 0 (Function.update t j s) j) =
      fun s => (s + γ * demand w (Function.update t j s) j - c) * demand w (Function.update t j s) j := by
    funext s
    simp [profit]
  have hder : HasDerivAt (fun s => profit w c γ 0 (Function.update t j s) j)
      ((1 + γ * (-(n * (1 - n)))) * n + (t j + γ * n - c) * (-(n * (1 - n)))) (t j) := by
    rw [hf]
    have h1 : HasDerivAt (fun s : ℝ => s + γ * demand w (Function.update t j s) j - c)
        (1 + γ * (-(n * (1 - n)))) (t j) :=
      (((hasDerivAt_id (t j)).add (hn.const_mul γ)).sub_const c)
    have h2 : HasDerivAt (fun s : ℝ => (s + γ * demand w (Function.update t j s) j - c) *
          demand w (Function.update t j s) j)
        ((1 + γ * (-(n * (1 - n)))) * demand w (Function.update t j (t j)) j +
          (t j + γ * demand w (Function.update t j (t j)) j - c) * (-(n * (1 - n)))) (t j) :=
      h1.mul hn
    rw [Function.update_eq_self] at h2
    exact h2
  have hmax : IsLocalMax (fun s => profit w c γ 0 (Function.update t j s) j) (t j) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have := ht j s
    simpa [Function.update_eq_self] using this
  have h0 := hmax.hasDerivAt_eq_zero hder
  have key : n * ((1 - γ * (n * (1 - n))) - (t j + γ * n - c) * (1 - n)) = 0 := by linarith
  have key2 : (1 - γ * (n * (1 - n))) - (t j + γ * n - c) * (1 - n) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hn0.ne'
    · exact h
  have : t j - c + 2 * γ * n = 1 / (1 - n) := by
    rw [eq_div_iff hn1.ne']
    linear_combination (-1) * key2
  linarith
