-- Prove2me | solution 1 for NetFeePlatform.Competition.logit_deriv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:13:32.435753+00:00
-- url     : https://prove2.me/submissions/0b2a0f97-15e4-40b9-bf86-94d288ec19b3

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

theorem solution {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (t : Fin J → ℝ) (j : Fin J) :
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
