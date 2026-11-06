-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.finite_expansion_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:25:33.022644+00:00
-- url     : https://prove2.me/submissions/d4168365-500f-4130-94cb-5ea787c25cf8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]
end OAI.SevenEighths.InverseMoment
