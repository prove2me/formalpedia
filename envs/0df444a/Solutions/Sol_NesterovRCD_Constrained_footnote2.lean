-- Prove2me | solution 1 for NesterovRCD.Constrained.footnote2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:55:53.551601+00:00
-- url     : https://prove2.me/submissions/f737f08c-16cb-492c-b847-dc79b810c555

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

set_option autoImplicit false

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

lemma nrc_wnorm_single (L : Fin n → ℝ) (hL : ∀ i, 0 < L i) (i : Fin n) (v : E i) :
    NesterovRCD.Sublinear.wnorm L 1 (Pi.single i v : NesterovRCD.Sublinear.Blocks E) ^ 2 = L i * ‖v‖ ^ 2 := by
  unfold NesterovRCD.Sublinear.wnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => mul_nonneg (Real.rpow_nonneg (hL j).le _) (sq_nonneg _)))]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem solution (hn : 0 < n) [∀ i, Nontrivial (E i)] (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : NesterovRCD.Sublinear.CoordLipschitz f L) (σ : ℝ) (hσ : 0 < σ) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ) :
    σ ≤ 1 := by
  obtain ⟨hdiff, hLi, hlip⟩ := hL
  obtain ⟨-, hsc⟩ := hsc
  set i : Fin n := ⟨0, hn⟩ with hi
  obtain ⟨v, hv⟩ := exists_ne (0 : E i)
  set y : NesterovRCD.Sublinear.Blocks E := Pi.single i v with hy
  have h1 := hsc 0 y
  have h2 := hsc y 0
  have hN1 : NesterovRCD.Sublinear.wnorm L 1 (y - 0) ^ 2 = L i * ‖v‖ ^ 2 := by
    rw [sub_zero]; exact nrc_wnorm_single L hLi i v
  have hN2 : NesterovRCD.Sublinear.wnorm L 1 (0 - y) ^ 2 = L i * ‖v‖ ^ 2 := by
    have : NesterovRCD.Sublinear.wnorm L 1 (0 - y) = NesterovRCD.Sublinear.wnorm L 1 y := by
      unfold NesterovRCD.Sublinear.wnorm
      simp
    rw [this]; exact nrc_wnorm_single L hLi i v
  rw [hN1] at h1
  rw [hN2] at h2
  have hb : fderiv ℝ f y (0 - y) = - fderiv ℝ f y y := by rw [zero_sub, map_neg]
  have ha : fderiv ℝ f 0 (y - 0) = fderiv ℝ f 0 y := by rw [sub_zero]
  rw [hb] at h2
  rw [ha] at h1
  have hlp := hlip i 0 v
  have hpg : NesterovRCD.Sublinear.partialGrad f (0 + Pi.single i v) i v - NesterovRCD.Sublinear.partialGrad f 0 i v
      = fderiv ℝ f y y - fderiv ℝ f 0 y := by
    simp [NesterovRCD.Sublinear.partialGrad, hy]
  have hbd : fderiv ℝ f y y - fderiv ℝ f 0 y ≤ L i * ‖v‖ ^ 2 := by
    rw [← hpg]
    have := (ContinuousLinearMap.le_opNorm
      (NesterovRCD.Sublinear.partialGrad f (0 + Pi.single i v) i - NesterovRCD.Sublinear.partialGrad f 0 i) v)
    simp only [ContinuousLinearMap.sub_apply] at this
    calc _ ≤ ‖NesterovRCD.Sublinear.partialGrad f (0 + Pi.single i v) i v - NesterovRCD.Sublinear.partialGrad f 0 i v‖ := le_abs_self _
      _ ≤ _ := this
      _ ≤ (L i * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hlp (norm_nonneg _)
      _ = _ := by ring
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  have hLpos := hLi i
  have : σ * (L i * ‖v‖ ^ 2) ≤ 1 * (L i * ‖v‖ ^ 2) := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)
