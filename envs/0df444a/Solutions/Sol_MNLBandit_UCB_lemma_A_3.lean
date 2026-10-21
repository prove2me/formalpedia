-- Prove2me | solution 1 for MNLBandit.UCB.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:32:53.329233+00:00
-- url     : https://prove2.me/submissions/7c8a2560-3784-4f7f-bfce-fce78685da3f

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting

set_option autoImplicit false
open ChoiceCDLP.MNL MNLBandit.UCB

theorem solution {N : ℕ} (𝒮 : Finset (Finset (Fin N))) (h𝒮 : DownClosed 𝒮)
    (r : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (w u : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwu : ∀ i, w i ≤ u i) (S : Finset (Fin N)) (hS : S ∈ 𝒮)
    (hopt : ∀ Q ∈ 𝒮, mnlObjective w r 1 Q ≤ mnlObjective w r 1 S)
    (hpos : ∀ j ∈ S, 0 < w j) :
    mnlObjective w r 1 S ≤ mnlObjective u r 1 S := by
  unfold mnlObjective at *
  have hV : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg (fun j _ => hw j)
  have hU : 0 ≤ ∑ j ∈ S, u j := Finset.sum_nonneg (fun j _ => (hw j).trans (hwu j))
  set R := (∑ j ∈ S, r j * w j) / (∑ j ∈ S, w j + 1) with hR
  have hRa : ∑ j ∈ S, r j * w j = R * (∑ j ∈ S, w j + 1) := by
    rw [hR]; field_simp
  have key : ∀ j ∈ S, R ≤ r j := by
    intro j hj
    have h1 := hopt (S.erase j) (h𝒮 S hS _ (Finset.erase_subset _ _))
    rw [Finset.sum_erase_eq_sub hj, Finset.sum_erase_eq_sub hj] at h1
    have hle : w j ≤ ∑ k ∈ S, w k :=
      Finset.single_le_sum (f := w) (fun k _ => hw k) hj
    have hp : 0 < ∑ k ∈ S, w k - w j + 1 := by linarith
    rw [div_le_iff₀ hp, hRa] at h1
    have hwj := hpos j hj
    have : R * w j ≤ r j * w j := by nlinarith
    exact le_of_mul_le_mul_right this hwj
  have hsum : ∑ j ∈ S, (r j - R) * w j ≤ ∑ j ∈ S, (r j - R) * u j :=
    Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hwu j) (sub_nonneg.2 (key j hj)))
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [le_div_iff₀ (by linarith)]
  nlinarith
