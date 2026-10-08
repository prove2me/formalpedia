-- Prove2me | solution 1 for LawlerWCT.RhoMax.rho_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:47:45.165602+00:00
-- url     : https://prove2.me/submissions/9f4497f9-f8d0-4543-946c-22b61ebec7f2

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

theorem solution {ι : Type*} (N : Finset ι) (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar) :
    ∀ I ⊆ N, I.Nonempty →
      -(wstar : ℝ) ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ∧
        LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≤ (wstar : ℝ) := by
  classical
  intro I hi hn
  obtain ⟨j, hj⟩ := hn
  have hs : (0 : ℝ) ≤ wstar := by
    have hh := hw j (hi hj)
    exact_mod_cast (show 0 ≤ wstar by omega)
  have hpos : 0 < ∑ j ∈ I, (p j : ℝ) := by
    apply Finset.sum_pos _ ⟨j, hj⟩
    intro j hj
    have hh := (hpb j (hi hj)).1
    exact_mod_cast (show 0 < p j by omega)
  unfold LawlerWCT.SeriesPar.rho
  constructor
  · rw [le_div_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hwj : -(wstar : ℝ) ≤ w j := by exact_mod_cast (hw j (hi hj)).1
    have hpj : (1 : ℝ) ≤ p j := by exact_mod_cast (hpb j (hi hj)).1
    nlinarith
  · rw [div_le_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hwj : (w j : ℝ) ≤ wstar := by exact_mod_cast (hw j (hi hj)).2
    have hpj : (1 : ℝ) ≤ p j := by exact_mod_cast (hpb j (hi hj)).1
    nlinarith

#print axioms solution
