-- Prove2me | solution 1 for MusicStreaming.Axioms.constant_user_total
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:39.017987+00:00
-- url     : https://prove2.me/submissions/3add2517-14ac-4eaa-b2a1-76f9ca5de084

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

section MSA2
variable {n : ℕ}

lemma msa2_erase_two (j j' : ℕ) (hjj : j ≠ j') (x y : Fin n → ℕ) :
    (Finsupp.single j x + Finsupp.single j' y : Problem n).erase j' = Finsupp.single j x := by
  refine Finsupp.ext fun k => ?_
  simp only [Finsupp.erase_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : k = j'
  · simp [h1, hjj]
  · by_cases h2 : k = j
    · simp [h2, hjj, Ne.symm hjj]
    · simp [h1, h2, Ne.symm h2, Ne.symm h1]

lemma msa2_two_users (I : Index n) (hG : EqualGlobalImpact I) (j j' : ℕ) (hjj : j ≠ j')
    (x y : Fin n → ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∑ i, I (Finsupp.single j x) i = ∑ i, I (Finsupp.single j' y) i := by
  have h0 : (Finsupp.single j x).support = {j} := Finsupp.support_single_ne_zero j hx
  have h1 : (Finsupp.single j' y).support = {j'} := Finsupp.support_single_ne_zero j' hy
  have hd : Disjoint (Finsupp.single j x).support (Finsupp.single j' y).support := by
    rw [h0, h1]; simpa using hjj
  have hsupp : (Finsupp.single j x + Finsupp.single j' y : Problem n).support = {j, j'} := by
    rw [Finsupp.support_add_eq hd, h0, h1]; rfl
  have hj : j ∈ (Finsupp.single j x + Finsupp.single j' y : Problem n).support := by
    rw [hsupp]; simp
  have hj' : j' ∈ (Finsupp.single j x + Finsupp.single j' y : Problem n).support := by
    rw [hsupp]; simp
  have := hG _ j' j hj' hj
  rw [msa2_erase_two j j' hjj x y] at this
  have e2 : (Finsupp.single j x + Finsupp.single j' y : Problem n).erase j = Finsupp.single j' y := by
    rw [add_comm]; exact msa2_erase_two j' j (Ne.symm hjj) y x
  rw [e2] at this
  exact this

end MSA2

theorem solution {n : ℕ} (I : Index n) (hG : EqualGlobalImpact I) :
    ∀ (j j' : ℕ) (x y : Fin n → ℕ), x ≠ 0 → y ≠ 0 →
      ∑ i, I (Finsupp.single j x) i = ∑ i, I (Finsupp.single j' y) i := by
  intro j j' x y hx hy
  by_cases hjj : j = j'
  · subst hjj
    have a := msa2_two_users I hG j (j + 1) (by omega) x y hx hy
    have b := msa2_two_users I hG j (j + 1) (by omega) y y hy hy
    rw [a, b]
  · exact msa2_two_users I hG j j' hjj x y hx hy
