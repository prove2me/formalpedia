-- Prove2me | solution 1 for KeskinZeevi.IncumbentSufficient.ls_error_eq_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:34:02.338306+00:00
-- url     : https://prove2.me/submissions/24e2b598-b00c-4261-a926-d160a4701a68

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares

open KeskinZeevi.IncumbentSufficient in
theorem solution (M : Model) {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (hJ : Jhat π β ε t ω ≠ 0) :
    betaHat π β ε t ω - β = noiseSum π β ε t ω / Jhat π β ε t ω := by
  have hnum : ∑ s ∈ Finset.Icc 1 t, (demand π β ε s ω - M.DHat) * dev π β ε s ω =
      β * Jhat π β ε t ω + noiseSum π β ε t ω := by
    unfold Jhat noiseSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    unfold demand
    ring
  unfold betaHat
  rw [hnum]
  field_simp
  ring
