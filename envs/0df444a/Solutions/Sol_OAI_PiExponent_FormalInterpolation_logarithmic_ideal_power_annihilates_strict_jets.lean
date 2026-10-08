-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_ideal_power_annihilates_strict_jets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:30:55.482519+00:00
-- url     : https://prove2.me/submissions/663963d0-c016-43c2-9d2d-9837352ad5a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_annihilates_strict_jets

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℝ) * v 0)
    (R : ℝ) (he : ∀ i, R ≤ (e i : ℝ) * v i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ FormalInterpolation.logarithmicCentersIdeal c T e ^ n)
    (j : Fin K) (a : ↥(strictWeightedSimplex v ((n : ℝ) * R))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
      (FormalInterpolation.formalJet (c j) P) = 0 := by
  let I : Fin K → Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    fun k => FormalInterpolation.logarithmicCenterIdeal (c k) T e
  have hprod : (∏ k, I k) ≤ I j := by
    calc
      (∏ k, I k) ≤ ∏ k, (if k = j then I k else ⊤) := by
        apply Finset.prod_le_prod'
        intro k hk
        by_cases hkj : k = j <;> simp [hkj]
      _ = I j := by
        classical
        simpa using (Finset.prod_eq_single j
          (s := Finset.univ)
          (f := fun k => if k = j then I k else ⊤)
          (by
            intro k hk hkj
            simp [hkj])
          (by simp))
  have hpow_aux : ∀ q : ℕ, (∏ k, I k) ^ q ≤ I j ^ q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul' ih hprod
  have hpow := hpow_aux n
  have hlocal : P ∈ I j ^ n := hpow hP
  exact FormalInterpolation.logarithmic_center_ideal_power_annihilates_strict_jets
    (c j) T e v hv hT R he n P hlocal a
