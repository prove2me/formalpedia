-- Prove2me | solution 1 for KhintchineTwoRegime.szarek_tau_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:05:01.908372+00:00
-- url     : https://prove2.me/submissions/217fd0a2-dc56-43e6-aec3-d119975edef3

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Supplement_tau
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
theorem AuxTZ_key (a s : ℝ) (hs : |s| = 1) (h : a + s / Real.sqrt 2 = 0) :
    |a| = 1 / Real.sqrt 2 := by
  rw [eq_neg_of_add_eq_zero_left h, abs_neg, abs_div, hs, abs_of_pos (by positivity)]

theorem AuxTZ_sign (b : Bool) : |KhintchineTwoRegime.Supplement.signR b| = 1 := by
  cases b <;> simp [KhintchineTwoRegime.Supplement.signR]


theorem KhintchineTwoRegime.szarek_tau_eq_zero {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hτ : KhintchineTwoRegime.Supplement.tau hn x = 0) :
    ∃ i j : Fin n, i ≠ j ∧ |x i| = 1 / Real.sqrt 2 ∧ |x j| = 1 / Real.sqrt 2 := by
  unfold KhintchineTwoRegime.Supplement.tau at hτ
  obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_inf' (KhintchineTwoRegime.Supplement.extremalIndex_nonempty hn)
    (fun p : (Fin n × Fin n) × (Bool × Bool) =>
      HighDimProb.SparseRecovery.l2Norm (x + (KhintchineTwoRegime.Supplement.signR p.2.1 / Real.sqrt 2) • (Pi.single p.1.1 (1 : ℝ) : Fin n → ℝ)
      + (KhintchineTwoRegime.Supplement.signR p.2.2 / Real.sqrt 2) • (Pi.single p.1.2 (1 : ℝ) : Fin n → ℝ)))
  rw [hpv] at hτ
  simp only [KhintchineTwoRegime.Supplement.extremalIndex, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, and_true] at hp
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp
  unfold HighDimProb.SparseRecovery.l2Norm at hτ
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hτ
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hτ
  have hi := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hz p.1.1 (Finset.mem_univ _))
  have hj := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hz p.1.2 (Finset.mem_univ _))
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
    Pi.single_eq_of_ne hne.symm, smul_eq_mul, mul_one, mul_zero, add_zero] at hi hj
  exact ⟨p.1.1, p.1.2, hne, AuxTZ_key _ _ (AuxTZ_sign _) hi, AuxTZ_key _ _ (AuxTZ_sign _) hj⟩


theorem solution {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hτ : KhintchineTwoRegime.Supplement.tau hn x = 0) :
    ∃ i j : Fin n, i ≠ j ∧ |x i| = 1 / Real.sqrt 2 ∧ |x j| = 1 / Real.sqrt 2 :=
  KhintchineTwoRegime.szarek_tau_eq_zero hn x hτ
