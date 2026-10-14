-- Prove2me | solution 1 for L0BnB.BigMvsPR.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:06:46.646924+00:00
-- url     : https://prove2.me/submissions/5ad9b793-a1ac-48cf-a367-3b89fc5c3fcc

import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations
import Mathlib

open L0BnB.BigMvsPR L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    IsLeast (L0BnB.Strength.H X y lam0 lam2 M '' L0BnB.Reduced.box p M) (L0BnB.Strength.VB X y lam0 lam2 M) := by
  classical
  have hc : IsCompact (box p M) := by
    have heq : box p M = Set.Icc (fun _ : Fin p => -M) (fun _ => M) := by
      ext b
      simp [box, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rw [heq]
    exact isCompact_Icc
  have hne : (box p M).Nonempty := ⟨0, by simpa [box] using fun _ : Fin p => hM.le⟩
  have hcont : Continuous (H X y lam0 lam2 M) := by
    unfold H lsLoss Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨b, hb, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hbest : IsLeast {v | ∃ β z : Fin p → ℝ,
      bigMIntervalFeasible M β z ∧ bigMObj X y lam0 lam2 β z = v}
      (H X y lam0 lam2 M b) := by
    constructor
    · refine ⟨b, fun i => |b i| / M, ?_, ?_⟩
      · intro i
        have hi := hb i
        have hcanc : M * (|b i| / M) = |b i| := by field_simp
        refine ⟨?_, ?_, div_nonneg (abs_nonneg _) hM.le, (div_le_one hM).mpr hi⟩
        · nlinarith [neg_abs_le (b i)]
        · nlinarith [le_abs_self (b i)]
      · unfold bigMObj H
        simp only [Finset.mul_sum, Finset.sum_add_distrib, div_mul_eq_mul_div, mul_div_assoc]
        ring
    · rintro v ⟨β, z, hfeas, rfl⟩
      have hβ : β ∈ box p M := by
        intro i
        have hi := hfeas i
        apply abs_le.mpr
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hi.2.2.2 hM.le]
      apply (hmin hβ).trans
      have hsum : (∑ i, lam0 / M * |β i|) ≤ ∑ i, lam0 * z i := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hfeas i
        have habs : |β i| ≤ M * z i := abs_le.mpr ⟨by nlinarith, hi.2.1⟩
        have hdiv : |β i| / M ≤ z i := (div_le_iff₀ hM).mpr (by simpa [mul_comm] using habs)
        calc
          _ = lam0 * (|β i| / M) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hlam0.le
      unfold H bigMObj
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
      linarith
  have hv : VB X y lam0 lam2 M = H X y lam0 lam2 M b := hbest.csInf_eq
  rw [hv]
  refine ⟨⟨b, hb, rfl⟩, ?_⟩
  rintro _ ⟨β, hβ, rfl⟩
  exact hmin hβ
