-- Prove2me | solution 1 for MaxPressure.FluidStab.xstar_mem_alloc
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:47:46.019268+00:00
-- url     : https://prove2.me/submissions/2c171fca-adbf-4079-8d26-454eeb3945c5

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

set_option autoImplicit false
open MaxPressure.FluidStab Matrix

theorem solution {I J K : ℕ} (N : Network I J K)
    (xt : Fin J → ℝ) (ρ : ℝ) (hρ : ρ < 1) (hLP : LPFeasible N xt ρ)
    (xh : Fin J → ℝ) (hxh : ∀ j, 0 ≤ xh j) (hpos : ∀ i, 0 < (R N *ᵥ xh) i)
    (hin : ∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) :
    ∃ c : ℝ, 0 < c ∧
      (∀ k, ¬ N.inputProc k → ∑ j, N.A k j * (c • xh) j ≤ 1 - ρ) ∧
      xt + c • xh ∈ allocSet N ∧
      R N *ᵥ (xt + c • xh) = R N *ᵥ (c • xh) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ (R N *ᵥ (xt + c • xh)) i := by
  obtain ⟨hR0, hserv, hinp, hxt⟩ := hLP
  set M : ℝ := ∑ k, ∑ j, |N.A k j * xh j| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have h1ρ : 0 < 1 - ρ := by linarith
  set c : ℝ := (1 - ρ) / (M + 1) with hc
  have hcpos : 0 < c := div_pos h1ρ (by linarith)
  have hsk : ∀ k, ∑ j, N.A k j * xh j ≤ M := by
    intro k
    calc ∑ j, N.A k j * xh j ≤ ∑ j, |N.A k j * xh j| :=
          Finset.sum_le_sum (fun j _ => le_abs_self _)
      _ ≤ ∑ k', ∑ j, |N.A k' j * xh j| :=
          Finset.single_le_sum (f := fun k' => ∑ j, |N.A k' j * xh j|)
            (fun k' _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ k)
  have hcM : c * M ≤ 1 - ρ := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hsum : ∀ k, ∑ j, N.A k j * (c • xh) j = c * ∑ j, N.A k j * xh j := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hRlin : R N *ᵥ (xt + c • xh) = R N *ᵥ (c • xh) := by
    rw [mulVec_add, hR0, zero_add]
  refine ⟨c, hcpos, ?_, ?_, hRlin, ?_⟩
  · intro k _
    rw [hsum k]
    calc c * ∑ j, N.A k j * xh j ≤ c * M := mul_le_mul_of_nonneg_left (hsk k) hcpos.le
      _ ≤ 1 - ρ := hcM
  · refine ⟨fun j => ?_, fun k => ?_, fun k hk => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hxt j) (mul_nonneg hcpos.le (hxh j))
    · have hsplit : ∑ j, N.A k j * (xt + c • xh) j
          = ∑ j, N.A k j * xt j + ∑ j, N.A k j * (c • xh) j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Pi.add_apply]
        ring
      rw [hsplit, hsum k]
      by_cases hk : N.inputProc k
      · rw [hinp k hk, hin k hk]; simp
      · have := hserv k hk
        have h3 : c * ∑ j, N.A k j * xh j ≤ 1 - ρ :=
          le_trans (mul_le_mul_of_nonneg_left (hsk k) hcpos.le) hcM
        linarith
    · have hsplit : ∑ j, N.A k j * (xt + c • xh) j
          = ∑ j, N.A k j * xt j + ∑ j, N.A k j * (c • xh) j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Pi.add_apply]
        ring
      rw [hsplit, hsum k, hinp k hk, hin k hk]; simp
  · have hcpos' : ∀ i, 0 < (R N *ᵥ (xt + c • xh)) i := by
      intro i
      rw [hRlin, mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_pos hcpos (hpos i)
    by_cases hI : Nonempty (Fin I)
    · obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => (R N *ᵥ (xt + c • xh)) i)
      exact ⟨_, hcpos' i0, hi0⟩
    · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hI⟩
