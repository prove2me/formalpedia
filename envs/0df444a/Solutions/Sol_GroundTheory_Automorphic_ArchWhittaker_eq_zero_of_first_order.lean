-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_first_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:47.051915+00:00
-- url     : https://prove2.me/submissions/22a68b0d-923a-4e79-9f65-846b747affd3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_exp_growth_false
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_inner_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {F : ℝ → ℂ} {m : ℤ} {b : ℝ} (hb : 0 < b)
    (hF : ∀ y > 0, HasDerivAt F ((((m : ℝ) / (2 * y) + b : ℝ) : ℂ) * F y) y)
    (hgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ 1, ‖F y‖ ≤ C * y ^ N) : ∀ y > 0, F y = 0 := by
  obtain ⟨C, N, hC⟩ := hgr
  set u : ℝ → ℝ := fun y => ‖F y‖ ^ 2 with hudef
  set V : ℝ → ℝ := fun y => u y * (y ^ (-m) * Real.exp (-(2 * b * y))) with hVdef
  have hu : ∀ y > 0, HasDerivAt u (2 * ((m : ℝ) / (2 * y) + b) * u y) y := by
    intro y hy
    have := (hF y hy).norm_sq
    refine this.congr_deriv ?_
    rw [inner_mul_self, Complex.ofReal_re]
    simp only [hudef]
    ring
  have hV : ∀ y > 0, HasDerivAt V 0 y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => y ^ (-m)) (((-m : ℤ) : ℝ) * y ^ (-m - 1)) y :=
      hasDerivAt_zpow (-m) y (Or.inl hy.ne')
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(2 * b * y)))
        (Real.exp (-(2 * b * y)) * -(2 * b * 1)) y :=
      ((hasDerivAt_id y).const_mul (2 * b)).neg.exp
    have := (hu y hy).mul (h1.mul h2)
    refine this.congr_deriv ?_
    have hy0 : y ≠ 0 := hy.ne'
    have e : y ^ (-m - 1) = y ^ (-m) / y := by
      rw [zpow_sub₀ hy0, zpow_one]
    simp only [Pi.mul_apply]
    rw [e]
    push_cast
    field_simp
    ring
  have hconst : ∀ y > 0, V y = V 1 := fun y hy =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hV z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hV z hz).deriv) hy (mem_Ioi.2 one_pos)
  have hV1 : 0 ≤ V 1 := by
    simp only [hVdef]; positivity
  have hV10 : V 1 = 0 := by
    by_contra hne
    have hV1pos : 0 < V 1 := lt_of_le_of_ne hV1 (Ne.symm hne)
    refine exp_growth_false (A := V 1) (b := 2 * b) (K := C ^ 2) (M := 2 * N + m.natAbs)
      (Y := 1) hV1pos (by positivity) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have h1 : u y * (y ^ (-m) * Real.exp (-(2 * b * y))) = V 1 := hconst y hy0
    have hu_le : u y ≤ C ^ 2 * y ^ (2 * N) := by
      have := hC y hy
      calc u y = ‖F y‖ ^ 2 := rfl
        _ ≤ (C * y ^ N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = C ^ 2 * y ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]
    have hpow : y ^ (-m) ≤ y ^ m.natAbs := by
      have : y ^ (-m) ≤ y ^ ((m.natAbs : ℤ)) := zpow_le_zpow_right₀ hy (by omega)
      rwa [zpow_natCast] at this
    have hexp : Real.exp (2 * b * y) * Real.exp (-(2 * b * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hC2 : 0 ≤ C ^ 2 * y ^ (2 * N) := le_trans (by positivity) hu_le
    calc V 1 * Real.exp (2 * b * y) = u y * y ^ (-m) := by
          rw [← h1]
          calc u y * (y ^ (-m) * Real.exp (-(2 * b * y))) * Real.exp (2 * b * y)
              = u y * y ^ (-m) * (Real.exp (2 * b * y) * Real.exp (-(2 * b * y))) := by ring
            _ = u y * y ^ (-m) := by rw [hexp, mul_one]
      _ ≤ C ^ 2 * y ^ (2 * N) * y ^ m.natAbs :=
          mul_le_mul hu_le hpow (zpow_nonneg hy0.le _) hC2
      _ = C ^ 2 * y ^ (2 * N + m.natAbs) := by rw [pow_add, mul_assoc]
  intro y hy
  have h1 := hconst y hy
  rw [hV10] at h1
  simp only [hVdef] at h1
  have hpos : 0 < y ^ (-m) * Real.exp (-(2 * b * y)) :=
    mul_pos (zpow_pos hy _) (Real.exp_pos _)
  have hu0 : u y = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hpos.ne'
  have : ‖F y‖ = 0 := by
    have : ‖F y‖ ^ 2 = 0 := hu0
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  exact norm_eq_zero.1 this
end GroundTheory.Automorphic.ArchWhittaker
