-- Prove2me | solution 1 for LindbladTolerant.Testing.time_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:01.525451+00:00
-- url     : https://prove2.me/submissions/2651b783-958c-4293-a725-e0cd3560eacc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LindbladTolerant_Testing_dephasing_family_facts
import Theorems.Thm_LindbladTolerant_Testing_adaptive_poisson_data_processing
import Theorems.Thm_LindbladTolerant_Testing_poisson_tv_hellinger_bound
import Theorems.Thm_LindbladTolerant_Testing_dephasing_time_arithmetic

set_option autoImplicit false
open scoped ComplexOrder
open LindbladTolerant.Testing

theorem solution : LindbladTolerant.Testing.UniformLower := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt
  refine ⟨?_, ?_⟩
  · exact mul_pos hsqrt (Real.log_pos (by norm_num))
  · intro k hk n hn bound eps1 eps2 hbound heps1 heps12 heps2 Ω mΩ
    letI := mΩ
    intro p T hp hTime hsolves
    let gamma0 := eps1 / Real.sqrt 2
    let gamma1 := eps2 / Real.sqrt 2
    have heps2_pos : 0 < eps2 := lt_of_le_of_lt heps1 heps12
    have hgamma0 : 0 ≤ gamma0 := div_nonneg heps1 (le_of_lt hsqrt)
    have hgamma1 : 0 ≤ gamma1 := div_nonneg (le_of_lt heps2_pos) (le_of_lt hsqrt)
    have hgamma01 : gamma0 ≤ gamma1 := by
      exact div_le_div_of_nonneg_right (le_of_lt heps12) (le_of_lt hsqrt)
    have hfacts0 := dephasing_family_facts n k hn hk gamma0 hgamma0
    have hfacts1 := dephasing_family_facts n k hn hk gamma1 hgamma1
    have hnorm0 : frobenius (canonicalD (dephasing n gamma0)) = eps1 := by
      rw [hfacts0.2.2.1, hfacts0.2.2.2]
      dsimp [gamma0]
      field_simp
    have hnorm1 : frobenius (canonicalD (dephasing n gamma1)) = eps2 := by
      rw [hfacts1.2.2.1, hfacts1.2.2.2]
      dsimp [gamma1]
      field_simp
    have htwo1 : 2 * gamma1 = Real.sqrt 2 * eps2 := by
      dsimp [gamma1]
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have heps2' : eps2 * Real.sqrt 2 ≤ bound := (le_div_iff₀ hsqrt).mp heps2
    have hdiamond1 : diamond (dephasing n gamma1) ≤ bound := by
      rw [hfacts1.2.1]
      nlinarith
    have hdiamond0 : diamond (dephasing n gamma0) ≤ bound := by
      rw [hfacts0.2.1]
      nlinarith
    have hsource0 : SourceClass k bound (dephasing n gamma0) :=
      ⟨hfacts0.1, hdiamond0⟩
    have hsource1 : SourceClass k bound (dephasing n gamma1) :=
      ⟨hfacts1.1, hdiamond1⟩
    have hyes := (hsolves _ hsource0).1 (le_of_eq hnorm0)
    have hno := (hsolves _ hsource1).2 (le_of_eq hnorm1.symm)
    have hsep := adaptive_poisson_data_processing p T gamma0 gamma1 hp hTime
      hgamma0 hgamma1 hyes hno
    have hhell := poisson_tv_hellinger_bound (gamma0 * T) (gamma1 * T)
      (mul_nonneg hgamma0 hTime.1) (mul_nonneg hgamma1 hTime.1)
    exact dephasing_time_arithmetic eps1 eps2 T gamma0 gamma1 heps1 heps12 hTime.1
      rfl rfl hsep hhell
