-- Prove2me | solution 2 for MasulloRH.rational_theta_cutoff_trace_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:25:50.069518+00:00
-- url     : https://prove2.me/submissions/7fe63991-187d-4cfb-b028-5094a5bea816
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_cofinal_rational_theta_gram_certificates
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
open MasulloRH MasulloGRH Filter MeasureTheory
open scoped Topology InnerProductSpace

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
          (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re ≤
            (operatorTrace T).re + ε := by
  classical
  have hRH := finite_theta_approximation_excludes_rectangle_zeros.2
    cofinal_rational_theta_gram_certificates
  have he (n : ℕ) : ∃ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T := by
    obtain ⟨T,hT,_⟩ := (rational_theta_annihilator_jet_trace ((n:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2 _ (regularized_test_admissible n 3)
    exact ⟨T,hT.1⟩
  choose T hT using he
  obtain ⟨hlim,_,hiff⟩ := rational_theta_cutoff_trace_defect T hT
  rw [hiff.mpr hRH] at hlim
  intro ε hε N
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  let n := max N m
  refine ⟨n,le_max_left _ _,?_⟩
  intro S hS
  have hEq : S = T n := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply ext_inner_left ℂ
    intro v
    exact (hS u v).trans ((hT n u v).symm)
  rw [hEq]
  have h := hm n (le_max_right _ _)
  linarith
