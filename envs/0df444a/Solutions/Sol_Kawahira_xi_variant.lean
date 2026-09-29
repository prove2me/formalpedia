-- Prove2me | solution 1 for Kawahira.xi_variant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:59:15.825765+00:00
-- url     : https://prove2.me/submissions/9da6b4c1-b314-4e4d-b632-bfd73f3b0140

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_deriv_xi_ne_zero_iff
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_norm_one_sub_inv
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_Kawahira_symmetric_indifferent_zero_simple
import Theorems.Thm_Kawahira_xi_analyticOrderAt_ne_top
import Theorems.Thm_Kawahira_xi_eq_zero_iff_nontrivial
import Theorems.Thm_Kawahira_xi_one_sub

open Complex Topology
open Kawahira

theorem solution :
    (∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0) ↔
      (∀ a : ℂ, a ≠ 0 → (xi a = 0 ∨ deriv xi a ≠ 0) → nuXi a = a →
        IsIndifferentFixedPoint nuXi a) := by
  constructor
  · intro hRH a ha0 hreg hfix
    have hxi : xi a = 0 := by
      rcases hreg with hzero | hderiv
      · exact hzero
      · by_contra hzero
        have hquot : xi a / (a * deriv xi a) = 0 := by
          have heq : a - xi a / (a * deriv xi a) = a := by
            simpa [nuXi, nu] using hfix
          exact sub_eq_self.mp heq
        exact (div_ne_zero hzero (mul_ne_zero ha0 hderiv)) hquot
    have hnontrivial : IsNontrivialZero a :=
      (xi_eq_zero_iff_nontrivial a ha0).mp hxi
    have hRH_a := hRH a hnontrivial
    have hxideriv : deriv xi a ≠ 0 :=
      (deriv_xi_ne_zero_iff a hnontrivial).mpr hRH_a.2
    have hxian : AnalyticAt ℂ xi a := differentiable_xi.analyticAt a
    have horder : analyticOrderAt xi a = (1 : ℕ∞) :=
      hxian.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hxi hxideriv
    have hnu := nu_at_zero_of_order xi a 1 ha0 (by norm_num) hxian horder
    refine ⟨hfix, ?_⟩
    have hderiv_nu : deriv nuXi a = 1 - a⁻¹ := by
      simpa [nuXi] using hnu.2
    rw [hderiv_nu]
    exact (norm_one_sub_inv a ha0).1.2 hRH_a.1
  · intro hind s hs
    have hstrip := nontrivial_zero_mem_strip s hs.1 hs.2
    have hs0 : s ≠ 0 := by
      intro hzero
      subst s
      norm_num at hstrip
    have hxis : xi s = 0 := (xi_eq_zero_iff_nontrivial s hs0).mpr hs
    have hindzero : ∀ a : ℂ, a ≠ 0 → xi a = 0 →
        IsIndifferentFixedPoint (nu xi) a := by
      intro a ha hxia
      have hfix : nuXi a = a := by simp [nuXi, nu, hxia]
      simpa [nuXi] using hind a ha (.inl hxia) hfix
    have hxi_result := symmetric_indifferent_zero_simple xi
      (fun a => differentiable_xi.analyticAt a)
      xi_analyticOrderAt_ne_top xi_one_sub hindzero s hxis hstrip
    exact ⟨hxi_result.1, (deriv_xi_ne_zero_iff s hs).mp hxi_result.2⟩
