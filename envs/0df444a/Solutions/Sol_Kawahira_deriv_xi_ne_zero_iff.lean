-- Prove2me | solution 1 for Kawahira.deriv_xi_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:48:13.963078+00:00
-- url     : https://prove2.me/submissions/4663f56d-7b28-403b-9bfc-c5808d54102d

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip

open Complex Topology Filter Set
open Kawahira

theorem solution (s : ℂ) (hs : IsNontrivialZero s) :
    deriv xi s ≠ 0 ↔ deriv riemannZeta s ≠ 0 := by
  have hstrip := nontrivial_zero_mem_strip s hs.1 hs.2
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hstrip
  have hs1 : s ≠ 1 := by
    intro hone
    subst s
    norm_num at hstrip
  let u : ℂ → ℂ := fun z => z * (1 - z) / 2 * Gammaℝ z
  have hloc : xi =ᶠ[𝓝 s] fun z => u z * riemannZeta z := by
    have hpos : {z : ℂ | 0 < z.re} ∈ 𝓝 s := isOpen_re_gt 0 |>.mem_nhds hstrip.1
    have hne1 : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
      isOpen_compl_singleton.mem_nhds (by simpa)
    filter_upwards [hpos, hne1] with z hzpos hz1
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      norm_num at hzpos
    have hz1' : z ≠ 1 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz1
    have hG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hzpos
    rw [xi_eq_completed z hz0 hz1', riemannZeta_def_of_ne_zero hz0]
    dsimp [u]
    field_simp
  have hGamma : DifferentiableAt ℂ Gammaℝ s := by
    change DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    · apply (differentiableAt_Gamma (s / 2) ?_).comp s
        ((hasDerivAt_id s).div_const 2).differentiableAt
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num at hre
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
  have hu : DifferentiableAt ℂ u s := by
    dsimp [u]
    fun_prop
  have hzeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hderiv : deriv xi s = u s * deriv riemannZeta s := by
    rw [hloc.deriv_eq]
    change deriv (u * riemannZeta) s = u s * deriv riemannZeta s
    rw [(hu.hasDerivAt.mul hzeta.hasDerivAt).deriv, hs.1]
    ring
  have hu0 : u s ≠ 0 := by
    dsimp [u]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) two_ne_zero)
      (Gammaℝ_ne_zero_of_re_pos hstrip.1)
  rw [hderiv, mul_ne_zero_iff]
  simp [hu0]
