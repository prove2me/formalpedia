-- Prove2me | solution 1 for MasulloRH.derivative_identity_continuation
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:03:28.976675+00:00
-- url     : https://prove2.me/submissions/5e49ad19-7840-4253-8205-da0562890aa1

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff
open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2)
    (hhol : ∀ s : ℂ, InTraceContinuationDomain α s →
      AnalyticAt ℂ (regularizedTraceRHS α) s)
    (hinit : ∀ s : ℂ, (3 / 2 : ℝ) < s.re →
      regularizedTraceRHS α s = zetaLogDeriv s)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    deriv riemannZeta s = regularizedTraceRHS α s * riemannZeta s := by
  set c : ℝ := 1 / 2 + α with hc
  have hc1 : c < 1 := by rw [hc]; linarith
  -- the domain
  set D : Set ℂ := {z : ℂ | c < z.re ∧ z ≠ 1} with hD
  have hDeq : D = {z : ℂ | InTraceContinuationDomain α z} := by
    ext z; simp [hD, InTraceContinuationDomain, hc]
  have hDopen : IsOpen D := by
    have h1 : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
    exact h1.inter h2
  -- the function
  set F : ℂ → ℂ := fun z => deriv riemannZeta z - regularizedTraceRHS α z * riemannZeta z
    with hF
  -- zeta is analytic on the open set {z ≠ 1}
  have hzetaAn : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn isOpen_ne]
    intro z hz
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ F D := by
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    have hzA : AnalyticAt ℂ riemannZeta z := hzetaAn z hz1
    have hH : AnalyticAt ℂ (regularizedTraceRHS α) z := hhol z ⟨by simpa [hc] using hz.1, hz1⟩
    exact hzA.deriv.sub (hH.mul hzA)
  -- preconnectedness of D via four convex pieces
  set U1 : Set ℂ := {z : ℂ | c < z.re ∧ 0 < z.im}
  set U2 : Set ℂ := {z : ℂ | c < z.re ∧ z.im < 0}
  set U3 : Set ℂ := {z : ℂ | 1 < z.re}
  set U4 : Set ℂ := {z : ℂ | c < z.re ∧ z.re < 1}
  have cvx1 : Convex ℝ U1 :=
    (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_gt 0)
  have cvx2 : Convex ℝ U2 :=
    (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_lt 0)
  have cvx3 : Convex ℝ U3 := convex_halfSpace_re_gt 1
  have cvx4 : Convex ℝ U4 :=
    (convex_halfSpace_re_gt c).inter (convex_halfSpace_re_lt 1)
  have hDunion : D = ((U3 ∪ U1) ∪ U2) ∪ U4 := by
    ext z
    simp only [hD, U1, U2, U3, U4, mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · left; right; exact ⟨hre, him⟩
      · rcases lt_trichotomy z.re 1 with hr | hr | hr
        · right; exact ⟨hre, hr⟩
        · exact absurd (Complex.ext (by simpa using hr) (by simpa using him)) hne
        · left; left; left; exact hr
      · left; left; right; exact ⟨hre, him⟩
    · rintro (((h | h) | h) | h)
      · refine ⟨by linarith, ?_⟩
        rintro rfl; simp at h
      · refine ⟨h.1, ?_⟩
        rintro rfl; simp at h
      · refine ⟨h.1, ?_⟩
        rintro rfl; simp at h
      · refine ⟨h.1, ?_⟩
        rintro rfl; simp at h
  have hDpre : IsPreconnected D := by
    rw [hDunion]
    have p13 : IsPreconnected (U3 ∪ U1) :=
      cvx3.isPreconnected.union (2 + Complex.I)
        (by norm_num [U3]) (by simp [U1]; linarith) cvx1.isPreconnected
    have p132 : IsPreconnected ((U3 ∪ U1) ∪ U2) :=
      p13.union (2 - Complex.I) (by left; norm_num [U3])
        (by simp [U2]; linarith) cvx2.isPreconnected
    refine p132.union (((c + 1) / 2 : ℝ) + Complex.I) ?_ ?_ cvx4.isPreconnected
    · left; right; simp [U1]; linarith
    · simp [U4]; constructor <;> linarith
  -- F vanishes near z₀ = 2
  have hz0 : (2 : ℂ) ∈ D := by
    refine ⟨by simp; linarith, by norm_num⟩
  have hFnear : F =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} := by simp; norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : (3 / 2 : ℝ) < z.re := hz
    have hne : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    simp only [hF, Pi.zero_apply, hinit z hz', zetaLogDeriv]
    field_simp
    ring
  have hEq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDpre hz0 hFnear
  have hsD : s ∈ D := by rw [hDeq]; exact hs
  have := hEq hsD
  simp only [hF, Pi.zero_apply] at this
  exact sub_eq_zero.mp this
