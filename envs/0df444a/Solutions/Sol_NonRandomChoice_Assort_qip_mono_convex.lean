-- Prove2me | solution 1 for NonRandomChoice.Assort.qip_mono_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:05:54.661233+00:00
-- url     : https://prove2.me/submissions/3b375af4-e0d6-4a2f-96c6-68ea2dcf9a19

import Mathlib
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NRCAux
open NonRandomChoice.Assort

noncomputable def K (y : ℝ) : ℝ := ∫ s in (0:ℝ)..1, y ^ s

lemma K_eq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    K y = (1 - y) / (-Real.log y) := by
  have hL : Real.log y ≠ 0 := (Real.log_neg hy0 hy1).ne
  have h1 : ∀ s : ℝ, y ^ s = Real.exp (Real.log y * s) := fun s => Real.rpow_def_of_pos hy0 s
  unfold K
  simp_rw [h1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (Real.log y * s) / Real.log y)]
  · simp only [mul_one, mul_zero, Real.exp_zero, Real.exp_log hy0]
    field_simp
    ring
  · intro s _
    have := ((hasDerivAt_id s).const_mul (Real.log y)).exp.div_const (Real.log y)
    simp only [id, mul_one] at this
    rwa [mul_div_assoc, div_self hL, mul_one] at this
  · exact (by fun_prop : Continuous fun s => Real.exp (Real.log y * s)).intervalIntegrable _ _

lemma rpow_cont {y : ℝ} (hy : 0 < y) : Continuous fun s : ℝ => y ^ s :=
  continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')

lemma K_concave : ConcaveOn ℝ (Set.Ioi 0) K := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (0:ℝ) < x := hx
  have hy' : (0:ℝ) < y := hy
  simp only [smul_eq_mul]
  unfold K
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on zero_le_one
    · exact (((rpow_cont hx').const_mul a).add ((rpow_cont hy').const_mul b)).intervalIntegrable _ _
    · have : 0 < a * x + b * y := by
        rcases ha.lt_or_eq with ha | ha
        · nlinarith
        · subst ha; simp at hab; subst hab; simpa using hy'
      exact (rpow_cont this).intervalIntegrable _ _
    · intro s hs
      have := (Real.concaveOn_rpow hs.1 hs.2).2 (Set.mem_Ici.2 hx'.le) (Set.mem_Ici.2 hy'.le) ha hb hab
      simpa [smul_eq_mul] using this
  · exact ((rpow_cont hx').const_mul a).intervalIntegrable _ _
  · exact ((rpow_cont hy').const_mul b).intervalIntegrable _ _

lemma K_strictMono : StrictMonoOn K (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) < x := hx
  have hy' : (0:ℝ) < y := hy
  unfold K
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    (rpow_cont hx').continuousOn (rpow_cont hy').continuousOn
  · intro s hs
    exact Real.rpow_le_rpow hx'.le hxy.le hs.1.le
  · exact ⟨1, by simp, by simpa using hxy⟩

lemma q0_eq (Λ : ℝ) {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    qZeroOfQip Λ y = Λ * K y := by
  rw [K_eq hy.1 hy.2, qZeroOfQip, mul_div_assoc]

lemma q0_strictMono (Λ : ℝ) (hΛ : 0 < Λ) : StrictMonoOn (qZeroOfQip Λ) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  rw [q0_eq Λ hx, q0_eq Λ hy]
  exact mul_lt_mul_of_pos_left (K_strictMono hx.1 hy.1 hxy) hΛ

lemma q0_concave (Λ : ℝ) (hΛ : 0 < Λ) : ConcaveOn ℝ (Set.Ioo 0 1) (qZeroOfQip Λ) := by
  have h : ConcaveOn ℝ (Set.Ioo 0 1) (fun y => Λ * K y) :=
    ((K_concave.subset Set.Ioo_subset_Ioi_self (convex_Ioo 0 1)).smul hΛ.le)
  exact h.congr (fun y hy => (q0_eq Λ hy).symm)

lemma q0_contOn (Λ : ℝ) : ContinuousOn (qZeroOfQip Λ) (Set.Ioo 0 1) := by
  unfold qZeroOfQip
  apply ContinuousOn.div (by fun_prop)
  · exact (Real.continuousOn_log.mono (fun y hy => (ne_of_gt hy.1))).neg
  · intro y hy; exact neg_ne_zero.2 (Real.log_neg hy.1 hy.2).ne


lemma inv_convex (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ g : ℝ → ℝ, (∀ y ∈ Set.Ioo (0 : ℝ) 1, g (qZeroOfQip Λ y) = y) ∧
      MonotoneOn g (qZeroOfQip Λ '' Set.Ioo 0 1) ∧
      ConvexOn ℝ (qZeroOfQip Λ '' Set.Ioo 0 1) g := by
  set h := qZeroOfQip Λ
  have hsm : StrictMonoOn h (Set.Ioo 0 1) := q0_strictMono Λ hΛ
  have hinv : ∀ y ∈ Set.Ioo (0 : ℝ) 1, Function.invFunOn h (Set.Ioo 0 1) (h y) = y :=
    fun y hy => hsm.injOn.leftInvOn_invFunOn hy
  have hcvx : Convex ℝ (h '' Set.Ioo 0 1) :=
    Real.convex_iff_isPreconnected.2 (isPreconnected_Ioo.image _ (q0_contOn Λ))
  refine ⟨Function.invFunOn h (Set.Ioo 0 1), hinv, ?_, hcvx, ?_⟩
  · rintro _ ⟨y1, hy1, rfl⟩ _ ⟨y2, hy2, rfl⟩ hle
    rw [hinv y1 hy1, hinv y2 hy2]
    by_contra hlt
    push Not at hlt
    exact absurd hle (not_le.2 (hsm hy2 hy1 hlt))
  · rintro _ ⟨y1, hy1, rfl⟩ _ ⟨y2, hy2, rfl⟩ a b ha hb hab
    have hmem := hcvx ⟨y1, hy1, rfl⟩ ⟨y2, hy2, rfl⟩ ha hb hab
    obtain ⟨y', hy', hy'eq⟩ := hmem
    rw [← hy'eq, hinv y' hy', hinv y1 hy1, hinv y2 hy2]
    have hy : a • y1 + b • y2 ∈ Set.Ioo (0:ℝ) 1 := convex_Ioo 0 1 hy1 hy2 ha hb hab
    have hc := (q0_concave Λ hΛ).2 hy1 hy2 ha hb hab
    by_contra hlt
    push Not at hlt
    have := hsm hy hy' hlt
    rw [hy'eq] at this
    exact absurd hc (not_le.2 this)

end NRCAux

open NonRandomChoice.Assort in
theorem solution (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ g : ℝ → ℝ, (∀ y ∈ Set.Ioo (0 : ℝ) 1, g (qZeroOfQip Λ y) = y) ∧
      MonotoneOn g (qZeroOfQip Λ '' Set.Ioo 0 1) ∧
      ConvexOn ℝ (qZeroOfQip Λ '' Set.Ioo 0 1) g :=
  NRCAux.inv_convex Λ hΛ
