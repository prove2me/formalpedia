-- Prove2me | solution 1 for MeasureTheory.contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/73f4d261-88b9-5329-ad2d-738ac0f99ea6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

namespace L1C9

open MeasureTheory Topology Filter

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β] [FiniteDimensional ℝ β]
  [MeasurableSpace β] [BorelSpace β]
  {α : Type} [MeasurableSpace α] (μ : Measure α)
  (π : α → β) (hπ : Measurable π)
  (h : α → ℂ) (hh : AEStronglyMeasurable h μ)
  (A : Set α) (hA : MeasurableSet A) (hμA : μ A < ⊤)
  (C : ℝ) (hhA : ∀ a ∈ A, ‖h a‖ ≤ C) (hh0 : ∀ a, a ∉ A → h a = 0)

noncomputable def dG (G : E × β → ℂ) (p : E × β) : E →L[ℝ] ℂ :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E β)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ β] [MeasurableSpace β] [BorelSpace β] in
theorem contDiff_dG {G : E × β → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dG G) :=
  ((contDiff_infty_iff_fderiv.1 hG).2).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ β] [MeasurableSpace β] [BorelSpace β] in
theorem hasCompactSupport_dG {G : E × β → ℂ} (hGc : HasCompactSupport G) : HasCompactSupport (dG G) := by
  have h1 : HasCompactSupport (fderiv ℝ G) := hGc.fderiv ℝ
  exact h1.comp_left (g := fun L : E × β →L[ℝ] ℂ => L.comp (ContinuousLinearMap.inl ℝ E β)) (by simp)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ β] [MeasurableSpace β] [BorelSpace β] in
theorem hasFDerivAt_G {G : E × β → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (x : E) (b : β) :
    HasFDerivAt (fun x : E => G (x, b)) (dG G (x, b)) x := by
  have hd : HasFDerivAt G (fderiv ℝ G (x, b)) (x, b) :=
    (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp x (hasFDerivAt_prodMk_left x b)

theorem exists_bound {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y] {f : X → Y}
    (hc : Continuous f) (hs : HasCompactSupport f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hc
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

include hπ hh hA hμA hhA hh0 in

theorem integrable_smul {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace ℂ Y]
    [SecondCountableTopology Y]
    {Φ : E × β → Y} (hΦc : Continuous Φ) {M : ℝ} (hM : ∀ p, ‖Φ p‖ ≤ M) (x : E) :
    Integrable (fun a => h a • Φ (x, π a)) μ ∧
      ∀ a, ‖h a • Φ (x, π a)‖ ≤ A.indicator (fun _ => max C 0 * max M 0) a := by
  have hmeas : AEStronglyMeasurable (fun a => h a • Φ (x, π a)) μ :=
    hh.smul ((hΦc.comp (continuous_const.prodMk continuous_id) :
      Continuous fun b : β => Φ (x, b)).stronglyMeasurable.comp_measurable hπ).aestronglyMeasurable
  have hbound : ∀ a, ‖h a • Φ (x, π a)‖ ≤ A.indicator (fun _ => max C 0 * max M 0) a := by
    intro a
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha, norm_smul]
      exact mul_le_mul ((hhA a ha).trans (le_max_left _ _)) ((hM _).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
    · rw [Set.indicator_of_notMem ha, hh0 a ha, zero_smul, norm_zero]
  have hint : Integrable (A.indicator fun _ => max C 0 * max M 0) μ :=
    (integrableOn_const hμA.ne).integrable_indicator hA
  exact ⟨hint.mono' hmeas (Eventually.of_forall hbound), hbound⟩

include hπ hh hA hμA hhA hh0 in

theorem hasFDerivAt_integral {G : E × β → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hGc : HasCompactSupport G) (x₀ : E) :
    HasFDerivAt (fun x : E => ∫ a, h a * G (x, π a) ∂μ) (∫ a, h a • dG G (x₀, π a) ∂μ) x₀ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound hG.continuous hGc
  obtain ⟨M', hM0', hM'⟩ := exists_bound (contDiff_dG hG).continuous (hasCompactSupport_dG hGc)
  have h1 := fun x => integrable_smul μ π hπ h hh A hA hμA C hhA hh0 (Y := ℂ) hG.continuous hM x
  have h2 := fun x => integrable_smul μ π hπ h hh A hA hμA C hhA hh0 (Y := E →L[ℝ] ℂ)
    (contDiff_dG hG).continuous hM' x
  have e : (fun x : E => ∫ a, h a * G (x, π a) ∂μ) = fun x : E => ∫ a, h a • G (x, π a) ∂μ := by
    simp only [smul_eq_mul]
  rw [e]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := A.indicator fun _ => max C 0 * max M' 0)
    Filter.univ_mem (Eventually.of_forall fun x => (h1 x).1.aestronglyMeasurable) (h1 x₀).1
    (h2 x₀).1.aestronglyMeasurable (Eventually.of_forall fun a x _ => (h2 x).2 a)
    ((integrableOn_const hμA.ne).integrable_indicator hA)
    (Eventually.of_forall fun a x _ => ?_)
  exact (hasFDerivAt_G hG x (π a)).const_smul (h a)

include hπ hh hA hμA hhA hh0 in
theorem contDiff_nat : ∀ (n : ℕ) (G : E × β → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → HasCompactSupport G →
    ContDiff ℝ (n : WithTop ℕ∞) (fun x : E => ∫ a, h a * G (x, π a) ∂μ) := by
  intro n
  induction n with
  | zero =>
    intro G hG hGc
    rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_integral μ π hπ h hh A hA hμA C hhA hh0 hG hGc x).continuousAt
  | succ n ih =>
    intro G hG hGc
    have hD := fun x => hasFDerivAt_integral μ π hπ h hh A hA hμA C hhA hh0 hG hGc x
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hD x).differentiableAt, fun hn => absurd hn (by simp), ?_⟩
    have efd : fderiv ℝ (fun x : E => ∫ a, h a * G (x, π a) ∂μ) = fun x => ∫ a, h a • dG G (x, π a) ∂μ :=
      funext fun x => (hD x).fderiv
    rw [efd, contDiff_clm_apply_iff]
    intro y

    obtain ⟨M', hM0', hM'⟩ := exists_bound (contDiff_dG hG).continuous (hasCompactSupport_dG hGc)
    have h2 := fun x => integrable_smul μ π hπ h hh A hA hμA C hhA hh0 (Y := E →L[ℝ] ℂ)
      (contDiff_dG hG).continuous hM' x
    have e2 : (fun x : E => (∫ a, h a • dG G (x, π a) ∂μ) y) = fun x => ∫ a, h a * dG G (x, π a) y ∂μ := by
      funext x
      rw [ContinuousLinearMap.integral_apply (h2 x).1 y]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [e2]
    exact ih (fun p => dG G p y) ((contDiff_dG hG).clm_apply contDiff_const)
      ((hasCompactSupport_dG hGc).comp_left (g := fun L : E →L[ℝ] ℂ => L y) (by simp))

end L1C9

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β] [FiniteDimensional ℝ β]
    [MeasurableSpace β] [BorelSpace β]
    {α : Type} [MeasurableSpace α] (μ : Measure α)
    (G : E × β → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (π : α → β) (hπ : Measurable π)
    (h : α → ℂ) (hh : AEStronglyMeasurable h μ)
    (A : Set α) (hA : MeasurableSet A) (hμA : μ A < ⊤)
    (C : ℝ) (hhA : ∀ a ∈ A, ‖h a‖ ≤ C) (hh0 : ∀ a, a ∉ A → h a = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    HasCompactSupport (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    ∀ x : E, x ∉ Prod.fst '' tsupport G → (∫ a, h a * G (x, π a) ∂μ) = 0  := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ∫ a, h a * G (x, π a) ∂μ) :=
    contDiff_infty.2 fun n => L1C9.contDiff_nat μ π hπ h hh A hA hμA C hhA hh0 n G hG hGc
  have hzero : ∀ x : E, x ∉ Prod.fst '' tsupport G → (∫ a, h a * G (x, π a) ∂μ) = 0 := by
    intro x hx
    have h0 : ∀ b : β, G (x, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport fun hm => hx ⟨(x, b), hm, rfl⟩
    simp only [h0, mul_zero, integral_zero]
  refine ⟨hcd, ?_, hzero⟩
  exact HasCompactSupport.intro (hGc.image continuous_fst) hzero

end S_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport (solution)
