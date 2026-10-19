-- Prove2me | solution 1 for HunterPDE.Elliptic.smooth_slab_poincare
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:13:35.030985+00:00
-- url     : https://prove2.me/submissions/e039c2a3-89aa-4a16-83aa-512a26bbba83

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_H10

open MeasureTheory
open scoped ContDiff
lemma h41_sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 < L) :
    (∫ s in (-L)..0, f s) ^ 2 ≤ L * ∫ s in (-L)..0, f s ^ 2 := by
  set I := ∫ s in (-L)..0, f s
  set c := I / L
  have hnn : 0 ≤ ∫ s in (-L)..0, (f s - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun s _ => sq_nonneg _)
  have e : ∫ s in (-L)..0, (f s - c) ^ 2 =
      (∫ s in (-L)..0, f s ^ 2) - 2 * c * I + c ^ 2 * L := by
    have h1 : (fun s => (f s - c) ^ 2) = fun s => (f s ^ 2 - 2 * c * f s) + c ^ 2 := by
      funext s; ring
    rw [h1, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul]
    · simp; ring
    all_goals first
      | exact (hf.pow 2).intervalIntegrable _ _
      | exact (continuous_const.mul hf).intervalIntegrable _ _
      | exact ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _
  rw [e] at hnn
  have hc : c * L = I := by simp only [c]; field_simp
  have : I ^ 2 = L * (2 * c * I - c ^ 2 * L) := by
    rw [← hc]; ring
  nlinarith

lemma h41_point {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ) (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) {L : ℝ} (hL : 0 < L)
    (x : EuclideanSpace ℝ (Fin n)) (h0 : φ (x + (-L) • e) = 0)
    (hCS : ∀ f : ℝ → ℝ, Continuous f → (∫ s in (-L)..0, f s) ^ 2 ≤ L * ∫ s in (-L)..0, f s ^ 2) :
    φ x ^ 2 ≤ L * ∫ s in (-L)..0, ‖gradient φ (x + s • e)‖ ^ 2 := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hline : Continuous (fun s : ℝ => x + s • e) := by fun_prop
  set f : ℝ → ℝ := fun s => fderiv ℝ φ (x + s • e) e
  have hfc : Continuous f := by
    simp only [f]; exact (hcf.comp hline).clm_apply continuous_const
  have hderiv : ∀ s, HasDerivAt (fun s : ℝ => φ (x + s • e)) (f s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • e) e s := by
      simpa using ((hasDerivAt_id s).smul_const e).const_add x
    exact (hd (x + s • e)).hasFDerivAt.comp_hasDerivAt s h1
  have hftc : ∫ s in (-L)..0, f s = φ x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hfc.intervalIntegrable _ _)]
    have h0' : φ (x + -(L • e)) = 0 := by rwa [neg_smul] at h0
    simp [h0']
  have hbound : ∀ s, f s ^ 2 ≤ ‖gradient φ (x + s • e)‖ ^ 2 := by
    intro s
    have : |f s| ≤ ‖gradient φ (x + s • e)‖ := by
      have h := (fderiv ℝ φ (x + s • e)).le_opNorm e
      rw [he, mul_one] at h
      rw [← Real.norm_eq_abs]
      calc ‖f s‖ ≤ ‖fderiv ℝ φ (x + s • e)‖ := h
        _ = ‖gradient φ (x + s • e)‖ := by
          simp [gradient]
    have h2 := sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    simpa using h2
  have hgc : Continuous (fun s : ℝ => ‖gradient φ (x + s • e)‖ ^ 2) := by
    have : Continuous (gradient φ) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp hcf
    fun_prop
  calc φ x ^ 2 = (∫ s in (-L)..0, f s) ^ 2 := by rw [hftc]
    _ ≤ L * ∫ s in (-L)..0, f s ^ 2 := hCS f hfc
    _ ≤ L * ∫ s in (-L)..0, ‖gradient φ (x + s • e)‖ ^ 2 := by
      gcongr
      exact intervalIntegral.integral_mono_on (by linarith) ((hfc.pow 2).intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _) (fun s _ => hbound s)

lemma h41_prod_int {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : Continuous G) (hGc : HasCompactSupport G) (e : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    Integrable (Function.uncurry fun x (s : ℝ) => G (x + s • e))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume.restrict (Set.Ioc (-L) 0))) := by
  have hFc : Continuous (Function.uncurry fun x (s : ℝ) => G (x + s • e)) := by
    apply hG.comp; fun_prop
  rw [← Measure.restrict_univ (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))), Measure.prod_restrict]
  set K : Set (EuclideanSpace ℝ (Fin n) × ℝ) := (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.1 - p.2 • e, p.2)) '' (tsupport G ×ˢ Set.Icc (-L) 0)
  have hK : IsCompact K := (hGc.isCompact.prod isCompact_Icc).image (by fun_prop)
  have h1 : IntegrableOn (Function.uncurry fun x (s : ℝ) => G (x + s • e)) K
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) := hFc.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (Function.uncurry fun x (s : ℝ) => G (x + s • e)) (Set.univ ×ˢ Set.Icc (-L) 0)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) := by
    refine h1.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) ?_
    rintro ⟨x, s⟩ ⟨⟨-, hs⟩, hnot⟩
    simp only [Function.uncurry_apply_pair]
    by_contra hne
    apply hnot
    refine ⟨(x + s • e, s), ⟨subset_tsupport _ hne, hs⟩, ?_⟩
    simp
  exact h2.mono_set (Set.prod_mono le_rfl Set.Ioc_subset_Icc_self)

lemma h41_swap {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : Continuous G) (hGc : HasCompactSupport G) (e : EuclideanSpace ℝ (Fin n)) {L : ℝ}
    (hL : 0 < L) :
    Integrable (fun x => L * ∫ s in (-L)..0, G (x + s • e)) ∧
    ∫ x, L * ∫ s in (-L)..0, G (x + s • e) = L ^ 2 * ∫ x, G x := by
  have hI := h41_prod_int G hG hGc e L
  have hle : -L ≤ 0 := by linarith
  simp only [intervalIntegral.integral_of_le hle]
  refine ⟨(hI.integral_prod_left).const_mul L, ?_⟩
  rw [integral_const_mul, integral_integral_swap hI]
  simp only [integral_add_right_eq_self (fun x => G x)]
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hle, smul_eq_mul]
  ring

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (a b : ℝ)
    (hab : ∀ x ∈ Ω, a < inner ℝ x e ∧ inner ℝ x e < b)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x in Ω, φ x ^ 2 ≤ (b-a)^2 * ∫ x in Ω, ‖gradient φ x‖ ^ 2 := by
  have hsupp0 : ∀ x ∉ Ω, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  have hgrad0 : ∀ x ∉ Ω, gradient φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have hev : φ =ᶠ[nhds x] fun _ => (0:ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx'
    simp [gradient, hev.fderiv_eq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hsupp0 x hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hgrad0 x hx])]
  by_cases hL : 0 < b - a
  swap
  · have hφ0 : ∀ x, φ x = 0 := by
      intro x
      by_cases hx : x ∈ Ω
      · have := hab x hx; exact absurd (by linarith [this.1, this.2] : 0 < b - a) hL
      · exact hsupp0 x hx
    simp only [hφ0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun x => by positivity)
  set L := b - a with hLdef
  have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hgc : Continuous (gradient φ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp hcf
  have hGc : HasCompactSupport (fun x => ‖gradient φ x‖ ^ 2) := by
    apply HasCompactSupport.intro hc.isCompact
    intro x hx
    have hev : φ =ᶠ[nhds x] fun _ => (0:ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
    simp [gradient, hev.fderiv_eq]
  obtain ⟨hint, heq⟩ := h41_swap (fun x => ‖gradient φ x‖ ^ 2) (by fun_prop) hGc e hL
  have hpt : ∀ x, φ x ^ 2 ≤ L * ∫ s in (-L)..0, ‖gradient φ (x + s • e)‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ Ω
    · apply h41_point φ hφ e he hL x _ (fun f hf => h41_sq_integral_le hf hL)
      apply hsupp0
      intro hmem
      have h1 := (hab _ hmem).1
      have h2 := (hab x hx).2
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he] at h1
      linarith
    · rw [hsupp0 x hx]
      have : 0 ≤ ∫ s in (-L)..0, ‖gradient φ (x + s • e)‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) (fun s _ => by positivity)
      nlinarith
  calc ∫ x, φ x ^ 2 ≤ ∫ x, L * ∫ s in (-L)..0, ‖gradient φ (x + s • e)‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by positivity)) hint
          (Filter.Eventually.of_forall hpt)
    _ = L ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := heq

