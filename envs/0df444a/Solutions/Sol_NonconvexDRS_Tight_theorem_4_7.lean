-- Prove2me | solution 1 for NonconvexDRS.Tight.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:03:11.833296+00:00
-- url     : https://prove2.me/submissions/f2ab3779-3686-4068-8f8e-744f460ed22c

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace RRAux_NonconvexDRS_Tight_theorem_4_7

open NonconvexDRS.Tight
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hasGrad (L : ℝ) (x : E) :
    HasGradientAt (fun x : E => L / 2 * ‖x‖ ^ 2) (L • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (L / 2)
  refine h.congr_fderiv ?_
  ext y
  simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  try ring

lemma grad_eq (L : ℝ) (x : E) : gradient (fun x : E => L / 2 * ‖x‖ ^ 2) x = L • x :=
  (hasGrad L x).gradient

lemma lsmooth (L : ℝ) (hL : 0 < L) : IsLSmooth (fun x : E => L / 2 * ‖x‖ ^ 2) L := by
  refine ⟨fun x => (hasGrad L x).differentiableAt, fun x y => ?_⟩
  rw [grad_eq, grad_eq, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hL]

lemma hypo (L σ : ℝ) (hσ : σ ≤ L) : IsHypoconvex (fun x : E => L / 2 * ‖x‖ ^ 2) σ := by
  have h1 : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have h2 := h1.smul (c := (L - σ) / 2) (by linarith)
  unfold IsHypoconvex
  refine h2.congr fun x _ => ?_
  simp only [smul_eq_mul]
  ring

/-- key identity for the prox of the quadratic -/
lemma quad_id (a : ℝ) (ha : a ≠ 0) (w s : E) :
    (a - 1) * ‖w‖ ^ 2 + ‖w - s‖ ^ 2 = a * ‖w - a⁻¹ • s‖ ^ 2 + (‖s‖ ^ 2 - a⁻¹ * ‖s‖ ^ 2) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp
  ring

lemma prox1 (L γ : ℝ) (hγ : 0 < γ) (hL : 0 < L) (s u : E)
    (hu : u ∈ proxSet (fun x => ((L / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) γ s) :
    u = (1 + γ * L)⁻¹ • s := by
  set a := 1 + γ * L with ha
  have hapos : 0 < a := by positivity
  have h := hu (a⁻¹ • s)
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have h' : (a - 1) * ‖u‖ ^ 2 + ‖u - s‖ ^ 2 ≤ (a - 1) * ‖a⁻¹ • s‖ ^ 2 + ‖a⁻¹ • s - s‖ ^ 2 := by
    have e : ∀ w : E, (a - 1) * ‖w‖ ^ 2 + ‖w - s‖ ^ 2
        = 2 * γ * (L / 2 * ‖w‖ ^ 2 + ‖w - s‖ ^ 2 / (2 * γ)) := by
      intro w; rw [ha]; field_simp; ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  rw [quad_id a hapos.ne', quad_id a hapos.ne', sub_self, norm_zero] at h'
  have h3 : a * ‖u - a⁻¹ • s‖ ^ 2 ≤ 0 := by nlinarith
  have h4 : ‖u - a⁻¹ • s‖ ^ 2 ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h5 : ‖u - a⁻¹ • s‖ = 0 := by nlinarith [norm_nonneg (u - a⁻¹ • s)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

lemma prox2 (S : Set E) (γ : ℝ) (hγ : 0 < γ) (x v e : E) (he : e ∈ S)
    (hS : ∀ y ∈ S, -y ∈ S)
    (hv : v ∈ proxSet (indic S) γ x) : v ∈ S ∧ 0 ≤ ⟪v, x⟫ := by
  have hvS : v ∈ S := by
    by_contra hc
    have h := hv e
    simp only [indic, hc, he, if_false, if_true, zero_add] at h
    rw [EReal.top_add_coe] at h
    exact absurd h (not_le.mpr (EReal.coe_lt_top _))
  refine ⟨hvS, ?_⟩
  have h := hv (-v)
  simp only [indic, hvS, hS v hvS, if_true, zero_add, EReal.coe_le_coe_iff] at h
  have h2 : ‖v - x‖ ^ 2 ≤ ‖-v - x‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h (le_of_lt (by positivity : (0:ℝ) < 2 * γ))
    rwa [mul_div_cancel₀ _ (by positivity), mul_div_cancel₀ _ (by positivity)] at this
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_neg, inner_neg_left] at h2
  linarith

lemma inner_nonpos (c x y : ℝ) (hc : c < 0) (h : 0 ≤ c * x) : x ≤ 0 := by nlinarith

lemma ge_one (t : ℝ) (ht : 0 ≤ t) (h : 1 ≤ t ^ 2) : 1 ≤ t := by nlinarith

lemma final (γ L lam : ℝ) (hγL : 1 < γ * L) (hlam : 0 < lam) (s u v s' : E)
    (hu : u = (1 + γ * L)⁻¹ • s) (hv1 : ‖v‖ = 1) (hvx : 0 ≤ ⟪v, (2 : ℕ) • u - s⟫)
    (hs : s' = s + lam • (v - u)) : lam ≤ ‖s - s'‖ := by
  have ha : (1 + γ * L) ≠ 0 := by linarith
  have hs2 : s = (1 + γ * L) • u := by rw [hu, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have h2 : (2 : ℕ) • u - s = (1 - γ * L) • u := by rw [hs2]; module
  rw [h2, inner_smul_right] at hvx
  have hvu : ⟪v, u⟫ ≤ 0 := inner_nonpos (1 - γ * L) _ 0 (by linarith) hvx
  have hn : 1 ≤ ‖v - u‖ ^ 2 := by
    rw [norm_sub_sq_real, hv1]; nlinarith [sq_nonneg ‖u‖]
  have hn' : 1 ≤ ‖v - u‖ := ge_one _ (norm_nonneg _) hn
  rw [hs, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  nlinarith

end RRAux_NonconvexDRS_Tight_theorem_4_7

open NonconvexDRS.Tight in
theorem solution (p : ℕ) (hp : 1 ≤ p) (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) :
    ∃ (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal),
      (IsLSmooth φ₁ L ∧ IsHypoconvex φ₁ σ) ∧
      (IsProper φ₂ ∧ LowerSemicontinuous φ₂) ∧
      (∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x) ∧
      ∀ (γ lam : ℝ), 1 < γ * L → 0 < lam →
        ∀ s u v : ℕ → EuclideanSpace ℝ (Fin p), IsDRSRun φ₁ φ₂ γ lam s u v →
          ¬ Tendsto (fun k => ‖s k - s (k + 1)‖) atTop (𝓝 0) := by
  open RRAux_NonconvexDRS_Tight_theorem_4_7 in
  set e : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single ⟨0, hp⟩ 1 with he_def
  have he1 : ‖e‖ = 1 := by simp [he_def]
  set S : Set (EuclideanSpace ℝ (Fin p)) := {e, -e} with hS_def
  have hSn : ∀ y ∈ S, ‖y‖ = 1 := by
    intro y hy
    rcases hy with rfl | rfl
    · exact he1
    · rw [norm_neg, he1]
  have hSneg : ∀ y ∈ S, -y ∈ S := by
    intro y hy
    rcases hy with rfl | rfl
    · exact Or.inr rfl
    · left; simp
  have heS : e ∈ S := Or.inl rfl
  refine ⟨fun x => L / 2 * ‖x‖ ^ 2, indic S, ⟨lsmooth L hL, hypo L σ hσ.2⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨fun x => ?_, ⟨e, ?_⟩⟩
    · unfold indic; split_ifs <;> simp
    · simp [indic, heS]
  · have hc : IsClosed S := by
      rw [hS_def]; exact (Set.Finite.insert _ (Set.finite_singleton _)).isClosed
    have : indic S = Set.indicator Sᶜ (fun _ => (⊤ : EReal)) := by
      funext x; by_cases hx : x ∈ S <;> simp [indic, hx]
    rw [this]
    exact hc.isOpen_compl.lowerSemicontinuous_indicator le_top
  · refine ⟨e, fun x => ?_⟩
    by_cases hx : x ∈ S
    · simp [indic, hx, heS, hSn x hx, he1]
    · simp only [indic, hx, if_false, EReal.coe_add_top]
      exact le_top
  · intro γ lam hγL hlam s u v hrun hT
    have hγ : 0 < γ := by
      by_contra hc; push Not at hc; nlinarith
    have key : ∀ k, lam ≤ ‖s k - s (k + 1)‖ := by
      intro k
      obtain ⟨hu, hv, hs⟩ := hrun k
      have hu' := prox1 L γ hγ hL (s k) (u k) hu
      obtain ⟨hvS, hvx⟩ := prox2 S γ hγ _ (v k) e heS hSneg hv
      exact final γ L lam hγL hlam (s k) (u k) (v k) (s (k + 1)) hu' (hSn _ hvS) hvx hs
    have := hT.eventually (gt_mem_nhds hlam)
    obtain ⟨k, hk⟩ := this.exists
    linarith [key k]

#print axioms solution
