-- Prove2me | solution 1 for NonconvexDRS.ImageSmooth.theorem_5_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T21:17:31.051453+00:00
-- url     : https://prove2.me/submissions/a032fa75-175e-47d8-be05-153630a474d9

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

set_option autoImplicit false

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace ImgSm513

section generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hasGradientAt_of_sandwich (F : E → ℝ) (y : E → E) (C : ℝ)
    (h : ∀ s d, |F (s + d) - F s - ⟪y s, d⟫_ℝ| ≤ C * ‖d‖ ^ 2) (s : E) :
    HasGradientAt F (y s) s := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have h1 : (fun d : E => F (s + d) - F s - ⟪y s, d⟫_ℝ) =O[nhds 0] (fun d : E => ‖d‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    exact h s d
  exact h1.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))

/-- convexity from a global lower first-order bound -/
lemma convexOn_of_lower (F : E → ℝ) (y : E → E) (σ : ℝ)
    (hlo : ∀ s d, σ / 2 * ‖d‖ ^ 2 ≤ F (s + d) - F s - ⟪y s, d⟫_ℝ) :
    ConvexOn ℝ Set.univ (fun x => F x - σ / 2 * ‖x‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  set w := a • x + (1 - a) • z with hw
  have h1 := hlo w (x - w)
  have h2 := hlo w (z - w)
  rw [add_sub_cancel] at h1 h2
  have hx : x - w = (1 - a) • (x - z) := by rw [hw]; module
  have hz : z - w = (-a) • (x - z) := by rw [hw]; module
  rw [hx, norm_smul, inner_smul_right] at h1
  rw [hz, norm_smul, inner_smul_right] at h2
  have hn : ‖w‖ ^ 2 = ‖a • x + (1 - a) • z‖ ^ 2 := by rw [hw]
  have e1 : ‖a • x + (1 - a) • z‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 + 2 * a * (1 - a) * ⟪x, z⟫_ℝ
      + (1 - a) ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
    simp only [Real.norm_eq_abs, conj_trivial, mul_pow, sq_abs]
    ring
  have e2 : ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, z⟫_ℝ + ‖z‖ ^ 2 := norm_sub_sq_real x z
  simp only [Real.norm_eq_abs, mul_pow, sq_abs] at h1 h2
  rw [e2] at h1 h2
  simp only [smul_eq_mul]
  rw [e1]
  nlinarith [h1, h2, mul_nonneg ha hb]

/-- Lipschitz gradient from a two-sided quadratic sandwich (co-coercivity argument). -/
lemma lip_of_sandwich (F : E → ℝ) (y : E → E) (σ L : ℝ) (hσL : -L ≤ σ)
    (hlo : ∀ s d, σ / 2 * ‖d‖ ^ 2 ≤ F (s + d) - F s - ⟪y s, d⟫_ℝ)
    (hup : ∀ s d, F (s + d) - F s - ⟪y s, d⟫_ℝ ≤ L / 2 * ‖d‖ ^ 2) :
    ∀ s t, ‖y s - y t‖ ≤ L * ‖s - t‖ := by
  by_cases hne : ∃ d : E, d ≠ 0
  · obtain ⟨d0, hd0⟩ := hne
    have hσL' : σ ≤ L := by
      have := (hlo 0 d0).trans (hup 0 d0)
      have hp : 0 < ‖d0‖ ^ 2 := by positivity
      nlinarith
    have hL : 0 ≤ L := by linarith
    -- g = F - σ/2‖·‖², h = y - σ • id, K = L - σ
    set K := L - σ with hK
    have gsand : ∀ s d, 0 ≤ (F (s + d) - σ / 2 * ‖s + d‖ ^ 2) - (F s - σ / 2 * ‖s‖ ^ 2)
          - ⟪y s - σ • s, d⟫_ℝ ∧
        (F (s + d) - σ / 2 * ‖s + d‖ ^ 2) - (F s - σ / 2 * ‖s‖ ^ 2)
          - ⟪y s - σ • s, d⟫_ℝ ≤ K / 2 * ‖d‖ ^ 2 := by
      intro s d
      have e : ‖s + d‖ ^ 2 = ‖s‖ ^ 2 + 2 * ⟪s, d⟫_ℝ + ‖d‖ ^ 2 := norm_add_sq_real s d
      rw [inner_sub_left, real_inner_smul_left, e]
      constructor <;> nlinarith [hlo s d, hup s d]
    -- co-coercivity: for any δ
    have step : ∀ s t δ, (F s - σ / 2 * ‖s‖ ^ 2) + ⟪y s - σ • s, (t - s) + δ⟫_ℝ
        ≤ (F t - σ / 2 * ‖t‖ ^ 2) + ⟪y t - σ • t, δ⟫_ℝ + K / 2 * ‖δ‖ ^ 2 := by
      intro s t δ
      have h1 := (gsand s ((t - s) + δ)).1
      have h2 := (gsand t δ).2
      have e : s + ((t - s) + δ) = t + δ := by abel
      rw [e] at h1
      linarith
    intro s t
    set w := (y t - σ • t) - (y s - σ • s) with hw
    set e := t - s with he
    have hwe_up : ⟪w, e⟫_ℝ ≤ K * ‖e‖ ^ 2 := by
      have h1 := (gsand s e).2
      have h2 := (gsand t (-e)).2
      have e1 : s + e = t := by rw [he]; abel
      have e2 : t + -e = s := by rw [he]; abel
      rw [e1] at h1
      rw [e2, norm_neg, inner_neg_right] at h2
      rw [hw, inner_sub_left]
      linarith
    have hwe_lo : 0 ≤ ⟪w, e⟫_ℝ := by
      have h1 := (gsand s e).1
      have h2 := (gsand t (-e)).1
      have e1 : s + e = t := by rw [he]; abel
      have e2 : t + -e = s := by rw [he]; abel
      rw [e1] at h1
      rw [e2, inner_neg_right] at h2
      rw [hw, inner_sub_left]
      linarith
    have cocoer : ∀ c : ℝ, 0 < c → c * K ≤ 1 → c * ‖w‖ ^ 2 ≤ ⟪w, e⟫_ℝ := by
      intro c hc hcK
      have h1 := step s t (-(c • w))
      have h2 := step t s (c • w)
      rw [inner_add_right, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
        inner_neg_right, inner_smul_right] at h1
      rw [inner_add_right, inner_smul_right, norm_smul, inner_smul_right] at h2
      have ht : t - s = e := rfl
      have hst : s - t = -e := by rw [he]; abel
      rw [ht] at h1
      rw [hst, inner_neg_right] at h2
      have ew : ⟪y t - σ • t, w⟫_ℝ - ⟪y s - σ • s, w⟫_ℝ = ‖w‖ ^ 2 := by
        rw [← inner_sub_left, ← hw, real_inner_self_eq_norm_sq]
      have ee : ⟪y t - σ • t, e⟫_ℝ - ⟪y s - σ • s, e⟫_ℝ = ⟪w, e⟫_ℝ := by
        rw [← inner_sub_left, ← hw]
      simp only [Real.norm_eq_abs, mul_pow, sq_abs] at h1 h2
      have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
      have : c * ‖w‖ ^ 2 * (c * K) ≤ c * ‖w‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hcK (by positivity : 0 ≤ c * ‖w‖ ^ 2)
        linarith
      nlinarith
    have key : ‖w‖ ^ 2 ≤ K * ⟪w, e⟫_ℝ := by
      rcases eq_or_lt_of_le (show 0 ≤ K by rw [hK]; linarith) with hK0 | hKpos
      · have := cocoer 1 one_pos (by rw [← hK0]; norm_num)
        rw [← hK0] at hwe_up ⊢
        nlinarith
      · have := cocoer (1 / K) (by positivity) (by field_simp; rfl)
        have h2 : K * (1 / K * ‖w‖ ^ 2) = ‖w‖ ^ 2 := by field_simp
        nlinarith
    have hyd : y t - y s = w + σ • e := by rw [hw, he, smul_sub]; abel
    have hsq : ‖y t - y s‖ ^ 2 ≤ (L * ‖e‖) ^ 2 := by
      rw [hyd, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
      have h3 : (L + σ) * ⟪w, e⟫_ℝ ≤ (L + σ) * (K * ‖e‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hwe_up (by linarith)
      rw [hK] at h3 key
      nlinarith
    have hsq' : ‖y s - y t‖ ≤ L * ‖s - t‖ := by
      rw [norm_sub_rev (y s), norm_sub_rev s]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    exact hsq'
  · simp only [not_exists, not_not] at hne
    intro s t
    rw [hne (y s - y t), hne (s - t)]
    simp

lemma hasDerivAt_line (f : E → ℝ) (hf : Differentiable ℝ f) (x d : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪gradient f (x + t • d), d⟫_ℝ t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := (hf (x + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  exact this.congr_deriv (by rw [InnerProductSpace.toDual_apply_apply])

lemma descent (f : E → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x d : E) :
    f (x + d) - f x - ⟪gradient f x, d⟫_ℝ ≤ L / 2 * ‖d‖ ^ 2 := by
  let φ : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪gradient f x, d⟫_ℝ - L / 2 * t ^ 2 * ‖d‖ ^ 2
  have hφ : ∀ t, HasDerivAt φ (⟪gradient f (x + t • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ
      - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := hasDerivAt_line f hf x d t
    have h2 := (hasDerivAt_id t).mul_const ⟪gradient f x, d⟫_ℝ
    have h3 := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
    exact ((h1.sub h2).sub h3).congr_deriv (by
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; simp only [id, one_mul]; push_cast; ring)
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφ t).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      have hb := hL (x + t • d) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
      have hc : ⟪gradient f (x + t • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ
          ≤ ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ := by
        rw [← inner_sub_left]; exact real_inner_le_norm _ _
      have := mul_le_mul_of_nonneg_right hb (norm_nonneg d)
      nlinarith
  have h := hanti (show (0:ℝ) ∈ Set.Ici 0 by norm_num) (show (1:ℝ) ∈ Set.Ici 0 by norm_num) zero_le_one
  simp only [φ, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
  linarith

lemma hypo_lower (f : E → ℝ) (σ : ℝ) (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ (fun x => f x - σ / 2 * ‖x‖ ^ 2)) (x d : E) :
    σ / 2 * ‖d‖ ^ 2 ≤ f (x + d) - f x - ⟪gradient f x, d⟫_ℝ := by
  have hEq : ∀ t : ℝ, ‖x + t • d‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * ⟪x, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2 := by
    intro t
    rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  let ψ : ℝ → ℝ := fun t => f (x + t • d) - σ / 2 * (‖x‖ ^ 2 + 2 * t * ⟪x, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2)
  have hψc : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have h := hc.2 (Set.mem_univ (x + s • d)) (Set.mem_univ (x + t • d)) ha hb hab
    have e : a • (x + s • d) + b • (x + t • d) = x + (a • s + b • t) • d := by
      obtain rfl : b = 1 - a := by linarith
      simp only [smul_eq_mul]
      module
    simp only [smul_eq_mul] at h ⊢
    rw [e] at h
    simp only [ψ]
    rw [← hEq, ← hEq, ← hEq]
    exact h
  have hd : HasDerivAt ψ (⟪gradient f (x + (0:ℝ) • d), d⟫_ℝ
      - σ / 2 * (2 * ⟪x, d⟫_ℝ + 2 * 0 * ‖d‖ ^ 2)) 0 := by
    have h1 := hasDerivAt_line f hf x d 0
    have h2 : HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + 2 * t * ⟪x, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2)
        (2 * ⟪x, d⟫_ℝ + 2 * 0 * ‖d‖ ^ 2) 0 := by
      have a1 := ((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ⟪x, d⟫_ℝ
      have a2 := (hasDerivAt_pow 2 (0:ℝ)).mul_const (‖d‖ ^ 2)
      exact ((a1.const_add (‖x‖ ^ 2)).add a2).congr_deriv (by norm_num [id])
    exact h1.sub (h2.const_mul (σ / 2))
  have hs := hψc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at hs
  simp only [ψ, zero_smul, add_zero, one_smul, mul_zero, zero_mul, sub_zero, div_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow, mul_one] at hs
  linarith

/-- quadratic sandwich for `F` with slopes `y` gives image smoothness -/
lemma lip_grad_of_sandwich (F : E → ℝ) (y : E → E) (σc σl L : ℝ) (hσL : -L ≤ σl)
    (hloc : ∀ s d, σc / 2 * ‖d‖ ^ 2 ≤ F (s + d) - F s - ⟪y s, d⟫_ℝ)
    (hlol : ∀ s d, σl / 2 * ‖d‖ ^ 2 ≤ F (s + d) - F s - ⟪y s, d⟫_ℝ)
    (hup : ∀ s d, F (s + d) - F s - ⟪y s, d⟫_ℝ ≤ L / 2 * ‖d‖ ^ 2) :
    (Differentiable ℝ F ∧ ∀ s t, ‖gradient F s - gradient F t‖ ≤ L * ‖s - t‖) ∧
      ConvexOn ℝ Set.univ (fun x => F x - σc / 2 * ‖x‖ ^ 2) := by
  have hg : ∀ s, HasGradientAt F (y s) s := hasGradientAt_of_sandwich F y ((|σl| + |L|) / 2)
    (fun s d => by
      have a1 := mul_nonneg (by linarith [neg_abs_le σl] : 0 ≤ σl + |σl|) (sq_nonneg ‖d‖)
      have a2 := mul_nonneg (abs_nonneg L) (sq_nonneg ‖d‖)
      have a3 := mul_nonneg (by linarith [le_abs_self L] : 0 ≤ |L| - L) (sq_nonneg ‖d‖)
      have a4 := mul_nonneg (abs_nonneg σl) (sq_nonneg ‖d‖)
      rw [abs_le]; constructor <;> nlinarith [hlol s d, hup s d])
  refine ⟨⟨fun s => (hg s).hasFDerivAt.differentiableAt, fun s t => ?_⟩,
    convexOn_of_lower F y σc hloc⟩
  rw [(hg s).gradient, (hg t).gradient]
  exact lip_of_sandwich F y σl L hσL hlol hup s t

end generic

section euclid

variable {n p : ℕ}

lemma grad_mem_range (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f) (x : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ x', A x' = A x → f x ≤ f x') :
    ∃ y, ContinuousLinearMap.adjoint A y = gradient f x := by
  have hker : ∀ v, A v = 0 → ⟪gradient f x, v⟫_ℝ = 0 := by
    intro v hv
    have hloc : IsLocalMin (fun t : ℝ => f (x + t • v)) 0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [zero_smul, add_zero]
      apply hmin
      rw [map_add, map_smul, hv, smul_zero, add_zero]
    have := hloc.hasDerivAt_eq_zero (hasDerivAt_line f hf x v 0)
    simpa using this
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ContinuousLinearMap.adjoint A).range
  have hK : Kᗮ = A.ker := by
    have := ContinuousLinearMap.orthogonal_range (ContinuousLinearMap.adjoint A)
    rw [ContinuousLinearMap.adjoint_adjoint] at this
    exact this
  have hmem : gradient f x ∈ Kᗮᗮ := by
    rw [hK, Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact hker v (by simpa using hv)
  rw [Submodule.orthogonal_orthogonal] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

lemma exists_min_fiber (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : Function.Surjective A) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (s : EuclideanSpace ℝ (Fin p)) : ∃ x, A x = s ∧ ∀ x', A x' = s → f x ≤ f x' := by
  obtain ⟨β, -, hb⟩ := hlev
  obtain ⟨x0, hx0⟩ := hA s
  set S := {x | A x = s} ∩ f ⁻¹' Set.Iic (f x0) with hS
  have hSb : Bornology.IsBounded S := by
    refine (hb s (f x0)).subset ?_
    rintro x ⟨hx1, hx2⟩
    simp only [Set.mem_setOf_eq] at hx1 ⊢
    simp only [Set.mem_preimage, Set.mem_Iic] at hx2
    rw [hx1, sub_self, norm_zero]; simpa using hx2
  have hSc : IsClosed S :=
    (isClosed_eq A.continuous continuous_const).inter (hf.isClosed_preimage (f x0))
  have hSk : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSc hSb
  obtain ⟨x, hxS, hxmin⟩ :=
    (hf.lowerSemicontinuousOn S).exists_isMinOn (show S.Nonempty from ⟨x0, hx0, le_refl (f x0)⟩) hSk
  refine ⟨x, hxS.1, fun x' hx' => ?_⟩
  by_cases h : f x' ≤ f x0
  · exact hxmin ⟨hx', h⟩
  · exact le_trans hxS.2 (le_of_lt (not_le.1 h))

lemma imageFn_eq (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin n)) (hx : A x = s) (hmin : ∀ x', A x' = s → f x ≤ f x') :
    NonconvexDRS.ImageSmooth.imageFn A (fun x => (f x : EReal)) s = (f x : EReal) := by
  unfold NonconvexDRS.ImageSmooth.imageFn
  apply le_antisymm
  · exact iInf₂_le x hx
  · exact le_iInf₂ fun x' hx' => EReal.coe_le_coe (hmin x' hx')

lemma divnorm_aux (σf a b N : ℝ) (hσ : 0 ≤ σf) (h : a ≤ N ^ 2 * b) (hb : 0 ≤ b) :
    σf / N ^ 2 * a ≤ σf * b := by
  rcases eq_or_ne N 0 with hN | hN
  · rw [hN, show (0:ℝ) ^ 2 = 0 by norm_num, div_zero, zero_mul]
    exact mul_nonneg hσ hb
  · have hN2 : 0 < N ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hN2]
    have := mul_le_mul_of_nonneg_left h hσ
    nlinarith

lemma part2 (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (Lf σf M : ℝ)
    (hfL : NonconvexDRS.DRS.IsLSmooth f Lf) (hfh : NonconvexDRS.DRS.IsHypoconvex f σf)
    (h1 : -Lf ≤ σf) (h2 : σf ≤ Lf)
    (X : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n))
    (hX1 : ∀ s, A (X s) = s ∧ ∀ x, A x = s → f (X s) ≤ f x)
    (hXL : ∀ s s', ‖X s - X s'‖ ≤ M * ‖s - s'‖) :
    NonconvexDRS.ImageSmooth.IsImageSmooth A f (Lf * M ^ 2)
      (if 0 ≤ σf then σf / ‖A‖ ^ 2 else σf * M ^ 2) := by
  have hy : ∀ s, ∃ y, ContinuousLinearMap.adjoint A y = gradient f (X s) := fun s =>
    grad_mem_range A f hfL.1 (X s) (fun x' hx' => (hX1 s).2 x' (by rw [hx', (hX1 s).1]))
  choose y hy using hy
  have hLf : 0 ≤ Lf := by linarith
  have hAX : ∀ s d, A (X (s + d) - X s) = d := fun s d => by
    rw [map_sub, (hX1 _).1, (hX1 _).1, add_sub_cancel_left]
  have hin : ∀ s d, ⟪y s, d⟫_ℝ = ⟪gradient f (X s), X (s + d) - X s⟫_ℝ := by
    intro s d
    rw [← hy s, ContinuousLinearMap.adjoint_inner_left, hAX]
  have hex : ∀ s d, f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ
      = f (X s + (X (s + d) - X s)) - f (X s) - ⟪gradient f (X s), X (s + d) - X s⟫_ℝ := by
    intro s d; rw [hin, add_sub_cancel]
  have hdx : ∀ s d, ‖X (s + d) - X s‖ ≤ M * ‖d‖ := fun s d => by
    simpa using hXL (s + d) s
  have hdxA : ∀ s d, ‖d‖ ≤ ‖A‖ * ‖X (s + d) - X s‖ := by
    intro s d
    calc ‖d‖ = ‖A (X (s + d) - X s)‖ := by rw [hAX]
      _ ≤ ‖A‖ * ‖X (s + d) - X s‖ := A.le_opNorm _
  have hsq : ∀ s d, ‖X (s + d) - X s‖ ^ 2 ≤ M ^ 2 * ‖d‖ ^ 2 := fun s d => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hdx s d) 2
  have hsqA : ∀ s d, ‖d‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖X (s + d) - X s‖ ^ 2 := fun s d => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hdxA s d) 2
  set σ' := (if 0 ≤ σf then σf / ‖A‖ ^ 2 else σf * M ^ 2) with hσ'
  have hup : ∀ s d, (fun s => f (X s)) (s + d) - (fun s => f (X s)) s - ⟪y s, d⟫_ℝ
      ≤ Lf * M ^ 2 / 2 * ‖d‖ ^ 2 := by
    intro s d
    show f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ ≤ _
    rw [hex]
    have := descent f Lf hfL.1 hfL.2 (X s) (X (s + d) - X s)
    have := mul_le_mul_of_nonneg_left (hsq s d) hLf
    nlinarith
  have hlo : ∀ s d, σ' / 2 * ‖d‖ ^ 2
      ≤ (fun s => f (X s)) (s + d) - (fun s => f (X s)) s - ⟪y s, d⟫_ℝ := by
    intro s d
    show _ ≤ f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ
    rw [hex]
    have hl := hypo_lower f σf hfL.1 hfh (X s) (X (s + d) - X s)
    have key : σ' * ‖d‖ ^ 2 ≤ σf * ‖X (s + d) - X s‖ ^ 2 := by
      rw [hσ']
      split_ifs with hσ
      · exact divnorm_aux σf _ _ ‖A‖ hσ (hsqA s d) (sq_nonneg _)
      · have := mul_le_mul_of_nonpos_left (hsq s d) (le_of_lt (not_le.1 hσ))
        nlinarith
    nlinarith
  have hσL : -(Lf * M ^ 2) ≤ σ' := by
    rw [hσ']
    split_ifs with hσ
    · have : 0 ≤ σf / ‖A‖ ^ 2 := by positivity
      nlinarith [sq_nonneg M]
    · nlinarith [sq_nonneg M]
  obtain ⟨hsm, hcv⟩ :=
    lip_grad_of_sandwich (fun s => f (X s)) y σ' σ' (Lf * M ^ 2) hσL hlo hlo hup
  exact ⟨fun s => f (X s), fun s => imageFn_eq A f s (X s) (hX1 s).1 (hX1 s).2, hsm, hcv⟩

lemma part3 (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (Lf σf c : ℝ) (hconv : ConvexOn ℝ Set.univ f) (hfL : NonconvexDRS.DRS.IsLSmooth f Lf)
    (hfh : NonconvexDRS.DRS.IsHypoconvex f σf) (h1 : -Lf ≤ σf) (h2 : σf ≤ Lf)
    (hc : IsLeast {t | ∃ y : EuclideanSpace ℝ (Fin p), ‖y‖ = 1 ∧
        t = ‖ContinuousLinearMap.adjoint A y‖ ^ 2} c) :
    NonconvexDRS.ImageSmooth.IsImageSmooth A f (Lf / c) (σf / ‖A‖ ^ 2) := by
  choose X hXA hXmin using exists_min_fiber A hA f hf hlev
  have hy : ∀ s, ∃ y, ContinuousLinearMap.adjoint A y = gradient f (X s) := fun s =>
    grad_mem_range A f hfL.1 (X s) (fun x' hx' => hXmin s x' (by rw [hx', hXA s]))
  choose y hy using hy
  have hLf : 0 ≤ Lf := by linarith
  have hadj_inj : ∀ w, ContinuousLinearMap.adjoint A w = 0 → w = 0 := by
    intro w hw
    obtain ⟨x, hx⟩ := hA w
    have h0 : ⟪A x, w⟫_ℝ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hw, inner_zero_right]
    rw [hx] at h0
    exact inner_self_eq_zero.1 h0
  obtain ⟨⟨y0, hy0, rfl⟩, hlb⟩ := hc
  have hcpos : 0 < ‖ContinuousLinearMap.adjoint A y0‖ ^ 2 := by
    have : ContinuousLinearMap.adjoint A y0 ≠ 0 := by
      intro h
      have := hadj_inj y0 h
      rw [this, norm_zero] at hy0
      exact zero_ne_one hy0
    positivity
  set c := ‖ContinuousLinearMap.adjoint A y0‖ ^ 2 with hcdef
  have hcw : ∀ w, c * ‖w‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A w‖ ^ 2 := by
    intro w
    by_cases hw : w = 0
    · rw [hw]; simp
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hu := hlb ⟨‖w‖⁻¹ • w, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hwpos)], rfl⟩
    rw [map_smul, norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, inv_mul_eq_div,
      le_div_iff₀ (by positivity)] at hu
    linarith
  let B : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p) :=
    ((A.comp (ContinuousLinearMap.adjoint A)) : EuclideanSpace ℝ (Fin p) →L[ℝ]
      EuclideanSpace ℝ (Fin p))
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun w hw => ?_
    have hw' : A (ContinuousLinearMap.adjoint A w) = 0 := hw
    apply hadj_inj
    have : ⟪ContinuousLinearMap.adjoint A w, ContinuousLinearMap.adjoint A w⟫_ℝ = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left, hw', inner_zero_right]
    exact inner_self_eq_zero.1 this
  have hBsurj : Function.Surjective B := LinearMap.injective_iff_surjective.1 hBinj
  have hAX : ∀ s d, A (X (s + d) - X s) = d := fun s d => by
    rw [map_sub, hXA, hXA, add_sub_cancel_left]
  have hex : ∀ s d, f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ
      = f (X s + (X (s + d) - X s)) - f (X s) - ⟪gradient f (X s), X (s + d) - X s⟫_ℝ := by
    intro s d
    rw [← hy s, ContinuousLinearMap.adjoint_inner_left, hAX, add_sub_cancel]
  have hconv0 : ConvexOn ℝ Set.univ (fun x => f x - 0 / 2 * ‖x‖ ^ 2) := by
    simpa using hconv
  have hlo0 : ∀ s d, (0:ℝ) / 2 * ‖d‖ ^ 2
      ≤ (fun s => f (X s)) (s + d) - (fun s => f (X s)) s - ⟪y s, d⟫_ℝ := by
    intro s d
    show _ ≤ f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ
    rw [hex]
    have := hypo_lower f 0 hfL.1 hconv0 (X s) (X (s + d) - X s)
    simp only [zero_div, zero_mul] at this ⊢
    exact this
  have hloc : ∀ s d, σf / ‖A‖ ^ 2 / 2 * ‖d‖ ^ 2
      ≤ (fun s => f (X s)) (s + d) - (fun s => f (X s)) s - ⟪y s, d⟫_ℝ := by
    intro s d
    by_cases hσ : 0 ≤ σf
    · show _ ≤ f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ
      rw [hex]
      have hl := hypo_lower f σf hfL.1 hfh (X s) (X (s + d) - X s)
      have hdxA : ‖d‖ ≤ ‖A‖ * ‖X (s + d) - X s‖ := by
        calc ‖d‖ = ‖A (X (s + d) - X s)‖ := by rw [hAX]
          _ ≤ ‖A‖ * ‖X (s + d) - X s‖ := A.le_opNorm _
      have hsqA : ‖d‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖X (s + d) - X s‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hdxA 2
      have := divnorm_aux σf _ _ ‖A‖ hσ hsqA (sq_nonneg _)
      nlinarith
    · have h0 := hlo0 s d
      have : σf / ‖A‖ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      have : σf / ‖A‖ ^ 2 / 2 * ‖d‖ ^ 2 ≤ 0 := by
        have := mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg ‖d‖)
        linarith
      linarith
  have hup : ∀ s d, (fun s => f (X s)) (s + d) - (fun s => f (X s)) s - ⟪y s, d⟫_ℝ
      ≤ Lf / c / 2 * ‖d‖ ^ 2 := by
    intro s d
    show f (X (s + d)) - f (X s) - ⟪y s, d⟫_ℝ ≤ _
    obtain ⟨w, hw⟩ := hBsurj d
    have hw' : A (ContinuousLinearMap.adjoint A w) = d := hw
    have hmin := hXmin (s + d) (X s + ContinuousLinearMap.adjoint A w)
      (by rw [map_add, hXA, hw'])
    have hdes := descent f Lf hfL.1 hfL.2 (X s) (ContinuousLinearMap.adjoint A w)
    have hin : ⟪gradient f (X s), ContinuousLinearMap.adjoint A w⟫_ℝ = ⟪y s, d⟫_ℝ := by
      rw [← hy s, ContinuousLinearMap.adjoint_inner_left, hw']
    have hnn : ‖ContinuousLinearMap.adjoint A w‖ ^ 2 = ⟪w, d⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left, hw']
    have hcs := real_inner_le_norm w d
    have hcw' := hcw w
    have hkey : ‖ContinuousLinearMap.adjoint A w‖ ^ 2 * c ≤ ‖d‖ ^ 2 := by
      rcases (norm_nonneg w).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul] at hcs
        nlinarith [norm_nonneg d]
      · have h3 : c * ‖w‖ ≤ ‖d‖ := by nlinarith
        have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg d)
        nlinarith [norm_nonneg d, norm_nonneg w]
    have hkey' : ‖ContinuousLinearMap.adjoint A w‖ ^ 2 ≤ ‖d‖ ^ 2 / c := by
      rw [le_div_iff₀ hcpos]; exact hkey
    have : Lf * ‖ContinuousLinearMap.adjoint A w‖ ^ 2 ≤ Lf * (‖d‖ ^ 2 / c) :=
      mul_le_mul_of_nonneg_left hkey' hLf
    have e : Lf / c / 2 * ‖d‖ ^ 2 = Lf * (‖d‖ ^ 2 / c) / 2 := by ring
    rw [e]
    linarith
  have hσL : -(Lf / c) ≤ 0 := by
    have : 0 ≤ Lf / c := div_nonneg hLf hcpos.le
    linarith
  obtain ⟨hsm, hcv⟩ :=
    lip_grad_of_sandwich (fun s => f (X s)) y (σf / ‖A‖ ^ 2) 0 (Lf / c) hσL hloc hlo0 hup
  exact ⟨fun s => f (X s), fun s => imageFn_eq A f s (X s) (hXA s) (hXmin s), hsm, hcv⟩

end euclid

section dini

/-- `a` is a (one-dimensional, Fréchet) supergradient of `φ` at `t`. -/
def SupG (φ : ℝ → ℝ) (a t : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t' in nhds t, φ t' ≤ φ t + a * (t' - t) + ε * |t' - t|

lemma SupG.sub_deriv {G q : ℝ → ℝ} {a b t : ℝ} (hG : SupG G a t) (hq : HasDerivAt q b t) :
    SupG (fun t => G t - q t) (a - b) t := by
  intro ε hε
  have h1 := hG (ε / 2) (by positivity)
  have h2 := (hasDerivAt_iff_isLittleO.1 hq).def (show 0 < ε / 2 by positivity)
  filter_upwards [h1, h2] with t' h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at h2
  have h3 := (abs_le.1 (le_trans (le_refl _) h2)).1
  linarith

lemma dini_core (φ ψ : ℝ → ℝ) (hc : ContinuousOn φ (Set.Icc 0 1))
    (hsup : ∀ t ∈ Set.Ico (0:ℝ) 1, SupG φ (ψ t) t) (hψ : ∀ t ∈ Set.Ico (0:ℝ) 1, ψ t ≤ 0) :
    φ 1 ≤ φ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hf' : ∀ x ∈ Set.Ico (0:ℝ) 1, ∀ r, (fun _ : ℝ => ε / 2) x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope φ x z < r := by
    intro x hx r hr
    have hr' : ε / 2 < r := hr
    have hev := hsup x hx (ε / 4) (by positivity)
    have hev' : ∀ᶠ z in nhdsWithin x (Set.Ioi x),
        (φ z ≤ φ x + ψ x * (z - x) + ε / 4 * |z - x|) ∧ z ∈ Set.Ioi x :=
      (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    refine hev'.frequently.mono fun z hz => ?_
    obtain ⟨h1, h2⟩ := hz
    have h2' : x < z := h2
    rw [slope_def_field, div_lt_iff₀ (by linarith)]
    rw [abs_of_pos (by linarith)] at h1
    have h4 := mul_nonpos_of_nonpos_of_nonneg (hψ x hx) (by linarith : (0:ℝ) ≤ z - x)
    have h5 := mul_pos (by linarith : (0:ℝ) < r - ε / 4) (by linarith : (0:ℝ) < z - x)
    nlinarith
  have hB' : ∀ x ∈ Set.Ico (0:ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => φ 0 + ε * t) ((fun _ : ℝ => ε) x) (Set.Ici x) x := by
    intro x _
    exact (((hasDerivAt_id x).const_mul ε).const_add (φ 0)).hasDerivWithinAt.congr_deriv
      (by simp)
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := φ)
    (f' := fun _ => ε / 2) (a := 0) (b := 1) hc hf' (B := fun t => φ 0 + ε * t)
    (B' := fun _ => ε) (by simp) (by fun_prop) hB'
    (fun x _ _ => by show ε / 2 < ε; linarith) (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa using key

lemma dini_core' (φ ψ : ℝ → ℝ) (hc : ContinuousOn φ (Set.Icc 0 1))
    (hsup : ∀ t ∈ Set.Ioc (0:ℝ) 1, SupG φ (ψ t) t) (hψ : ∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ ψ t) :
    φ 0 ≤ φ 1 := by
  have hc' : ContinuousOn (fun u => φ (1 - u)) (Set.Icc 0 1) := by
    refine hc.comp (by fun_prop) (fun u hu => ?_)
    obtain ⟨h1, h2⟩ := hu
    exact ⟨by linarith, by linarith⟩
  have hsup' : ∀ u ∈ Set.Ico (0:ℝ) 1, SupG (fun u => φ (1 - u)) (-ψ (1 - u)) u := by
    intro u hu ε hε
    have hm : 1 - u ∈ Set.Ioc (0:ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h := hsup (1 - u) hm ε hε
    have ht : Filter.Tendsto (fun u' : ℝ => 1 - u') (nhds u) (nhds (1 - u)) :=
      (continuous_const.sub continuous_id).tendsto u
    refine (ht.eventually h).mono fun u' hu' => ?_
    have hu'' : φ (1 - u') ≤ φ (1 - u) + ψ (1 - u) * ((1 - u') - (1 - u))
        + ε * |(1 - u') - (1 - u)| := hu'
    have e1 : (1 - u') - (1 - u) = -(u' - u) := by ring
    rw [e1, abs_neg] at hu''
    show φ (1 - u') ≤ φ (1 - u) + -ψ (1 - u) * (u' - u) + ε * |u' - u|
    linarith
  have := dini_core (fun u => φ (1 - u)) (fun u => -ψ (1 - u)) hc' hsup'
    (fun u hu => by
      have hm : 1 - u ∈ Set.Ioc (0:ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      linarith [hψ (1 - u) hm])
  simpa using this

end dini

section supergrad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma contF (F : E → ℝ) (y : E → E)
    (hsup : ∀ s, ∀ ε > 0, ∀ᶠ δ in nhds (0:E), F (s + δ) ≤ F s + ⟪y s, δ⟫_ℝ + ε * ‖δ‖)
    (hlsc : ∀ s, ∀ ε > 0, ∀ᶠ x in nhds s, F s - ε < F x) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have ht : Filter.Tendsto (fun x : E => x - s) (nhds s) (nhds 0) :=
    (by fun_prop : Continuous fun x : E => x - s).tendsto' s 0 (sub_self s)
  have hu := ht.eventually (hsup s 1 one_pos)
  have hpos : 0 < ε / (‖y s‖ + 1 + 1) := by positivity
  have hsm : ∀ᶠ x in nhds s, dist x s < ε / (‖y s‖ + 1 + 1) := Metric.ball_mem_nhds s hpos
  filter_upwards [hu, hsm, hlsc s ε hε] with x h1 h2 h3
  rw [add_sub_cancel] at h1
  rw [dist_eq_norm] at h2
  rw [Real.dist_eq, abs_sub_lt_iff]
  have hcs := real_inner_le_norm (y s) (x - s)
  constructor
  · rw [lt_div_iff₀ (by positivity)] at h2
    nlinarith [norm_nonneg (x - s), norm_nonneg (y s)]
  · linarith

lemma sandwich_of_supergrad (F : E → ℝ) (y : E → E) (σ L : ℝ) (hFc : Continuous F)
    (hsup : ∀ s, ∀ ε > 0, ∀ᶠ δ in nhds (0:E), F (s + δ) ≤ F s + ⟪y s, δ⟫_ℝ + ε * ‖δ‖)
    (hmono : ∀ s t, σ * ‖s - t‖ ^ 2 ≤ ⟪y s - y t, s - t⟫_ℝ ∧
      ⟪y s - y t, s - t⟫_ℝ ≤ L * ‖s - t‖ ^ 2) (s d : E) :
    σ / 2 * ‖d‖ ^ 2 ≤ F (s + d) - F s - ⟪y s, d⟫_ℝ ∧
      F (s + d) - F s - ⟪y s, d⟫_ℝ ≤ L / 2 * ‖d‖ ^ 2 := by
  set G : ℝ → ℝ := fun t => F (s + t • d) - t * ⟪y s, d⟫_ℝ with hG
  have hGc : Continuous G := by rw [hG]; fun_prop
  have hGs : ∀ t, SupG G (⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ) t := by
    intro t ε hε
    have h1 := hsup (s + t • d) (ε / (‖d‖ + 1)) (by positivity)
    have ht : Filter.Tendsto (fun t' : ℝ => (t' - t) • d) (nhds t) (nhds 0) := by
      have : Continuous (fun t' : ℝ => (t' - t) • d) := by fun_prop
      simpa using this.tendsto t
    filter_upwards [ht.eventually h1] with t' ht'
    have e : s + t • d + (t' - t) • d = s + t' • d := by
      rw [add_assoc, ← add_smul]; congr 2; ring
    rw [e, inner_smul_right, norm_smul, Real.norm_eq_abs] at ht'
    show F (s + t' • d) - t' * ⟪y s, d⟫_ℝ ≤ F (s + t • d) - t * ⟪y s, d⟫_ℝ
      + (⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ) * (t' - t) + ε * |t' - t|
    have hb : ε / (‖d‖ + 1) * (|t' - t| * ‖d‖) ≤ ε * |t' - t| := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (t' - t), norm_nonneg d, mul_nonneg hε.le (abs_nonneg (t' - t))]
    linarith
  have hq : ∀ (c t : ℝ), HasDerivAt (fun t : ℝ => c / 2 * t ^ 2 * ‖d‖ ^ 2) (c * t * ‖d‖ ^ 2) t := by
    intro c t
    exact (((hasDerivAt_pow 2 t).const_mul (c / 2)).mul_const (‖d‖ ^ 2)).congr_deriv (by
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
  have hψ : ∀ t, 0 < t → σ * t * ‖d‖ ^ 2 ≤ ⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ ∧
      ⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ ≤ L * t * ‖d‖ ^ 2 := by
    intro t htp
    have hm := hmono (s + t • d) s
    rw [add_sub_cancel_left, inner_smul_right, inner_sub_left, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at hm
    obtain ⟨hm1, hm2⟩ := hm
    constructor <;> nlinarith
  have hG0 : G 0 = F s := by simp [hG]
  have hG1 : G 1 = F (s + d) - ⟪y s, d⟫_ℝ := by simp [hG]
  constructor
  · have hlow := dini_core' (fun t => G t - σ / 2 * t ^ 2 * ‖d‖ ^ 2)
      (fun t => (⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ) - σ * t * ‖d‖ ^ 2)
      (by fun_prop) (fun t _ => SupG.sub_deriv (hGs t) (hq σ t))
      (fun t ht => by linarith [(hψ t ht.1).1])
    try dsimp only at hlow
    rw [hG0, hG1] at hlow
    linarith
  · have hupp := dini_core (fun t => G t - L / 2 * t ^ 2 * ‖d‖ ^ 2)
      (fun t => (⟪y (s + t • d), d⟫_ℝ - ⟪y s, d⟫_ℝ) - L * t * ‖d‖ ^ 2)
      (by fun_prop) (fun t _ => SupG.sub_deriv (hGs t) (hq L t))
      (fun t ht => by
        rcases eq_or_lt_of_le ht.1 with h0 | hpos
        · rw [← h0]; simp
        · linarith [(hψ t hpos).2])
    try dsimp only at hupp
    rw [hG0, hG1] at hupp
    linarith

end supergrad

section part1

variable {n p : ℕ}

lemma supergrad_F (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (X : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n)) (hXA : ∀ s, A (X s) = s)
    (hXmin : ∀ s x, A x = s → f (X s) ≤ f x)
    (y : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hy : ∀ s, ContinuousLinearMap.adjoint A (y s) = gradient f (X s))
    (R : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hR : ∀ v, A (R v) = v)
    (s : EuclideanSpace ℝ (Fin p)) :
    ∀ ε > 0, ∀ᶠ δ in nhds (0 : EuclideanSpace ℝ (Fin p)),
      f (X (s + δ)) ≤ f (X s) + ⟪y s, δ⟫_ℝ + ε * ‖δ‖ := by
  intro ε hε
  have hg := (hf (X s)).hasGradientAt
  rw [hasGradientAt_iff_isLittleO_nhds_zero] at hg
  have hRt : Filter.Tendsto (fun δ => R δ) (nhds 0) (nhds 0) := by
    simpa using R.continuous.tendsto 0
  have h1 : (fun δ => f (X s + R δ) - f (X s) - ⟪gradient f (X s), R δ⟫_ℝ)
      =o[nhds 0] (fun δ => R δ) := hg.comp_tendsto hRt
  have h2 := h1.trans_isBigO (R.isBigO_id (nhds 0))
  filter_upwards [h2.def hε] with δ hδ
  have hm := hXmin (s + δ) (X s + R δ) (by rw [map_add, hXA, hR])
  have hin : ⟪gradient f (X s), R δ⟫_ℝ = ⟪y s, δ⟫_ℝ := by
    rw [← hy s, ContinuousLinearMap.adjoint_inner_left, hR]
  rw [hin, Real.norm_eq_abs] at hδ
  linarith [le_abs_self (f (X s + R δ) - f (X s) - ⟪y s, δ⟫_ℝ)]

lemma lscF (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (X : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n)) (hXA : ∀ s, A (X s) = s)
    (hXmin : ∀ s x, A x = s → f (X s) ≤ f x) (s : EuclideanSpace ℝ (Fin p)) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ x in nhds s, f (X s) - ε < f (X x) := by
  set K := {x | f x ≤ f (X s) - ε} ∩ {x | ‖A x - s‖ ≤ 1} with hK
  have hKb : Bornology.IsBounded K := by
    refine (hb s (f (X s) - ε + β / 2)).subset ?_
    rintro x ⟨h1, h2⟩
    have h1' : f x ≤ f (X s) - ε := h1
    have h2' : ‖A x - s‖ ≤ 1 := h2
    show f x + β / 2 * ‖A x - s‖ ^ 2 ≤ f (X s) - ε + β / 2
    have : ‖A x - s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (A x - s)]
    nlinarith
  have hKc : IsClosed K :=
    (hf.isClosed_preimage _).inter (isClosed_le (by fun_prop) continuous_const)
  have hKk : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  set C := (fun x => A x - s) '' K with hC
  have hCc : IsClosed C := (hKk.image (by fun_prop)).isClosed
  have h0 : (0 : EuclideanSpace ℝ (Fin p)) ∉ C := by
    rintro ⟨x, ⟨h1, -⟩, hx⟩
    have h1' : f x ≤ f (X s) - ε := h1
    have hAx : A x = s := sub_eq_zero.1 hx
    have := hXmin s x hAx
    linarith
  have ht : Filter.Tendsto (fun x => x - s) (nhds s) (nhds 0) :=
    (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin p) => x - s).tendsto' s 0
      (sub_self s)
  have hev1 : ∀ᶠ x in nhds s, x - s ∉ C := ht.eventually (hCc.isOpen_compl.mem_nhds h0)
  have hev2 : ∀ᶠ x in nhds s, dist x s < 1 := Metric.ball_mem_nhds s one_pos
  filter_upwards [hev1, hev2] with x h1 h2
  by_contra hcon
  apply h1
  refine ⟨X x, ⟨not_lt.1 hcon, ?_⟩, ?_⟩
  · show ‖A (X x) - s‖ ≤ 1
    rw [hXA, ← dist_eq_norm]; exact h2.le
  · show A (X x) - s = x - s
    rw [hXA]

lemma part1 (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (L σ : ℝ) (hrel : NonconvexDRS.ImageSmooth.IsSmoothRel f A L σ) :
    NonconvexDRS.ImageSmooth.IsImageSmooth A f L σ := by
  obtain ⟨hfd, hσL, hmon⟩ := hrel
  choose X hXA hXmin using exists_min_fiber A hA f hf hlev
  have hy0 : ∀ s, ∃ y, ContinuousLinearMap.adjoint A y = gradient f (X s) := fun s =>
    grad_mem_range A f hfd (X s) (fun x' hx' => hXmin s x' (by rw [hx', hXA s]))
  choose y hy using hy0
  obtain ⟨R, hR⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective A
    (LinearMap.range_eq_top.2 hA)
  have hR' : ∀ v, A (R v) = v := fun v => by
    have := congrArg (fun T => T v) hR
    simpa using this
  obtain ⟨β, hβ, hb⟩ := hlev
  have hsup := fun s => supergrad_F A f hfd X hXA hXmin y hy R hR' s
  have hlsc := fun s ε hε => lscF A f hf β hβ hb X hXA hXmin s ε hε
  have hFc := contF (fun s => f (X s)) y hsup hlsc
  have hmono : ∀ s t, σ * ‖s - t‖ ^ 2 ≤ ⟪y s - y t, s - t⟫_ℝ ∧
      ⟪y s - y t, s - t⟫_ℝ ≤ L * ‖s - t‖ ^ 2 := by
    intro s t
    have h := hmon (X s) (X t) ⟨y s, hy s⟩ ⟨y t, hy t⟩
    have e1 : A (X s - X t) = s - t := by rw [map_sub, hXA, hXA]
    have e2 : ⟪gradient f (X s) - gradient f (X t), X s - X t⟫_ℝ = ⟪y s - y t, s - t⟫_ℝ := by
      rw [← hy s, ← hy t, ← map_sub, ContinuousLinearMap.adjoint_inner_left, e1]
    rw [e1, e2] at h
    exact h
  have hsand := sandwich_of_supergrad (fun s => f (X s)) y σ L hFc hsup hmono
  have hσL' : -L ≤ σ := by linarith [neg_abs_le σ]
  obtain ⟨hsm, hcv⟩ := lip_grad_of_sandwich (fun s => f (X s)) y σ σ L hσL'
    (fun s d => (hsand s d).1) (fun s d => (hsand s d).1) (fun s d => (hsand s d).2)
  exact ⟨fun s => f (X s), fun s => imageFn_eq A f s (X s) (hXA s) (hXmin s), hsm, hcv⟩

end part1

end ImgSm513

open NonconvexDRS.ImageSmooth in
theorem solution {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α}) :
    (∀ L σ : ℝ, IsSmoothRel f A L σ → IsImageSmooth A f L σ) ∧
    (∀ Lf σf M : ℝ, NonconvexDRS.DRS.IsLSmooth f Lf → NonconvexDRS.DRS.IsHypoconvex f σf → -Lf ≤ σf → σf ≤ Lf →
      (∃ X : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n),
        (∀ s, A (X s) = s ∧ ∀ x, A x = s → f (X s) ≤ f x) ∧
        (∀ s x, A x = s → (∀ x', A x' = s → f x ≤ f x') → x = X s) ∧
        ∀ s s', ‖X s - X s'‖ ≤ M * ‖s - s'‖) →
      IsImageSmooth A f (Lf * M ^ 2) (if 0 ≤ σf then σf / ‖A‖ ^ 2 else σf * M ^ 2)) ∧
    (∀ Lf σf c : ℝ, ConvexOn ℝ Set.univ f → NonconvexDRS.DRS.IsLSmooth f Lf → NonconvexDRS.DRS.IsHypoconvex f σf →
      -Lf ≤ σf → σf ≤ Lf →
      IsLeast {t | ∃ y : EuclideanSpace ℝ (Fin p), ‖y‖ = 1 ∧
        t = ‖ContinuousLinearMap.adjoint A y‖ ^ 2} c →
      IsImageSmooth A f (Lf / c) (σf / ‖A‖ ^ 2)) := by
  refine ⟨fun L σ h => ImgSm513.part1 A hA f hf hlev L σ h, fun Lf σf M hfL hfh h1 h2 hX => ?_,
    fun Lf σf c hconv hfL hfh h1 h2 hc =>
      ImgSm513.part3 A hA f hf hlev Lf σf c hconv hfL hfh h1 h2 hc⟩
  obtain ⟨X, hX1, -, hXL⟩ := hX
  exact ImgSm513.part2 A f Lf σf M hfL hfh h1 h2 X hX1 hXL
