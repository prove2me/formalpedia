-- Prove2me | solution 1 for ModernConvex.ConicDuality.dual_cone_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:30:29.114862+00:00
-- url     : https://prove2.me/submissions/f846d7d3-6147-4458-bbe9-699b9cb54ee0

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

theorem g69a1_vec {κ : Type*} [Fintype κ] [DecidableEq κ] (g : (κ → ℝ) →ₗ[ℝ] ℝ) :
    ∀ z : κ → ℝ, g z = (fun j => g (Pi.single j 1)) ⬝ᵥ z := by
  intro z
  conv_lhs => rw [show z = ∑ j, z j • Pi.single j (1:ℝ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, dotProduct, mul_comm]

theorem g69a1_sep_zero {κ : Type} [Fintype κ] [DecidableEq κ] (D : Set (κ → ℝ))
    (hD : D.Nonempty) (hDc : Convex ℝ D) (h0 : (0 : κ → ℝ) ∉ D) :
    ∃ g : (κ → ℝ) →ₗ[ℝ] ℝ, g ≠ 0 ∧ ∀ d ∈ D, g d ≤ 0 := by
  by_cases hint : (interior D).Nonempty
  · have hdisj : Disjoint (interior D) {0} := by
      rw [Set.disjoint_singleton_right]
      exact fun h => h0 (interior_subset h)
    obtain ⟨f, u, hf0, hfD, hfu⟩ := geometric_hahn_banach_of_nonempty_interior hDc
      (convex_singleton 0) hdisj hint (Set.singleton_nonempty 0)
    refine ⟨f.toLinearMap, ?_, ?_⟩
    · intro h; apply hf0; ext x; exact LinearMap.congr_fun h x
    · intro d hd
      have := hfu 0 rfl
      have := hfD d hd
      simp only [map_zero] at *
      show f d ≤ 0
      linarith
  · rw [hDc.interior_nonempty_iff_affineSpan_eq_top] at hint
    have hvs : vectorSpan ℝ D < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hint
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty (hD.mono (subset_affineSpan ℝ D)),
        direction_affineSpan, htop]
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hvs
    obtain ⟨d0, hd0⟩ := hD
    have hconst : ∀ d ∈ D, f d = f d0 := by
      intro d hd
      have := hker (vsub_mem_vectorSpan ℝ hd hd0)
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
      exact this
    by_cases hs : f d0 ≤ 0
    · exact ⟨f, hf0, fun d hd => by rw [hconst d hd]; exact hs⟩
    · refine ⟨-f, neg_ne_zero.mpr hf0, fun d hd => ?_⟩
      rw [LinearMap.neg_apply, hconst d hd]; linarith


open ModernConvex.ConicDuality

lemma g69cd_convex {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) : Convex ℝ K := by
  intro a ha b hb s t hs ht _
  exact hK.2.1 _ (hK.2.2 a ha s hs) _ (hK.2.2 b hb t ht)

lemma g69cd_zero {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) : (0 : Fin m → ℝ) ∈ K := by
  obtain ⟨a, ha⟩ := hK.1
  simpa using hK.2.2 a ha 0 le_rfl

lemma g69cd_dual_cone {m : ℕ} (K : Set (Fin m → ℝ)) :
    IsConvexCone (dualCone K) ∧ IsClosed (dualCone K) := by
  refine ⟨⟨⟨0, fun a _ => by simp⟩, fun l hl l' hl' a ha => ?_, fun l hl t ht a ha => ?_⟩, ?_⟩
  · rw [add_dotProduct]; exact add_nonneg (hl a ha) (hl' a ha)
  · rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg ht (hl a ha)
  · have : dualCone K = ⋂ a ∈ K, {l : Fin m → ℝ | 0 ≤ l ⬝ᵥ a} := by
      ext l; simp [dualCone]
    rw [this]
    refine isClosed_biInter fun a _ => isClosed_le continuous_const ?_
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const

lemma g69cd_bidual {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) (hKc : IsClosed K) :
    dualCone (dualCone K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hxK
    obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed (g69cd_convex hK) hKc hxK
    have hu : u < 0 := by have := hfK 0 (g69cd_zero hK); simpa using this
    have hpos : ∀ a ∈ K, 0 ≤ f a := by
      intro a ha
      by_contra hneg; push Not at hneg
      have ht : 0 ≤ u / f a := div_nonneg_of_nonpos hu.le hneg.le
      have := hfK _ (hK.2.2 a ha (u / f a + 1) (by linarith))
      rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hneg.ne, one_mul] at this
      linarith
    set l : Fin m → ℝ := fun j => f (Pi.single j 1)
    have hl : ∀ z, f z = l ⬝ᵥ z := g69a1_vec f.toLinearMap
    have hlK : l ∈ dualCone K := fun a ha => by rw [← hl]; exact hpos a ha
    have := hx l hlK
    rw [dotProduct_comm, ← hl] at this
    linarith
  · intro hx l hl
    rw [dotProduct_comm]; exact hl x hx

lemma g69cd_pointed {m : ℕ} {K : Set (Fin m → ℝ)} (hint : (interior K).Nonempty) :
    IsPointedSet (dualCone K) := by
  intro l hl hl'
  have h0 : ∀ a ∈ K, l ⬝ᵥ a = 0 := fun a ha => by
    have h1 := hl a ha; have h2 := hl' a ha; rw [neg_dotProduct] at h2; linarith
  obtain ⟨a0, ha0⟩ := hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha0)
  ext i
  have hz : a0 + (ε / 2) • Pi.single i (1:ℝ) ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc ε / 2 * ‖(Pi.single i (1:ℝ) : Fin m → ℝ)‖ ≤ ε / 2 * 1 := by
          gcongr; rw [Pi.norm_single]; simp
      _ < ε := by linarith
  have := h0 _ hz
  rw [dotProduct_add, h0 a0 (interior_subset ha0), dotProduct_smul, dotProduct_single, mul_one,
    smul_eq_mul, zero_add] at this
  simpa [hε.ne'] using this

lemma g69cd_int {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) (hKc : IsClosed K)
    (hp : IsPointedSet K) : (interior (dualCone K)).Nonempty := by
  by_contra hint
  have hD := g69cd_dual_cone K
  have hDc : Convex ℝ (dualCone K) := g69cd_convex hD.1
  have h0D : (0 : Fin m → ℝ) ∈ dualCone K := g69cd_zero hD.1
  rw [hDc.interior_nonempty_iff_affineSpan_eq_top] at hint
  have hvs : vectorSpan ℝ (dualCone K) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hint
    have hne : (affineSpan ℝ (dualCone K) : Set (Fin m → ℝ)).Nonempty := ⟨0, subset_affineSpan ℝ _ h0D⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne, direction_affineSpan, htop]
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hvs
  have hfD : ∀ l ∈ dualCone K, f l = 0 := by
    intro l hl
    have := hker (vsub_mem_vectorSpan ℝ hl h0D)
    rw [LinearMap.mem_ker, vsub_eq_sub, sub_zero] at this
    exact this
  set v : Fin m → ℝ := fun j => f (Pi.single j 1)
  have hv : ∀ z, f z = v ⬝ᵥ z := g69a1_vec f
  have hvK : v ∈ K := by
    rw [← g69cd_bidual hK hKc]
    intro l hl; rw [← hv, hfD l hl]
  have hvK' : -v ∈ K := by
    rw [← g69cd_bidual hK hKc]
    intro l hl; rw [neg_dotProduct, ← hv, hfD l hl]; simp
  have := hp v hvK hvK'
  apply hf0
  refine LinearMap.ext fun z => ?_
  rw [hv, this, zero_dotProduct]; rfl


open Matrix
open ModernConvex.ConicDuality
/-- Ben-Tal–Nemirovski, Theorem 2.3.1 (properties of the dual cone), p. 52. For a nonempty set
`K ⊂ ℝᵐ` and `K∗ = {λ | λᵀa ≥ 0 ∀ a ∈ K}`:
(i) `K∗` is a closed convex cone; (ii) if `int K ≠ ∅` then `K∗` is pointed;
(iii) if `K` is a closed convex pointed cone then `int K∗ ≠ ∅`;
(iv) if `K` is a closed convex cone then so is `K∗`, and `(K∗)∗ = K`. -/
theorem solution {m : ℕ} (K : Set (Fin m → ℝ)) (hK : K.Nonempty) :
    -- (i)
    (IsConvexCone (dualCone K) ∧ IsClosed (dualCone K)) ∧
    -- (ii)
    ((interior K).Nonempty → IsPointedSet (dualCone K)) ∧
    -- (iii)
    (IsConvexCone K ∧ IsClosed K ∧ IsPointedSet K → (interior (dualCone K)).Nonempty) ∧
    -- (iv)
    (IsConvexCone K ∧ IsClosed K →
      (IsConvexCone (dualCone K) ∧ IsClosed (dualCone K)) ∧ dualCone (dualCone K) = K) := by
  refine ⟨g69cd_dual_cone K, g69cd_pointed, fun h => g69cd_int h.1 h.2.1 h.2.2,
    fun h => ⟨g69cd_dual_cone K, g69cd_bidual h.1 h.2⟩⟩


