-- Prove2me | solution 1 for ModernConvex.ConicDuality.both_strictly_feasible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:41:32.104864+00:00
-- url     : https://prove2.me/submissions/06c380c8-1aee-441b-8a8c-93eb5501d829

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

lemma g69cd_ball_cone {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) {k0 : Fin m → ℝ}
    (hk0 : k0 ∈ interior K) (k : Fin m → ℝ) (hk : k ∈ K) : k0 + k ∈ interior K := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hk0)
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun z hz => ?_⟩
  have : z - k ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rwa [show z - k - k0 = z - (k0 + k) by abel])
  simpa using hK.2.1 _ this _ hk

open scoped Pointwise in
lemma g69cd_smul_int {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsConvexCone K) {k0 : Fin m → ℝ}
    (hk0 : k0 ∈ interior K) {t : ℝ} (ht : 0 < t) : t • k0 ∈ interior K := by
  have h1 : t • K ⊆ K := by
    rintro _ ⟨k, hk, rfl⟩; exact hK.2.2 k hk t ht.le
  have : t • k0 ∈ t • interior K := ⟨k0, hk0, rfl⟩
  rw [← interior_smul₀ ht.ne'] at this
  exact interior_mono h1 this

lemma g69cd_scalar {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsConvexCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hS : ∃ x : Fin n → ℝ, A *ᵥ x - b ∈ interior K)
    (h : ∀ x : Fin n → ℝ, A *ᵥ x - b ∈ K → d ≤ c ⬝ᵥ x) :
    ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = c ∧ d ≤ l ⬝ᵥ b := by
  obtain ⟨x0, hx0⟩ := hS
  by_cases hc : c = 0
  · refine ⟨0, fun a _ => by simp, by simp [hc], ?_⟩
    have := h x0 (interior_subset hx0); simp [hc] at this; simpa using this
  have hcc : 0 < c ⬝ᵥ c := by
    have h0 : 0 ≤ c ⬝ᵥ c := Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h' => hc (dotProduct_self_eq_zero.mp h')))
  set U : Set (Fin m → ℝ) := (fun x => A *ᵥ x - b) '' {x | c ⬝ᵥ x < d} with hU
  have hpt : ∀ s : ℝ, c ⬝ᵥ ((s / (c ⬝ᵥ c)) • c) = s := by
    intro s; rw [dotProduct_smul, smul_eq_mul]; field_simp
  have hUc : Convex ℝ U := by
    rintro _ ⟨x1, hx1, rfl⟩ _ ⟨x2, hx2, rfl⟩ s t hs ht hst
    refine ⟨s • x1 + t • x2, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hx1 hx2 ⊢
      rcases eq_or_lt_of_le hs with h0 | hpos
      · subst h0; have : t = 1 := by linarith
        subst this; linarith
      · have h1 := mul_lt_mul_of_pos_left hx1 hpos
        have h2 := mul_le_mul_of_nonneg_left hx2.le ht
        have : s * d + t * d = d := by rw [← add_mul, hst, one_mul]
        linarith
    · ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul]
      linear_combination (b i) * hst
  have hdisj : Disjoint (interior K) U := by
    rw [Set.disjoint_left]
    rintro _ hk ⟨x, hx, rfl⟩
    have := h x (interior_subset hk)
    simp only [Set.mem_setOf_eq] at hx; linarith
  obtain ⟨f, u, hfK, hfU⟩ := geometric_hahn_banach_open (g69cd_convex hK).interior isOpen_interior hUc hdisj
  set g : Fin m → ℝ := fun j => f (Pi.single j 1)
  have hg : ∀ z, f z = g ⬝ᵥ z := g69a1_vec f.toLinearMap
  clear_value g
  set lam := -g with hlam
  clear_value lam
  have hAt : ∀ (v : Fin m → ℝ) (x : Fin n → ℝ), (Aᵀ *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (A *ᵥ x) := by
    intro v x; rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  -- lam ∈ K*
  have hlamK : lam ∈ dualCone K := by
    intro k hk
    by_contra hneg; push Not at hneg
    have hgk : 0 < g ⬝ᵥ k := by rw [hlam, neg_dotProduct] at hneg; linarith
    have ht : 0 < (u - g ⬝ᵥ (A *ᵥ x0 - b)) / (g ⬝ᵥ k) + 1 := by
      have := hfK _ hx0; rw [hg] at this
      have : 0 < u - g ⬝ᵥ (A *ᵥ x0 - b) := by linarith
      positivity
    have := hfK _ (g69cd_ball_cone hK hx0 _ (hK.2.2 k hk _ ht.le))
    rw [hg, dotProduct_add, dotProduct_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hgk.ne'] at this
    linarith
  -- u ≥ 0
  have hu : 0 ≤ u := by
    by_contra hneg; push Not at hneg
    have hk0 := hfK _ hx0; rw [hg] at hk0
    have hgk0 : g ⬝ᵥ (A *ᵥ x0 - b) < 0 := by linarith
    have ht : 0 < u / (2 * g ⬝ᵥ (A *ᵥ x0 - b)) := div_pos_of_neg_of_neg hneg (by linarith)
    have := hfK _ (g69cd_smul_int hK hx0 ht)
    rw [hg, dotProduct_smul, smul_eq_mul] at this
    have e : u / (2 * g ⬝ᵥ (A *ᵥ x0 - b)) * (g ⬝ᵥ (A *ᵥ x0 - b)) = u / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hgk0.ne]
    linarith
  -- on U
  have hU' : ∀ x, c ⬝ᵥ x < d → (Aᵀ *ᵥ lam) ⬝ᵥ x - lam ⬝ᵥ b ≤ -u := by
    intro x hx
    have := hfU _ ⟨x, hx, rfl⟩
    rw [hg, dotProduct_sub] at this
    rw [hAt, hlam, neg_dotProduct, neg_dotProduct]; linarith
  set w := Aᵀ *ᵥ lam with hw
  clear_value w
  obtain ⟨x1, hx1d⟩ : ∃ x1 : Fin n → ℝ, x1 = ((d - 1) / (c ⬝ᵥ c)) • c := ⟨_, rfl⟩
  have hx1 : c ⬝ᵥ x1 < d := by rw [hx1d, hpt]; linarith
  -- w ⊥ (c⊥)
  have hperp : ∀ z, c ⬝ᵥ z = 0 → w ⬝ᵥ z = 0 := by
    intro z hz
    by_contra hne
    have key : ∀ s : ℝ, s * (w ⬝ᵥ z) ≤ -u - w ⬝ᵥ x1 + lam ⬝ᵥ b := by
      intro s
      have := hU' (x1 + s • z) (by rw [dotProduct_add, dotProduct_smul, hz, smul_eq_mul]; linarith)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this; linarith
    have := key ((-u - w ⬝ᵥ x1 + lam ⬝ᵥ b + 1) / (w ⬝ᵥ z))
    rw [div_mul_cancel₀ _ hne] at this; linarith
  set μ := (w ⬝ᵥ c) / (c ⬝ᵥ c) with hμ
  clear_value μ
  have hwμ : w = μ • c := by
    have hz : c ⬝ᵥ (w - μ • c) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hμ, dotProduct_comm c w]; field_simp; ring
    have h1 := hperp _ hz
    have hz' : (w - μ • c) ⬝ᵥ c = 0 := by rw [dotProduct_comm]; exact hz
    have h2 : (w - μ • c) ⬝ᵥ (w - μ • c) = 0 := by
      rw [sub_dotProduct, h1, smul_dotProduct]; simp [hz, hz']
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h2)
  -- μ > 0
  have hμpos : 0 < μ := by
    rcases lt_trichotomy μ 0 with hneg | hzero | hpos
    · exfalso
      set C := |-u - μ * (c ⬝ᵥ x1) + lam ⬝ᵥ b| + 1 with hC
      have hden : 0 < -μ * (c ⬝ᵥ c) := mul_pos (by linarith) hcc
      set sc := C / (-μ * (c ⬝ᵥ c))
      have hsc : 0 < sc := div_pos (by positivity) hden
      have := hU' (x1 - sc • c) (by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have : 0 < sc * (c ⬝ᵥ c) := mul_pos hsc hcc
        linarith)
      rw [hwμ, smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      have e : μ * (c ⬝ᵥ x1 - sc * (c ⬝ᵥ c)) = μ * (c ⬝ᵥ x1) + C := by
        have : sc * (-μ * (c ⬝ᵥ c)) = C := div_mul_cancel₀ _ hden.ne'
        linear_combination this
      rw [e] at this
      have := le_abs_self (-u - μ * (c ⬝ᵥ x1) + lam ⬝ᵥ b)
      linarith
    · exfalso
      have hw0 : w = 0 := by rw [hwμ, hzero, zero_smul]
      have h1 := hU' x1 hx1
      rw [hw0, zero_dotProduct] at h1
      have hk0 := hfK _ hx0
      rw [hg, dotProduct_sub, ← hAt] at hk0
      have : Aᵀ *ᵥ g = -w := by rw [hw, hlam, mulVec_neg, neg_neg]
      rw [this, hw0, neg_zero, zero_dotProduct] at hk0
      rw [hlam, neg_dotProduct] at h1
      linarith
    · exact hpos
  refine ⟨μ⁻¹ • lam, fun a ha => ?_, ?_, ?_⟩
  · rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg (inv_pos.mpr hμpos).le (hlamK a ha)
  · rw [mulVec_smul, ← hw, hwμ, smul_smul, inv_mul_cancel₀ hμpos.ne', one_smul]
  · rw [smul_dotProduct, smul_eq_mul]
    by_contra hlt; push Not at hlt
    obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = (μ⁻¹ * lam ⬝ᵥ b + d) / 2 := ⟨_, rfl⟩
    have hs : s < d := by rw [hsd]; linarith
    have := hU' ((s / (c ⬝ᵥ c)) • c) (by rw [hpt]; exact hs)
    rw [hwμ, smul_dotProduct, hpt, smul_eq_mul] at this
    have : s ≤ μ⁻¹ * lam ⬝ᵥ b := by
      rw [le_inv_mul_iff₀ hμpos]; linarith
    rw [hsd] at this; linarith

lemma g69cd_At {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin m → ℝ) (x : Fin n → ℝ) :
    (Aᵀ *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

lemma g69cf_wd {m n : ℕ} {K : Set (Fin m → ℝ)} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {x : Fin n → ℝ} {l : Fin m → ℝ} (hx : PrimalFeasible K A b x)
    (hl : DualFeasible K A c l) : b ⬝ᵥ l ≤ c ⬝ᵥ x := by
  have h1 := hl.2 _ hx
  have h2 := g69cd_At A l x
  rw [hl.1] at h2
  rw [dotProduct_sub, ← h2, dotProduct_comm l b] at h1
  linarith

lemma g69cf_gram {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (hA : AssumptionA A) :
    IsUnit (Aᵀ * A).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : (Aᵀ * A) *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have h1 : (A *ᵥ (x - y)) ⬝ᵥ (A *ᵥ (x - y)) = 0 := by
    have : (x - y) ⬝ᵥ ((Aᵀ * A) *ᵥ (x - y)) = 0 := by rw [h0, dotProduct_zero]
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at this
    exact this
  rw [dotProduct_self_eq_zero, mulVec_sub, sub_eq_zero] at h1
  have := hA h1
  exact this

lemma g69cf_left {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (hA : AssumptionA A) (x : Fin n → ℝ) :
    ((Aᵀ * A)⁻¹ * Aᵀ) *ᵥ (A *ᵥ x) = x := by
  rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (g69cf_gram hA), one_mulVec]

lemma g69cf_dscalar {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (l0 : Fin m → ℝ) (hl0 : l0 ∈ interior (dualCone K)) (hc : Aᵀ *ᵥ l0 = c) (U : ℝ)
    (hU : ∀ l, DualFeasible K A c l → b ⬝ᵥ l ≤ U) :
    ∃ x, PrimalFeasible K A b x ∧ c ⬝ᵥ x ≤ U := by
  set M := (Aᵀ * A)⁻¹ with hM
  have hMu := g69cf_gram hA
  set N : Matrix (Fin m) (Fin m) ℝ := 1 - A * M * Aᵀ with hN
  have hAN : Aᵀ * N = 0 := by
    rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, sub_self]
  have hNt : Nᵀ = N := by
    rw [hN, transpose_sub, transpose_one, transpose_mul, transpose_mul, transpose_transpose,
      hM, transpose_nonsing_inv, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  obtain ⟨μ, hμ, hμN, hμd⟩ := g69cd_scalar (dualCone K) (g69cd_dual_cone K).1 N (-l0)
    (-(Nᵀ *ᵥ b)) (b ⬝ᵥ l0 - U) ⟨0, by simpa using hl0⟩ (by
      intro y hy
      rw [sub_neg_eq_add] at hy
      have hf : DualFeasible K A c (N *ᵥ y + l0) := by
        refine ⟨?_, hy⟩
        rw [mulVec_add, mulVec_mulVec, hAN, zero_mulVec, zero_add, hc]
      have := hU _ hf
      rw [dotProduct_add] at this
      have e : (Nᵀ *ᵥ b) ⬝ᵥ y = b ⬝ᵥ (N *ᵥ y) := by
        rw [mulVec_transpose, dotProduct_mulVec]
      rw [neg_dotProduct, e]
      linarith)
  rw [g69cd_bidual hK hKc] at hμ
  refine ⟨M *ᵥ (Aᵀ *ᵥ (μ + b)), ?_, ?_⟩
  · have hNz : N *ᵥ (μ + b) = 0 := by
      rw [hNt] at hμN
      rw [mulVec_add, hμN, neg_add_cancel]
    have : A *ᵥ (M *ᵥ (Aᵀ *ᵥ (μ + b))) = μ + b := by
      have h2 : N *ᵥ (μ + b) = (μ + b) - (A * M * Aᵀ) *ᵥ (μ + b) := by
        rw [hN, sub_mulVec, one_mulVec]
      rw [mulVec_mulVec, mulVec_mulVec]
      rw [hNz] at h2
      have := sub_eq_zero.mp h2.symm
      rw [← this]
    unfold PrimalFeasible
    rw [this, add_sub_cancel_right]; exact hμ
  · have h1 := g69cd_At A l0 (M *ᵥ (Aᵀ *ᵥ (μ + b)))
    rw [hc] at h1
    rw [h1]
    have : A *ᵥ (M *ᵥ (Aᵀ *ᵥ (μ + b))) = μ + b := by
      have hNz : N *ᵥ (μ + b) = 0 := by
        rw [hNt] at hμN
        rw [mulVec_add, hμN, neg_add_cancel]
      have h2 : N *ᵥ (μ + b) = (μ + b) - (A * M * Aᵀ) *ᵥ (μ + b) := by
        rw [hN, sub_mulVec, one_mulVec]
      rw [mulVec_mulVec, mulVec_mulVec]
      rw [hNz] at h2
      exact (sub_eq_zero.mp h2.symm).symm
    rw [this, dotProduct_add, dotProduct_neg, dotProduct_comm μ l0] at *
    rw [dotProduct_comm b l0] at hμd
    linarith

lemma g69cf_key {m : ℕ} {K : Set (Fin m → ℝ)} {l0 : Fin m → ℝ}
    (hl0 : l0 ∈ interior (dualCone K)) :
    ∃ ε > 0, ∀ k ∈ K, ∀ i, ε * |k i| ≤ l0 ⬝ᵥ k := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hl0)
  refine ⟨ε / 2, by positivity, fun k hk i => ?_⟩
  have hs : ∀ t : ℝ, |t| < ε → 0 ≤ l0 ⬝ᵥ k + t * k i := by
    intro t ht
    have hmem : l0 + Pi.single i t ∈ dualCone K := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single]
      simpa using ht)
    have := hmem k hk
    rwa [add_dotProduct, single_dotProduct] at this
  have h1 := hs (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have h2 := hs (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  rcases le_total 0 (k i) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

lemma g69cf_attain {m n : ℕ} (K : Set (Fin m → ℝ)) (hKc : IsClosed K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (l0 : Fin m → ℝ) (hl0 : l0 ∈ interior (dualCone K)) (hc : Aᵀ *ᵥ l0 = c)
    (x1 : Fin n → ℝ) (hx1 : PrimalFeasible K A b x1) :
    ∃ x, IsPrimalOptimal K A b c x := by
  obtain ⟨ε, hε, hkey⟩ := g69cf_key hl0
  have hl0' : l0 ∈ dualCone K := interior_subset hl0
  have hcx : ∀ x, c ⬝ᵥ x = l0 ⬝ᵥ (A *ᵥ x - b) + l0 ⬝ᵥ b := by
    intro x; rw [← hc, g69cd_At, dotProduct_sub]; ring
  set R := (l0 ⬝ᵥ (A *ᵥ x1 - b)) / ε with hR
  have hR0 : 0 ≤ R := div_nonneg (hl0' _ hx1) hε.le
  set S := {x : Fin n → ℝ | A *ᵥ x - b ∈ K ∧ c ⬝ᵥ x ≤ c ⬝ᵥ x1} with hS
  have hcont : Continuous fun x : Fin n → ℝ => A *ᵥ x - b :=
    (Continuous.matrix_mulVec continuous_const continuous_id).sub continuous_const
  have hccont : Continuous fun x : Fin n → ℝ => c ⬝ᵥ x :=
    Continuous.dotProduct continuous_const continuous_id
  have hSc : IsClosed S :=
    (hKc.preimage hcont).inter (isClosed_le hccont continuous_const)
  have hsub : S ⊆ (fun y => ((Aᵀ * A)⁻¹ * Aᵀ) *ᵥ y) '' Metric.closedBall b R := by
    intro x hx
    refine ⟨A *ᵥ x, ?_, g69cf_left hA x⟩
    rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR0]
    intro i
    rw [Real.norm_eq_abs, hR, le_div_iff₀ hε, mul_comm]
    have := hkey _ hx.1 i
    have h2 := hcx x
    have h3 := hcx x1
    have h4 := hx.2
    simp only [Pi.sub_apply] at this ⊢
    linarith
  have hSk : IsCompact S :=
    ((isCompact_closedBall b R).image
      (Continuous.matrix_mulVec continuous_const continuous_id)).of_isClosed_subset hSc hsub
  obtain ⟨x, hxS, hmin⟩ := hSk.exists_isMinOn ⟨x1, hx1, le_rfl⟩ hccont.continuousOn
  refine ⟨x, hxS.1, fun x' hx' => ?_⟩
  by_cases h : c ⬝ᵥ x' ≤ c ⬝ᵥ x1
  · exact hmin ⟨hx', h⟩
  · have := hxS.2; have h2 := not_le.mp h; linarith

lemma g69cf_pglb {m n : ℕ} {K : Set (Fin m → ℝ)} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {x : Fin n → ℝ} (hx : IsPrimalOptimal K A b c x) :
    IsPrimalOptimalValue K A b c (c ⬝ᵥ x) := by
  refine ⟨?_, fun v hv => hv ⟨x, hx.1, rfl⟩⟩
  rintro t ⟨x', hx', rfl⟩; exact hx.2 x' hx'

lemma g69cf_dlub {m n : ℕ} {K : Set (Fin m → ℝ)} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {l : Fin m → ℝ} (hl : IsDualOptimal K A b c l) :
    IsDualOptimalValue K A b c (b ⬝ᵥ l) := by
  refine ⟨?_, fun v hv => hv ⟨l, hl.1, rfl⟩⟩
  rintro t ⟨l', hl', rfl⟩; exact hl.2 l' hl'

lemma g69cf_3a {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hB : PrimalBoundedBelow K A b c) (hP : PrimalStrictlyFeasible K A b) :
    ∃ l : Fin m → ℝ, IsDualOptimal K A b c l ∧ IsPrimalOptimalValue K A b c (b ⬝ᵥ l) := by
  obtain ⟨L, hL⟩ := hB
  obtain ⟨x0, hx0⟩ := hP
  set T := {t : ℝ | ∃ x, PrimalFeasible K A b x ∧ t = c ⬝ᵥ x}
  have hne : T.Nonempty := ⟨_, x0, interior_subset hx0, rfl⟩
  have hbdd : BddBelow T := ⟨L, by rintro t ⟨x, hx, rfl⟩; exact hL x hx⟩
  have hglb := isGLB_csInf hne hbdd
  obtain ⟨l, hl, hlc, hld⟩ := g69cd_scalar K hK.1 A b c (sInf T) ⟨x0, hx0⟩
    (fun x hx => hglb.1 ⟨x, hx, rfl⟩)
  have hdf : DualFeasible K A c l := ⟨hlc, hl⟩
  have hup : ∀ l', DualFeasible K A c l' → b ⬝ᵥ l' ≤ sInf T := fun l' hl' =>
    hglb.2 (by rintro t ⟨x, hx, rfl⟩; exact g69cf_wd hx hl')
  have heq : b ⬝ᵥ l = sInf T := le_antisymm (hup l hdf) (by rw [dotProduct_comm]; exact hld)
  refine ⟨l, ⟨hdf, fun l' hl' => heq ▸ hup l' hl'⟩, ?_⟩
  rw [heq]; exact hglb

lemma g69cf_3b {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hB : DualBoundedAbove K A b c) (hD : DualStrictlyFeasible K A c) :
    ∃ x : Fin n → ℝ, IsPrimalOptimal K A b c x ∧ IsDualOptimalValue K A b c (c ⬝ᵥ x) := by
  obtain ⟨U, hU⟩ := hB
  obtain ⟨l0, hl0c, hl0⟩ := hD
  obtain ⟨x1, hx1, -⟩ := g69cf_dscalar K hK.1 hK.2.2.1 A hA b c l0 hl0 hl0c U hU
  obtain ⟨x, hx⟩ := g69cf_attain K hK.2.2.1 A hA b c l0 hl0 hl0c x1 hx1
  refine ⟨x, hx, ?_, ?_⟩
  · rintro t ⟨l, hl, rfl⟩; exact g69cf_wd hx.1 hl
  · intro V hV
    obtain ⟨x2, hx2, hx2V⟩ := g69cf_dscalar K hK.1 hK.2.2.1 A hA b c l0 hl0 hl0c V
      (fun l hl => hV ⟨l, hl, rfl⟩)
    exact (hx.2 x2 hx2).trans hx2V

lemma g69cf_iff {m n : ℕ} {K : Set (Fin m → ℝ)} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} (v : ℝ) (hv1 : IsPrimalOptimalValue K A b c v)
    (hv2 : IsDualOptimalValue K A b c v) (x : Fin n → ℝ) (l : Fin m → ℝ)
    (hx : PrimalFeasible K A b x) (hl : DualFeasible K A c l) :
    ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ b ⬝ᵥ l = c ⬝ᵥ x) ∧
      ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ l ⬝ᵥ (A *ᵥ x - b) = 0) := by
  have h1 : (IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ b ⬝ᵥ l = c ⬝ᵥ x := by
    constructor
    · rintro ⟨hxo, hlo⟩
      rw [(g69cf_pglb hxo).unique hv1, (g69cf_dlub hlo).unique hv2]
    · intro h
      refine ⟨⟨hx, fun x' hx' => ?_⟩, ⟨hl, fun l' hl' => ?_⟩⟩
      · rw [← h]; exact g69cf_wd hx' hl
      · rw [h]; exact g69cf_wd hx hl'
  refine ⟨h1, h1.trans ?_⟩
  have := g69cd_At A l x
  rw [hl.1] at this
  rw [dotProduct_sub, ← this, dotProduct_comm l b]
  constructor <;> intro h <;> linarith

theorem solution {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : PrimalStrictlyFeasible K A b) (hD : DualStrictlyFeasible K A c) :
    PrimalSolvable K A b c ∧ DualSolvable K A b c ∧
    (∃ v : ℝ, IsPrimalOptimalValue K A b c v ∧ IsDualOptimalValue K A b c v) ∧
    (∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ b ⬝ᵥ l = c ⬝ᵥ x) ∧
      ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ l ⬝ᵥ (A *ᵥ x - b) = 0)) := by
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨l0, hl0c, hl0⟩ := hD
  have hBB : PrimalBoundedBelow K A b c :=
    ⟨b ⬝ᵥ l0, fun x hx => g69cf_wd hx ⟨hl0c, interior_subset hl0⟩⟩
  have hDA : DualBoundedAbove K A b c :=
    ⟨c ⬝ᵥ x0, fun l hl => g69cf_wd (interior_subset hx0) hl⟩
  obtain ⟨l, hl, hv⟩ := g69cf_3a K hK A b c hBB ⟨x0, hx0⟩
  obtain ⟨x, hx, -⟩ := g69cf_3b K hK A hA b c hDA ⟨l0, hl0c, hl0⟩
  exact ⟨⟨x, hx⟩, ⟨l, hl⟩, ⟨_, hv, g69cf_dlub hl⟩, g69cf_iff _ hv (g69cf_dlub hl)⟩
