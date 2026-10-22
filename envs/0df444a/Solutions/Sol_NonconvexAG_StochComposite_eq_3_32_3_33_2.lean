-- Prove2me | solution 2 for NonconvexAG.StochComposite.eq_3_32_3_33
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:47:27.506676+00:00
-- url     : https://prove2.me/submissions/347a5dc3-fd37-4702-9674-2535ba452de0

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

set_option autoImplicit false

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD
open NonconvexAG.StochComposite

section YProx
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma yprox_var (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X) (x y p : V) (c : ℝ) (hc : 0 < c)
    (hpK : p ∈ K)
    (hmin : ∀ u ∈ K, inner ℝ y p + ‖p - x‖ ^ 2 / (2 * c) + X p ≤
      inner ℝ y u + ‖u - x‖ ^ 2 / (2 * c) + X u)
    (u : V) (hu : u ∈ K) :
    0 ≤ inner ℝ y (u - p) + (1 / c) * inner ℝ (p - x) (u - p) + X u - X p := by
  set A := inner ℝ y (u - p) + (1 / c) * inner ℝ (p - x) (u - p) + X u - X p with hA
  set B := ‖u - p‖ ^ 2 / (2 * c) with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B := by
    intro t ht ht1
    have hut : (1 - t) • p + t • u ∈ K := hX.1 hpK hu (by linarith) ht.le (by ring)
    have h1 := hmin _ hut
    have h2 : X ((1 - t) • p + t • u) ≤ (1 - t) • X p + t • X u :=
      hX.2 hpK hu (by linarith) ht.le (by ring)
    have e1 : (1 - t) • p + t • u - x = (p - x) + t • (u - p) := by module
    have e2 : inner ℝ y ((1 - t) • p + t • u) = inner ℝ y p + t * inner ℝ y (u - p) := by
      have : (1 - t) • p + t • u = p + t • (u - p) := by module
      rw [this, inner_add_right, inner_smul_right]
    have e3 : ‖(p - x) + t • (u - p)‖ ^ 2 = ‖p - x‖ ^ 2 + 2 * t * inner ℝ (p - x) (u - p) + t ^ 2 * ‖u - p‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e1, e3, e2] at h1
    simp only [smul_eq_mul] at h2
    have h3 : 0 ≤ t * A + t ^ 2 * B := by
      rw [hA, hB]
      have : t * (1 / c * inner ℝ (p - x) (u - p)) = 2 * t * inner ℝ (p - x) (u - p) / (2 * c) := by
        field_simp
      have h4 : t ^ 2 * ‖u - p‖ ^ 2 / (2 * c) = t ^ 2 * (‖u - p‖ ^ 2 / (2 * c)) := by ring
      have h5 : (‖p - x‖ ^ 2 + 2 * t * inner ℝ (p - x) (u - p) + t ^ 2 * ‖u - p‖ ^ 2) / (2 * c)
          = ‖p - x‖ ^ 2 / (2 * c) + 2 * t * inner ℝ (p - x) (u - p) / (2 * c) + t ^ 2 * ‖u - p‖ ^ 2 / (2 * c) := by
        ring
      rw [h5] at h1
      nlinarith [h1, h2, this, h4]
    have h6 : 0 ≤ t * (A + t * B) := by nlinarith [h3]
    exact (mul_nonneg_iff_of_pos_left ht).mp h6
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < min 1 (-A / (B + 1)) := lt_min one_pos (div_pos (by linarith) (by linarith))
  have := key _ hpos (min_le_left _ _)
  have h7 : min 1 (-A / (B + 1)) * (B + 1) ≤ -A := by
    have := min_le_right 1 (-A / (B + 1))
    calc min 1 (-A / (B + 1)) * (B + 1) ≤ (-A / (B + 1)) * (B + 1) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = -A := by field_simp
  nlinarith

/-- three-point inequality for a prox step -/
lemma yprox_three (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X) (x y p : V) (c : ℝ) (hc : 0 < c)
    (hpK : p ∈ K)
    (hmin : ∀ u ∈ K, inner ℝ y p + ‖p - x‖ ^ 2 / (2 * c) + X p ≤
      inner ℝ y u + ‖u - x‖ ^ 2 / (2 * c) + X u)
    (u : V) (hu : u ∈ K) :
    inner ℝ y (p - u) + X p ≤
      X u + 1 / (2 * c) * (‖x - u‖ ^ 2 - ‖p - u‖ ^ 2 - ‖p - x‖ ^ 2) := by
  have h := yprox_var K X hX x y p c hc hpK hmin u hu
  have e : 2 * inner ℝ (p - x) (u - p) = ‖u - x‖ ^ 2 - ‖p - x‖ ^ 2 - ‖u - p‖ ^ 2 := by
    have : u - x = (p - x) + (u - p) := by abel
    rw [this, norm_add_sq_real]; ring
  have e2 : inner ℝ y (p - u) = - inner ℝ y (u - p) := by
    rw [← inner_neg_right]; congr 1; abel
  have e3 : 1 / c * inner ℝ (p - x) (u - p) = 1 / (2 * c) * (2 * inner ℝ (p - x) (u - p)) := by
    field_simp
  rw [e3, e] at h
  have n1 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
  have n2 : ‖p - u‖ = ‖u - p‖ := norm_sub_rev _ _
  rw [n1, n2, e2]
  nlinarith [h]

end YProx

section YProx2
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma yprox_comb (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X)
    (g xp xagp xk xag xmd x : V) (α β lam : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 < β) (hlam : 0 < lam) (hαl : α * lam ≤ β)
    (hxmd : xmd = (1 - α) • xagp + α • xp)
    (hagp : α = 1 ∨ xagp ∈ K) (hxk : xk ∈ K) (hx : x ∈ K)
    (h1 : ∀ u ∈ K, inner ℝ g (xk - u) + X xk ≤
      X u + 1 / (2 * lam) * (‖xp - u‖ ^ 2 - ‖xk - u‖ ^ 2 - ‖xk - xp‖ ^ 2))
    (h2 : ∀ u ∈ K, inner ℝ g (xag - u) + X xag ≤
      X u + 1 / (2 * β) * (‖xmd - u‖ ^ 2 - ‖xag - u‖ ^ 2 - ‖xag - xmd‖ ^ 2)) :
    inner ℝ g (xag - α • x - (1 - α) • xagp) + X xag ≤
      (1 - α) * X xagp + α * X x + α / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2) -
        1 / (2 * β) * ‖xag - xmd‖ ^ 2 := by
  set u : V := (1 - α) • xagp + α • xk with hu
  have huK : u ∈ K ∧ X u ≤ (1 - α) * X xagp + α * X xk := by
    rcases hagp with h | h
    · have : u = xk := by rw [hu, h]; simp
      rw [this, h]; simp [hxk]
    · refine ⟨hX.1 h hxk (by linarith) hα0 (by ring), ?_⟩
      have := hX.2 h hxk (by linarith) hα0 (by ring : (1 - α) + α = 1)
      simpa [smul_eq_mul] using this
  have A := h2 u huK.1
  have B := h1 x hx
  have hn : ‖xmd - u‖ ^ 2 = α ^ 2 * ‖xp - xk‖ ^ 2 := by
    have : xmd - u = α • (xp - xk) := by rw [hxmd, hu]; module
    rw [this, norm_smul, mul_pow, Real.norm_of_nonneg hα0]
  have hin : inner ℝ g (xag - α • x - (1 - α) • xagp) =
      inner ℝ g (xag - u) + α * inner ℝ g (xk - x) := by
    have : xag - α • x - (1 - α) • xagp = (xag - u) + α • (xk - x) := by rw [hu]; module
    rw [this, inner_add_right, inner_smul_right]
  have hc : α ^ 2 / (2 * β) ≤ α / (2 * lam) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hα0 hα0, mul_nonneg hα0 (sub_nonneg.mpr hαl)]
  have hc2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖xp - xk‖)
  have hB := mul_le_mul_of_nonneg_left B hα0
  have hnn : 0 ≤ 1 / (2 * β) * ‖xag - u‖ ^ 2 := by positivity
  have hsw : ‖xk - xp‖ = ‖xp - xk‖ := norm_sub_rev _ _
  rw [hn] at A
  rw [hsw] at hB
  rw [hin]
  have e1 : 1 / (2 * β) * (α ^ 2 * ‖xp - xk‖ ^ 2 - ‖xag - u‖ ^ 2 - ‖xag - xmd‖ ^ 2)
      = α ^ 2 / (2 * β) * ‖xp - xk‖ ^ 2 - 1 / (2 * β) * ‖xag - u‖ ^ 2
        - 1 / (2 * β) * ‖xag - xmd‖ ^ 2 := by ring
  have e2 : α * (1 / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2 - ‖xp - xk‖ ^ 2))
      = α / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2) - α / (2 * lam) * ‖xp - xk‖ ^ 2 := by ring
  rw [e1] at A
  nlinarith [A, hB, hc2, hnn, huK.2, e2]

end YProx2

theorem solution {n : ℕ} (gΨ : E n → E n) (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k ω) + δ k ω) (xk k ω - x) + X (xk k ω) ≤
          X x + 1 / (2 * lam k) *
            (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2 - ‖xk k ω - xk (k - 1) ω‖ ^ 2) ∧
        inner ℝ (gΨ (xmd k ω) + δ k ω) (xag k ω - x) + X (xag k ω) ≤
          X x + 1 / (2 * β k) *
            (‖xmd k ω - x‖ ^ 2 - ‖xag k ω - x‖ ^ 2 - ‖xag k ω - xmd k ω‖ ^ 2) := by
  intro xk xag xmd δ ω k hk x hx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlam : 0 < lam (j + 1) := hstep.2.2.2.1 (j + 1) (by omega)
  have hβ : 0 < β (j + 1) := hstep.2.2.1 (j + 1) (by omega)
  have hg : gΨ (xmd (j + 1) ω) + δ (j + 1) ω =
      sampleAvg G m (j + 1) (xmd (j + 1) ω) (fun i => ξ i ω) := by
    show gΨ (xmd (j + 1) ω) + (Gbar G P α β lam m x0 ξ (j + 1) ω - gΨ (xmd (j + 1) ω)) = _
    rw [add_sub_cancel]; rfl
  set g := gΨ (xmd (j + 1) ω) + δ (j + 1) ω with hgdef
  have e1 : xk (j + 1) ω = P (xk j ω) g (lam (j + 1)) := by rw [hg]; rfl
  have e2 : xag (j + 1) ω = P (xmd (j + 1) ω) g (β (j + 1)) := by rw [hg]; rfl
  have e3 : xk (j + 1 - 1) ω = xk j ω := rfl
  rw [e3]
  refine ⟨?_, ?_⟩
  · have := yprox_three K X hX (xk j ω) g (xk (j + 1) ω) (lam (j + 1)) hlam
      (by rw [e1]; exact (hP _ _ _ hlam).1) (by rw [e1]; exact (hP _ _ _ hlam).2) x hx
    exact this
  · have := yprox_three K X hX (xmd (j + 1) ω) g (xag (j + 1) ω) (β (j + 1)) hβ
      (by rw [e2]; exact (hP _ _ _ hβ).1) (by rw [e2]; exact (hP _ _ _ hβ).2) x hx
    exact this
