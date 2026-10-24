-- Prove2me | solution 1 for MonoSkew.Main.theorem_2_5_i
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T12:26:04.671982+00:00
-- url     : https://prove2.me/submissions/352fcbc2-6cf5-4588-ba19-e01985acb734

import Mathlib
import Definitions.Def_MonoSkew_Main_Basic
import Theorems.Thm_GradErrors_Deterministic_lemma_1


/-!
# Deterministic quasi-Fejer convergence with summable errors

Source: Benar F. Svaiter, *Fejer-convergent algorithms which accept summable
errors, approximated resolvents and the Hybrid Proximal-Extragradient method*,
Definition 2.1 and Proposition 2.2 (2)-(3), printed pp. 2-3.
https://webdoc.sub.gwdg.de/ebook/serien/e/IMPA_A/715.pdf

These are formalizations of standard published results, not new mathematical
claims. The scalar proof uses Mathlib's monotone convergence and convergence of
partial sums. The metric result needs neither completeness nor compactness:
the required convergent subsequence is an explicit hypothesis.
-/

open Filter Topology
open scoped BigOperators

namespace MonoSkew.FBFScalar

/-- A nonnegative real sequence whose upward increments are bounded by a
nonnegative summable error sequence has a finite limit. This is the scalar
core of Svaiter's Proposition 2.2 (2). -/
theorem scalar_converges_of_summable_error (a e : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (he : ∀ n, 0 ≤ e n) (hsum : Summable e)
    (hstep : ∀ n, a (n + 1) ≤ a n + e n) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  let b : ℕ → ℝ := fun n => a n - ∑ i ∈ Finset.range n, e i
  have hb : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [b]
    rw [Finset.sum_range_succ]
    linarith [hstep n]
  have hbounded : BddBelow (Set.range b) := by
    refine ⟨-(∑' i, e i), ?_⟩
    rintro _ ⟨n, rfl⟩
    have hs := hsum.sum_le_tsum (Finset.range n) (fun i _ => he i)
    dsimp [b]
    linarith [ha n]
  refine ⟨(⨅ n, b n) + ∑' i, e i, ?_⟩
  have hlim := (tendsto_atTop_ciInf hb hbounded).add hsum.hasSum.tendsto_sum_nat
  simpa only [b, sub_add_cancel] using hlim

universe u

/-- Svaiter's Proposition 2.2 (2), specialized to a fixed target point. -/
theorem dist_converges_of_summable_error {X : Type u} [MetricSpace X]
    (x : ℕ → X) (y : X) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hsum : Summable e)
    (hstep : ∀ n, dist (x (n + 1)) y ≤ dist (x n) y + e n) :
    ∃ L : ℝ, Tendsto (fun n => dist (x n) y) atTop (𝓝 L) :=
  scalar_converges_of_summable_error (fun n => dist (x n) y) e
    (fun _ => dist_nonneg) he hsum hstep

/-- Svaiter's Proposition 2.2 (3), with the cluster point supplied by an
explicit strictly increasing subsequence. A summable error controls the distance
to the target, not the distance between successive iterates. -/
theorem tendsto_of_summable_error_of_subseq {X : Type u} [MetricSpace X]
    (x : ℕ → X) (y : X) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hsum : Summable e)
    (hstep : ∀ n, dist (x (n + 1)) y ≤ dist (x n) y + e n)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsub : Tendsto (x ∘ φ) atTop (𝓝 y)) :
    Tendsto x atTop (𝓝 y) := by
  obtain ⟨L, hL⟩ := dist_converges_of_summable_error x y e he hsum hstep
  have hzero : Tendsto (fun n => dist (x (φ n)) y) atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hsub
  have heq : L = 0 := tendsto_nhds_unique (hL.comp hφ.tendsto_atTop) hzero
  rw [heq] at hL
  exact tendsto_iff_dist_tendsto_zero.mpr hL

end MonoSkew.FBFScalar

open InnerProductSpace
open ThreeOpSplitting.Convergence MonoSkew.Main
namespace MonoSkew.FBF
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Resolvent nonexpansiveness from monotonicity; no maximality is needed when J is supplied. -/
theorem resolvent_nonexpansive (A : E → Set E) (hA : IsMonotoneOp A)
    (γ : ℝ) (hγ : 0 < γ) (J : E → E) (hJ : IsResolvent γ A J) (u v : E) :
    ‖J u - J v‖ ≤ ‖u - v‖ := by
  have hm := hA (J u) (J v) (γ⁻¹ • (u-J u)) (γ⁻¹ • (v-J v)) (hJ u) (hJ v)
  rw [← smul_sub, inner_smul_right] at hm
  have hm' : 0 ≤ ⟪J u-J v, (u-J u)-(v-J v)⟫_ℝ :=
    nonneg_of_mul_nonneg_right hm (inv_pos.mpr hγ)
  have he : (u-J u)-(v-J v) = (u-v)-(J u-J v) := by abel
  rw [he, inner_sub_right, real_inner_self_eq_norm_sq] at hm'
  have hc := real_inner_le_norm (J u-J v) (u-v)
  have hp := norm_nonneg (J u-J v)
  have hq := norm_nonneg (u-v)
  nlinarith

/-- Briceño-Arias--Combettes arXiv:1011.5517v1, (2.7), p.6:
the exact comparison FBF step decreases distance by the residual energy. -/
theorem energy_step (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (hB : IsMonotoneOp (fun u => ({B u} : Set E)))
    (β : ℝ) (hβ : 0 ≤ β) (hBlip : ∀ u v, ‖B u-B v‖ ≤ β*‖u-v‖)
    (γ : ℝ) (hγ : 0 < γ) (J : E → E) (hJ : IsResolvent γ A J)
    (x z : E) (hz : z ∈ zer (addSingle A B)) :
    let p := J (x-γ • B x)
    ‖p+γ • (B x-B p)-z‖^2 ≤ ‖x-z‖^2-(1-γ^2*β^2)*‖x-p‖^2 := by
  dsimp only
  let p := J (x-γ • B x)
  change ‖p+γ • (B x-B p)-z‖^2 ≤ ‖x-z‖^2-(1-γ^2*β^2)*‖x-p‖^2
  obtain ⟨az, haz, hez⟩ := hz
  have haz' : -B z ∈ A z := by
    have hazEq : az = -B z := eq_neg_of_add_eq_zero_left hez.symm
    simpa only [hazEq] using haz
  have hm := hA p z (γ⁻¹ • ((x-γ • B x)-p)) (-B z) (hJ _) haz'
  have hb := hB p z (B p) (B z) (by simp) (by simp)
  have hg : γ ≠ 0 := ne_of_gt hγ
  have hm2 := mul_nonneg (le_of_lt hγ) hm
  simp only [inner_sub_right, inner_smul_right, inner_neg_right] at hm2
  have hi : γ * (γ⁻¹ * ⟪p-z, x-p⟫_ℝ - ⟪p-z, B x⟫_ℝ + ⟪p-z, B z⟫_ℝ) ≥ 0 := by
    have heq : γ * (γ⁻¹ * ⟪p-z, x-p⟫_ℝ - ⟪p-z, B x⟫_ℝ + ⟪p-z, B z⟫_ℝ) =
        γ * (γ⁻¹ * (⟪p-z, x⟫_ℝ - γ * ⟪p-z, B x⟫_ℝ - ⟪p-z,p⟫_ℝ) - -⟪p-z,B z⟫_ℝ) := by
      simp only [inner_sub_right]
      field_simp
      <;> ring
    rw [heq]
    exact hm2
  have hmono : γ * ⟪p-z, B x-B p⟫_ℝ ≤ ⟪p-z,x-p⟫_ℝ := by
    simp only [inner_sub_right] at hb ⊢
    simp only [inner_sub_right] at hi
    field_simp at hi
    nlinarith [mul_nonneg (le_of_lt hγ) hb]
  have hl := hBlip x p
  have hl2 : ‖B x-B p‖^2 ≤ β^2*‖x-p‖^2 := by
    nlinarith [norm_nonneg (B x-B p), norm_nonneg (x-p)]
  have he1 : p+γ • (B x-B p)-z = (p-z)+γ • (B x-B p) := by abel
  have he2 : x-z = (p-z)+(x-p) := by abel
  rw [he1, he2, norm_add_sq_real, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hγ]
  nlinarith [mul_nonneg (sq_nonneg γ) (sub_nonneg.mpr hl2)]
end MonoSkew.FBF


/-! One-step error estimates for the inexact forward-backward-forward iteration,
Briceño-Arias--Combettes, arXiv:1011.5517v1, (2.8)--(2.11).
The resolvent is supplied; maximality and completeness are not needed for these estimates. -/

open ThreeOpSplitting.Convergence MonoSkew.Main

namespace MonoSkew.FBF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The perturbed resolvent point differs from its exact comparison point by at most
`γ ‖a‖ + ‖b‖`. -/
theorem perturbed_resolvent_bound (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (γ : ℝ) (hγ : 0 < γ) (J : E → E) (hJ : IsResolvent γ A J)
    (x a b : E) :
    ‖(J (x - γ • (B x + a)) + b) - J (x - γ • B x)‖ ≤ γ * ‖a‖ + ‖b‖ := by
  have hin : (x - γ • (B x + a)) - (x - γ • B x) = -(γ • a) := by
    simp only [smul_add]
    abel
  calc
    _ = ‖(J (x - γ • (B x + a)) - J (x - γ • B x)) + b‖ := by
      congr 1
      abel
    _ ≤ ‖J (x - γ • (B x + a)) - J (x - γ • B x)‖ + ‖b‖ := norm_add_le _ _
    _ ≤ ‖(x - γ • (B x + a)) - (x - γ • B x)‖ + ‖b‖ :=
      by
        gcongr
        exact resolvent_nonexpansive A hA γ hγ J hJ _ _
    _ = γ * ‖a‖ + ‖b‖ := by
      rw [hin, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]

/-- General step error estimate before imposing an upper bound on the step size. -/
theorem perturbation_step_bound (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (β : ℝ) (hβ : 0 ≤ β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℝ) (hγ : 0 < γ) (J : E → E) (hJ : IsResolvent γ A J)
    (x a b c : E) :
    let y := x - γ • (B x + a)
    let p := J y + b
    let q := p - γ • (B p + c)
    let pt := J (x - γ • B x)
    ‖(x - y + q) - (pt + γ • (B x - B pt))‖ ≤
      (1 + γ * β) * (γ * ‖a‖ + ‖b‖) + γ * ‖a‖ + γ * ‖c‖ := by
  dsimp only
  let p := J (x - γ • (B x + a)) + b
  let pt := J (x - γ • B x)
  change ‖(x - (x - γ • (B x + a)) + (p - γ • (B p + c))) -
      (pt + γ • (B x - B pt))‖ ≤ _
  have he : (x - (x - γ • (B x + a)) + (p - γ • (B p + c))) -
      (pt + γ • (B x - B pt)) =
      ((p - pt) + γ • (B pt - B p)) + γ • a - γ • c := by
    simp only [smul_add, smul_sub]
    abel
  have hp : ‖p - pt‖ ≤ γ * ‖a‖ + ‖b‖ :=
    perturbed_resolvent_bound A hA B γ hγ J hJ x a b
  have hb : ‖B pt - B p‖ ≤ β * ‖p - pt‖ := by
    simpa only [norm_sub_rev] using hBlip pt p
  have hcoef : 0 ≤ 1 + γ * β := by positivity
  rw [he]
  calc
    _ ≤ (‖p - pt‖ + ‖γ • (B pt - B p)‖) + ‖γ • a‖ + ‖γ • c‖ := by
      calc
        _ ≤ ‖(p - pt) + γ • (B pt - B p) + γ • a‖ + ‖γ • c‖ := norm_sub_le _ _
        _ ≤ (‖(p - pt) + γ • (B pt - B p)‖ + ‖γ • a‖) + ‖γ • c‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ = ‖p - pt‖ + γ * ‖B pt - B p‖ + γ * ‖a‖ + γ * ‖c‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    _ ≤ ‖p - pt‖ + γ * (β * ‖p - pt‖) + γ * ‖a‖ + γ * ‖c‖ := by
      gcongr
    _ = (1 + γ * β) * ‖p - pt‖ + γ * ‖a‖ + γ * ‖c‖ := by ring
    _ ≤ _ := by gcongr

/-- For `γ ≤ 1/β`, the step error is bounded by `3γ ‖a‖ + 2 ‖b‖ + γ ‖c‖`. -/
theorem perturbation_step_bound_three (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (β : ℝ) (hβ : 0 < β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℝ) (hγ : 0 < γ) (hγub : γ ≤ 1 / β)
    (J : E → E) (hJ : IsResolvent γ A J) (x a b c : E) :
    let y := x - γ • (B x + a)
    let p := J y + b
    let q := p - γ • (B p + c)
    let pt := J (x - γ • B x)
    ‖(x - y + q) - (pt + γ • (B x - B pt))‖ ≤
      3 * γ * ‖a‖ + 2 * ‖b‖ + γ * ‖c‖ := by
  have hγβ : γ * β ≤ 1 := (le_div_iff₀ hβ).mp hγub
  refine (perturbation_step_bound A hA B β hβ.le hBlip γ hγ J hJ x a b c).trans ?_
  calc
    _ ≤ 2 * (γ * ‖a‖ + ‖b‖) + γ * ‖a‖ + γ * ‖c‖ := by
      gcongr
      linarith
    _ = _ := by ring

/-- Uniform bound (2.11) on the error in the actual FBF update relative to its exact
comparison update. No monotonicity of the Lipschitz forward operator is needed here. -/
theorem perturbation_step_bound_uniform (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (β : ℝ) (hβ : 0 < β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℝ) (hγ : 0 < γ) (hγub : γ ≤ 1 / β)
    (J : E → E) (hJ : IsResolvent γ A J) (x a b c : E) :
    let y := x - γ • (B x + a)
    let p := J y + b
    let q := p - γ • (B p + c)
    let pt := J (x - γ • B x)
    ‖(x - y + q) - (pt + γ • (B x - B pt))‖ ≤
      (3 / β) * ‖a‖ + 2 * ‖b‖ + (1 / β) * ‖c‖ := by
  refine (perturbation_step_bound_three A hA B β hβ hBlip γ hγ hγub J hJ x a b c).trans ?_
  have ha : 3 * γ * ‖a‖ ≤ (3 / β) * ‖a‖ := by
    gcongr
    calc
      3 * γ ≤ 3 * (1 / β) := mul_le_mul_of_nonneg_left hγub (by norm_num)
      _ = 3 / β := by ring
  have hc : γ * ‖c‖ ≤ (1 / β) * ‖c‖ := by gcongr
  linarith

/-- The difference between the two forward evaluations is controlled by the FBF
resolvent residual and the two forward errors. -/
theorem forward_residual_bound (B : E → E) (β : ℝ) (hβ : 0 < β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℝ) (hγ : 0 < γ) (hγub : γ ≤ 1 / β) (x p a c : E) :
    ‖(x - γ • (B x + a)) - (p - γ • (B p + c))‖ ≤
      2 * ‖x - p‖ + (1 / β) * (‖a‖ + ‖c‖) := by
  have hγβ : γ * β ≤ 1 := (le_div_iff₀ hβ).mp hγub
  have he : (x - γ • (B x + a)) - (p - γ • (B p + c)) =
      ((x - p) - γ • (B x - B p)) - γ • a + γ • c := by
    simp only [smul_add, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ (‖x - p‖ + ‖γ • (B x - B p)‖) + ‖γ • a‖ + ‖γ • c‖ := by
      calc
        _ ≤ ‖(x - p) - γ • (B x - B p) - γ • a‖ + ‖γ • c‖ := norm_add_le _ _
        _ ≤ (‖(x - p) - γ • (B x - B p)‖ + ‖γ • a‖) + ‖γ • c‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖x - p‖ + γ * ‖B x - B p‖ + γ * ‖a‖ + γ * ‖c‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    _ ≤ ‖x - p‖ + γ * (β * ‖x - p‖) + γ * ‖a‖ + γ * ‖c‖ := by
      gcongr
      exact hBlip x p
    _ ≤ 2 * ‖x - p‖ + (1 / β) * (‖a‖ + ‖c‖) := by
      have hr : γ * (β * ‖x - p‖) ≤ ‖x - p‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hγβ (norm_nonneg (x - p))]
      have ha := mul_le_mul_of_nonneg_right hγub (norm_nonneg a)
      have hc := mul_le_mul_of_nonneg_right hγub (norm_nonneg c)
      nlinarith

/-- The uniform resolvent estimate specialized to the platform's iteration predicate. -/
theorem IsFBFRun.resolvent_bound (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (β : ℝ) (γ : ℕ → ℝ) (J : ℕ → E → E)
    (a b c x y p q : ℕ → E) (hrun : IsFBFRun B γ J a b c x y p q)
    (hγ : ∀ n, 0 < γ n) (hγub : ∀ n, γ n ≤ 1 / β)
    (hJ : ∀ n, IsResolvent (γ n) A (J n)) (n : ℕ) :
    ‖p n - J n (x n - γ n • B (x n))‖ ≤ (1 / β) * ‖a n‖ + ‖b n‖ := by
  obtain ⟨hy, hp, _, _⟩ := hrun n
  rw [hp, hy]
  refine (perturbed_resolvent_bound A hA B (γ n) (hγ n) (J n) (hJ n)
    (x n) (a n) (b n)).trans ?_
  gcongr
  exact hγub n

/-- The uniform one-step estimate specialized to the platform's iteration predicate. -/
theorem IsFBFRun.perturbation_bound (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (β : ℝ) (hβ : 0 < β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℕ → ℝ) (J : ℕ → E → E) (a b c x y p q : ℕ → E)
    (hrun : IsFBFRun B γ J a b c x y p q)
    (hγ : ∀ n, 0 < γ n) (hγub : ∀ n, γ n ≤ 1 / β)
    (hJ : ∀ n, IsResolvent (γ n) A (J n)) (n : ℕ) :
    let pt := J n (x n - γ n • B (x n))
    ‖x (n + 1) - (pt + γ n • (B (x n) - B pt))‖ ≤
      (3 / β) * ‖a n‖ + 2 * ‖b n‖ + (1 / β) * ‖c n‖ := by
  obtain ⟨hy, hp, hq, hx⟩ := hrun n
  rw [hx, hq, hp, hy]
  exact perturbation_step_bound_uniform A hA B β hβ hBlip (γ n) (hγ n) (hγub n)
    (J n) (hJ n) (x n) (a n) (b n) (c n)

/-- The forward residual estimate specialized to the platform's iteration predicate. -/
theorem IsFBFRun.forward_residual_bound (B : E → E) (β : ℝ) (hβ : 0 < β)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (γ : ℕ → ℝ) (J : ℕ → E → E) (a b c x y p q : ℕ → E)
    (hrun : IsFBFRun B γ J a b c x y p q)
    (hγ : ∀ n, 0 < γ n) (hγub : ∀ n, γ n ≤ 1 / β) (n : ℕ) :
    ‖y n - q n‖ ≤ 2 * ‖x n - p n‖ + (1 / β) * (‖a n‖ + ‖c n‖) := by
  obtain ⟨hy, _, hq, _⟩ := hrun n
  rw [hy, hq]
  exact _root_.MonoSkew.FBF.forward_residual_bound B β hβ hBlip (γ n) (hγ n) (hγub n)
    (x n) (p n) (a n) (c n)

end MonoSkew.FBF


/-! The perturbation argument behind arXiv:1011.5517v1, equations (2.12)--(2.15).
The ideal step has squared-distance descent; the actual step differs by a
summable distance error. The existing platform scalar descent theorem is reused.
-/
open Filter Topology

namespace QuasiFejerOpial

theorem summable_sq_of_nonneg {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (hs : Summable e) : Summable (fun n => e n ^ 2) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hs.tendsto_atTop_zero).exists_norm_le
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg (e n)) _ (hs.mul_left B)
  intro n
  have hb := hB (e n) ⟨n, rfl⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (he n)] at hb
  nlinarith [mul_nonneg (he n) (sub_nonneg.mpr hb)]

theorem summable_residual_of_perturbed_descent {X : Type*} [MetricSpace X]
    (x ideal : ℕ → X) (z : X) (e r : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (he : ∀ n, 0 ≤ e n) (hs : Summable e)
    (herr : ∀ n, dist (x (n + 1)) (ideal n) ≤ e n)
    (hdesc : ∀ n, dist (ideal n) z ^ 2 ≤ dist (x n) z ^ 2 - δ * r n ^ 2) :
    Summable (fun n => r n ^ 2) ∧
      ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Summable η ∧
        ∀ n, dist (x (n + 1)) z ^ 2 ≤ dist (x n) z ^ 2 - δ * r n ^ 2 + η n := by
  have hideal (n : ℕ) : dist (ideal n) z ≤ dist (x n) z := by
    have hd := hdesc n
    have hr := mul_nonneg hδ.le (sq_nonneg (r n))
    nlinarith [dist_nonneg (x := ideal n) (y := z), dist_nonneg (x := x n) (y := z)]
  have htri (n : ℕ) : dist (x (n + 1)) z ≤ dist (ideal n) z + e n := by
    have := dist_triangle (x (n + 1)) (ideal n) z
    linarith [herr n]
  have hstep (n : ℕ) : dist (x (n + 1)) z ≤ dist (x n) z + e n := by
    linarith [htri n, hideal n]
  obtain ⟨L, hL⟩ := MonoSkew.FBFScalar.dist_converges_of_summable_error x z e he hs hstep
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hL).exists_norm_le
  have hbound (n : ℕ) : dist (x n) z ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hM (dist (x n) z) ⟨n, rfl⟩
  have hM0 : 0 ≤ M := dist_nonneg.trans (hbound 0)
  let η : ℕ → ℝ := fun n => 2 * M * e n + e n ^ 2
  have hη : ∀ n, 0 ≤ η n := fun n => add_nonneg (mul_nonneg (by positivity) (he n)) (sq_nonneg _)
  have hsη : Summable η := (hs.mul_left (2 * M)).add (summable_sq_of_nonneg he hs)
  have hrec (n : ℕ) : dist (x (n + 1)) z ^ 2 ≤ dist (x n) z ^ 2 - δ * r n ^ 2 + η n := by
    have hi := hideal n
    have hb := hbound n
    have ht := htri n
    have hd := hdesc n
    have hen := he n
    have hp : 0 ≤ (dist (ideal n) z + e n - dist (x (n + 1)) z) *
        (dist (ideal n) z + e n + dist (x (n + 1)) z) :=
      mul_nonneg (by linarith) (by positivity)
    have hm : 0 ≤ (M - dist (ideal n) z) * e n := mul_nonneg (by linarith) (he n)
    dsimp [η]
    nlinarith
  obtain hbad | ⟨_, hsum⟩ := GradErrors.Deterministic.lemma_1
    (fun n => dist (x n) z ^ 2) (fun n => δ * r n ^ 2) η
    (fun n => mul_nonneg hδ.le (sq_nonneg _)) hrec
    ⟨∑' n, η n, hsη.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)⟩
  · obtain ⟨N, hN⟩ := (tendsto_atTop_atBot.mp hbad) (-1)
    have := hN N le_rfl
    nlinarith [sq_nonneg (dist (x N) z)]
  · exact ⟨(summable_mul_left_iff (ne_of_gt hδ)).mp hsum, η, hη, hsη, hrec⟩

end QuasiFejerOpial


/-! Scalar bookkeeping for the inexact FBF residual estimates. -/
namespace MonoSkew.FBF

theorem step_coefficient_lower (β ε γ : ℝ) (hβ : 0 < β)
    (hε0 : 0 < ε) (hε1 : ε < 1 / (β + 1))
    (hγ : ε ≤ γ ∧ γ ≤ (1 - ε) / β) :
    0 < γ ∧ γ ≤ 1 / β ∧ ε ^ 2 ≤ 1 - γ ^ 2 * β ^ 2 := by
  have hεlt : ε < 1 := by
    have hmul := (lt_div_iff₀ (by linarith : 0 < β + 1)).mp hε1
    nlinarith [mul_pos hε0 hβ]
  have hγ0 : 0 < γ := hε0.trans_le hγ.1
  have hgb : γ * β ≤ 1 - ε := (le_div_iff₀ hβ).mp hγ.2
  refine ⟨hγ0, (le_div_iff₀ hβ).mpr (by linarith), ?_⟩
  have hs : (γ * β) ^ 2 ≤ (1 - ε) ^ 2 := by
    nlinarith [mul_pos hγ0 hβ]
  nlinarith [mul_nonneg hε0.le (sub_nonneg.mpr hεlt.le)]

theorem summable_sq_of_le_add (f u v : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hfu : ∀ n, f n ≤ u n + v n)
    (hsu : Summable (fun n => u n ^ 2)) (hsv : Summable (fun n => v n ^ 2)) :
    Summable (fun n => f n ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg (f n)) _
    ((hsu.mul_left 2).add (hsv.mul_left 2))
  intro n
  have hprod : 0 ≤ (u n + v n - f n) * (u n + v n + f n) :=
    mul_nonneg (sub_nonneg.mpr (hfu n)) (by linarith [hu n, hv n, hf n])
  nlinarith [sq_nonneg (u n - v n)]

end MonoSkew.FBF


/-! Inexact FBF residual square summability and the retained quasi-Fejer estimate.
Source: Briceno-Arias--Combettes, arXiv:1011.5517v1, Theorem 2.5(i).
-/
open Filter Topology InnerProductSpace
open ThreeOpSplitting.Convergence MonoSkew.Main

namespace MonoSkew.FBF
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem at_solution (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (hB : IsMonotoneOp (fun u => ({B u} : Set E)))
    (β : ℝ) (hβ : 0 < β) (hBlip : ∀ u w : E, ‖B u - B w‖ ≤ β * ‖u - w‖)
    (a b c : ℕ → E) (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖))
    (hc : Summable (fun n => ‖c n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (β + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / β)
    (J : ℕ → E → E) (hJ : ∀ n, IsResolvent (γ n) A (J n))
    (x y p q : ℕ → E) (hrun : IsFBFRun B γ J a b c x y p q)
    (z : E) (hz : z ∈ zer (addSingle A B)) :
    Summable (fun n => ‖x n - J n (x n - γ n • B (x n))‖ ^ 2) ∧
      ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Summable η ∧
        ∀ n, ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 + η n := by
  let pt : ℕ → E := fun n => J n (x n - γ n • B (x n))
  let ideal : ℕ → E := fun n => pt n + γ n • (B (x n) - B (pt n))
  let err : ℕ → ℝ := fun n => (3 / β) * ‖a n‖ + 2 * ‖b n‖ + (1 / β) * ‖c n‖
  have herr0 : ∀ n, 0 ≤ err n := fun n => by dsimp [err]; positivity
  have herrs : Summable err := ((ha.mul_left (3 / β)).add (hb.mul_left 2)).add (hc.mul_left (1 / β))
  have hstep (n : ℕ) := step_coefficient_lower β ε (γ n) hβ hε0 hε1 (hγ n)
  have herr (n : ℕ) : dist (x (n + 1)) (ideal n) ≤ err n := by
    simpa only [dist_eq_norm, ideal, pt, err] using
      IsFBFRun.perturbation_bound A hA B β hβ hBlip γ J a b c x y p q hrun
        (fun n => (hstep n).1) (fun n => (hstep n).2.1) hJ n
  have hdes (n : ℕ) : dist (ideal n) z ^ 2 ≤ dist (x n) z ^ 2 - ε ^ 2 * ‖x n - pt n‖ ^ 2 := by
    have hd := energy_step A hA B hB β hβ.le hBlip (γ n) (hstep n).1 (J n) (hJ n) (x n) z hz
    have hcoef := mul_le_mul_of_nonneg_right (hstep n).2.2 (sq_nonneg ‖x n - pt n‖)
    simp only [dist_eq_norm]
    change ‖ideal n - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 - (1 - γ n ^ 2 * β ^ 2) * ‖x n - pt n‖ ^ 2 at hd
    linarith
  obtain ⟨hs, η, hη, hsη, hrec⟩ := QuasiFejerOpial.summable_residual_of_perturbed_descent
    x ideal z err (fun n => ‖x n - pt n‖) (ε ^ 2) (sq_pos_of_pos hε0) herr0 herrs herr hdes
  refine ⟨hs, η, hη, hsη, ?_⟩
  intro n
  have hd := hrec n
  simp only [dist_eq_norm] at hd
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖x n - pt n‖)]

theorem residual_summability (A : E → Set E) (hA : IsMonotoneOp A)
    (B : E → E) (hB : IsMonotoneOp (fun u => ({B u} : Set E)))
    (hzer : (zer (addSingle A B)).Nonempty)
    (β : ℝ) (hβ : 0 < β) (hBlip : ∀ u w : E, ‖B u - B w‖ ≤ β * ‖u - w‖)
    (a b c : ℕ → E) (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖))
    (hc : Summable (fun n => ‖c n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (β + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / β)
    (J : ℕ → E → E) (hJ : ∀ n, IsResolvent (γ n) A (J n))
    (x y p q : ℕ → E) (hrun : IsFBFRun B γ J a b c x y p q) :
    Summable (fun n => ‖x n - p n‖ ^ 2) ∧ Summable (fun n => ‖y n - q n‖ ^ 2) := by
  obtain ⟨z, hz⟩ := hzer
  have hspt := (at_solution A hA B hB β hβ hBlip a b c ha hb hc ε hε0 hε1 γ hγ J hJ x y p q hrun z hz).1
  let pt : ℕ → E := fun n => J n (x n - γ n • B (x n))
  let g : ℕ → ℝ := fun n => (1 / β) * ‖a n‖ + ‖b n‖
  let h : ℕ → ℝ := fun n => (1 / β) * (‖a n‖ + ‖c n‖)
  have hg0 : ∀ n, 0 ≤ g n := fun n => by dsimp [g]; positivity
  have hh0 : ∀ n, 0 ≤ h n := fun n => by dsimp [h]; positivity
  have hgs : Summable g := (ha.mul_left (1 / β)).add hb
  have hhs : Summable h := (ha.add hc).mul_left (1 / β)
  have hstep (n : ℕ) := step_coefficient_lower β ε (γ n) hβ hε0 hε1 (hγ n)
  have hgp (n : ℕ) : ‖p n - pt n‖ ≤ g n :=
    IsFBFRun.resolvent_bound A hA B β γ J a b c x y p q hrun
      (fun n => (hstep n).1) (fun n => (hstep n).2.1) hJ n
  have hdom (n : ℕ) : ‖x n - p n‖ ≤ ‖x n - pt n‖ + g n := by
    have ht : ‖x n - p n‖ ≤ ‖x n - pt n‖ + ‖p n - pt n‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using dist_triangle (x n) (pt n) (p n)
    linarith [hgp n]
  have hsxp := summable_sq_of_le_add (fun n => ‖x n - p n‖) (fun n => ‖x n - pt n‖) g
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) hg0 hdom hspt
    (QuasiFejerOpial.summable_sq_of_nonneg hg0 hgs)
  refine ⟨hsxp, ?_⟩
  apply summable_sq_of_le_add (fun n => ‖y n - q n‖) (fun n => 2 * ‖x n - p n‖) h
    (fun n => norm_nonneg _) (fun n => by positivity) hh0
  · intro n
    exact IsFBFRun.forward_residual_bound B β hβ hBlip γ J a b c x y p q hrun
      (fun n => (hstep n).1) (fun n => (hstep n).2.1) n
  · simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsxp.mul_left 4
  · exact QuasiFejerOpial.summable_sq_of_nonneg hh0 hhs

end MonoSkew.FBF


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

open MonoSkew.Main

/-- Theorem 2.5(i) (p. 5): for the inexact forward–backward–forward iteration (2.3) with
absolutely summable errors and step sizes in `[ε, (1 − ε)/β]`,
`Σ ‖x_n − p_n‖² < ∞` and `Σ ‖y_n − q_n‖² < ∞`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → Set E) (hA : IsMaximalMonotone A)
    (B : E → E) (hB : IsMonotoneOp (fun u => ({B u} : Set E)))
    (hzer : (zer (addSingle A B)).Nonempty)
    (β : ℝ) (hβ : 0 < β) (hBlip : ∀ u w : E, ‖B u - B w‖ ≤ β * ‖u - w‖)
    (a b c : ℕ → E) (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖))
    (hc : Summable (fun n => ‖c n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (β + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / β)
    (J : ℕ → E → E) (hJ : ∀ n, IsResolvent (γ n) A (J n))
    (x y p q : ℕ → E) (hrun : IsFBFRun B γ J a b c x y p q) :
    Summable (fun n => ‖x n - p n‖ ^ 2) ∧ Summable (fun n => ‖y n - q n‖ ^ 2) := by
  exact MonoSkew.FBF.residual_summability A hA.1 B hB hzer β hβ hBlip
    a b c ha hb hc ε hε0 hε1 γ hγ J hJ x y p q hrun

