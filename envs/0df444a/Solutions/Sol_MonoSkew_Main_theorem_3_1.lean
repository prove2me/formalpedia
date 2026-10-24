-- Prove2me | solution 1 for MonoSkew.Main.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T13:38:51.636251+00:00
-- url     : https://prove2.me/submissions/d24bea90-0d90-46b7-9747-928f0c9b725b

import Mathlib
import Definitions.Def_MonoSkew_Main_Basic
import Theorems.Thm_GradErrors_Deterministic_lemma_1
import Theorems.Thm_MonoSkew_Main_theorem_2_5_i
import Theorems.Thm_MonoSkew_Main_theorem_2_5_ii
import Theorems.Thm_MonoSkew_Main_proposition_2_7_i_iii
import Theorems.Thm_MonoSkew_Main_proposition_2_7_iv
import Theorems.Thm_MonoSkew_Main_proposition_2_8_i
import Theorems.Thm_MonoSkew_Main_proposition_2_8_ii_vi

/-! Standalone proof of the full primal-dual Theorem 3.1. Six public
theorem APIs are imported and actually used. New helper declarations
are isolated from the implementation namespaces of those dependencies.
Packaging phase: final; consult the package record for dependency status. -/
section PDRootInlineQuasiFejer

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

namespace MonoSkew.PDRootScalar

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

end MonoSkew.PDRootScalar

end PDRootInlineQuasiFejer

section PDRootInlineFBFEnergy

open InnerProductSpace
open ThreeOpSplitting.Convergence MonoSkew.Main
namespace MonoSkew.PDRootFBF
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
end MonoSkew.PDRootFBF

end PDRootInlineFBFEnergy

section PDRootInlineFBFPerturbation

/-! One-step error estimates for the inexact forward-backward-forward iteration,
Briceño-Arias--Combettes, arXiv:1011.5517v1, (2.8)--(2.11).
The resolvent is supplied; maximality and completeness are not needed for these estimates. -/

open ThreeOpSplitting.Convergence MonoSkew.Main

namespace MonoSkew.PDRootFBF

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
  exact _root_.MonoSkew.PDRootFBF.forward_residual_bound B β hβ hBlip (γ n) (hγ n) (hγub n)
    (x n) (p n) (a n) (c n)

end MonoSkew.PDRootFBF

end PDRootInlineFBFPerturbation

section PDRootInlinePerturbedDescent

/-! The perturbation argument behind arXiv:1011.5517v1, equations (2.12)--(2.15).
The ideal step has squared-distance descent; the actual step differs by a
summable distance error. The existing platform scalar descent theorem is reused.
-/
open Filter Topology

namespace MonoSkew.PDRootPerturbation

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
  obtain ⟨L, hL⟩ := MonoSkew.PDRootScalar.dist_converges_of_summable_error x z e he hs hstep
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

end MonoSkew.PDRootPerturbation

end PDRootInlinePerturbedDescent

section PDRootInlineFBFSummability

/-! Scalar bookkeeping for the inexact FBF residual estimates. -/
namespace MonoSkew.PDRootFBF

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

end MonoSkew.PDRootFBF

end PDRootInlineFBFSummability

section PDRootInlineFBFResiduals

/-! Inexact FBF residual square summability and the retained quasi-Fejer estimate.
Source: Briceno-Arias--Combettes, arXiv:1011.5517v1, Theorem 2.5(i).
-/
open Filter Topology InnerProductSpace
open ThreeOpSplitting.Convergence MonoSkew.Main

namespace MonoSkew.PDRootFBF
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
  obtain ⟨hs, η, hη, hsη, hrec⟩ := MonoSkew.PDRootPerturbation.summable_residual_of_perturbed_descent
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
    (MonoSkew.PDRootPerturbation.summable_sq_of_nonneg hg0 hgs)
  refine ⟨hsxp, ?_⟩
  apply summable_sq_of_le_add (fun n => ‖y n - q n‖) (fun n => 2 * ‖x n - p n‖) h
    (fun n => norm_nonneg _) (fun n => by positivity) hh0
  · intro n
    exact IsFBFRun.forward_residual_bound B β hβ hBlip γ J a b c x y p q hrun
      (fun n => (hstep n).1) (fun n => (hstep n).2.1) n
  · simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsxp.mul_left 4
  · exact MonoSkew.PDRootPerturbation.summable_sq_of_nonneg hh0 hhs

end MonoSkew.PDRootFBF

end PDRootInlineFBFResiduals

section PDRootInlineFBFWeakTools

/-! Sequential convergence and graph-point bookkeeping for Theorem 2.5(ii). -/
open Filter Topology InnerProductSpace
open ThreeOpSplitting.Convergence MonoSkew.Main

namespace MonoSkew.PDRootFBF
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tendsto_zero_of_summable_norm_sq (d : ℕ → E)
    (hd : Summable (fun n => ‖d n‖ ^ 2)) : Tendsto d atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto 0).comp hd.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

theorem weakTendsto_of_sub_tendsto_zero (x p : ℕ → E) (w : E)
    (hx : WeakTendsto x w) (hd : Tendsto (fun n => x n - p n) atTop (𝓝 0)) :
    WeakTendsto p w := by
  intro y
  have hi : Tendsto (fun n => inner ℝ (x n - p n) y) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inner_zero_left] using hd.inner (tendsto_const_nhds (x := y))
  have h := (hx y).sub hi
  simpa only [inner_sub_left, sub_sub_cancel, sub_zero] using h

theorem norm_bounded_of_sq_dist_limit (x : ℕ → E) (z : E) (L : ℝ)
    (hL : Tendsto (fun n => ‖x n - z‖ ^ 2) atTop (𝓝 L)) :
    ∃ R : ℝ, ∀ n, ‖x n‖ ≤ R := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hL).exists_norm_le
  have hsq (n : ℕ) : ‖x n - z‖ ^ 2 ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x n - z‖)] using
      hM (‖x n - z‖ ^ 2) ⟨n, rfl⟩
  have hM0 : 0 ≤ M := (sq_nonneg _).trans (hsq 0)
  refine ⟨M + 1 + ‖z‖, ?_⟩
  intro n
  have hd : ‖x n - z‖ ≤ M + 1 := by nlinarith [hsq n, sq_nonneg (‖x n - z‖ - 1)]
  have hn : ‖x n‖ ≤ ‖x n - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x n - z) z
  linarith

theorem comparison_graph (A : E → Set E) (B : E → E)
    (γ : ℝ) (hγ : 0 < γ) (J : E → E) (hJ : IsResolvent γ A J) (x : E) :
    let p := J (x - γ • B x)
    γ⁻¹ • (x - p) + (B p - B x) ∈ addSingle A B p := by
  dsimp only
  let p := J (x - γ • B x)
  refine ⟨γ⁻¹ • ((x - γ • B x) - p), hJ _, ?_⟩
  change γ⁻¹ • (x - p) + (B p - B x) = γ⁻¹ • ((x - γ • B x) - p) + B p
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hγ), one_smul]
  abel

theorem comparison_graph_norm (B : E → E) (β : ℝ)
    (hBlip : ∀ u v, ‖B u - B v‖ ≤ β * ‖u - v‖)
    (ε γ : ℝ) (hε : 0 < ε) (hγ : ε ≤ γ) (x p : E) :
    ‖γ⁻¹ • (x - p) + (B p - B x)‖ ≤ (ε⁻¹ + β) * ‖x - p‖ := by
  have hγ0 : 0 < γ := hε.trans_le hγ
  have hi : γ⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hγ0 hε).mpr hγ
  have hl : ‖B p - B x‖ ≤ β * ‖x - p‖ := by
    simpa only [norm_sub_rev] using hBlip p x
  calc
    _ ≤ ‖γ⁻¹ • (x - p)‖ + ‖B p - B x‖ := norm_add_le _ _
    _ = γ⁻¹ * ‖x - p‖ + ‖B p - B x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ0)]
    _ ≤ ε⁻¹ * ‖x - p‖ + β * ‖x - p‖ := by gcongr
    _ = _ := by ring

end MonoSkew.PDRootFBF

end PDRootInlineFBFWeakTools

section PDRootInlineFBFComparisonLimits

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open MonoSkew.Main MonoSkew.PDRootFBF

namespace MonoSkew.PDRootFBF

/-- Comparison iterates have vanishing graph residuals, stay bounded, and approach the actual iterates.
Extracted from the already verified proof of Theorem 2.5(ii). -/
theorem comparison_limits {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
    let pt := fun n => J n (x n - γ n • B (x n))
    let u := fun n => (γ n)⁻¹ • (x n - pt n) + (B (pt n) - B (x n))
    Tendsto (fun n => x n - pt n) atTop (𝓝 0) ∧
      Tendsto u atTop (𝓝 0) ∧ (∀ n, u n ∈ addSingle A B (pt n)) ∧
      ∃ R : ℝ, ∀ n, ‖pt n‖ ≤ R := by
  let pt : ℕ → E := fun n => J n (x n - γ n • B (x n))
  let u : ℕ → E := fun n => (γ n)⁻¹ • (x n - pt n) + (B (pt n) - B (x n))
  have hstep (n : ℕ) := step_coefficient_lower β ε (γ n) hβ hε0 hε1 (hγ n)
  have hfejer : ∀ z ∈ zer (addSingle A B), ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧
      Summable η ∧ ∀ n, ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 + η n := by
    intro z hz
    exact (at_solution A hA.1 B hB β hβ hBlip a b c ha hb hc ε hε0 hε1 γ hγ J hJ x y p q hrun z hz).2
  obtain ⟨z₀, hz₀⟩ := hzer
  have hspt := (at_solution A hA.1 B hB β hβ hBlip a b c ha hb hc ε hε0 hε1 γ hγ J hJ x y p q hrun z₀ hz₀).1
  have hd : Tendsto (fun n => x n - pt n) atTop (𝓝 0) :=
    tendsto_zero_of_summable_norm_sq _ hspt
  have hdnorm : Tendsto (fun n => ‖x n - pt n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hd
  have hu : Tendsto u atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg (u n))
      (fun n => comparison_graph_norm B β hBlip ε (γ n) hε0 (hγ n).1 (x n) (pt n))
    simpa only [mul_zero] using hdnorm.const_mul (ε⁻¹ + β)
  have hgraph (n : ℕ) : u n ∈ addSingle A B (pt n) :=
    comparison_graph A B (γ n) (hstep n).1 (J n) (hJ n) (x n)
  obtain ⟨η, hη, hsη, hrec⟩ := hfejer z₀ hz₀
  obtain ⟨L, hL⟩ := MonoSkew.PDRootScalar.scalar_converges_of_summable_error
    (fun n => ‖x n - z₀‖ ^ 2) η (fun n => sq_nonneg _) hη hsη hrec
  obtain ⟨R, hR⟩ := norm_bounded_of_sq_dist_limit x z₀ L hL
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ hd).exists_norm_le
  have hpt (n : ℕ) : ‖pt n‖ ≤ R + D := by
    have hb := hD (x n - pt n) ⟨n, rfl⟩
    have he : x n - (x n - pt n) = pt n := by abel
    have hn := norm_sub_le (x n) (x n - pt n)
    rw [he] at hn
    linarith [hR n]
  exact ⟨hd, hu, hgraph, R+D, hpt⟩

end MonoSkew.PDRootFBF

end PDRootInlineFBFComparisonLimits

section PDRootInlineWeakStrongClosed

/-! Standard weak-strong sequential closedness of a maximal monotone graph,
with the bound on the weakly convergent sequence supplied explicitly.
No completeness or uniform boundedness theorem is needed. -/

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence

namespace MonoSkew.PDRootFBF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point monotonically related to a maximal monotone graph belongs to the graph. -/
theorem mem_of_monotone_related (A : E → Set E) (hA : IsMaximalMonotone A)
    (w v : E) (hrel : ∀ p a, a ∈ A p → 0 ≤ ⟪w - p, v - a⟫_ℝ) : v ∈ A w := by
  let T : E → Set E := fun p => {a | a ∈ A p ∨ (p = w ∧ a = v)}
  have hT : IsMonotoneOp T := by
    intro p q a b ha hb
    rcases ha with ha | ⟨hpw, hav⟩
    · rcases hb with hb | ⟨hqw, hbv⟩
      · exact hA.1 p q a b ha hb
      · subst q
        subst b
        have he : ⟪p - w, a - v⟫_ℝ = ⟪w - p, v - a⟫_ℝ := by
          calc
            _ = ⟪-(w - p), -(v - a)⟫_ℝ := by simp only [neg_sub]
            _ = _ := inner_neg_neg _ _
        rw [he]
        exact hrel p a ha
    · subst p
      subst a
      rcases hb with hb | ⟨hqw, hbv⟩
      · exact hrel q b hb
      · subst q
        subst b
        simp
  have heq : T = A := hA.2 T hT (fun p a ha => Or.inl ha)
  rw [← heq]
  exact Or.inr ⟨rfl, rfl⟩

/-- Pairing a bounded weakly convergent sequence with a strongly convergent sequence
converges to the pairing of their limits. -/
theorem inner_tendsto_of_weak_strong_bounded (x u : ℕ → E) (w v : E) (R : ℝ)
    (hweak : WeakTendsto x w) (hstrong : Tendsto u atTop (𝓝 v))
    (hbound : ∀ n, ‖x n‖ ≤ R) :
    Tendsto (fun n => ⟪x n, u n⟫_ℝ) atTop (𝓝 ⟪w, v⟫_ℝ) := by
  have hnorm : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
    simpa using (hstrong.sub_const v).norm
  have herror : Tendsto (fun n => ⟪x n, u n - v⟫_ℝ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => R * ‖u n - v‖)
    · intro n
      calc
        ‖⟪x n, u n - v⟫_ℝ‖ = |⟪x n, u n - v⟫_ℝ| := Real.norm_eq_abs _
        _ ≤ ‖x n‖ * ‖u n - v‖ := abs_real_inner_le_norm _ _
        _ ≤ R * ‖u n - v‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    · simpa using hnorm.const_mul R
  have hsum := (hweak v).add herror
  have he (n : ℕ) : v + (u n - v) = u n := by abel
  simpa only [← inner_add_right, he, add_zero] using hsum

/-- A maximal monotone graph is sequentially closed for weak convergence of its first
coordinate and strong convergence of its second, when a bound on the first is supplied. -/
theorem weak_strong_closed_of_bounded (A : E → Set E) (hA : IsMaximalMonotone A)
    (x u : ℕ → E) (w v : E) (R : ℝ)
    (hweak : WeakTendsto x w) (hstrong : Tendsto u atTop (𝓝 v))
    (hbound : ∀ n, ‖x n‖ ≤ R) (hgraph : ∀ n, u n ∈ A (x n)) : v ∈ A w := by
  apply mem_of_monotone_related A hA w v
  intro p a ha
  have hweak' : WeakTendsto (fun n => x n - p) (w - p) := by
    intro z
    simpa only [inner_sub_left] using (hweak z).sub_const ⟪p, z⟫_ℝ
  have hbound' : ∀ n, ‖x n - p‖ ≤ R + ‖p‖ := by
    intro n
    calc
      _ ≤ ‖x n‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ R + ‖p‖ := by gcongr; exact hbound n
  have hlim := inner_tendsto_of_weak_strong_bounded (fun n => x n - p)
    (fun n => u n - a) (w - p) (v - a) (R + ‖p‖)
    hweak' (hstrong.sub_const a) hbound'
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hA.1 (x n) p (u n) a (hgraph n) ha)

end MonoSkew.PDRootFBF

end PDRootInlineWeakStrongClosed

section PDRootInlineProductMonotone

/-! Elementary maximal-monotone calculus for the product-space construction.
All maximality arguments use monotonically related points; no resolvent
existence theorem or completeness assumption is required. -/

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.PDRootStructure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The related-point criterion also suffices to prove maximality. -/
theorem maximal_of_monotone_related (A : E → Set E) (hA : IsMonotoneOp A)
    (hmem : ∀ w v, (∀ p a, a ∈ A p → 0 ≤ ⟪w - p, v - a⟫_ℝ) → v ∈ A w) :
    IsMaximalMonotone A := by
  refine ⟨hA, ?_⟩
  intro T hT hsub
  funext w
  apply Set.Subset.antisymm
  · intro v hv
    exact hmem w v (fun p a ha => hT w p v a hv (hsub p ha))
  · exact hsub w

/-- At any candidate point a maximal graph has a graph point with nonpositive
monotonicity pairing. This includes the candidate itself when it is in the graph. -/
theorem exists_graph_nonpos (A : E → Set E) (hA : IsMaximalMonotone A) (w v : E) :
    ∃ p a, a ∈ A p ∧ ⟪w - p, v - a⟫_ℝ ≤ 0 := by
  classical
  by_cases hv : v ∈ A w
  · exact ⟨w, v, hv, by simp⟩
  · by_contra hn
    push Not at hn
    exact hv (MonoSkew.PDRootFBF.mem_of_monotone_related A hA w v (fun p a ha => (hn p a ha).le))

/-- Inverting a maximal monotone graph preserves maximal monotonicity. -/
theorem maximal_inv (A : E → Set E) (hA : IsMaximalMonotone A) :
    IsMaximalMonotone (opInv A) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    simpa only [real_inner_comm] using hA.1 u v x y hu hv
  · intro w v hrel
    exact MonoSkew.PDRootFBF.mem_of_monotone_related A hA v w (fun p a ha => by
      simpa only [real_inner_comm] using hrel a p ha)

/-- A constant output shift preserves maximal monotonicity. The shifted
operator sends `x` to the values `u` such that `u+c ∈ A x`. -/
theorem maximal_outputShift (A : E → Set E) (hA : IsMaximalMonotone A) (c : E) :
    IsMaximalMonotone (fun x => {u | u + c ∈ A x}) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    have he : (u + c) - (v + c) = u - v := by abel
    simpa only [he] using hA.1 x y (u + c) (v + c) hu hv
  · intro w v hrel
    apply MonoSkew.PDRootFBF.mem_of_monotone_related A hA w (v + c)
    intro p a ha
    have hr := hrel p (a - c) (by
      change (a - c) + c ∈ A p
      simpa only [sub_add_cancel] using ha)
    have he : v - (a - c) = (v + c) - a := by abel
    simpa only [he] using hr

section Product

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The Cartesian product of two set-valued operators on the Hilbert direct sum. -/
def productOp (A : H → Set H) (B : G → Set G) : K H G → Set (K H G) :=
  fun x => {u | u.fst ∈ A x.fst ∧ u.snd ∈ B x.snd}

/-- The product graph of two maximal monotone graphs is maximal monotone. -/
theorem maximal_product (A : H → Set H) (B : G → Set G)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) :
    IsMaximalMonotone (productOp A B) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    rw [WithLp.prod_inner_apply]
    exact add_nonneg (hA.1 x.fst y.fst u.fst v.fst hu.1 hv.1)
      (hB.1 x.snd y.snd u.snd v.snd hu.2 hv.2)
  · intro w v hrel
    obtain ⟨q, b, hb, hnonpos⟩ := exists_graph_nonpos B hB w.snd v.snd
    have hfst : v.fst ∈ A w.fst := by
      apply MonoSkew.PDRootFBF.mem_of_monotone_related A hA w.fst v.fst
      intro p a ha
      have hr := hrel (WithLp.toLp 2 (p, q)) (WithLp.toLp 2 (a, b)) ⟨ha, hb⟩
      rw [WithLp.prod_inner_apply] at hr
      change 0 ≤ ⟪w.fst - p, v.fst - a⟫_ℝ + ⟪w.snd - q, v.snd - b⟫_ℝ at hr
      linarith
    refine ⟨hfst, ?_⟩
    apply MonoSkew.PDRootFBF.mem_of_monotone_related B hB w.snd v.snd
    intro q b hb
    have hr := hrel (WithLp.toLp 2 (w.fst, q)) (WithLp.toLp 2 (v.fst, b)) ⟨hfst, hb⟩
    rw [WithLp.prod_inner_apply] at hr
    change 0 ≤ ⟪w.fst - w.fst, v.fst - v.fst⟫_ℝ + ⟪w.snd - q, v.snd - b⟫_ℝ at hr
    simpa only [sub_self, inner_zero_left, zero_add] using hr

/-- Maximality of the translated primal/inverse-dual product operator `M`. -/
theorem opM_maximal (A : H → Set H) (B : G → Set G)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (z : H) (r : G) :
    IsMaximalMonotone (opM A B z r) := by
  have he : opM A B z r = productOp (fun x => {u | u + z ∈ A x})
      (fun v => {w | w + -r ∈ opInv B v}) := by
    funext x
    apply Set.ext
    intro u
    change (u.fst + z ∈ A x.fst ∧ u.snd - r ∈ opInv B x.snd) ↔
      (u.fst + z ∈ A x.fst ∧ u.snd + -r ∈ opInv B x.snd)
    simp only [sub_eq_add_neg]
  rw [he]
  exact maximal_product (fun x => {u | u + z ∈ A x})
      (fun v => {w | w + -r ∈ opInv B v})
      (maximal_outputShift A hA z) (maximal_outputShift (opInv B) (maximal_inv B hB) (-r))

end Product

/-- An everywhere-defined map with zero monotonicity pairing may be added to a
maximal monotone graph. In particular this applies to any linear skew map. -/
theorem maximal_addSingle_skew (A : E → Set E) (hA : IsMaximalMonotone A)
    (S : E → E) (hskew : ∀ x y, ⟪x - y, S x - S y⟫_ℝ = 0) :
    IsMaximalMonotone (addSingle A S) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have he : (a + S x) - (b + S y) = (a - b) + (S x - S y) := by abel
    rw [he, inner_add_right, hskew x y, add_zero]
    exact hA.1 x y a b ha hb
  · intro w v hrel
    have hv : v - S w ∈ A w := by
      apply MonoSkew.PDRootFBF.mem_of_monotone_related A hA w (v - S w)
      intro p a ha
      have hr := hrel p (a + S p) ⟨a, ha, rfl⟩
      have he : v - (a + S p) = ((v - S w) - a) + (S w - S p) := by abel
      rw [he, inner_add_right, hskew w p, add_zero] at hr
      exact hr
    exact ⟨v - S w, hv, by abel⟩

end MonoSkew.PDRootStructure

end PDRootInlineProductMonotone

section PDRootInlineSkewOperator

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.PDRootStructure
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

noncomputable def skewCLM (L : H →L[ℝ] G) : K H G →L[ℝ] K H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H G).symm.toContinuousLinearMap.comp
    ((L.adjoint.comp (WithLp.sndL 2 ℝ H G)).prod
      (-(L.comp (WithLp.fstL 2 ℝ H G))))

theorem skewCLM_apply (L : H →L[ℝ] G) (p : K H G) : skewCLM L p = opS L p := rfl

theorem skewCLM_adjoint (L : H →L[ℝ] G) : (skewCLM L).adjoint = -skewCLM L := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change ⟪-(opS L x), y⟫_ℝ = ⟪x, opS L y⟫_ℝ
  simp only [inner_neg_left, WithLp.prod_inner_apply, opS, WithLp.toLp_fst,
    WithLp.toLp_snd, inner_neg_left, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  simp only [WithLp.fst, WithLp.snd]
  ring

theorem skewCLM_norm (L : H →L[ℝ] G) : ‖skewCLM L‖ = ‖L‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro p
    have h1 := L.adjoint.le_opNorm p.snd
    have h2 := L.le_opNorm p.fst
    have hn : ‖L.adjoint‖ = ‖L‖ := ContinuousLinearMap.adjoint.norm_map L
    rw [hn] at h1
    have hs1 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h1
    have hs2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h2
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖L.adjoint p.snd‖ ^ 2 + ‖-(L p.fst)‖ ^ 2 ≤ _
    rw [norm_neg]
    nlinarith
  · apply L.opNorm_le_bound (norm_nonneg (skewCLM L))
    intro x
    have h := (skewCLM L).le_opNorm (WithLp.toLp 2 (x, (0 : G)))
    simpa [skewCLM_apply, opS, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using h

theorem opS_self_inner (L : H →L[ℝ] G) (p : K H G) : ⟪p, opS L p⟫_ℝ = 0 := by
  simp only [WithLp.prod_inner_apply, opS, WithLp.toLp_fst, WithLp.toLp_snd,
    inner_neg_right, ContinuousLinearMap.adjoint_inner_right]
  change ⟪L p.fst, p.snd⟫_ℝ + -⟪p.snd, L p.fst⟫_ℝ = 0
  rw [real_inner_comm (L p.fst) p.snd]
  ring

theorem opS_monotone (L : H →L[ℝ] G) : IsMonotoneOp (fun p => ({opS L p} : Set (K H G))) := by
  intro x y u v hu hv
  obtain rfl := hu
  obtain rfl := hv
  have he : opS L x - opS L y = opS L (x-y) := (map_sub (skewCLM L) x y).symm
  rw [he, opS_self_inner]

end MonoSkew.PDRootStructure

end PDRootInlineSkewOperator

section PDRootInlineProductGraph

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main
namespace MonoSkew.PDRootStructure
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable (A : H → Set H) (B : G → Set G) (L : H →L[ℝ] G) (z : H) (r : G)
theorem opZero_characterization (w : K H G) : w ∈ zer (addSingle (opM A B z r) (opS L)) ↔
      z - L.adjoint w.snd ∈ A w.fst ∧ w.snd ∈ B (L w.fst - r) := by
    constructor
    · rintro ⟨u, ⟨hu, hv⟩, he⟩
      have he1 := congrArg WithLp.fst he
      have he2 := congrArg WithLp.snd he
      change 0 = u.fst + L.adjoint w.snd at he1
      change 0 = u.snd + -(L w.fst) at he2
      have hu' : u.fst + z = z - L.adjoint w.snd := by linear_combination (norm := module) -he1
      have hv' : u.snd - r = L w.fst - r := by linear_combination (norm := module) -he2
      exact ⟨by simpa only [hu'] using hu, by simpa only [opInv, hv', Set.mem_setOf_eq] using hv⟩
    · rintro ⟨hx, hv⟩
      refine ⟨WithLp.toLp 2 (-L.adjoint w.snd, L w.fst), ?_, ?_⟩
      · constructor
        · change -L.adjoint w.snd + z ∈ A w.fst
          simpa only [sub_eq_add_neg, add_comm] using hx
        · exact hv
      · apply WithLp.ofLp_injective
        apply Prod.ext <;> simp [opS]

end MonoSkew.PDRootStructure

end PDRootInlineProductGraph

section PDRootInlinePrimalDualTransport

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.PDRootStructure
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem product_norm_le (x : H) (v : G) :
    ‖WithLp.toLp 2 (x,v)‖ ≤ ‖x‖ + ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖x‖^2 + ‖v‖^2 ≤ _
  nlinarith [norm_nonneg x, norm_nonneg v]

theorem product_summable (x : ℕ → H) (v : ℕ → G)
    (hx : Summable (fun n => ‖x n‖)) (hv : Summable (fun n => ‖v n‖)) :
    Summable (fun n => ‖WithLp.toLp 2 (x n,v n)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => product_norm_le _ _) (hx.add hv)

theorem product_weak_fst (X : ℕ → K H G) (w : K H G) (h : WeakTendsto X w) :
    WeakTendsto (fun n => (X n).fst) w.fst := by
  intro y
  simpa [WithLp.prod_inner_apply] using h (WithLp.toLp 2 (y,(0:G)))

theorem product_weak_snd (X : ℕ → K H G) (w : K H G) (h : WeakTendsto X w) :
    WeakTendsto (fun n => (X n).snd) w.snd := by
  intro y
  simpa [WithLp.prod_inner_apply] using h (WithLp.toLp 2 ((0:H),y))

theorem primalDual_to_FBF (L : H →L[ℝ] G) (z : H) (r : G) (γ : ℕ → ℝ)
    (JA : ℕ → H → H) (JBi : ℕ → G → G)
    (a₁ b₁ c₁ : ℕ → H) (a₂ b₂ c₂ : ℕ → G)
    (x y₁ p₁ q₁ : ℕ → H) (v y₂ p₂ q₂ : ℕ → G)
    (hrun : IsPDRun L z r γ JA JBi a₁ b₁ c₁ a₂ b₂ c₂ x y₁ p₁ q₁ v y₂ p₂ q₂) :
    IsFBFRun (opS L) γ
      (fun n w => WithLp.toLp 2 (JA n (w.fst + γ n • z), JBi n (w.snd - γ n • r)))
      (fun n => WithLp.toLp 2 (a₁ n, -a₂ n))
      (fun n => WithLp.toLp 2 (b₁ n, b₂ n))
      (fun n => WithLp.toLp 2 (c₁ n, -c₂ n))
      (fun n => WithLp.toLp 2 (x n,v n))
      (fun n => WithLp.toLp 2 (y₁ n,y₂ n))
      (fun n => WithLp.toLp 2 (p₁ n,p₂ n))
      (fun n => WithLp.toLp 2 (q₁ n,q₂ n)) := by
  intro n
  rcases hrun n with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  refine ⟨?_,?_,?_,?_⟩ <;> apply WithLp.ofLp_injective 2 <;> apply Prod.ext <;>
    dsimp [opS] <;> simp only [h1,h2,h3,h4,h5,h6,h7,h8, smul_neg, smul_add, smul_sub] <;> abel

end MonoSkew.PDRootStructure

end PDRootInlinePrimalDualTransport

section PDRootInlineUniformMonotoneTransfer

/-! Coordinate strong convergence from uniform monotonicity in the product model.
The exact graph points need only be bounded and their graph values tend to zero.
The modulus may take the value infinity; no finite-valuedness is assumed. -/

open InnerProductSpace Filter Topology NNReal ENNReal
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.PDRootStructure

/-- An increasing nonnegative extended-real modulus vanishing only at zero
forces its arguments to zero if it is bounded above by a real sequence tending
to zero. A finite positive threshold is selected inside `EReal`, even when
the modulus value is infinity. -/
theorem tendsto_zero_of_modulus (φ : ℝ≥0 → ℝ≥0∞) (hmono : Monotone φ)
    (hzero : ∀ t, φ t = 0 ↔ t = 0) (d : ℕ → ℝ≥0) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ n, ((φ (d n) : ℝ≥0∞) : EReal) ≤ (r n : EReal)) :
    Tendsto (fun n => (d n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (d n).coe_nonneg)
  · intro ε hε
    let t : ℝ≥0 := ⟨ε, hε.le⟩
    have ht : t ≠ 0 := by
      intro ht
      have : ε = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) ht
      linarith
    have hp : (0 : EReal) < (φ t : EReal) :=
      EReal.coe_ennreal_pos_iff_ne_zero.mpr ((hzero t).not.mpr ht)
    obtain ⟨δ, hδ, hδφ⟩ := EReal.exists_between_coe_real hp
    have hδ0 : 0 < δ := by exact_mod_cast hδ
    filter_upwards [(tendsto_order.1 hr).2 δ hδ0] with n hn
    by_contra hnot
    have htd : t ≤ d n := by
      change ε ≤ (d n : ℝ)
      exact le_of_not_gt hnot
    have hm : (φ t : EReal) ≤ (r n : EReal) :=
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmono htd)).trans (hbound n)
    have hle : δ ≤ r n := EReal.coe_le_coe_iff.mp (hδφ.le.trans hm)
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bounded first coordinates and graph values converging strongly to zero
make the monotonicity pairing at any fixed point tend to zero. -/
theorem graph_pairing_tendsto_zero (p u : ℕ → E) (w : E) (R : ℝ)
    (hbound : ∀ n, ‖p n‖ ≤ R) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ⟪w - p n, -(u n)⟫_ℝ) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n => (‖w‖ + R) * ‖u n‖)
  · intro n
    have hp : ‖w - p n‖ ≤ ‖w‖ + R :=
      (norm_sub_le w (p n)).trans (by gcongr; exact hbound n)
    calc
      ‖⟪w - p n, -(u n)⟫_ℝ‖ = |⟪w - p n, -(u n)⟫_ℝ| := Real.norm_eq_abs _
      _ ≤ ‖w - p n‖ * ‖-(u n)‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖w‖ + R) * ‖u n‖ := by rw [norm_neg]; gcongr
  · simpa only [norm_zero, mul_zero] using hu.norm.const_mul (‖w‖ + R)

section Product

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The skew contribution disappears from the graph pairing, and the two
constant output translations disappear from the coordinate differences. -/
theorem product_graph_pairing (A : H → Set H) (B : G → Set G)
    (L : H →L[ℝ] G) (z : H) (r : G) (w p u : K H G)
    (hw : w ∈ zer (addSingle (opM A B z r) (opS L)))
    (hu : u ∈ addSingle (opM A B z r) (opS L) p) :
    ∃ mw ∈ opM A B z r w, ∃ mp ∈ opM A B z r p,
      ⟪w - p, -u⟫_ℝ =
        ⟪w.fst - p.fst, (mw.fst + z) - (mp.fst + z)⟫_ℝ +
        ⟪w.snd - p.snd, (mw.snd - r) - (mp.snd - r)⟫_ℝ := by
  obtain ⟨mw, hmw, hew⟩ := hw
  obtain ⟨mp, hmp, hep⟩ := hu
  refine ⟨mw, hmw, mp, hmp, ?_⟩
  have he : -u = (mw - mp) + (opS L w - opS L p) := by
    rw [hep]
    have hadd : (mw - mp) + (opS L w - opS L p) =
        (mw + opS L w) - (mp + opS L p) := by abel
    rw [hadd, ← hew, zero_sub]
  have hs : ⟪w - p, opS L w - opS L p⟫_ℝ = 0 := by
    have hsub : opS L w - opS L p = opS L (w - p) := (map_sub (skewCLM L) w p).symm
    rw [hsub, opS_self_inner]
  rw [he, inner_add_right, hs, add_zero, WithLp.prod_inner_apply]
  change ⟪w.fst - p.fst, mw.fst - mp.fst⟫_ℝ +
      ⟪w.snd - p.snd, mw.snd - mp.snd⟫_ℝ = _
  have hfst : (mw.fst + z) - (mp.fst + z) = mw.fst - mp.fst := by abel
  have hsnd : (mw.snd - r) - (mp.snd - r) = mw.snd - mp.snd := by abel
  rw [hfst, hsnd]

/-- Uniform monotonicity of the primal operator forces strong convergence
of the first coordinate of bounded comparison graph points. -/
theorem uniform_primal_strong (A : H → Set H) (B : G → Set G)
    (hB : IsMonotoneOp B) (L : H →L[ℝ] G) (z : H) (r : G)
    (p u : ℕ → K H G) (w : K H G)
    (hw : w ∈ zer (addSingle (opM A B z r) (opS L)))
    (hgraph : ∀ n, u n ∈ addSingle (opM A B z r) (opS L) (p n))
    (R : ℝ) (hbound : ∀ n, ‖p n‖ ≤ R) (hu : Tendsto u atTop (𝓝 0))
    (huni : IsUniformlyMonotoneAt A w.fst) :
    Tendsto (fun n => (p n).fst) atTop (𝓝 w.fst) := by
  obtain ⟨φ, hmono, hzero, hφ⟩ := huni
  have hpair := graph_pairing_tendsto_zero p u w R hbound hu
  have hd := tendsto_zero_of_modulus φ hmono hzero (fun n => ‖w.fst - (p n).fst‖₊)
    (fun n => ⟪w - p n, -(u n)⟫_ℝ) hpair (by
      intro n
      obtain ⟨mw, hmw, mp, hmp, he⟩ := product_graph_pairing A B L z r w (p n) (u n) hw (hgraph n)
      have ha := hφ (mw.fst + z) hmw.1 (p n).fst (mp.fst + z) hmp.1
      have hb := hB (mw.snd - r) (mp.snd - r) w.snd (p n).snd hmw.2 hmp.2
      have hb' : 0 ≤ ⟪w.snd - (p n).snd, (mw.snd - r) - (mp.snd - r)⟫_ℝ := by
        simpa only [real_inner_comm] using hb
      rw [he]
      exact ha.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right hb')))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [coe_nnnorm, dist_eq_norm, norm_sub_rev] using hd

/-- Uniform monotonicity of the inverse dual operator forces strong convergence
of the second coordinate of bounded comparison graph points. -/
theorem uniform_dual_strong (A : H → Set H) (B : G → Set G)
    (hA : IsMonotoneOp A) (L : H →L[ℝ] G) (z : H) (r : G)
    (p u : ℕ → K H G) (w : K H G)
    (hw : w ∈ zer (addSingle (opM A B z r) (opS L)))
    (hgraph : ∀ n, u n ∈ addSingle (opM A B z r) (opS L) (p n))
    (R : ℝ) (hbound : ∀ n, ‖p n‖ ≤ R) (hu : Tendsto u atTop (𝓝 0))
    (huni : IsUniformlyMonotoneAt (opInv B) w.snd) :
    Tendsto (fun n => (p n).snd) atTop (𝓝 w.snd) := by
  obtain ⟨φ, hmono, hzero, hφ⟩ := huni
  have hpair := graph_pairing_tendsto_zero p u w R hbound hu
  have hd := tendsto_zero_of_modulus φ hmono hzero (fun n => ‖w.snd - (p n).snd‖₊)
    (fun n => ⟪w - p n, -(u n)⟫_ℝ) hpair (by
      intro n
      obtain ⟨mw, hmw, mp, hmp, he⟩ := product_graph_pairing A B L z r w (p n) (u n) hw (hgraph n)
      have hb := hφ (mw.snd - r) hmw.2 (p n).snd (mp.snd - r) hmp.2
      have ha := hA w.fst (p n).fst (mw.fst + z) (mp.fst + z) hmw.1 hmp.1
      rw [he]
      exact hb.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_left ha)))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [coe_nnnorm, dist_eq_norm, norm_sub_rev] using hd

end Product
end MonoSkew.PDRootStructure

end PDRootInlineUniformMonotoneTransfer

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open MonoSkew.Main

/-- Theorem 3.1 (pp. 10–11): in Problem 1.1 with `L ≠ 0` and
`z ∈ ran(A + L* ∘ B ∘ (L · − r))`, the iterates of the inexact primal–dual
forward–backward–forward method (3.1) with absolutely summable errors and step sizes in
`[ε, (1 − ε)/‖L‖]` satisfy, for some primal solution `x̄` and dual solution `v̄` with
`z − L*v̄ ∈ Ax̄` and `v̄ ∈ B(Lx̄ − r)`: (i) `x_n − p_{1,n} → 0`, `v_n − p_{2,n} → 0`;
(ii) `x_n, p_{1,n} ⇀ x̄` and `v_n, p_{2,n} ⇀ v̄`; (iii) if `A` is uniformly monotone at `x̄`
then `x_n, p_{1,n} → x̄`; (iv) if `B⁻¹` is uniformly monotone at `v̄` then `v_n, p_{2,n} → v̄`. -/
theorem solution {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G)
    (hL : L ≠ 0) (hran : ∃ x, z ∈ primalOp A B L r x)
    (a₁ b₁ c₁ : ℕ → H) (a₂ b₂ c₂ : ℕ → G)
    (ha₁ : Summable (fun n => ‖a₁ n‖)) (hb₁ : Summable (fun n => ‖b₁ n‖))
    (hc₁ : Summable (fun n => ‖c₁ n‖))
    (ha₂ : Summable (fun n => ‖a₂ n‖)) (hb₂ : Summable (fun n => ‖b₂ n‖))
    (hc₂ : Summable (fun n => ‖c₂ n‖))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / (‖L‖ + 1))
    (γ : ℕ → ℝ) (hγ : ∀ n, ε ≤ γ n ∧ γ n ≤ (1 - ε) / ‖L‖)
    (JA : ℕ → H → H) (hJA : ∀ n, IsResolvent (γ n) A (JA n))
    (JBinv : ℕ → G → G) (hJB : ∀ n, IsResolvent (γ n) (opInv B) (JBinv n))
    (x y₁ p₁ q₁ : ℕ → H) (v y₂ p₂ q₂ : ℕ → G)
    (hrun : IsPDRun L z r γ JA JBinv a₁ b₁ c₁ a₂ b₂ c₂ x y₁ p₁ q₁ v y₂ p₂ q₂) :
    ∃ xbar : H, ∃ vbar : G,
      xbar ∈ primalSet A B L z r ∧ vbar ∈ dualSet A B L z r ∧
      z - ContinuousLinearMap.adjoint L vbar ∈ A xbar ∧ vbar ∈ B (L xbar - r) ∧
      (Tendsto (fun n => x n - p₁ n) atTop (𝓝 0) ∧
        Tendsto (fun n => v n - p₂ n) atTop (𝓝 0)) ∧
      (WeakTendsto x xbar ∧ WeakTendsto p₁ xbar ∧ WeakTendsto v vbar ∧
        WeakTendsto p₂ vbar) ∧
      (IsUniformlyMonotoneAt A xbar →
        Tendsto x atTop (𝓝 xbar) ∧ Tendsto p₁ atTop (𝓝 xbar)) ∧
      (IsUniformlyMonotoneAt (opInv B) vbar →
        Tendsto v atTop (𝓝 vbar) ∧ Tendsto p₂ atTop (𝓝 vbar)) := by
  let X : ℕ → K H G := fun n => WithLp.toLp 2 (x n,v n)
  let Y : ℕ → K H G := fun n => WithLp.toLp 2 (y₁ n,y₂ n)
  let P : ℕ → K H G := fun n => WithLp.toLp 2 (p₁ n,p₂ n)
  let Q : ℕ → K H G := fun n => WithLp.toLp 2 (q₁ n,q₂ n)
  let aa : ℕ → K H G := fun n => WithLp.toLp 2 (a₁ n,-a₂ n)
  let bb : ℕ → K H G := fun n => WithLp.toLp 2 (b₁ n,b₂ n)
  let cc : ℕ → K H G := fun n => WithLp.toLp 2 (c₁ n,-c₂ n)
  let J : ℕ → K H G → K H G := fun n w =>
    WithLp.toLp 2 (JA n (w.fst + γ n • z), JBinv n (w.snd - γ n • r))
  have hβ : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hstep (n : ℕ) := MonoSkew.PDRootFBF.step_coefficient_lower ‖L‖ ε (γ n) hβ hε0 hε1 (hγ n)
  have hM := (MonoSkew.Main.proposition_2_7_i_iii A B hA hB L z r).1
  have hS := MonoSkew.PDRootStructure.opS_monotone L
  have hlip : ∀ u w : K H G, ‖opS L u - opS L w‖ ≤ ‖L‖ * ‖u-w‖ := by
    intro u w
    simpa only [map_sub, MonoSkew.PDRootStructure.skewCLM_apply,
      MonoSkew.PDRootStructure.skewCLM_norm] using (MonoSkew.PDRootStructure.skewCLM L).le_opNorm (u-w)
  have hzero : (zer (addSingle (opM A B z r) (opS L))).Nonempty :=
    ((MonoSkew.Main.proposition_2_8_ii_vi A B hA hB L z r).out 0 2).mp hran
  have ha : Summable (fun n => ‖aa n‖) :=
    MonoSkew.PDRootStructure.product_summable a₁ (fun n => -a₂ n) ha₁ (by simpa using ha₂)
  have hb : Summable (fun n => ‖bb n‖) := MonoSkew.PDRootStructure.product_summable b₁ b₂ hb₁ hb₂
  have hc : Summable (fun n => ‖cc n‖) :=
    MonoSkew.PDRootStructure.product_summable c₁ (fun n => -c₂ n) hc₁ (by simpa using hc₂)
  have hj : ∀ n, IsResolvent (γ n) (opM A B z r) (J n) := fun n =>
    MonoSkew.Main.proposition_2_7_iv A B hA hB L z r (γ n) (hstep n).1 (JA n) (hJA n) (JBinv n) (hJB n)
  have hr : IsFBFRun (opS L) γ J aa bb cc X Y P Q :=
    MonoSkew.PDRootStructure.primalDual_to_FBF L z r γ JA JBinv a₁ b₁ c₁ a₂ b₂ c₂
      x y₁ p₁ q₁ v y₂ p₂ q₂ hrun
  have hres := (MonoSkew.Main.theorem_2_5_i (opM A B z r) hM (opS L) hS hzero ‖L‖ hβ hlip
    aa bb cc ha hb hc ε hε0 hε1 γ hγ J hj X Y P Q hr).1
  have hxp := MonoSkew.PDRootFBF.tendsto_zero_of_summable_norm_sq (fun n => X n - P n) hres
  obtain ⟨w, hw, hxw, hpw⟩ := MonoSkew.Main.theorem_2_5_ii (opM A B z r) hM (opS L) hS hzero ‖L‖ hβ hlip
    aa bb cc ha hb hc ε hε0 hε1 γ hγ J hj X Y P Q hr
  have hmem := (MonoSkew.Main.proposition_2_8_i A B hA hB L z r).2.2 w hw
  have hpair := (MonoSkew.PDRootStructure.opZero_characterization A B L z r w).mp hw
  have hxp1 : Tendsto (fun n => x n - p₁ n) atTop (𝓝 0) := by
    simpa [X, P, Function.comp_def] using ((WithLp.fstL 2 ℝ H G).continuous.tendsto 0).comp hxp
  have hxp2 : Tendsto (fun n => v n - p₂ n) atTop (𝓝 0) := by
    simpa [X, P, Function.comp_def] using ((WithLp.sndL 2 ℝ H G).continuous.tendsto 0).comp hxp
  refine ⟨w.fst,w.snd,hmem.1,hmem.2,hpair.1,hpair.2,⟨hxp1,hxp2⟩,
    ⟨MonoSkew.PDRootStructure.product_weak_fst X w hxw,
     MonoSkew.PDRootStructure.product_weak_fst P w hpw,
     MonoSkew.PDRootStructure.product_weak_snd X w hxw,
     MonoSkew.PDRootStructure.product_weak_snd P w hpw⟩, ?_, ?_⟩
  all_goals
    let pt := fun n => J n (X n - γ n • opS L (X n))
    let u := fun n => (γ n)⁻¹ • (X n - pt n) + (opS L (pt n) - opS L (X n))
    obtain ⟨hd, hu, hg, R, hR⟩ := MonoSkew.PDRootFBF.comparison_limits
      (opM A B z r) hM (opS L) hS hzero ‖L‖ hβ hlip aa bb cc ha hb hc
      ε hε0 hε1 γ hγ J hj X Y P Q hr
  · intro huni
    have hpt := MonoSkew.PDRootStructure.uniform_primal_strong A B hB.1 L z r pt u w hw hg R hR hu huni
    have hd1 : Tendsto (fun n => x n - (pt n).fst) atTop (𝓝 0) := by
      simpa [X, pt, Function.comp_def] using ((WithLp.fstL 2 ℝ H G).continuous.tendsto 0).comp hd
    have hx : Tendsto x atTop (𝓝 w.fst) := by
      simpa only [sub_add_cancel, zero_add] using hd1.add hpt
    exact ⟨hx, by simpa only [sub_sub_cancel, sub_zero] using hx.sub hxp1⟩
  · intro huni
    have hpt := MonoSkew.PDRootStructure.uniform_dual_strong A B hA.1 L z r pt u w hw hg R hR hu huni
    have hd2 : Tendsto (fun n => v n - (pt n).snd) atTop (𝓝 0) := by
      simpa [X, pt, Function.comp_def] using ((WithLp.sndL 2 ℝ H G).continuous.tendsto 0).comp hd
    have hv : Tendsto v atTop (𝓝 w.snd) := by
      simpa only [sub_add_cancel, zero_add] using hd2.add hpt
    exact ⟨hv, by simpa only [sub_sub_cancel, sub_zero] using hv.sub hxp2⟩
