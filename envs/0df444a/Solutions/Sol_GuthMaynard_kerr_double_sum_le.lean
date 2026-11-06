-- Prove2me | solution 1 for GuthMaynard.kerr_double_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:20:45.135914+00:00
-- url     : https://prove2.me/submissions/c2fa1f42-4480-47bd-b3cc-6a27c2bf1b84

import Mathlib
import Theorems.Thm_GuthMaynard_kerr_double_sum_mono
import Theorems.Thm_GuthMaynard_kerr_double_sum_le_dual
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Definitions.Def_GuthMaynard
section
/-!
# Basic definitions

This module contains the definitions mentioned in the blueprint's Basic notation chapter
(`notation-chapter`).

When a blueprint convention already has a standard Mathlib representation,
prefer using that representation directly, for example:
-the notation `e(θ)` is `𝐞 θ` after `open scoped FourierTransform`;
-for indicator functions, use `Set.indicator`;
-for suprema and infima, including those of empty sets, use Mathlib's `sSup` and `sInf`;
-for finite cardinalities use `Finset.card`;
-/


namespace Expdb

/-- A family in a pseudo-metric space is `δ`-separated when distinct indices have values at
least `δ` apart. This uses a non-strict inequality, unlike `Metric.IsSeparated`. -/
def IsSeparatedFamily {ι α : Type*} [PseudoMetricSpace α] (δ : ℝ) (x : ι → α) : Prop :=
  Pairwise fun i j => δ ≤ dist (x i) (x j)

end Expdb
end

section
/-!
# A normalized smooth bump and its Fourier transform

This module collects the concrete bump function used in the proof of the `L²` integral
estimate of the blueprint's Basic Fourier estimates chapter (`l2-chapter`), together with its
Fourier transform and the orthonormal family formed by its translates.

The bump `bump` is a fixed smooth, nonnegative, compactly supported function with
`‖bump‖_{L²} = 1` and support in `[-1/4, 1/4]`. Its translates by `1`-separated shifts are
therefore orthonormal, which is what the `L²` estimate uses.

These declarations are auxiliary to `Expdb.Fourier.L2Integral` and are collected in the
namespace `Expdb.L2Bump`.
-/


open MeasureTheory Real Complex Filter Topology BigOperators
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

namespace Expdb.L2Bump

/-! ## A normalized smooth bump -/

def rawBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def rawL2 : ℝ := ∫ x : ℝ, (rawBump x) ^ 2

private lemma rawL2_pos : 0 < rawL2 := by
  have hraw : Continuous (rawBump : ℝ → ℝ) :=
    (rawBump.contDiff (n := ⊤)).continuous
  have hsq : Continuous (fun x : ℝ => (rawBump x) ^ 2) := by
    convert (continuous_pow 2).comp hraw using 1
    ext x
    rfl
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · exact hsq
  · apply hsq.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact rawBump.hasCompactSupport.isCompact
    intro x hx
    apply subset_tsupport rawBump
    simp only [Function.mem_support] at hx ⊢
    intro hzero
    apply hx
    simp [hzero]
  · intro x
    positivity
  · have hzero : (rawBump : ℝ → ℝ) 0 = 1 := by
      apply rawBump.one_of_mem_closedBall
      simp [rawBump, Metric.mem_closedBall]
    simp [hzero]

def bump (x : ℝ) : ℝ := rawBump x / Real.sqrt rawL2

lemma bump_smooth : ContDiff ℝ ∞ bump := by
  change ContDiff ℝ ∞ (fun x => rawBump x / Real.sqrt rawL2)
  exact (rawBump.contDiff (n := ⊤)).div_const (Real.sqrt rawL2)

lemma bump_hasCompactSupport : HasCompactSupport bump := by
  apply HasCompactSupport.of_support_subset_isCompact rawBump.hasCompactSupport.isCompact
  intro x hx
  apply subset_tsupport rawBump
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  simp [bump, hzero]

lemma bump_supp (x : ℝ) (hx : bump x ≠ 0) : |x| ≤ 1 / 4 := by
  have hraw : (rawBump : ℝ → ℝ) x ≠ 0 := by
    intro hzero
    apply hx
    simp [bump, hzero]
  have hmem : x ∈ Metric.ball (0 : ℝ) rawBump.rOut := by
    rw [← rawBump.support_eq]
    exact hraw
  have : |x| < 1 / 4 := by
    simpa [rawBump, Metric.mem_ball, Real.dist_eq] using hmem
  exact this.le

lemma bump_nonneg (x : ℝ) : 0 ≤ bump x :=
  div_nonneg (rawBump.nonneg' x) (Real.sqrt_nonneg rawL2)

lemma bump_l2norm : ∫ x : ℝ, (bump x) ^ 2 = 1 := by
  rw [show (fun x : ℝ => (bump x) ^ 2) = fun x => (rawBump x) ^ 2 / rawL2 by
        funext x
        simp only [bump, div_pow]
        rw [Real.sq_sqrt rawL2_pos.le]]
  rw [integral_div]
  exact div_self (ne_of_gt rawL2_pos)

-- bump̂(u) = ∫_ℝ bump(x) e(-xu) dx
def bumpFourier (u : ℝ) : ℂ :=
  ∫ x : ℝ, (bump x : ℂ) * 𝐞 (-(x * u))

-- bump is integrable
lemma bump_integrable : Integrable bump :=
  bump_smooth.continuous.integrable_of_hasCompactSupport bump_hasCompactSupport

-- ∫ bump > 0  (from proof: "bump(t) ≥ 0 and ‖bump‖_{L²} = 1 so bump ≢ 0")
private lemma bump_integral_pos : 0 < ∫ x : ℝ, bump x := by
  have hne : ∃ x, bump x ≠ 0 := by
    by_contra h
    push Not at h
    have hsquare : ∫ x : ℝ, (bump x) ^ 2 = 0 := by
      calc
        ∫ x : ℝ, (bump x) ^ 2
            = ∫ x : ℝ, (0 : ℝ) ^ 2 := by
              congr 1
              ext x
              rw [h x]
        _ = 0 := by simp
    linarith [bump_l2norm, hsquare]
  obtain ⟨x, hx⟩ := hne
  exact integral_pos_of_integrable_nonneg_nonzero
    bump_smooth.continuous bump_integrable bump_nonneg hx

/-! ## Plancherel and decay of the bump's Fourier transform -/

private lemma bump_complex_hasCompactSupport : HasCompactSupport (fun x : ℝ => (bump x : ℂ)) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -1 / 4) (b := 1 / 4)) (by
      intro x hx
      simp only [Function.mem_support] at hx
      have h := bump_supp x (by exact_mod_cast hx)
      simp only [Set.mem_Icc, abs_le] at h ⊢
      simpa only [neg_div] using h)

private lemma bump_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ => (bump x : ℂ)) := by
  change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ bump)
  exact (Complex.ofRealCLM.contDiff (n := ∞)).comp bump_smooth

private def bumpSchwartz : 𝓢(ℝ, ℂ) :=
  bump_complex_hasCompactSupport.toSchwartzMap bump_complex_smooth

private lemma bumpFourier_eq_fourier : bumpFourier = 𝓕 (bumpSchwartz : ℝ → ℂ) := by
  funext u
  rw [Real.fourier_real_eq]
  simp only [bumpFourier, Real.fourierChar_apply, mul_neg, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul, bumpSchwartz,
    HasCompactSupport.toSchwartzMap_toFun, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

lemma bumpFourier_continuous : Continuous bumpFourier := by
  rw [bumpFourier_eq_fourier]
  exact (𝓕 bumpSchwartz).continuous

lemma bumpFourier_l2 : ∫ u : ℝ, ‖bumpFourier u‖ ^ 2 = 1 := by
  simp_rw [bumpFourier_eq_fourier]
  rw [← SchwartzMap.fourier_coe, SchwartzMap.integral_norm_sq_fourier]
  simpa [bumpSchwartz, Real.norm_eq_abs, abs_of_nonneg (bump_nonneg _)] using bump_l2norm

lemma bumpFourier_sq_integrable :
    Integrable (fun u : ℝ => ‖bumpFourier u‖ ^ 2) := by
  by_contra h
  have hzero := bumpFourier_l2
  rw [integral_undef h] at hzero
  norm_num at hzero

lemma bumpFourier_decay (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, ‖bumpFourier u‖ ≤ C * (1 + |u|) ^ (-(K : ℝ)) := by
  let g : 𝓢(ℝ, ℂ) := 𝓕 bumpSchwartz
  have hfourier : ∀ u : ℝ, bumpFourier u = g u := by
    intro u
    exact congr_fun bumpFourier_eq_fourier u
  let c : ℝ := 2 ^ K * (Finset.Iic (K, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨|c| + 1, by positivity, ?_⟩
  intro u
  have hweight : (1 + |u|) ^ K * ‖bumpFourier u‖ ≤ c := by
    have hw := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (K, 0)) (k := K) (n := 0) le_rfl le_rfl g u
    rw [norm_iteratedFDeriv_zero, ← hfourier u] at hw
    simpa [c, Real.norm_eq_abs] using hw
  have hbase : 0 < 1 + |u| := by positivity
  have hpow : 0 < (1 + |u|) ^ K := by positivity
  have hrpow : (1 + |u|) ^ (-(K : ℝ)) = ((1 + |u|) ^ K)⁻¹ := by
    rw [← Real.rpow_natCast, Real.rpow_neg hbase.le]
  rw [hrpow, ← div_eq_mul_inv]
  apply (le_div_iff₀ hpow).2
  calc
    ‖bumpFourier u‖ * (1 + |u|) ^ K =
        (1 + |u|) ^ K * ‖bumpFourier u‖ := by ring
    _ ≤ c := hweight
    _ ≤ |c| + 1 := by linarith [le_abs_self c]

lemma bumpFourier_lower_bound :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ u : ℝ, |u| ≤ δ → c ≤ ‖bumpFourier u‖ ^ 2 := by
  have hcts : Continuous bumpFourier := bumpFourier_continuous
  have hpsi0_eq : (bumpFourier 0).re = ∫ x : ℝ, bump x := by
    simp only [bumpFourier, mul_zero, neg_zero]
    have hbumpc : Integrable (fun x : ℝ => (bump x : ℂ)) := bump_integrable.ofReal
    simpa using (integral_re hbumpc).symm
  have hpsi0 : 0 < (bumpFourier 0).re := by
    rw [hpsi0_eq]
    exact bump_integral_pos
  have hpos : 0 < ‖bumpFourier 0‖ := by
    rw [norm_pos_iff]
    intro hzero
    have : (bumpFourier 0).re = 0 := by rw [hzero]; rfl
    linarith
  set v₀ := ‖bumpFourier 0‖
  obtain ⟨δ, hδ, hball⟩ :=
    (Metric.continuousAt_iff.mp hcts.continuousAt) (v₀ / 2) (by linarith)
  refine ⟨(v₀ / 2) ^ 2, δ / 2, by positivity, by positivity, ?_⟩
  intro u hu
  have hdist : dist (bumpFourier u) (bumpFourier 0) < v₀ / 2 := by
    apply hball
    rw [Real.dist_eq]
    simp only [sub_zero]
    exact lt_of_le_of_lt hu (by linarith)
  have hbound : v₀ - ‖bumpFourier u‖ < v₀ / 2 := by
    calc
      v₀ - ‖bumpFourier u‖ = ‖bumpFourier 0‖ - ‖bumpFourier u‖ := rfl
      _ ≤ ‖bumpFourier 0 - bumpFourier u‖ := norm_sub_norm_le _ _
      _ = dist (bumpFourier u) (bumpFourier 0) := by
        rw [dist_eq_norm_sub, norm_sub_rev]
      _ < v₀ / 2 := hdist
  have hball' : v₀ / 2 < ‖bumpFourier u‖ := by linarith
  nlinarith [norm_nonneg (bumpFourier u)]

/-! ## Weighted Plancherel identity -/

-- Package translates of the concrete bump as Schwartz functions.
def bumpShift (w : ℝ) : 𝓢(ℝ, ℂ) := by
  let f : ℝ → ℂ := fun x => (bump (x + w) : ℂ)
  have hcomp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -w - 1 / 4) (b := -w + 1 / 4))
    intro x hx
    change (bump (x + w) : ℂ) ≠ 0 at hx
    have hx' : bump (x + w) ≠ 0 := by exact_mod_cast hx
    have h := abs_le.mp (bump_supp (x + w) hx')
    constructor <;> linarith
  have hsmooth : ContDiff ℝ ∞ f := by
    change ContDiff ℝ ∞ ((fun x : ℝ => (bump x : ℂ)) ∘ fun x => x + w)
    exact
      ((Complex.ofRealCLM.contDiff (n := ∞)).comp bump_smooth).comp
        (contDiff_id.add contDiff_const)
  exact hcomp.toSchwartzMap hsmooth

lemma bumpShift_apply (w x : ℝ) : bumpShift w x = bump (x + w) := rfl

lemma fourier_bumpShift (w u : ℝ) :
    (𝓕 (bumpShift w : ℝ → ℂ)) u =
      𝐞 (w * u) * bumpFourier u := by
  have hcoe : (bumpShift w : ℝ → ℂ) = fun x : ℝ => (bump (x + w) : ℂ) := by
    ext x
    exact_mod_cast bumpShift_apply w x
  rw [hcoe, Real.fourier_real_eq]
  have hpsi : bumpFourier u =
      ∫ x : ℝ, 𝐞 (-(x * u)) * (bump x : ℂ) := by
    simp only [bumpFourier]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hpsi]
  have ht := congr_fun
    (Fourier.fourierIntegral_comp_add_right 𝐞 volume (fun x : ℝ => (bump x : ℂ)) w) u
  simpa [Fourier.fourierIntegral_def, Circle.smul_def, Real.fourierChar_apply] using ht

private lemma bumpShift_inner_eq_zero {v w : ℝ} (hvw : 1 ≤ |v - w|) :
    ∫ x : ℝ, inner ℂ (bumpShift v x) (bumpShift w x) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hxv : bump (x + v) = 0
  · simp [bumpShift_apply, hxv]
  by_cases hxw : bump (x + w) = 0
  · simp [bumpShift_apply, hxw]
  exfalso
  have hv := bump_supp (x + v) hxv
  have hw := bump_supp (x + w) hxw
  have hbound : |v - w| ≤ 1 / 2 := by
    calc
      |v - w| = |(x + v) - (x + w)| := by ring_nf
      _ ≤ |x + v| + |x + w| := abs_sub _ _
      _ ≤ 1 / 4 + 1 / 4 := by linarith
      _ = 1 / 2 := by norm_num
  linarith

private lemma bumpShift_inner_self (w : ℝ) :
    ∫ x : ℝ, inner ℂ (bumpShift w x) (bumpShift w x) = 1 := by
  calc
    ∫ x : ℝ, inner ℂ (bumpShift w x) (bumpShift w x) =
        ∫ x : ℝ, (((bump (x + w)) ^ 2 : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [bumpShift_apply, abs_of_nonneg (bump_nonneg _)]
    _ = ((∫ x : ℝ, (bump (x + w)) ^ 2 : ℝ) : ℂ) := integral_ofReal
    _ = ((∫ x : ℝ, (bump x) ^ 2 : ℝ) : ℂ) := by
      rw [integral_add_right_eq_self (fun x : ℝ => (bump x) ^ 2) w]
    _ = 1 := by rw [bump_l2norm]; norm_num

lemma bumpShift_orthonormal {ι : Type*} [Finite ι]
    (ξ : ι → ℝ) (N : ℝ) (hN : 0 < N)
    (hsep : IsSeparatedFamily (1 / N) ξ) :
    Orthonormal ℂ (fun r => (bumpShift (N * ξ r)).toLp 2) := by
  classical
  letI := Fintype.ofFinite ι
  rw [orthonormal_iff_ite]
  intro r s
  rw [SchwartzMap.inner_toL2_toL2_eq
    (bumpShift (N * ξ r)) (bumpShift (N * ξ s)) volume]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl, bumpShift_inner_self]
  · rw [if_neg hrs]
    apply bumpShift_inner_eq_zero
    rw [show N * ξ r - N * ξ s = N * (ξ r - ξ s) by ring, abs_mul, abs_of_pos hN]
    calc
      1 = N * (1 / N) := by field_simp
      _ ≤ N * |ξ r - ξ s| := mul_le_mul_of_nonneg_left (hsep hrs) hN.le

end Expdb.L2Bump

end
end

section
/-!
# `L²` integral estimate

This module formalizes the `L²` integral estimate from the blueprint's Basic Fourier estimates
chapter (`l2-chapter`).
It proves both the blueprint's equality with a bounded error coefficient
and the corresponding absolute-error bound.
-/


open MeasureTheory Real Complex Filter Topology BigOperators
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

namespace Expdb

open L2Bump

/-! ### The exponential sum -/

/-- The exponential sum with coefficients `a` and frequencies `ξ`, evaluated at `t`. -/
def expSum {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ r, a r * 𝐞 (ξ r * t)

private def expSumSq {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℝ :=
  ‖expSum a ξ t‖ ^ 2

private lemma expSumSq_nonneg {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) :
    0 ≤ expSumSq a ξ t :=
  sq_nonneg _

private lemma coeff_eq_zero_of_sum_norm_sq_eq_zero
    {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (h : ∑ r, ‖a r‖ ^ 2 = 0) : ∀ r, a r = 0 := by
  intro r
  apply norm_eq_zero.mp
  have hr : ‖a r‖ ^ 2 = 0 :=
    ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ sq_nonneg ‖a i‖)).1 h) r (Finset.mem_univ r)
  nlinarith [norm_nonneg (a r)]

/-- An exponential sum is continuous in its evaluation point. -/
@[fun_prop]
lemma expSum_continuous {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (expSum a ξ) := by
  unfold expSum
  fun_prop

private lemma expSumSq_continuous {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (expSumSq a ξ) := by
  unfold expSumSq
  fun_prop

private lemma weighted_l2_identity {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ)
    (N : ℝ) (hN : 0 < N) (t₀ : ℝ)
    (hsep : IsSeparatedFamily (1 / N) ξ) :
    ∫ t : ℝ, expSumSq a ξ t * ‖bumpFourier ((t - t₀) / N)‖ ^ 2 =
      N * ∑ r, ‖a r‖ ^ 2 := by
  classical
  let c : ι → ℂ := fun r => a r * 𝐞 (ξ r * t₀)
  let G : 𝓢(ℝ, ℂ) := ∑ r, c r • bumpShift (N * ξ r)
  have hfourier (u : ℝ) :
      (𝓕 G : 𝓢(ℝ, ℂ)) u = expSum a ξ (t₀ + N * u) * bumpFourier u := by
    change (SchwartzMap.fourierTransformCLM ℂ
      (∑ r, c r • bumpShift (N * ξ r))) u = _
    rw [map_sum]
    simp_rw [map_smul]
    have hsum_apply (s : Finset ι) (f : ι → 𝓢(ℝ, ℂ)) :
        (∑ r ∈ s, f r) u = ∑ r ∈ s, f r u := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert r s hrs ih =>
          simp [Finset.sum_insert, hrs, ih]
    rw [hsum_apply Finset.univ]
    simp_rw [smul_apply, smul_eq_mul]
    have hshift (r : ι) :
        SchwartzMap.fourierTransformCLM ℂ (bumpShift (N * ξ r)) u =
          𝐞 ((N * ξ r) * u) * bumpFourier u := by
      rw [SchwartzMap.fourierTransformCLM_apply]
      rw [SchwartzMap.fourier_coe]
      exact fourier_bumpShift (N * ξ r) u
    simp_rw [hshift]
    rw [show (∑ r, c r * (𝐞 ((N * ξ r) * u) * bumpFourier u)) =
        (∑ r, c r * 𝐞 ((N * ξ r) * u)) * bumpFourier u by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    simp only [c]
    calc
      a r * 𝐞 (ξ r * t₀) * 𝐞 ((N * ξ r) * u) =
          a r * (𝐞 (ξ r * t₀) * 𝐞 ((N * ξ r) * u)) := by ring
      _ = a r * 𝐞 (ξ r * (t₀ + N * u)) := by
        simp only [Real.fourierChar_apply]
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring
  have hG_toLp :
      G.toLp 2 = ∑ r, c r • (bumpShift (N * ξ r)).toLp 2 := by
    change SchwartzMap.toLpCLM ℂ ℂ 2 volume G = _
    simp [G]
  have hG_norm : ‖G.toLp 2‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
    have horth := (bumpShift_orthonormal ξ N hN hsep).inner_sum c c Finset.univ
    have hc_norm : ∑ r, ‖c r‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
      simp only [c, norm_mul, Circle.norm_coe, mul_one]
    have hsum_norm :
        ‖∑ r, c r • (bumpShift (N * ξ r)).toLp 2‖ ^ 2 = ∑ r, ‖c r‖ ^ 2 := by
      calc
        ‖∑ r, c r • (bumpShift (N * ξ r)).toLp 2‖ ^ 2 =
            (inner ℂ (∑ r, c r • (bumpShift (N * ξ r)).toLp 2)
              (∑ r, c r • (bumpShift (N * ξ r)).toLp 2)).re :=
                by
                  exact norm_sq_eq_re_inner (𝕜 := ℂ)
                    (∑ r, c r • (bumpShift (N * ξ r)).toLp 2)
        _ = (∑ r, (starRingEnd ℂ) (c r) * c r).re := congrArg Complex.re horth
        _ = ∑ r, ‖c r‖ ^ 2 := by
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [Complex.conj_mul']
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hG_toLp, hsum_norm, hc_norm]
  have hG_inner : inner ℂ (G.toLp 2) (G.toLp 2) =
      ((∑ r, ‖a r‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    exact congrArg (RCLike.ofReal : ℝ → ℂ) hG_norm
  have hG_l2 : ∫ x : ℝ, ‖G x‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
    have hinner_integral : ∫ x : ℝ, inner ℂ (G x) (G x) =
        ((∑ r, ‖a r‖ ^ 2 : ℝ) : ℂ) := by
      rw [← SchwartzMap.inner_toL2_toL2_eq G G volume]
      exact hG_inner
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using hinner_integral
  let H : ℝ → ℝ := fun u => ‖(𝓕 G : 𝓢(ℝ, ℂ)) u‖ ^ 2
  have hrewrite : (fun t : ℝ =>
      expSumSq a ξ t * ‖bumpFourier ((t - t₀) / N)‖ ^ 2) =
      fun t => H ((1 / N) * t + (-t₀ / N)) := by
    funext t
    rw [show (1 / N) * t + -t₀ / N = (t - t₀) / N by
      field_simp
      ring]
    have hu : t₀ + N * ((t - t₀) / N) = t := by
      field_simp
      ring
    simp only [H, hfourier, hu, expSumSq, norm_mul, mul_pow]
  rw [hrewrite]
  let K : ℝ → ℝ := fun x => H (x + (-t₀ / N))
  change ∫ t : ℝ, K ((1 / N) * t) = N * ∑ r, ‖a r‖ ^ 2
  rw [Measure.integral_comp_mul_left K (1 / N)]
  rw [show (∫ y : ℝ, K y) = ∫ y : ℝ, H y by
    exact integral_add_right_eq_self H (-t₀ / N)]
  rw [show (∫ y : ℝ, H y) = ∑ r, ‖a r‖ ^ 2 by
    simpa only [H] using (SchwartzMap.integral_norm_sq_fourier G).trans hG_l2]
  simp [abs_of_pos hN]

/-! ### Local `L²` bound -/

private lemma local_l2_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (N : ℝ),
    0 < N →
    IsSeparatedFamily (1 / N) ξ →
    ∀ j₀ : ℝ,
    ∫ t in Set.Icc j₀ (j₀ + N), expSumSq a ξ t ≤
      C * N * ∑ r, ‖a r‖ ^ 2 := by
  obtain ⟨c, δ, hc, hδ, hlb⟩ := bumpFourier_lower_bound
  refine ⟨(1 + 1 / δ) / c, by positivity, ?_⟩
  intro ι _ a ξ N hN hsep j₀
  by_cases hmass : ∑ r, ‖a r‖ ^ 2 = 0
  · have hzero := coeff_eq_zero_of_sum_norm_sq_eq_zero hmass
    simp [expSumSq, expSum, hzero]
  have hmasspos : 0 < ∑ r, ‖a r‖ ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun r _ ↦ sq_nonneg ‖a r‖) (Ne.symm hmass)
  -- Enlarge the smoothing scale so that the whole interval lies in the
  -- neighbourhood on which `bumpFourier_lower_bound` applies.
  set M := N * (1 + 1 / δ)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hNM : N ≤ M := by
    have hinvδ : 0 ≤ 1 / δ := by positivity
    dsimp [M]
    nlinarith
  have hsepM : IsSeparatedFamily (1 / M) ξ := by
    intro r s hrs
    apply le_trans _ (hsep hrs)
    apply (div_le_div_iff₀ hM hN).2
    simpa using hNM
  set t₀ := j₀ + N / 2
  have h2 := weighted_l2_identity a ξ M hM t₀ hsepM
  have hlb_J : ∀ t ∈ Set.Icc j₀ (j₀ + N),
      c ≤ ‖bumpFourier ((t - t₀) / M)‖ ^ 2 := by
    intro t ht
    apply hlb
    rw [abs_div, abs_of_pos hM]
    apply (div_le_iff₀ hM).2
    have habs : |t - t₀| ≤ N / 2 := by
      rw [abs_le]
      constructor <;> simp only [t₀] <;> linarith [ht.1, ht.2]
    apply habs.trans
    have hscale : δ * M = δ * N + N := by
      dsimp [M]
      field_simp
    rw [hscale]
    nlinarith
  have hFcont : Continuous (expSumSq a ξ) := expSumSq_continuous a ξ
  have hweighted : Integrable (fun t : ℝ =>
      expSumSq a ξ t * ‖bumpFourier ((t - t₀) / M)‖ ^ 2) := by
    by_contra h
    rw [integral_undef h] at h2
    nlinarith
  have hFub : c * ∫ t in Set.Icc j₀ (j₀ + N), expSumSq a ξ t ≤
      M * ∑ r, ‖a r‖ ^ 2 := by
    calc c * ∫ t in Set.Icc j₀ (j₀ + N), expSumSq a ξ t
        = ∫ t in Set.Icc j₀ (j₀ + N), c * expSumSq a ξ t :=
            (integral_const_mul _ _).symm
      _ ≤ ∫ t in Set.Icc j₀ (j₀ + N),
            expSumSq a ξ t * ‖bumpFourier ((t - t₀) / M)‖ ^ 2 := by
          apply setIntegral_mono_on
          · exact (continuous_const.mul hFcont).integrableOn_Icc
          · exact hweighted.integrableOn
          · exact measurableSet_Icc
          · intro t ht
            calc
              c * expSumSq a ξ t = expSumSq a ξ t * c := by ring
              _ ≤ expSumSq a ξ t * ‖bumpFourier ((t - t₀) / M)‖ ^ 2 :=
                mul_le_mul_of_nonneg_left (hlb_J t ht) (sq_nonneg _)
      _ ≤ ∫ t : ℝ, expSumSq a ξ t * ‖bumpFourier ((t - t₀) / M)‖ ^ 2 :=
          setIntegral_le_integral hweighted (ae_of_all _ fun t =>
            mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = M * ∑ r, ‖a r‖ ^ 2 := h2
  rw [show (1 + 1 / δ) / c * N * ∑ r, ‖a r‖ ^ 2 =
      (M * ∑ r, ‖a r‖ ^ 2) / c by
    dsimp [M]
    ring]
  apply (le_div_iff₀ hc).2
  nlinarith

/-! ### Smoothing identity -/

-- E(t) = 1/N ∫_I |bump̂((t-t₀)/N)|² dt₀ - 1_I(t)
private def smoothingKernel (N : ℝ) (left right : ℝ) (t : ℝ) : ℝ :=
  (1 / N) * (∫ t₀ in Set.Icc left right, ‖bumpFourier ((t - t₀) / N)‖ ^ 2) -
  Set.indicator (Set.Icc left right) (fun _ => (1 : ℝ)) t

private lemma smoothingKernelAverage_eq_intervalIntegral (N : ℝ) (hN : 0 < N)
    (left right : ℝ) (hleft_right : left ≤ right) (t : ℝ) :
    (1 / N) * (∫ t₀ in Set.Icc left right, ‖bumpFourier ((t - t₀) / N)‖ ^ 2) =
    ∫ u in (t - right) / N..(t - left) / N, ‖bumpFourier u‖ ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hleft_right]
  have hchange : (fun t₀ : ℝ => ‖bumpFourier ((t - t₀) / N)‖ ^ 2) =
      fun t₀ => ‖bumpFourier (t / N - t₀ / N)‖ ^ 2 := by
    funext t₀
    rw [sub_div]
  rw [hchange]
  simpa only [one_div, smul_eq_mul] using
    (intervalIntegral.inv_smul_integral_comp_sub_div
      (f := fun u : ℝ => ‖bumpFourier u‖ ^ 2) (a := left) (b := right) N (t / N)).trans (by
        congr 1 <;> field_simp)

private lemma smoothing_identity {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ)
    (N : ℝ) (hN : 0 < N)
    (hsep : IsSeparatedFamily (1 / N) ξ)
    (left right : ℝ) (T : ℝ) (hT : T = right - left) (hleft_right : left ≤ right) :
    ∫ t in Set.Icc left right, expSumSq a ξ t =
    T * ∑ r, ‖a r‖ ^ 2 -
      ∫ t : ℝ, expSumSq a ξ t * smoothingKernel N left right t := by
  by_cases hmass : ∑ r, ‖a r‖ ^ 2 = 0
  · have hzero := coeff_eq_zero_of_sum_norm_sq_eq_zero hmass
    simp [expSumSq, expSum, hzero]
  have hmasspos : 0 < ∑ r, ‖a r‖ ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun r _ ↦ sq_nonneg ‖a r‖) (Ne.symm hmass)
  let F : ℝ → ℝ := expSumSq a ξ
  let K : ℝ → ℝ → ℝ := fun t₀ t => ‖bumpFourier ((t - t₀) / N)‖ ^ 2
  let H : ℝ × ℝ → ℝ := fun p => F p.2 * K p.1 p.2
  have hF_nonneg : ∀ t, 0 ≤ F t := expSumSq_nonneg a ξ
  have hK_nonneg : ∀ t₀ t, 0 ≤ K t₀ t := fun t₀ t => sq_nonneg _
  have hH_nonneg : ∀ p, 0 ≤ H p := fun p =>
    mul_nonneg (hF_nonneg p.2) (hK_nonneg p.1 p.2)
  have hF_cont : Continuous F := expSumSq_continuous a ξ
  have hbumpFourier_cont : Continuous bumpFourier := bumpFourier_continuous
  have hK_cont : Continuous (fun p : ℝ × ℝ => K p.1 p.2) := by
    exact ((hbumpFourier_cont.comp
      ((continuous_snd.sub continuous_fst).div_const N)).norm.pow 2)
  have hH_cont : Continuous H :=
    (hF_cont.comp continuous_snd).mul hK_cont
  -- From the blueprint's normalized L² identity (`art`):
  -- ∫_ℝ F(t)|bump̂((t-t₀)/N)|² dt = N for each t₀.
  have h31 : ∀ t₀ : ℝ,
      ∫ t : ℝ, H (t₀, t) = N * ∑ r, ‖a r‖ ^ 2 := by
    intro t₀
    simpa only [H, F, K] using weighted_l2_identity a ξ N hN t₀ hsep
  have hslice : ∀ t₀ : ℝ, Integrable (fun t => H (t₀, t)) := by
    intro t₀
    by_contra h
    have hzero := h31 t₀
    rw [integral_undef h] at hzero
    nlinarith
  -- The product-space integrability follows from the already evaluated slices.
  have hH_int : Integrable H ((volume.restrict (Set.Icc left right)).prod volume) := by
    apply (integrable_prod_iff hH_cont.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ hslice
    · have hmarginal : (fun t₀ : ℝ => ∫ t : ℝ, ‖H (t₀, t)‖) =
          fun _ => N * ∑ r, ‖a r‖ ^ 2 := by
        funext t₀
        rw [show (fun t : ℝ => ‖H (t₀, t)‖) = fun t => H (t₀, t) by
          funext t
          exact Real.norm_of_nonneg (hH_nonneg (t₀, t))]
        exact h31 t₀
      rw [hmarginal]
      exact integrableOn_const measure_Icc_lt_top.ne
  -- Integrate the constant marginal over t₀ ∈ I.
  have hNT : ∫ _ in Set.Icc left right, N * ∑ r, ‖a r‖ ^ 2 =
      N * T * ∑ r, ‖a r‖ ^ 2 := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hleft_right, smul_eq_mul, hT]
    ring
  -- Fubini, with the interval restriction built into the first measure.
  have hswap :
      (∫ t₀ in Set.Icc left right, ∫ t : ℝ, H (t₀, t)) =
      ∫ t : ℝ, ∫ t₀ in Set.Icc left right, H (t₀, t) := by
    exact integral_integral_swap hH_int
  have hFubini : ∫ t : ℝ, F t * (∫ t₀ in Set.Icc left right, K t₀ t) =
      N * T * ∑ r, ‖a r‖ ^ 2 := by
    calc
      ∫ t : ℝ, F t * (∫ t₀ in Set.Icc left right, K t₀ t) =
          ∫ t : ℝ, ∫ t₀ in Set.Icc left right, H (t₀, t) := by
            congr 1
            ext t
            change F t * (∫ t₀ in Set.Icc left right, K t₀ t) =
              ∫ t₀ in Set.Icc left right, F t * K t₀ t
            rw [integral_const_mul]
      _ = ∫ t₀ in Set.Icc left right, ∫ t : ℝ, H (t₀, t) := hswap.symm
      _ = ∫ _ in Set.Icc left right, N * ∑ r, ‖a r‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t₀ _
        exact h31 t₀
      _ = N * T * ∑ r, ‖a r‖ ^ 2 := hNT
  have hFK_int : Integrable (fun t : ℝ => F t *
      (∫ t₀ in Set.Icc left right, K t₀ t)) := by
    have hmarginal := hH_int.integral_prod_right
    apply hmarginal.congr
    apply ae_of_all
    intro t
    change (∫ t₀ in Set.Icc left right, F t * K t₀ t) =
      F t * (∫ t₀ in Set.Icc left right, K t₀ t)
    rw [integral_const_mul]
  have hFI_int : Integrable ((Set.Icc left right).indicator F) :=
    hF_cont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hexpand : (fun t : ℝ => expSumSq a ξ t * smoothingKernel N left right t) =
      fun t => (1 / N) * (F t * (∫ t₀ in Set.Icc left right, K t₀ t)) -
        (Set.Icc left right).indicator F t := by
    funext t
    simp only [smoothingKernel, F, K]
    by_cases ht : t ∈ Set.Icc left right
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  rw [hexpand, integral_sub (hFK_int.const_mul _) hFI_int,
    integral_const_mul, hFubini, integral_indicator measurableSet_Icc]
  field_simp
  ring

/-! ### Decay of the smoothing error -/

private lemma smoothing_kernel_decay :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℝ, 0 < N →
    ∀ left right : ℝ, left ≤ right →
    ∀ t : ℝ,
    |smoothingKernel N left right t| ≤
    C * (1 + min (|t - left| / N) (|t - right| / N)) ^ (-(10 : ℝ)) := by
  let f : ℝ → ℝ := fun u => ‖bumpFourier u‖ ^ 2
  have hf_nonneg : ∀ u, 0 ≤ f u := fun u => sq_nonneg _
  have hf_int : Integrable f := by
    simpa only [f] using bumpFourier_sq_integrable
  obtain ⟨C₀, hC₀, hdecay⟩ := bumpFourier_decay 6
  let w : ℝ → ℝ := fun u => (1 + |u|) ^ (-(2 : ℝ))
  have hw_nonneg : ∀ u, 0 ≤ w u := fun u => Real.rpow_nonneg (by positivity) _
  have hw_int : Integrable w := by
    simpa only [w, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num))
  let A := ∫ u : ℝ, w u
  have hA : 0 ≤ A := integral_nonneg hw_nonneg
  let C := C₀ ^ 2 * (A + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have htail : ∀ d : ℝ, 0 ≤ d →
      ∫ u in {u : ℝ | d ≤ |u|}, f u ≤ C * (1 + d) ^ (-(10 : ℝ)) := by
    intro d hd
    let q := (1 + d) ^ (-(10 : ℝ))
    have hq : 0 ≤ q := Real.rpow_nonneg (by positivity) _
    have hmajorant : Integrable (fun u => C₀ ^ 2 * q * w u) :=
      by simpa only [mul_assoc] using (hw_int.const_mul q).const_mul (C₀ ^ 2)
    calc
      ∫ u in {u : ℝ | d ≤ |u|}, f u ≤
          ∫ u in {u : ℝ | d ≤ |u|}, C₀ ^ 2 * q * w u := by
        apply setIntegral_mono_on hf_int.integrableOn hmajorant.integrableOn
          (measurableSet_le measurable_const (continuous_abs.measurable))
        intro u hu
        change d ≤ |u| at hu
        have hsquare : f u ≤ C₀ ^ 2 * (1 + |u|) ^ (-(12 : ℝ)) := by
          dsimp [f]
          have hd' := hdecay u
          have hp : 0 ≤ (1 + |u|) ^ (-(6 : ℝ)) := Real.rpow_nonneg (by positivity) _
          have hp_sq : (1 + |u|) ^ (-(12 : ℝ)) =
              ((1 + |u|) ^ (-(6 : ℝ))) ^ 2 := by
            rw [pow_two, ← Real.rpow_add (by positivity)]
            norm_num
          calc
            ‖bumpFourier u‖ ^ 2 ≤ (C₀ * (1 + |u|) ^ (-(6 : ℝ))) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC₀.le hp)).2 hd'
            _ = C₀ ^ 2 * ((1 + |u|) ^ (-(6 : ℝ))) ^ 2 := by ring
            _ = C₀ ^ 2 * (1 + |u|) ^ (-(12 : ℝ)) := by rw [hp_sq]
        have hfactor : (1 + |u|) ^ (-(12 : ℝ)) =
            w u * (1 + |u|) ^ (-(10 : ℝ)) := by
          dsimp [w]
          rw [← Real.rpow_add (by positivity)]
          norm_num
        have hmono : (1 + |u|) ^ (-(10 : ℝ)) ≤ q := by
          dsimp [q]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        calc
          f u ≤ C₀ ^ 2 * (1 + |u|) ^ (-(12 : ℝ)) := hsquare
          _ = C₀ ^ 2 * (w u * (1 + |u|) ^ (-(10 : ℝ))) := by rw [hfactor]
          _ ≤ C₀ ^ 2 * (w u * q) := by gcongr
          _ = C₀ ^ 2 * q * w u := by ring
      _ ≤ ∫ u : ℝ, C₀ ^ 2 * q * w u :=
        setIntegral_le_integral hmajorant (ae_of_all _ fun u => by positivity)
      _ = C₀ ^ 2 * q * A := by simp only [integral_const_mul, A]
      _ ≤ C * q := by
        dsimp [C]
        nlinarith [mul_nonneg (sq_nonneg C₀) hq]
      _ = C * (1 + d) ^ (-(10 : ℝ)) := rfl
  refine ⟨C, hC, ?_⟩
  intro N hN left right hleft_right t
  let uLower := (t - right) / N
  let uUpper := (t - left) / N
  let d := min |uUpper| |uLower|
  have hLowerUpper : uLower ≤ uUpper := by
    dsimp [uLower, uUpper]
    exact div_le_div_of_nonneg_right (sub_le_sub_left hleft_right t) hN.le
  have hd : 0 ≤ d := le_min (abs_nonneg _) (abs_nonneg _)
  have hsubst : (1 / N) * (∫ t₀ in Set.Icc left right, f ((t - t₀) / N)) =
      ∫ u in Set.Icc uLower uUpper, f u := by
    simpa only [f, uLower, uUpper, intervalIntegral.integral_of_le hLowerUpper,
      integral_Icc_eq_integral_Ioc] using
      smoothingKernelAverage_eq_intervalIntegral N hN left right hleft_right t
  have hd_eq : d = min (|t - left| / N) (|t - right| / N) := by
    dsimp [d, uLower, uUpper]
    rw [abs_div, abs_div, abs_of_pos hN]
  by_cases ht : t ∈ Set.Icc left right
  · have huLower_nonpos : uLower ≤ 0 := by
      dsimp [uLower]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.2) hN.le
    have huUpper_nonneg : 0 ≤ uUpper := by
      dsimp [uUpper]
      exact div_nonneg (sub_nonneg.mpr ht.1) hN.le
    have hsubset : (Set.Icc uLower uUpper)ᶜ ⊆ {u : ℝ | d ≤ |u|} := by
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hu
      simp only [Set.mem_setOf_eq]
      rcases hu with hu | hu
      · rw [abs_of_nonpos (hu.le.trans huLower_nonpos)]
        exact (min_le_right |uUpper| |uLower|).trans (by
          rw [abs_of_nonpos huLower_nonpos]
          linarith)
      · rw [abs_of_nonneg (huUpper_nonneg.trans hu.le)]
        exact (min_le_left |uUpper| |uLower|).trans (by
          rw [abs_of_nonneg huUpper_nonneg]
          linarith)
    have hcomp : (∫ u in Set.Icc uLower uUpper, f u) - 1 =
        -(∫ u in (Set.Icc uLower uUpper)ᶜ, f u) := by
      rw [setIntegral_compl measurableSet_Icc hf_int, bumpFourier_l2]
      ring
    rw [smoothingKernel, Set.indicator_of_mem ht]
    change |(1 / N) * (∫ t₀ in Set.Icc left right, f ((t - t₀) / N)) - 1| ≤ _
    rw [hsubst, hcomp, abs_neg, abs_of_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl fun u _ => hf_nonneg u)]
    rw [← hd_eq]
    exact (setIntegral_mono_set hf_int.integrableOn (ae_of_all _ hf_nonneg)
      (ae_of_all _ hsubset)).trans (htail d hd)
  · have hzero : (0 : ℝ) ∉ Set.Icc uLower uUpper := by
      intro h0
      apply ht
      constructor
      · apply sub_nonneg.mp
        rcases div_nonneg_iff.mp h0.2 with h | h
        · exact h.1
        · exact (hN.not_ge h.2).elim
      · apply sub_nonpos.mp
        rcases div_nonpos_iff.mp h0.1 with h | h
        · exact (hN.not_ge h.2).elim
        · exact h.1
    have hsubset : Set.Icc uLower uUpper ⊆ {u : ℝ | d ≤ |u|} := by
      intro u hu
      rcases hu with ⟨hu1, hu2⟩
      simp only [Set.mem_setOf_eq]
      have hzero' : 0 < uLower ∨ uUpper < 0 := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hzero
      rcases hzero' with hLowerPos | hUpperNeg
      · rw [abs_of_nonneg (hLowerPos.le.trans hu1)]
        exact (min_le_right |uUpper| |uLower|).trans (by
          rw [abs_of_nonneg hLowerPos.le]
          linarith)
      · rw [abs_of_nonpos (hu2.trans hUpperNeg.le)]
        exact (min_le_left |uUpper| |uLower|).trans (by
          rw [abs_of_nonpos hUpperNeg.le]
          linarith)
    rw [smoothingKernel, Set.indicator_of_notMem ht]
    change |(1 / N) * (∫ t₀ in Set.Icc left right, f ((t - t₀) / N)) - 0| ≤ _
    rw [sub_zero, hsubst, abs_of_nonneg
      (setIntegral_nonneg measurableSet_Icc fun u _ => hf_nonneg u)]
    rw [← hd_eq]
    exact (setIntegral_mono_set hf_int.integrableOn (ae_of_all _ hf_nonneg)
      (ae_of_all _ hsubset)).trans (htail d hd)

private lemma smoothingKernelAverage_continuous (N : ℝ) (hN : 0 < N)
    (left right : ℝ) (hleft_right : left ≤ right) :
    Continuous (fun t : ℝ =>
      (1 / N) * (∫ t₀ in Set.Icc left right, ‖bumpFourier ((t - t₀) / N)‖ ^ 2)) := by
  let f : ℝ → ℝ := fun u => ‖bumpFourier u‖ ^ 2
  have hf_int : Integrable f := by
    simpa only [f] using bumpFourier_sq_integrable
  let P : ℝ → ℝ := fun x => ∫ u in 0..x, f u
  have hP_cont : Continuous P :=
    intervalIntegral.continuous_primitive (fun x y => hf_int.intervalIntegrable) 0
  have havg : (fun t : ℝ =>
      (1 / N) * (∫ t₀ in Set.Icc left right, ‖bumpFourier ((t - t₀) / N)‖ ^ 2)) =
      fun t => P ((t - left) / N) - P ((t - right) / N) := by
    funext t
    rw [smoothingKernelAverage_eq_intervalIntegral N hN left right hleft_right t]
    dsimp [P]
    exact (intervalIntegral.integral_interval_sub_left
      hf_int.intervalIntegrable hf_int.intervalIntegrable).symm
  rw [havg]
  exact (hP_cont.comp ((continuous_id.sub continuous_const).div_const N)).sub
    (hP_cont.comp ((continuous_id.sub continuous_const).div_const N))

private lemma smoothingKernel_aestronglyMeasurable (N : ℝ) (hN : 0 < N)
    (left right : ℝ) (hleft_right : left ≤ right) :
    AEStronglyMeasurable (smoothingKernel N left right) := by
  have hind_meas : AEStronglyMeasurable
      (Set.indicator (Set.Icc left right) (fun _ => (1 : ℝ))) :=
    (Measurable.indicator measurable_const measurableSet_Icc).aestronglyMeasurable
  exact (smoothingKernelAverage_continuous N hN left right hleft_right).aestronglyMeasurable.sub
    hind_meas

/-! ### Integrated smoothing-error bound -/

private lemma smoothing_error_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (N : ℝ),
    0 < N →
    IsSeparatedFamily (1 / N) ξ →
    ∀ left right : ℝ, left ≤ right →
    |∫ t : ℝ, expSumSq a ξ t * smoothingKernel N left right t| ≤
      C * N * ∑ r, ‖a r‖ ^ 2 := by
  obtain ⟨C₃, hC₃, hlocal_bound⟩ := local_l2_bound
  obtain ⟨C₅, hC₅, hkernel_bound⟩ := smoothing_kernel_decay
  let b : ℤ → ℝ := fun k => |(k : ℝ) + 1 / 2| ^ (-(10 : ℝ))
  have hb_nonneg : ∀ k, 0 ≤ b k :=
    fun k => Real.rpow_nonneg (abs_nonneg _) _
  have hb_summable : Summable b := by
    have h := (Real.summable_one_div_int_add_rpow (1 / 2) 10).2 (by norm_num)
    apply h.congr
    intro k
    dsimp [b]
    rw [Real.rpow_neg (abs_nonneg _)]
    rw [one_div]
  let B := ∑' k : ℤ, b k
  have hB : 0 ≤ B := tsum_nonneg hb_nonneg
  refine ⟨2 * C₅ * C₃ * (B + 1), by positivity, ?_⟩
  intro ι _ a ξ N hN hsep left right hleft_right
  let F : ℝ → ℝ := expSumSq a ξ
  have hF_nonneg : ∀ t, 0 ≤ F t := expSumSq_nonneg a ξ
  have hF_cont : Continuous F := expSumSq_continuous a ξ
  have hlocal := hlocal_bound a ξ N hN hsep
  have hE := hkernel_bound N hN left right hleft_right
  let weight : ℝ → ℝ → ℝ :=
    fun c t => (1 + |t - c| / N) ^ (-(10 : ℝ))
  have hweight_nonneg : ∀ c t, 0 ≤ weight c t :=
    fun c t => Real.rpow_nonneg (by positivity) _
  have hweight_cont : ∀ c, Continuous (weight c) := by
    intro c
    dsimp [weight]
    apply Continuous.rpow_const
    · fun_prop
    · intro t
      left
      positivity
  let W : ℝ → ℝ → ℝ := fun c t => F t * weight c t
  have hW_nonneg : ∀ c t, 0 ≤ W c t :=
    fun c t => mul_nonneg (hF_nonneg t) (hweight_nonneg c t)
  have hW_cont : ∀ c, Continuous (W c) :=
    fun c => hF_cont.mul (hweight_cont c)
  let cell : ℝ → ℤ → Set ℝ :=
    fun c k => Set.Ico (c + k • N) (c + (k + 1) • N)
  have hcell_meas : ∀ c k, MeasurableSet (cell c k) :=
    fun c k => measurableSet_Ico
  have hcell_pairwise : ∀ c, Pairwise (fun i j => Disjoint (cell c i) (cell c j)) := by
    intro c
    simpa only [cell] using Set.pairwise_disjoint_Ico_add_zsmul c N
  have hcell_cover : ∀ c, ⋃ k : ℤ, cell c k = Set.univ := by
    intro c
    simpa only [cell] using iUnion_Ico_add_zsmul hN c
  have hcell_weight : ∀ c k t, t ∈ cell c k → weight c t ≤ b k := by
    intro c k t ht
    have ht' : c + (k : ℝ) * N ≤ t ∧ t < c + ((k : ℝ) + 1) * N := by
      change c + k • N ≤ t ∧ t < c + (k + 1) • N at ht
      simpa only [zsmul_eq_mul, Int.cast_add, Int.cast_one] using ht
    let x := (t - c) / N
    have hx_left : (k : ℝ) ≤ x := by
      apply (le_div_iff₀ hN).2
      linarith [ht'.1]
    have hx_right : x < (k : ℝ) + 1 := by
      apply (div_lt_iff₀ hN).2
      linarith [ht'.2]
    have hmid_pos : 0 < |(k : ℝ) + 1 / 2| := by
      rw [abs_pos]
      intro hk
      have hk' : (2 : ℝ) * (k : ℝ) = -1 := by linarith
      have hk'' : (2 * k : ℤ) = -1 := by exact_mod_cast hk'
      omega
    have hmid : |((k : ℝ) + 1 / 2) - x| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hbase : |(k : ℝ) + 1 / 2| ≤ 1 + |x| := by
      calc
        |(k : ℝ) + 1 / 2| = |(((k : ℝ) + 1 / 2) - x) + x| := by ring_nf
        _ ≤ |((k : ℝ) + 1 / 2) - x| + |x| := abs_add_le _ _
        _ ≤ 1 / 2 + |x| := by linarith
        _ ≤ 1 + |x| := by linarith
    have hrpow := Real.rpow_le_rpow_of_nonpos hmid_pos hbase (by norm_num : (-(10 : ℝ)) ≤ 0)
    have hxabs : |t - c| / N = |x| := by
      dsimp [x]
      rw [abs_div, abs_of_pos hN]
    simpa only [weight, b, hxabs] using hrpow
  have hcell_bound : ∀ c k,
      ∫ t in cell c k, W c t ≤
        b k * (C₃ * N * ∑ r, ‖a r‖ ^ 2) := by
    intro c k
    let cellLeft := c + k • N
    have hend : c + (k + 1) • N = cellLeft + N := by
      dsimp [cellLeft]
      rw [add_smul, one_smul]
      ring
    have hcell_eq : cell c k = Set.Ico cellLeft (cellLeft + N) := by
      dsimp [cell]
      rw [hend]
    have hWcell : IntegrableOn (W c) (cell c k) :=
      (hW_cont c).integrableOn_Icc.mono_set (by
        rw [hcell_eq]
        exact Set.Ico_subset_Icc_self)
    have hbFcell : IntegrableOn (fun t => b k * F t) (cell c k) :=
      ((continuous_const.mul hF_cont).integrableOn_Icc).mono_set (by
        rw [hcell_eq]
        exact Set.Ico_subset_Icc_self)
    have hFcell :
        ∫ t in cell c k, F t ≤ ∫ t in Set.Icc cellLeft (cellLeft + N), F t := by
      apply setIntegral_mono_set hF_cont.integrableOn_Icc
        (ae_of_all _ fun t => hF_nonneg t)
      apply ae_of_all
      rw [hcell_eq]
      exact Set.Ico_subset_Icc_self
    calc
      ∫ t in cell c k, W c t ≤ ∫ t in cell c k, b k * F t := by
        apply setIntegral_mono_on hWcell hbFcell (hcell_meas c k)
        intro t ht
        dsimp [W]
        calc
          F t * weight c t ≤ F t * b k :=
            mul_le_mul_of_nonneg_left (hcell_weight c k t ht) (hF_nonneg t)
          _ = b k * F t := by ring
      _ = b k * ∫ t in cell c k, F t := integral_const_mul _ _
      _ ≤ b k * ∫ t in Set.Icc cellLeft (cellLeft + N), F t :=
        mul_le_mul_of_nonneg_left hFcell (hb_nonneg k)
      _ ≤ b k * (C₃ * N * ∑ r, ‖a r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hlocal cellLeft) (hb_nonneg k)
  have hW : ∀ c, Integrable (W c) ∧ ∫ t : ℝ, W c t ≤
      B * (C₃ * N * ∑ r, ‖a r‖ ^ 2) := by
    intro c
    have hcell_int : ∀ k, IntegrableOn (W c) (cell c k) := by
      intro k
      exact (hW_cont c).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
    have hmajor_summable : Summable
        (fun k => b k * (C₃ * N * ∑ r, ‖a r‖ ^ 2)) :=
      hb_summable.mul_right (C₃ * N * ∑ r, ‖a r‖ ^ 2)
    have hsum_norm : Summable (fun k => ∫ t in cell c k, ‖W c t‖) := by
      refine Summable.of_nonneg_of_le
        (f := fun k => b k * (C₃ * N * ∑ r, ‖a r‖ ^ 2))
        (g := fun k => ∫ t in cell c k, ‖W c t‖) ?_ ?_
        hmajor_summable
      · intro k
        exact setIntegral_nonneg (hcell_meas c k) fun t _ => norm_nonneg _
      · intro k
        rw [show (fun t => ‖W c t‖) = W c by
          funext t
          exact Real.norm_of_nonneg (hW_nonneg c t)]
        exact hcell_bound c k
    have hsum : Summable (fun k => ∫ t in cell c k, W c t) := by
      apply hsum_norm.congr
      intro k
      rw [show (fun t => ‖W c t‖) = W c by
        funext t
        exact Real.norm_of_nonneg (hW_nonneg c t)]
    have hW_int : Integrable (W c) := by
      have hu := integrableOn_iUnion_of_summable_integral_norm hcell_int hsum_norm
      rw [hcell_cover c] at hu
      simpa only [integrableOn_univ] using hu
    refine ⟨hW_int, ?_⟩
    have hpartition :
        ∫ t : ℝ, W c t = ∑' k : ℤ, ∫ t in cell c k, W c t := by
      rw [← setIntegral_univ, ← hcell_cover c]
      exact integral_iUnion (hcell_meas c) (hcell_pairwise c) hW_int.integrableOn
    rw [hpartition]
    calc
      ∑' k : ℤ, ∫ t in cell c k, W c t ≤
          ∑' k : ℤ, b k * (C₃ * N * ∑ r, ‖a r‖ ^ 2) :=
        hsum.tsum_le_tsum (hcell_bound c) hmajor_summable
      _ = B * (C₃ * N * ∑ r, ‖a r‖ ^ 2) := by
        exact hb_summable.tsum_mul_right (C₃ * N * ∑ r, ‖a r‖ ^ 2)
  have hmin_split : ∀ t,
      (1 + min (|t - left| / N) (|t - right| / N)) ^ (-(10 : ℝ)) ≤
      weight left t + weight right t := by
    intro t
    rcases le_total (|t - left| / N) (|t - right| / N) with h | h
    · rw [min_eq_left h]
      dsimp [weight]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · rw [min_eq_right h]
      dsimp [weight]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  have hmajor : ∀ t,
      F t * |smoothingKernel N left right t| ≤ C₅ * (W left t + W right t) := by
    intro t
    calc
      F t * |smoothingKernel N left right t| ≤
          F t * (C₅ * (1 + min (|t - left| / N) (|t - right| / N)) ^ (-(10 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hE t) (hF_nonneg t)
      _ ≤ F t * (C₅ * (weight left t + weight right t)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hmin_split t) hC₅.le) (hF_nonneg t)
      _ = C₅ * (W left t + W right t) := by
        dsimp [W]
        ring
  have hWLeft := hW left
  have hWRight := hW right
  have hmajor_int : Integrable (fun t => C₅ * (W left t + W right t)) :=
    (hWLeft.1.add hWRight.1).const_mul C₅
  have hkernel_meas := smoothingKernel_aestronglyMeasurable N hN left right hleft_right
  have hkernel_abs_meas : AEStronglyMeasurable
      (fun t => |smoothingKernel N left right t|) := by
    simpa only [Real.norm_eq_abs] using hkernel_meas.norm
  have hFEabs_meas : AEStronglyMeasurable
      (fun t => F t * |smoothingKernel N left right t|) :=
    hF_cont.aestronglyMeasurable.mul hkernel_abs_meas
  have hFEabs : Integrable (fun t => F t * |smoothingKernel N left right t|) := by
    apply hmajor_int.mono' hFEabs_meas
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hF_nonneg t) (abs_nonneg _))]
    exact hmajor t
  have hFE : Integrable (fun t => F t * smoothingKernel N left right t) := by
    apply hFEabs.mono' (hF_cont.aestronglyMeasurable.mul hkernel_meas)
    filter_upwards with t
    change |F t * smoothingKernel N left right t| ≤ F t * |smoothingKernel N left right t|
    rw [abs_mul, abs_of_nonneg (hF_nonneg t)]
  calc
    |∫ t : ℝ, expSumSq a ξ t * smoothingKernel N left right t| =
        |∫ t : ℝ, F t * smoothingKernel N left right t| := by rfl
    _ ≤ ∫ t : ℝ, |F t * smoothingKernel N left right t| :=
      abs_integral_le_integral_abs
    _ = ∫ t : ℝ, F t * |smoothingKernel N left right t| := by
      congr 1
      funext t
      rw [abs_mul, abs_of_nonneg (hF_nonneg t)]
    _ ≤ ∫ t : ℝ, C₅ * (W left t + W right t) :=
      integral_mono hFEabs hmajor_int hmajor
    _ = C₅ * ((∫ t : ℝ, W left t) + ∫ t : ℝ, W right t) := by
      rw [integral_const_mul, integral_add hWLeft.1 hWRight.1]
    _ ≤ C₅ * (B * (C₃ * N * ∑ r, ‖a r‖ ^ 2) +
        B * (C₃ * N * ∑ r, ‖a r‖ ^ 2)) := by
      gcongr
      · exact hWLeft.2
      · exact hWRight.2
    _ ≤ 2 * C₅ * C₃ * (B + 1) * N * ∑ r, ‖a r‖ ^ 2 := by
      calc
        C₅ * (B * (C₃ * N * ∑ r, ‖a r‖ ^ 2) +
            B * (C₃ * N * ∑ r, ‖a r‖ ^ 2)) =
            (2 * C₅ * C₃ * N * ∑ r, ‖a r‖ ^ 2) * B := by ring
        _ ≤ (2 * C₅ * C₃ * N * ∑ r, ‖a r‖ ^ 2) * (B + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
        _ = 2 * C₅ * C₃ * (B + 1) * N * ∑ r, ‖a r‖ ^ 2 := by ring

/-! ### `L²` integral estimate lemma -/

/-- If `ξ` is a finite `1 / N`-separated
  family of real numbers, then over any interval of length `T`,
  `∫ |∑ r, a r * 𝐞 (ξ r * t)|² dt =
    (T + O(N)) * ∑ r, ‖a r‖²`.
  The conclusion expresses `O(N)` as `θ * N`, with `θ` bounded by a universal
  constant. -/
theorem l2_integral_estimate :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (N : ℝ),
    0 < N →
    IsSeparatedFamily (1 / N) ξ →
    ∀ left right T : ℝ,
    T = right - left →
    left ≤ right →
    ∃ θ : ℝ, |θ| ≤ C ∧
    ∫ t in Set.Icc left right,
      ‖∑ r, a r * 𝐞 (ξ r * t)‖ ^ 2 =
    (T + θ * N) * ∑ r, ‖a r‖ ^ 2 := by
  obtain ⟨C, hC, herror⟩ := smoothing_error_bound
  refine ⟨C, hC, ?_⟩
  intro ι _ a ξ N hN hsep left right T hT hleft_right
  change ∃ θ : ℝ, |θ| ≤ C ∧
    ∫ t in Set.Icc left right, expSumSq a ξ t =
    (T + θ * N) * ∑ r, ‖a r‖ ^ 2
  set M := ∑ r, ‖a r‖ ^ 2
  by_cases hM0 : M = 0
  · refine ⟨0, by simpa using hC.le, ?_⟩
    have hzero := coeff_eq_zero_of_sum_norm_sq_eq_zero (by simpa only [M] using hM0)
    simp [expSumSq, expSum, hzero, hM0]
  · have hMpos : 0 < M :=
      lt_of_le_of_ne (Finset.sum_nonneg fun r _ => sq_nonneg _) (Ne.symm hM0)
    have h4 := smoothing_identity a ξ N hN hsep left right T hT hleft_right
    have h6 := herror a ξ N hN hsep left right hleft_right
    set err := ∫ t : ℝ, expSumSq a ξ t * smoothingKernel N left right t
    have hA_eq : ∫ t in Set.Icc left right, expSumSq a ξ t = T * M - err := by
      simpa only [err, M] using h4
    have herr_bd : |err| ≤ C * N * M := by
      simpa only [err, M] using h6
    have hNM : 0 < N * M := mul_pos hN hMpos
    refine ⟨-err / (N * M), ?_, ?_⟩
    · rw [abs_div, abs_neg, abs_of_pos hNM, div_le_iff₀ hNM]
      simpa only [mul_assoc] using herr_bd
    · rw [hA_eq]
      field_simp [hN.ne', hMpos.ne']
      ring

end Expdb

end
end

section
namespace GuthMaynard.CitedLV.MVT

open MeasureTheory Set

lemma abs_intervalIntegral_le {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) {a b t t0 : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (ht0 : t0 ∈ Set.Icc a b) :
    |∫ s in t..t0, h s| ≤ ∫ s in a..b, h s := by
  rcases le_total t t0 with hle | hle
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hle (fun x _ => h0 x))]
    exact intervalIntegral.integral_mono_interval ht.1 hle ht0.2
      (Filter.Eventually.of_forall h0) (hc.intervalIntegrable _ _)
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hle (fun x _ => h0 x))]
    exact intervalIntegral.integral_mono_interval ht0.1 hle ht.2
      (Filter.Eventually.of_forall h0) (hc.intervalIntegrable _ _)

/-- Pointwise Gallagher/Sobolev inequality on a unit window. -/
lemma sq_le_window {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t) (hFc : Continuous F)
    (hF'c : Continuous F') (t0 : ℝ) :
    ‖F t0‖ ^ 2 ≤ ∫ s in (t0 - 1/2)..(t0 + 1/2), (‖F s‖ ^ 2 + 2 * ‖F s‖ * ‖F' s‖) := by
  set g : ℝ → ℝ := fun t => ‖F t‖ ^ 2 with hg
  set h : ℝ → ℝ := fun t => 2 * ‖F t‖ * ‖F' t‖ with hh
  have hgd : ∀ t, HasDerivAt g (2 * inner ℝ (F t) (F' t)) t := fun t => (hF t).norm_sq
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hg'c : Continuous fun t => 2 * (inner ℝ (F t) (F' t) : ℝ) := by fun_prop
  have hle : ∀ t, |2 * (inner ℝ (F t) (F' t) : ℝ)| ≤ h t := by
    intro t
    rw [hh]; simp only
    rw [abs_mul, abs_two]
    have := abs_real_inner_le_norm (F t) (F' t)
    nlinarith [this]
  have h0 : ∀ t, 0 ≤ h t := fun t => by rw [hh]; positivity
  have hab : t0 - 1/2 ≤ t0 + 1/2 := by linarith
  have hpt : ∀ t ∈ Set.Icc (t0 - 1/2) (t0 + 1/2),
      g t0 ≤ g t + ∫ s in (t0 - 1/2)..(t0 + 1/2), h s := by
    intro t ht
    have h1 : g t0 - g t = ∫ s in t..t0, 2 * (inner ℝ (F s) (F' s) : ℝ) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hgd s)
        (hg'c.intervalIntegrable _ _)).symm
    have h2 : |∫ s in t..t0, 2 * (inner ℝ (F s) (F' s) : ℝ)| ≤ |∫ s in t..t0, h s| := by
      have key : ∀ {x y : ℝ}, x ≤ y → |∫ s in x..y, 2 * (inner ℝ (F s) (F' s) : ℝ)| ≤
          ∫ s in x..y, h s := by
        intro x y hxy
        refine (intervalIntegral.abs_integral_le_integral_abs hxy).trans ?_
        exact intervalIntegral.integral_mono_on hxy
          (hg'c.abs.intervalIntegrable _ _) (hhc.intervalIntegrable _ _) (fun s _ => hle s)
      rcases le_total t t0 with hl | hl
      · exact (key hl).trans (le_abs_self _)
      · rw [intervalIntegral.integral_symm t0 t, intervalIntegral.integral_symm t0 t, abs_neg, abs_neg]
        exact (key hl).trans (le_abs_self _)
    have h4 := abs_intervalIntegral_le hhc h0 hab ht (t0 := t0) ⟨by linarith, by linarith⟩
    have := (le_abs_self _).trans (h2.trans h4)
    linarith
  have hgi : IntervalIntegrable g volume (t0 - 1/2) (t0 + 1/2) := hgc.intervalIntegrable _ _
  have hconst : ∫ s in (t0 - 1/2)..(t0 + 1/2), g t0 = g t0 := by
    simp; ring
  calc ‖F t0‖ ^ 2 = ∫ s in (t0 - 1/2)..(t0 + 1/2), g t0 := hconst.symm
    _ ≤ ∫ s in (t0 - 1/2)..(t0 + 1/2), (g s + ∫ s in (t0 - 1/2)..(t0 + 1/2), h s) := by
        apply intervalIntegral.integral_mono_on hab (by simp)
          (hgi.add (by simp))
        intro x hx; exact hpt x hx
    _ = ∫ s in (t0 - 1/2)..(t0 + 1/2), (g s + h s) := by
        rw [intervalIntegral.integral_add hgi (by simp)]
        rw [intervalIntegral.integral_add hgi (hhc.intervalIntegrable _ _)]
        simp; ring
    _ = _ := rfl

lemma sum_window_le {φ : ℝ → ℝ} (hc : Continuous φ) (h0 : ∀ x, 0 ≤ φ x) (W : Finset ℝ) {T : ℝ}
    (hT : 0 ≤ T)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) (hW : ∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T) :
    ∑ t ∈ W, ∫ s in (t - 1/2)..(t + 1/2), φ s ≤ ∫ s in (-1/2 : ℝ)..(T + 1/2), φ s := by
  have e1 : ∀ t ∈ W, ∫ s in (t - 1/2)..(t + 1/2), φ s = ∫ s in Set.Ioc (t - 1/2) (t + 1/2), φ s := by
    intro t _
    rw [intervalIntegral.integral_of_le (by linarith)]
  rw [Finset.sum_congr rfl e1, intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_biUnion_finset W (fun t _ => measurableSet_Ioc)]
  · apply setIntegral_mono_set (hc.integrableOn_Ioc)
      (Filter.Eventually.of_forall h0)
    apply Filter.Eventually.of_forall
    intro x hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    have := hW t ht
    exact ⟨by linarith [hx.1, this.1], by linarith [hx.2, this.2]⟩
  · intro t ht t' ht' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    have := hsep t (Finset.mem_coe.mp ht) t' (Finset.mem_coe.mp ht') hne
    rcases lt_or_ge t t' with hl | hl
    · rw [abs_of_neg (by linarith)] at this
      linarith [hx.1, hx.2, hx'.1, hx'.2]
    · rw [abs_of_nonneg (by linarith)] at this
      linarith [hx.1, hx.2, hx'.1, hx'.2]
  · intro t _
    exact hc.integrableOn_Ioc

end GuthMaynard.CitedLV.MVT
end

section
namespace GuthMaynard.CitedLV.MVT

open MeasureTheory Set Complex
open scoped FourierTransform

/-- The normalised dyadic exponential sum `∑ a_n (n/N)^{it}`. -/
noncomputable def E (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ))

lemma log_gap {N n m : ℕ} (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) (hm : m ∈ Finset.Icc N (2 * N))
    (hnm : m < n) : 1 / (2 * (N : ℝ)) ≤ Real.log n - Real.log m := by
  rw [Finset.mem_Icc] at hn hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : 1 - (m : ℝ) / n ≤ Real.log ((n : ℝ) / m) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hm0)
    rwa [inv_div] at this
  rw [Real.log_div hn0.ne' hm0.ne'] at h1
  have hnm' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hnm
  have h2n : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : 1 / (2 * (N : ℝ)) ≤ 1 - (m : ℝ) / n := by
    rw [one_sub_div hn0.ne', div_le_div_iff₀ (by positivity) hn0]
    nlinarith
  linarith

open Expdb in
/-- Interval mean value theorem for a dyadic Dirichlet polynomial, with absolute constants. -/
lemma interval_mvt : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (s : Finset ℕ),
    s ⊆ Finset.Icc N (2 * N) → ∀ (a : ℕ → ℂ) (α β : ℝ), α ≤ β →
    ∫ t in Set.Icc α β, ‖E N s a t‖ ^ 2 ≤ (β - α + C₁ * N) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := l2_integral_estimate
  refine ⟨4 * Real.pi * C, by positivity, ?_⟩
  intro N hN s hs a α β hab
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN' : (0 : ℝ) < 4 * Real.pi * N := by positivity
  let ξ : s → ℝ := fun n => Real.log ((n : ℕ) / N) / (2 * Real.pi)
  have hsep : IsSeparatedFamily (1 / (4 * Real.pi * N)) ξ := by
    intro i j hij
    have hne : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
    have key : ∀ i j : s, (j : ℕ) < i → 1 / (4 * Real.pi * N) ≤ dist (ξ i) (ξ j) := by
      intro i j hji
      have hgap := log_gap hN (hs i.2) (hs j.2) hji
      have hi0 : (0 : ℝ) < (i : ℕ) := by
        have := (Finset.mem_Icc.mp (hs i.2)).1; exact_mod_cast (by omega : 0 < (i : ℕ))
      have hj0 : (0 : ℝ) < (j : ℕ) := by
        have := (Finset.mem_Icc.mp (hs j.2)).1; exact_mod_cast (by omega : 0 < (j : ℕ))
      have hd : ξ i - ξ j = (Real.log i - Real.log j) / (2 * Real.pi) := by
        simp only [ξ]
        rw [Real.log_div hi0.ne' hN0.ne', Real.log_div hj0.ne' hN0.ne']
        ring
      rw [Real.dist_eq, hd, abs_of_nonneg (div_nonneg (by linarith [one_div_pos.mpr (show (0:ℝ) < 2 * N by positivity)]) (by positivity))]
      rw [div_le_div_iff₀ hN' (by positivity)]
      have := Real.pi_pos
      calc 1 * (2 * Real.pi) = (1 / (2 * (N : ℝ))) * (4 * Real.pi * N) := by field_simp; ring
        _ ≤ _ := by gcongr
    rcases lt_or_gt_of_ne hne with h | h
    · rw [dist_comm]; exact key j i h
    · exact key i j h
  obtain ⟨θ, hθ, hint⟩ := hmain (fun n : s => a n) ξ (4 * Real.pi * N) hN' hsep α β (β - α) rfl hab
  have hconv : ∀ t : ℝ, ∑ r : s, a r * 𝐞 (ξ r * t) = E N s a t := by
    intro t
    unfold E
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.fourierChar_apply]
    congr 2
    simp only [ξ]
    push_cast
    field_simp
  simp_rw [hconv] at hint
  rw [hint]
  have hS : ∑ r : s, ‖a r‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_coe_sort s (fun n => ‖a n‖ ^ 2)
  rw [hS]
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have := (le_abs_self θ).trans hθ
  nlinarith [mul_le_mul_of_nonneg_right hθ (le_of_lt hN'), abs_mul_abs_self θ, le_abs_self θ]

lemma E_continuous (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (E N s a) := by
  unfold E; fun_prop

lemma E_hasDerivAt (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (E N s a)
      (Complex.I * E N s (fun n => a n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ)) t) t := by
  unfold E
  have : ∀ n ∈ s, HasDerivAt
      (fun t : ℝ => a n * Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ)))
      (a n * (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I *
        Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ)))) t := by
    intro n _
    have h0 : HasDerivAt (fun y : ℝ => Complex.exp ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * (y : ℂ)))
        (Complex.exp ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) *
          ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * 1)) t :=
      (((hasDerivAt_id t).ofReal_comp).const_mul _).cexp
    refine (h0.const_mul (a n)).congr_deriv ?_
    ring
  refine (HasDerivAt.fun_sum this).congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma norm_E_derivSum_le (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : s ⊆ Finset.Icc N (2 * N))
    (a : ℕ → ℂ) :
    ∑ n ∈ s, ‖a n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ)‖ ^ 2 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_Icc.mp (hs hn)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn'.1
  have h2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn'.2
  have hl0 : 0 ≤ Real.log ((n : ℝ) / N) := Real.log_nonneg ((one_le_div hN0).mpr h1)
  have hl1 : Real.log ((n : ℝ) / N) ≤ 1 := by
    have : Real.log ((n : ℝ) / N) ≤ Real.log 2 := Real.log_le_log (div_pos (by linarith) hN0)
      ((div_le_iff₀ hN0).mpr (by linarith))
    have h2' := Real.log_two_lt_d9
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0, mul_pow]
  have : Real.log ((n : ℝ) / N) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ‖a n‖]

lemma norm_S_eq (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : s ⊆ Finset.Icc N (2 * N)) (c : ℕ → ℂ)
    (t : ℝ) :
    ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = ‖E N s c t‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) * E N s c t := by
    unfold E
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Icc.mp (hs hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Complex.cpow_def_of_ne_zero hnc]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    rw [hlog]
    have : Real.log ((n : ℝ) / N) = Real.log n - Real.log N := Real.log_div hn0.ne' hN0.ne'
    rw [this]
    have e : Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) *
        Complex.exp (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) =
        Complex.exp (((Real.log n : ℝ) : ℂ) * ((t : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc c n * Complex.exp (((Real.log n : ℝ) : ℂ) * ((t : ℂ) * Complex.I))
        = c n * (Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) *
        Complex.exp (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ))) := by rw [e]
      _ = _ := by ring
  rw [this, norm_mul]
  have : ‖Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    rw [show ((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ) = ((Real.log N * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]

/-- **Discrete mean value theorem** for a dyadic Dirichlet polynomial at `1`-separated points,
with absolute constants. -/
theorem disc_mvt : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (s : Finset ℕ),
    s ⊆ Finset.Icc N (2 * N) → ∀ (c : ℕ → ℂ) (W : Finset ℝ) (T : ℝ), 0 ≤ T →
    (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) → (∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T) →
    ∑ t ∈ W, ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      3 * (T + 1 + C₁ * N) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  obtain ⟨C₁, hC₁, hmv⟩ := interval_mvt
  refine ⟨C₁, hC₁, ?_⟩
  intro N hN s hs c W T hT hsep hW
  set c' : ℕ → ℂ := fun n => c n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ) with hc'
  set F := E N s c
  set F' : ℝ → ℂ := fun t => Complex.I * E N s c' t with hF'
  have hFd : ∀ t, HasDerivAt F (F' t) t := fun t => E_hasDerivAt N s c t
  have hFc : Continuous F := E_continuous N s c
  have hF'c : Continuous F' := by rw [hF']; have := E_continuous N s c'; fun_prop
  have hφ : Continuous fun x => 2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2 := by fun_prop
  have hφ0 : ∀ x, 0 ≤ 2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2 := fun x => by positivity
  have step1 : ∀ t ∈ W, ‖F t‖ ^ 2 ≤ ∫ x in (t - 1/2)..(t + 1/2), (2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2) := by
    intro t _
    refine (sq_le_window hFd hFc hF'c t).trans ?_
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun x => ‖F x‖ ^ 2 + 2 * ‖F x‖ * ‖F' x‖).intervalIntegrable _ _
    · exact hφ.intervalIntegrable _ _
    · intro x _
      nlinarith [sq_nonneg (‖F x‖ - ‖F' x‖)]
  have step2 := sum_window_le hφ hφ0 W hT hsep hW
  have step3 : ∑ t ∈ W, ‖F t‖ ^ 2 ≤ ∫ x in (-1/2 : ℝ)..(T + 1/2), (2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2) :=
    (Finset.sum_le_sum step1).trans step2
  have hab : (-1/2 : ℝ) ≤ T + 1/2 := by linarith
  have hnF' : ∀ x, ‖F' x‖ = ‖E N s c' x‖ := fun x => by rw [hF']; simp
  have hi1 : IntegrableOn (fun x => ‖F x‖ ^ 2) (Set.Icc (-1/2 : ℝ) (T + 1/2)) :=
    (by fun_prop : Continuous fun x => ‖F x‖ ^ 2).integrableOn_Icc
  have hi2 : IntegrableOn (fun x => ‖F' x‖ ^ 2) (Set.Icc (-1/2 : ℝ) (T + 1/2)) :=
    (by fun_prop : Continuous fun x => ‖F' x‖ ^ 2).integrableOn_Icc
  have hsplit : ∫ x in (-1/2 : ℝ)..(T + 1/2), (2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2) =
      2 * (∫ x in Set.Icc (-1/2 : ℝ) (T + 1/2), ‖F x‖ ^ 2) +
        ∫ x in Set.Icc (-1/2 : ℝ) (T + 1/2), ‖E N s c' x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_add (hi1.const_mul 2) hi2, integral_const_mul]
    simp only [hnF']
  have m1 := hmv N hN s hs c (-1/2) (T + 1/2) hab
  have m2 := hmv N hN s hs c' (-1/2) (T + 1/2) hab
  have hc'le := norm_E_derivSum_le N hN s hs c
  have hS0 : 0 ≤ ∑ n ∈ s, ‖c n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfac : 0 ≤ T + 1/2 - (-1/2) + C₁ * N := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hS : ∑ t ∈ W, ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 =
      ∑ t ∈ W, ‖F t‖ ^ 2 :=
    Finset.sum_congr rfl fun t _ => by rw [norm_S_eq N hN s hs c t]
  rw [hS]
  refine step3.trans ?_
  rw [hsplit]
  have m2' := m2.trans (mul_le_mul_of_nonneg_left hc'le hfac)
  have : (T + 1/2 - (-1/2) + C₁ * N) = T + 1 + C₁ * N := by ring
  rw [this] at m1 m2'
  have m1' : ∫ x in Set.Icc (-1/2 : ℝ) (T + 1/2), ‖F x‖ ^ 2 ≤ _ := m1
  linarith

end GuthMaynard.CitedLV.MVT
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-!
# Blueprint: Heath-Brown's large values estimate (Guth–Maynard Theorem 1.6)

Route: B. Kerr, arXiv:1909.12075, §§5–6 (Theorem 16 with `γ` the indicator of a well-spaced set), with
every double sum taken over *all* pairs (the set lies in an interval of length `T`), which makes the
majorant principle exact and removes the Fourier kernels.

`S A N = ∑_{x,y ∈ A} |∑_{N ≤ n ≤ 2N} n^{-1/2} n^{i(x-y)}|²`.

* `majorant`, `completion` (Kerr Lemmas 18, 19);
* `card_divisors_le`, `mono` (Kerr Lemma 20 / Corollary 21: `S(N) ≪ M^ε S(M)` for `M ≥ 64N`),
  `square` (Lemma 22);
* `dyadic_pointwise` (`|∑_{N≤n≤2N} n^{iu}| ≪ N/|u| + |u|^{1/2} log(|u|+2)`), `bprocess` (Kerr Lemma 26,
  van der Corput's B-process: the deep input), `mvt_bound`;
* `dual` (Kerr Lemma 24, 27, Corollary 28), `thm16`, `heath_brown_large_values`.
-/
/-- `∑_{L ≤ n ≤ U} a(n) n^{iu}`. -/
def D (a : ℕ → ℂ) (L U : ℕ) (u : ℝ) : ℂ := ∑ n ∈ Finset.Icc L U, a n * (n : ℂ) ^ ((u : ℂ) * I)

/-- `∑_{x,y ∈ A} |F(x - y)|²`. -/
def Q (A : Finset ℝ) (F : ℝ → ℂ) : ℝ := ∑ x ∈ A, ∑ y ∈ A, ‖F (x - y)‖ ^ 2

/-- The weight `n^{-1/2}`. -/
def w (n : ℕ) : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- Kerr's `S(N)` over all pairs, unit coefficients. -/
def S (A : Finset ℝ) (N : ℕ) : ℝ := Q A (D w N (2 * N))

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartM
open GuthMaynard.CitedLV.HB
noncomputable section
/-!
# Part M: the majorant principle and completion

* `Q_expand`: `∑_{x,y}|∑_n c_n n^{i(x-y)}|² = ∑_{n,m} c_n conj(c_m) |∑_x n^{ix} conj(m^{ix})|²`.
* `majorant`: immediate from `Q_expand`.
* `completion`: instead of Fourier completion we use a dyadic (binary) decomposition. With `s = h - L`,
  the prefix `[L, L+s)` telescopes over `k < K` into pieces `[L + s_{k+1}, L + s_k)`, `s_k = ⌊s/2^k⌋ 2^k`,
  each empty or a whole level-`k` dyadic block (offsets `j` with `j / 2^k = m`). Cauchy–Schwarz over
  `k < K` and over the two prefixes gives `|∑_{lo..hi}|² ≤ 4K ∑_{k<K} ∑_m |B_{k,m}|²`, and by `majorant`
  and `Q_expand` the blocks of one level sum to at most `Q A (D |a| L U)`. `K = log₂ U + 1 ≪ 1 + log(U+1)`.
-/
/-- `n^{ix}`. -/
def e (n : ℕ) (x : ℝ) : ℂ := (n : ℂ) ^ ((x : ℂ) * I)

/-- `∑_{x ∈ A} n^{ix} conj(m^{ix})`. -/
def G (A : Finset ℝ) (n m : ℕ) : ℂ := ∑ x ∈ A, e n x * (starRingEnd ℂ) (e m x)

/-- `|G|²`. -/
def g (A : Finset ℝ) (n m : ℕ) : ℝ := ‖G A n m‖ ^ 2

lemma g_nonneg (A : Finset ℝ) (n m : ℕ) : 0 ≤ g A n m := by unfold g; positivity

lemma cpow_sub_eq (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) :
    (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I) = e n x * (starRingEnd ℂ) (e n y) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold e
  rw [cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; simp
  rw [hlog]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma swap4 {M : Type*} [AddCommMonoid M] (A : Finset ℝ) (s t : Finset ℕ)
    (f : ℝ → ℝ → ℕ → ℕ → M) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ n ∈ s, ∑ m ∈ t, f x y n m = ∑ n ∈ s, ∑ m ∈ t, ∑ x ∈ A, ∑ y ∈ A, f x y n m := by
  calc _ = ∑ x ∈ A, ∑ n ∈ s, ∑ y ∈ A, ∑ m ∈ t, f x y n m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ A, ∑ n ∈ s, ∑ m ∈ t, ∑ y ∈ A, f x y n m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ n ∈ s, ∑ x ∈ A, ∑ m ∈ t, ∑ y ∈ A, f x y n m := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun n _ => Finset.sum_comm

lemma Q_expand (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (c : ℕ → ℂ) :
    (Q A (D c L U) : ℂ) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      c n * (starRingEnd ℂ) (c m) * ((g A n m : ℝ) : ℂ) := by
  have hterm : ∀ x y : ℝ, ((‖D c L U (x - y)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      c n * (starRingEnd ℂ) (c m) * (e n x * (starRingEnd ℂ) (e m x)) *
        ((starRingEnd ℂ) (e n y) * e m y) := by
    intro x y
    push_cast
    rw [← Complex.mul_conj']
    unfold D
    rw [Finset.sum_congr rfl fun n hn => by
      rw [cpow_sub_eq n (le_trans hL (Finset.mem_Icc.mp hn).1) x y], map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  unfold Q
  simp only [Complex.ofReal_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y, swap4]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  unfold g
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold G
  rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

lemma Q_real (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (r : ℕ → ℝ) :
    Q A (D (fun n => ((r n : ℝ) : ℂ)) L U) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      r n * r m * g A n m := by
  have h := Q_expand A L U hL (fun n => ((r n : ℝ) : ℂ))
  simp only [Complex.conj_ofReal] at h
  exact_mod_cast h

theorem majorant (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (a : ℕ → ℂ) (b : ℕ → ℝ)
    (h : ∀ n ∈ Finset.Icc L U, ‖a n‖ ≤ b n) :
    Q A (D a L U) ≤ Q A (D (fun n => ((b n : ℝ) : ℂ)) L U) := by
  rw [Q_real A L U hL b]
  have h1 : Q A (D a L U) = (Q A (D a L U) : ℂ).re := by simp
  rw [h1, Q_expand A L U hL a]
  calc _ ≤ ‖∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
        a n * (starRingEnd ℂ) (a m) * ((g A n m : ℝ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U, ‖a n‖ * ‖a m‖ * g A n m := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (g_nonneg _ _ _)]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
        have := h n hn
        exact mul_le_mul_of_nonneg_right (mul_le_mul (h n hn) (h m hm) (norm_nonneg _)
          (by linarith [norm_nonneg (a n)])) (g_nonneg _ _ _)

end
end GuthMaynard.CitedLV.HB.PartM
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part M -/
alias majorant := GuthMaynard.CitedLV.HB.PartM.majorant

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartM
open GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Completion -/

end
end GuthMaynard.CitedLV.HB.PartM
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartC
noncomputable section
/-!
# Heath-Brown large values, Part C: `card_divisors_le` and `mono`

* `card_divisors_le`: the divisor bound `τ(n) ≤ C_ε n^ε` (multiplicativity: each prime power
  contributes `(k+1)/p^{kε}`, which is `≤ 1` once `p^ε ≥ 2`).
* `mono` (Kerr Lemma 20 / Corollary 21): `S(N) ≤ C M^ε S(M)` for `M ≥ 64N`. Cut `[N, 2N]` into two
  blocks `[a, b]` with `2b ≤ 3a`. For one block put `U = ⌊M/a⌋ + 1`, `L = ⌊U/8⌋`, `K = L + 1`, and
  average `|D(t) E_ψ(t)|²` over the additive characters `ψ` of `ZMod K`, where
  `E_ψ(t) = ∑_{U ≤ u ≤ U+L} ψ(u) u^{-1/2} u^{it}`. Orthogonality gives
  `∑_ψ |E_ψ(t)|² = K ∑_u 1/u ≥ K/9`; each `D E_ψ` is a Dirichlet polynomial over `[M, 2M]` with
  coefficients bounded by `τ(m) m^{-1/2}`, so `majorant` bounds it by `τmax² S(M)`.
-/
/-! ### The divisor bound -/
/-- `k + 1 ≤ C (p^k)^ε` for all `p ≥ 2`. -/
lemma add_one_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ, ((k : ℝ) + 1) ≤ C * (((p ^ k : ℕ) : ℝ)) ^ ε := by
  set c := ε * Real.log 2 with hc
  have hc0 : 0 < c := mul_pos hε (Real.log_pos (by norm_num))
  refine ⟨max 1 (1 / c), le_max_left _ _, fun p hp k => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h1 : 1 + k * c ≤ (((p ^ k : ℕ) : ℝ)) ^ ε := by
    have e1 : (((p ^ k : ℕ) : ℝ)) ^ ε = Real.exp (k * ε * Real.log p) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      rw [Real.log_pow]; ring_nf
    rw [e1]
    have h2 : k * c ≤ k * ε * Real.log p := by
      rw [hc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hp)
    linarith [Real.add_one_le_exp (k * ε * Real.log p)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases le_total c 1 with hc1 | hc1
  · have : max 1 (1 / c) = 1 / c := max_eq_right (by rw [le_div_iff₀ hc0]; linarith)
    rw [this]
    calc (k : ℝ) + 1 ≤ (1 / c) * (1 + k * c) := by
          have e : (1 / c) * (1 + k * c) = 1 / c + k := by field_simp
          rw [e]
          have : 1 ≤ 1 / c := by rw [le_div_iff₀ hc0]; linarith
          linarith
      _ ≤ (1 / c) * (((p ^ k : ℕ) : ℝ)) ^ ε := mul_le_mul_of_nonneg_left h1 (by positivity)
  · have : max 1 (1 / c) = 1 := max_eq_left (by rw [div_le_iff₀ hc0]; linarith)
    rw [this, one_mul]
    have : (k : ℝ) ≤ k * c := le_mul_of_one_le_right hk0 hc1
    linarith

/-- The divisor bound `τ(n) ≤ C n^ε`. -/
theorem tau_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  obtain ⟨C₀, hC₀1, hC₀⟩ := add_one_le_rpow ε hε
  set N := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ + 1 with hN
  set Ssmall := (Finset.range N).filter (fun p : ℕ => ¬ (2 ≤ (p : ℝ) ^ ε)) with hS
  refine ⟨C₀ ^ Ssmall.card, by positivity, fun n hn => ?_⟩
  have hmemS : ∀ p : ℕ, 2 ≤ p → ¬ (2 ≤ (p : ℝ) ^ ε) → p ∈ Ssmall := by
    intro p hp2 hlt
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hlt' : (p : ℝ) ^ ε < 2 := lt_of_not_ge hlt
    have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
      rw [← Real.rpow_mul hp0, mul_one_div, div_self hε.ne', Real.rpow_one]
    have h2 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_lt_rpow (by positivity) hlt' (by positivity)
    rw [h1] at h2
    have h3 : (p : ℝ) < (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℝ) := lt_of_lt_of_le h2 (Nat.le_ceil _)
    have h4 : p < N := by
      have : p < ⌈(2 : ℝ) ^ (1 / ε)⌉₊ := by exact_mod_cast h3
      omega
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨h4, hlt⟩
  rw [Nat.card_divisors hn]
  push_cast
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (if p ∈ Ssmall then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpp.two_le
    by_cases hsm : 2 ≤ (p : ℝ) ^ ε
    · have hnot : p ∉ Ssmall := by simp [hS, hsm]
      rw [if_neg hnot, one_mul]
      set k := n.factorization p
      have hpk : (((p ^ k : ℕ)) : ℝ) ^ ε = ((p : ℝ) ^ ε) ^ k := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
          Real.rpow_mul (by positivity), Real.rpow_natCast]
      rw [hpk]
      have h2k : (k : ℝ) + 1 ≤ 2 ^ k := by
        have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
        exact_mod_cast this
      exact h2k.trans (pow_le_pow_left₀ (by norm_num) hsm k)
    · rw [if_pos (hmemS p hp2 hsm)]
      exact hC₀ p hp2 _
  have hconst : (∏ p ∈ n.primeFactors, (if p ∈ Ssmall then C₀ else 1)) ≤ C₀ ^ Ssmall.card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ hC₀1 ?_
    exact Finset.card_le_card fun x hx => (Finset.mem_filter.1 hx).2
  have hprod_n : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_prod]
    exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn).symm
  have hrpow : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε, hprod_n]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p ∈ Ssmall then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p ∈ Ssmall then C₀ else 1)) *
          (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_mul_distrib
    _ ≤ C₀ ^ Ssmall.card * (n : ℝ) ^ ε := by
        rw [hrpow]; exact mul_le_mul_of_nonneg_right hconst (by positivity)

theorem card_divisors_le : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := tau_le_rpow ε hε
  exact ⟨C, hC, fun n hn => h n (by omega)⟩

end
end GuthMaynard.CitedLV.HB.PartC
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part C -/
alias card_divisors_le := GuthMaynard.CitedLV.HB.PartC.card_divisors_le

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartC
noncomputable section
/-! ### Elementary facts -/

/-! ### The character sums -/

/-! ### The product polynomial -/

/-! ### One block -/

/-! ### `mono` -/

end
end GuthMaynard.CitedLV.HB.PartC
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
theorem mono : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    64 * N ≤ M → S A N ≤ C * (M : ℝ) ^ ε * S A M :=
  GuthMaynard.kerr_double_sum_mono

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartQ
noncomputable section
/-!
# Heath-Brown large values, Part Q: `square` and `mvt_bound`

* `square` (Kerr Lemma 22): Cauchy–Schwarz over the `R²` pairs gives `S(N)² ≤ R² ∑|D(x-y)|⁴`;
  `D² = ∑_{N² ≤ m ≤ 4N²} c_m m^{iu}` with `|c_m| ≤ τ(m) m^{-1/2}`, so `majorant` bounds the
  fourth moment by `τmax² Q A (D w N² 4N²) ≤ 2τmax² (S(N²) + S(2N²))`, and `mono` finishes.
* `mvt_bound`: for each `x`, translate `A` into `[0, T]` and apply the discrete mean value
  theorem `GuthMaynard.CitedLV.MVT.disc_mvt` with coefficients `n^{-1/2} n^{i(x - b)}`.
-/
/-! ### Elementary facts -/
/-- `u^{-1/2}`. -/
def r (u : ℕ) : ℝ := (u : ℝ) ^ (-(1 / 2 : ℝ))

lemma r_nonneg (u : ℕ) : 0 ≤ r u := Real.rpow_nonneg (Nat.cast_nonneg u) _

lemma r_sq (u : ℕ) : r u ^ 2 = 1 / (u : ℝ) := by
  have h0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  unfold r
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num
  rw [Real.rpow_neg_one, inv_eq_one_div]

lemma r_mul (n u : ℕ) : r n * r u = r (n * u) := by
  unfold r; push_cast; rw [Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg u)]

lemma w_eq (n : ℕ) : w n = ((r n : ℝ) : ℂ) := rfl

lemma norm_w (n : ℕ) : ‖w n‖ = r n := by
  rw [w_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (r_nonneg _)]

lemma norm_cpow_I {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp

lemma Q_nonneg (A : Finset ℝ) (F : ℝ → ℂ) : 0 ≤ Q A F := by
  unfold Q; positivity

lemma S_nonneg (A : Finset ℝ) (N : ℕ) : 0 ≤ S A N := Q_nonneg _ _

lemma Q_smul (A : Finset ℝ) (F : ℝ → ℂ) (z : ℂ) :
    Q A (fun t => z * F t) = ‖z‖ ^ 2 * Q A F := by
  unfold Q; simp [mul_pow, Finset.mul_sum]

lemma Q_add_le (A : Finset ℝ) (F G : ℝ → ℂ) :
    Q A (fun t => F t + G t) ≤ 2 * Q A F + 2 * Q A G := by
  unfold Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := norm_add_le (F (x - y)) (G (x - y))
  have h0 : 0 ≤ ‖F (x - y) + G (x - y)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖F (x - y)‖ - ‖G (x - y)‖), norm_nonneg (F (x - y)),
    norm_nonneg (G (x - y))]

/-! ### Cauchy–Schwarz over pairs -/
lemma sq_double_sum_le (A : Finset ℝ) (f : ℝ → ℝ → ℝ) :
    (∑ x ∈ A, ∑ y ∈ A, f x y) ^ 2 ≤ (A.card : ℝ) ^ 2 * ∑ x ∈ A, ∑ y ∈ A, f x y ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := A ×ˢ A) (f := fun p : ℝ × ℝ => f p.1 p.2)
  rw [Finset.sum_product, Finset.sum_product, Finset.card_product] at h
  push_cast at h
  rw [sq (A.card : ℝ)]
  exact h

lemma S_sq_le (A : Finset ℝ) (N : ℕ) :
    S A N ^ 2 ≤ (A.card : ℝ) ^ 2 * Q A (fun u => D w N (2 * N) u ^ 2) := by
  have h := sq_double_sum_le A (fun x y => ‖D w N (2 * N) (x - y)‖ ^ 2)
  unfold S Q
  refine le_trans h (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [norm_pow]

/-! ### The square of `D` as a Dirichlet polynomial -/
/-- `c(m) = ∑_{n₁ n₂ = m, N ≤ nᵢ ≤ 2N} w(n₁) w(n₂)`. -/
def c (N : ℕ) (m : ℕ) : ℂ :=
  ∑ p ∈ (Icc N (2 * N) ×ˢ Icc N (2 * N)).filter (fun p : ℕ × ℕ => p.1 * p.2 = m), w p.1 * w p.2

lemma D_sq (N : ℕ) (u : ℝ) : D w N (2 * N) u ^ 2 = D (c N) (N ^ 2) (4 * N ^ 2) u := by
  have lhs : D w N (2 * N) u ^ 2 = ∑ p ∈ Icc N (2 * N) ×ˢ Icc N (2 * N),
      w p.1 * w p.2 * ((p.1 * p.2 : ℕ) : ℂ) ^ ((u : ℂ) * I) := by
    unfold D
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring
  have hmap : ∀ p ∈ Icc N (2 * N) ×ˢ Icc N (2 * N),
      (fun p : ℕ × ℕ => p.1 * p.2) p ∈ Icc (N ^ 2) (4 * N ^ 2) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    constructor
    · rw [sq]; exact Nat.mul_le_mul hp.1.1 hp.2.1
    · calc p.1 * p.2 ≤ (2 * N) * (2 * N) := Nat.mul_le_mul hp.1.2 hp.2.2
        _ = 4 * N ^ 2 := by ring
  rw [lhs, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold D c
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]

lemma norm_c_le (N : ℕ) (hN : 1 ≤ N) (m : ℕ) (T : ℝ) (hT : (m.divisors.card : ℝ) ≤ T) :
    ‖c N m‖ ≤ T * r m := by
  classical
  unfold c
  set F := (Icc N (2 * N) ×ˢ Icc N (2 * N)).filter (fun p : ℕ × ℕ => p.1 * p.2 = m) with hF
  have hterm : ∀ p ∈ F, ‖w p.1 * w p.2‖ = r m := by
    intro p hp
    have hpm : p.1 * p.2 = m := (Finset.mem_filter.1 hp).2
    rw [norm_mul, norm_w, norm_w, ← hpm]
    exact r_mul p.1 p.2
  have hcard : F.card ≤ m.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
    · intro p hp
      have hp' := Finset.mem_filter.1 hp
      have hp1 : N ≤ p.1 := (Finset.mem_Icc.1 (Finset.mem_product.1 hp'.1).1).1
      have hp2 : N ≤ p.2 := (Finset.mem_Icc.1 (Finset.mem_product.1 hp'.1).2).1
      simp only [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨⟨p.2, hp'.2.symm⟩, ?_⟩
      rw [← hp'.2]; exact Nat.mul_ne_zero (by omega) (by omega)
    · intro p hp q hq hpq
      have hp' := Finset.mem_filter.1 hp
      have hq' := Finset.mem_filter.1 hq
      have hp1 : N ≤ p.1 := (Finset.mem_Icc.1 (Finset.mem_product.1 hp'.1).1).1
      simp only at hpq
      have h2 : p.2 = q.2 := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < p.1 by omega)
        rw [hp'.2, hpq, hq'.2]
      exact Prod.ext hpq h2
  calc ‖∑ p ∈ F, w p.1 * w p.2‖
      ≤ ∑ p ∈ F, ‖w p.1 * w p.2‖ := norm_sum_le _ _
    _ = ∑ p ∈ F, r m := Finset.sum_congr rfl hterm
    _ = F.card * r m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ T * r m := by
        apply mul_le_mul_of_nonneg_right _ (r_nonneg _)
        exact le_trans (by exact_mod_cast hcard) hT

lemma Q_D_c_le (A : Finset ℝ) (N : ℕ) (hN : 1 ≤ N) (T : ℝ)
    (hT : ∀ m ∈ Icc (N ^ 2) (4 * N ^ 2), (m.divisors.card : ℝ) ≤ T) :
    Q A (D (c N) (N ^ 2) (4 * N ^ 2)) ≤ T ^ 2 * Q A (D w (N ^ 2) (4 * N ^ 2)) := by
  have h := GuthMaynard.CitedLV.HB.majorant A (N ^ 2) (4 * N ^ 2) (Nat.one_le_pow _ _ hN)
    (c N) (fun m => T * r m) (fun m hm => norm_c_le N hN m T (hT m hm))
  have e : D (fun m => (((T * r m : ℝ)) : ℂ)) (N ^ 2) (4 * N ^ 2) =
      fun t => (T : ℂ) * D w (N ^ 2) (4 * N ^ 2) t := by
    funext t
    unfold D
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [w_eq]; push_cast; ring
  rw [e, Q_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-! ### Splitting `[N², 4N²]` -/
lemma Q_tail_le (A : Finset ℝ) (K U : ℕ) (hK : 1 ≤ K) :
    Q A (D w (K + 1) U) ≤ Q A (D w K U) := by
  classical
  set a : ℕ → ℂ := fun n => if K + 1 ≤ n then w n else 0 with ha
  have e : D w (K + 1) U = D a K U := by
    funext t
    unfold D
    have hs : Icc (K + 1) U = (Icc K U).filter (fun n => K + 1 ≤ n) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]
    split_ifs <;> simp
  rw [e]
  have h := GuthMaynard.CitedLV.HB.majorant A K U hK a (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (by
      intro n _
      simp only [ha]
      split_ifs
      · exact le_of_eq (norm_w n)
      · rw [norm_zero]; exact r_nonneg n)
  exact h

lemma Q_split (A : Finset ℝ) (L K U : ℕ) (h1 : L ≤ K + 1) (h2 : K ≤ U) :
    Q A (D w L U) ≤ 2 * Q A (D w L K) + 2 * Q A (D w (K + 1) U) := by
  have e : D w L U = fun t => D w L K t + D w (K + 1) U t := by
    funext t
    unfold D
    rw [← Finset.sum_union]
    · congr 1
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
  rw [e]
  exact Q_add_le A _ _

lemma Q_four_le (A : Finset ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Q A (D w (N ^ 2) (4 * N ^ 2)) ≤ 2 * S A (N ^ 2) + 2 * S A (2 * N ^ 2) := by
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have h1 := Q_split A (N ^ 2) (2 * N ^ 2) (4 * N ^ 2) (by omega) (by omega)
  have h2 := Q_tail_le A (2 * N ^ 2) (4 * N ^ 2) (by omega)
  have e : 4 * N ^ 2 = 2 * (2 * N ^ 2) := by ring
  unfold S
  rw [e] at h1 h2 ⊢
  linarith

/-! ### `square` -/
theorem square : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    256 * N ^ 2 ≤ M → S A N ^ 2 ≤ C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 * S A M := by
  intro ε hε
  obtain ⟨Cd, hCd, hτ⟩ := GuthMaynard.CitedLV.HB.card_divisors_le (ε / 4) (by linarith)
  obtain ⟨Cm, hCm, hmono⟩ := GuthMaynard.CitedLV.HB.mono (ε / 2) (by linarith)
  refine ⟨4 * Cd ^ 2 * Cm, by positivity, fun A N M hN hNM => ?_⟩
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  set T := Cd * (M : ℝ) ^ (ε / 4) with hTdef
  have hT : ∀ m ∈ Icc (N ^ 2) (4 * N ^ 2), (m.divisors.card : ℝ) ≤ T := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    refine le_trans (hτ m (by omega)) ?_
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow (Nat.cast_nonneg m) _ (by linarith)
    exact_mod_cast (show m ≤ M by omega)
  have hT2 : T ^ 2 = Cd ^ 2 * (M : ℝ) ^ (ε / 2) := by
    have e : ((M : ℝ) ^ (ε / 4)) ^ 2 = (M : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      ring_nf
    rw [hTdef, mul_pow, e]
  have hm1 := hmono A (N ^ 2) M hN2 (by omega)
  have hm2 := hmono A (2 * N ^ 2) M (by omega) (by omega)
  have hsq := S_sq_le A N
  have hDsq : (fun u => D w N (2 * N) u ^ 2) = D (c N) (N ^ 2) (4 * N ^ 2) := by
    funext u; exact D_sq N u
  rw [hDsq] at hsq
  have hc := Q_D_c_le A N hN T hT
  have h4 := Q_four_le A N hN
  have hMM : (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) = (M : ℝ) ^ ε := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hR : 0 ≤ (A.card : ℝ) ^ 2 := by positivity
  have hSM := S_nonneg A M
  have hP : 0 ≤ (M : ℝ) ^ (ε / 2) := by positivity
  have hQ4 : Q A (D w (N ^ 2) (4 * N ^ 2)) ≤ 4 * Cm * (M : ℝ) ^ (ε / 2) * S A M := by
    linarith
  calc S A N ^ 2 ≤ (A.card : ℝ) ^ 2 * (T ^ 2 * Q A (D w (N ^ 2) (4 * N ^ 2))) :=
        le_trans hsq (mul_le_mul_of_nonneg_left hc hR)
    _ ≤ (A.card : ℝ) ^ 2 * (T ^ 2 * (4 * Cm * (M : ℝ) ^ (ε / 2) * S A M)) := by
        apply mul_le_mul_of_nonneg_left _ hR
        exact mul_le_mul_of_nonneg_left hQ4 (sq_nonneg _)
    _ = 4 * Cd ^ 2 * Cm * ((M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2)) * (A.card : ℝ) ^ 2 * S A M := by
        rw [hT2]; ring
    _ = 4 * Cd ^ 2 * Cm * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 * S A M := by rw [hMM]

end
end GuthMaynard.CitedLV.HB.PartQ
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part Q -/
alias square := GuthMaynard.CitedLV.HB.PartQ.square

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartQ
noncomputable section
/-! ### `mvt_bound` -/
lemma sum_inv_le (M : ℕ) (hM : 1 ≤ M) : ∑ n ∈ Icc M (2 * M), r n ^ 2 ≤ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ∀ n ∈ Icc M (2 * M), r n ^ 2 ≤ 1 / (M : ℝ) := by
    intro n hn
    rw [r_sq]
    have hn' := (Finset.mem_Icc.1 hn).1
    apply one_div_le_one_div_of_le hM0
    exact_mod_cast hn'
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  rw [Nat.card_Icc, nsmul_eq_mul] at h2
  refine le_trans h2 ?_
  have e : ((2 * M + 1 - M : ℕ) : ℝ) = M + 1 := by
    rw [show 2 * M + 1 - M = M + 1 by omega]; push_cast; ring
  rw [e, mul_one_div, div_le_iff₀ hM0]
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

lemma row_bound (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hmv : ∀ (N : ℕ), 1 ≤ N → ∀ (s : Finset ℕ),
      s ⊆ Finset.Icc N (2 * N) → ∀ (c : ℕ → ℂ) (W : Finset ℝ) (T : ℝ), 0 ≤ T →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) → (∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T) →
      ∑ t ∈ W, ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        3 * (T + 1 + C₁ * N) * ∑ n ∈ s, ‖c n‖ ^ 2)
    (A : Finset ℝ) (T : ℝ) (M : ℕ) (hsep : IsSeparated 1 A)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) (hT : 0 ≤ T) (hM : 1 ≤ M) (x : ℝ) (hx : x ∈ A) :
    ∑ y ∈ A, ‖D w M (2 * M) (x - y)‖ ^ 2 ≤ 6 * (T + 1 + C₁ * M) := by
  set b := A.max' ⟨x, hx⟩ with hb
  have hbA : b ∈ A := A.max'_mem _
  set W := A.image (fun y => b - y) with hW
  have hinj : Set.InjOn (fun y : ℝ => b - y) A := by
    intro y _ y' _ h; simp only at h; linarith
  set cc : ℕ → ℂ := fun n => w n * (n : ℂ) ^ (((x - b : ℝ) : ℂ) * I) with hcc
  have hrow : ∀ y ∈ A, D w M (2 * M) (x - y) =
      ∑ n ∈ Icc M (2 * M), cc n * (n : ℂ) ^ (((b - y : ℝ) : ℂ) * I) := by
    intro y _
    unfold D
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    have e : (((x - y : ℝ) : ℂ) * I) = (((x - b : ℝ) : ℂ) * I) + (((b - y : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [hcc, e, Complex.cpow_add _ _ hn0]
    ring
  have hsum : ∑ y ∈ A, ‖D w M (2 * M) (x - y)‖ ^ 2 =
      ∑ t ∈ W, ‖∑ n ∈ Icc M (2 * M), cc n * (n : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 := by
    rw [hW, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun y hy => by rw [hrow y hy]
  have hsepW : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'| := by
    intro t ht t' ht' hne
    rw [hW, Finset.mem_image] at ht ht'
    obtain ⟨y, hy, rfl⟩ := ht
    obtain ⟨y', hy', rfl⟩ := ht'
    have hyy : y' ≠ y := by intro h; apply hne; rw [h]
    have := hsep y' hy' y hy hyy
    rw [show b - y - (b - y') = y' - y by ring]
    exact this
  have hWT : ∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [hW, Finset.mem_image] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    have h1 : y ≤ b := A.le_max' y hy
    have h2 := hdiam b hbA y hy
    rw [abs_of_nonneg (by linarith)] at h2
    exact ⟨by linarith, h2⟩
  have hmain := hmv M hM (Icc M (2 * M)) subset_rfl cc W T hT hsepW hWT
  have hcn : ∑ n ∈ Icc M (2 * M), ‖cc n‖ ^ 2 = ∑ n ∈ Icc M (2 * M), r n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have := (Finset.mem_Icc.1 hn).1
    rw [hcc, norm_mul, norm_w, norm_cpow_I (by omega), mul_one]
  rw [hcn] at hmain
  have h2 := sum_inv_le M hM
  have hpos : 0 ≤ 3 * (T + 1 + C₁ * M) := by positivity
  rw [hsum]
  calc _ ≤ _ := hmain
    _ ≤ 3 * (T + 1 + C₁ * M) * 2 := mul_le_mul_of_nonneg_left h2 hpos
    _ = 6 * (T + 1 + C₁ * M) := by ring

theorem mvt_bound : ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (M : ℕ), IsSeparated 1 A →
    (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 0 ≤ T → 1 ≤ M →
    S A M ≤ C * A.card * (T + M + 1) := by
  obtain ⟨C₁, hC₁, hmv⟩ := GuthMaynard.CitedLV.MVT.disc_mvt
  refine ⟨6 * (1 + C₁), by positivity, fun A T M hsep hdiam hT hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hrow : ∀ x ∈ A, ∑ y ∈ A, ‖D w M (2 * M) (x - y)‖ ^ 2 ≤ 6 * (1 + C₁) * (T + M + 1) := by
    intro x hx
    refine le_trans (row_bound C₁ hC₁ hmv A T M hsep hdiam hT hM x hx) ?_
    nlinarith
  have h := Finset.sum_le_card_nsmul _ _ _ hrow
  rw [nsmul_eq_mul] at h
  unfold S Q
  calc _ ≤ _ := h
    _ = _ := by ring

end
end GuthMaynard.CitedLV.HB.PartQ
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
alias mvt_bound := GuthMaynard.CitedLV.HB.PartQ.mvt_bound

/-! ## Part P -/

/-! ## Part D -/
theorem dual : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N M : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N → (N : ℝ) ≤ T →
    64 * (T / N + 1) ≤ M → (M : ℝ) ≤ 200 * T ^ 2 →
    S A N ≤ C * T ^ ε * (S A M + (A.card : ℝ) ^ 2 + N * A.card) :=
  GuthMaynard.kerr_double_sum_le_dual

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartT
noncomputable section
/-!
# Heath-Brown large values, Part T: `thm16` and `heath_brown_large_values`

Kerr's Theorem 16 for `γ = 1_A` from the Blueprint stubs `dual`, `square`, `mono`, `mvt_bound`:

* `case1`: if `X³ ≥ 3·10⁸ T²` then `S(X) ≪ T^ε (R² + XR)` (`dual` at `M₁ = ⌈64(T/X+1)⌉`, `square`
  at `M₂ = 256 M₁²`, `mono` from `M₂` up to `X`, then absorb `s ≤ a√s + b`; `mvt_bound` if `X > T`).
* `bound47`: for every `N`, `S(N) ≪ T^ε (R² + NR + (T/N) R^{3/2} + T^{1/2} R^{5/4})`
  (`dual`, `square`, `mono` up to `Y = max(64 M₂, ⌈700 T^{2/3}⌉)`, `case1` at `Y`).
* `thm16`: Kerr's U-trick: `mono` from `N` up to `X = max(64N, ⌈T^{1/2} R^{1/4}⌉)` and `bound47` at `X`.
* `heath_brown_large_values`: `majorant` with `|a_n| ≤ T^δ (2N)^{1/2} n^{-1/2}` and `thm16`.

The real-arithmetic steps are isolated in standalone lemmas; `R^{1/4} = u`, `T^{1/6} = v` turn the
fractional powers into polynomials.
-/
/-! ### Elementary facts -/
lemma Q_nonneg (A : Finset ℝ) (F : ℝ → ℂ) : 0 ≤ Q A F := by
  unfold Q; positivity

lemma S_nonneg (A : Finset ℝ) (N : ℕ) : 0 ≤ S A N := Q_nonneg _ _

/-- A `1`-separated set of diameter `≤ T` has at most `T + 1` points. -/
lemma card_le (A : Finset ℝ) (T : ℝ) (hsep : IsSeparated 1 A)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) (hT : 0 ≤ T) : (A.card : ℝ) ≤ T + 1 := by
  rcases A.eq_empty_or_nonempty with h | hne
  · simp [h]; linarith
  set a0 := A.min' hne with ha0
  have hinj : Set.InjOn (fun x => ⌊x - a0⌋₊) A := by
    intro x hx y hy hxy
    by_contra hne'
    have h1 := hsep x hx y hy hne'
    have hx0 : 0 ≤ x - a0 := sub_nonneg.2 (A.min'_le x hx)
    have hy0 : 0 ≤ y - a0 := sub_nonneg.2 (A.min'_le y hy)
    simp only at hxy
    have a1 := Nat.floor_le hx0
    have a2 := Nat.lt_floor_add_one (x - a0)
    have a3 := Nat.floor_le hy0
    have a4 := Nat.lt_floor_add_one (y - a0)
    rw [hxy] at a1 a2
    have : |x - y| < 1 := by rw [abs_sub_lt_iff]; constructor <;> linarith
    linarith
  have hsub : A.image (fun x => ⌊x - a0⌋₊) ⊆ Finset.range (⌊T⌋₊ + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [Finset.mem_range]
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    have := hdiam x hx a0 (A.min'_mem hne)
    exact le_trans (le_abs_self _) this
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h
  have h' : (A.card : ℝ) ≤ ⌊T⌋₊ + 1 := by exact_mod_cast h
  have := Nat.floor_le hT
  linarith

/-! ### Real-arithmetic lemmas -/
lemma sq_absorb (s a b : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : s ≤ a * Real.sqrt s + b) : s ≤ a ^ 2 + 2 * b := by
  have hr := Real.sq_sqrt hs
  have hr0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  nlinarith [sq_nonneg (a - Real.sqrt s)]

lemma le_of_sq_le_sq'' {p q : ℝ} (hq : 0 ≤ q) (h : p ^ 2 ≤ q ^ 2) : p ≤ q := by
  nlinarith

lemma absorb1 (s p τ R B Cd K : ℝ) (hs : 0 ≤ s) (hτ : 1 ≤ τ) (hR : 0 ≤ R)
    (hRB : R ^ 2 ≤ B) (hCd : 0 < Cd) (hK : 0 < K)
    (h1 : p ^ 2 ≤ K * τ ^ 2 * R ^ 2 * s) (h2 : s ≤ Cd * τ * (p + B)) :
    s ≤ (Cd ^ 2 * K + 2 * Cd) * τ ^ 4 * B := by
  have hτ0 : 0 ≤ τ := by linarith
  have hB : 0 ≤ B := le_trans (sq_nonneg R) hRB
  have hsK := Real.sq_sqrt hK.le
  have hss := Real.sq_sqrt hs
  have hpq : p ≤ Real.sqrt K * τ * R * Real.sqrt s := by
    apply le_of_sq_le_sq'' (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hsK, hss]
    exact h1
  have h3 : s ≤ (Cd * Real.sqrt K * τ ^ 2 * R) * Real.sqrt s + Cd * τ * B := by
    have hCt : 0 ≤ Cd * τ := by positivity
    calc s ≤ Cd * τ * (p + B) := h2
      _ ≤ Cd * τ * (Real.sqrt K * τ * R * Real.sqrt s + B) := by
          apply mul_le_mul_of_nonneg_left _ hCt; linarith
      _ = _ := by ring
  have h4 := sq_absorb s (Cd * Real.sqrt K * τ ^ 2 * R) (Cd * τ * B) hs (by positivity)
    (by positivity) h3
  have e : (Cd * Real.sqrt K * τ ^ 2 * R) ^ 2 = Cd ^ 2 * K * τ ^ 4 * R ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hsK]; ring
  rw [e] at h4
  have hτ4 : τ ≤ τ ^ 4 := le_self_pow₀ hτ (by norm_num)
  have h5 : Cd ^ 2 * K * τ ^ 4 * R ^ 2 ≤ Cd ^ 2 * K * τ ^ 4 * B :=
    mul_le_mul_of_nonneg_left hRB (by positivity)
  have h6 : Cd * τ * B ≤ Cd * τ ^ 4 * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    exact mul_le_mul_of_nonneg_left hτ4 hCd.le
  nlinarith

lemma absorb2 (S0 p τ G B K Cd : ℝ) (hτ : 1 ≤ τ) (hG : 0 ≤ G) (hBG : B ≤ G)
    (hK : 1 ≤ K) (hCd : 0 < Cd)
    (h1 : p ^ 2 ≤ K * τ ^ 8 * G ^ 2) (h2 : S0 ≤ Cd * τ * (p + B)) :
    S0 ≤ Cd * (K + 1) * τ ^ 5 * G := by
  have hτ0 : 0 ≤ τ := by linarith
  have hp : p ≤ K * τ ^ 4 * G := by
    apply le_of_sq_le_sq'' (by positivity)
    have : K * τ ^ 8 * G ^ 2 ≤ (K * τ ^ 4 * G) ^ 2 := by
      have e : (K * τ ^ 4 * G) ^ 2 = K * (K * τ ^ 8 * G ^ 2) := by ring
      rw [e]
      have : 0 ≤ K * τ ^ 8 * G ^ 2 := by positivity
      nlinarith
    linarith
  have hτ4 : 1 ≤ τ ^ 4 := one_le_pow₀ hτ
  have hG4 : G ≤ τ ^ 4 * G := by nlinarith
  have hCt : 0 ≤ Cd * τ := by positivity
  calc S0 ≤ Cd * τ * (p + B) := h2
    _ ≤ Cd * τ * (K * τ ^ 4 * G + τ ^ 4 * G) := by
        apply mul_le_mul_of_nonneg_left _ hCt; linarith
    _ = _ := by ring

lemma M1_facts (T x : ℝ) (hT : 1 ≤ T) (hx1 : 1 ≤ x) (hxT : x ≤ T) :
    64 * (T / x + 1) ≤ (⌈64 * (T / x + 1)⌉₊ : ℝ) ∧ (⌈64 * (T / x + 1)⌉₊ : ℝ) * x ≤ 129 * T ∧
    1 ≤ ⌈64 * (T / x + 1)⌉₊ ∧ (⌈64 * (T / x + 1)⌉₊ : ℝ) ≤ 200 * T ^ 2 := by
  set m := ⌈64 * (T / x + 1)⌉₊ with hm
  have hx0 : 0 < x := by linarith
  have hTx : 1 ≤ T / x := (one_le_div hx0).2 hxT
  have h1 : 64 * (T / x + 1) ≤ (m : ℝ) := Nat.le_ceil _
  have h2 : (m : ℝ) < 64 * (T / x + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : (m : ℝ) * x ≤ 129 * T := by
    have : (m : ℝ) ≤ 129 * (T / x) := by linarith
    calc (m : ℝ) * x ≤ 129 * (T / x) * x := mul_le_mul_of_nonneg_right this hx0.le
      _ = 129 * T := by field_simp
  refine ⟨h1, h3, ?_, ?_⟩
  · have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  · have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (m : ℝ) ≤ (m : ℝ) * x := by nlinarith
    nlinarith

lemma m2_le (m x T : ℝ) (hm : 0 ≤ m) (hx : 1 ≤ x) (hT : 0 ≤ T) (hmx : m * x ≤ 129 * T)
    (hX : 300000000 * T ^ 2 ≤ x ^ 3) : 16384 * m ^ 2 ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : (m * x) ^ 2 ≤ (129 * T) ^ 2 := pow_le_pow_left₀ (by positivity) hmx 2
  have h2 : 16384 * m ^ 2 * x ^ 2 ≤ x * x ^ 2 := by nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  exact le_of_mul_le_mul_right h2 hx2

lemma chain1 (p q s τ R Cs Cm a b : ℝ) (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hq : 0 ≤ q)
    (hs0 : 0 ≤ s) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (h1 : p ^ 2 ≤ Cs * a * R ^ 2 * q) (h2 : q ≤ Cm * b * s) (ha : a ≤ τ) (hb : b ≤ τ) :
    p ^ 2 ≤ (Cs * Cm) * τ ^ 2 * R ^ 2 * s := by
  have hτ : 0 ≤ τ := le_trans ha0 ha
  have h3 : q ≤ Cm * τ * s := le_trans h2 (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb hCm) hs0)
  have h4 : Cs * a * R ^ 2 * q ≤ Cs * τ * R ^ 2 * (Cm * τ * s) := by
    apply mul_le_mul _ h3 hq (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hCs) (sq_nonneg R)
  calc p ^ 2 ≤ _ := le_trans h1 h4
    _ = _ := by ring

lemma amgm0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : b ^ 2 * a ≤ a ^ 3 + b ^ 3 := by
  rcases le_total a b with h | h
  · have : b ^ 2 * a ≤ b ^ 2 * b := mul_le_mul_of_nonneg_left h (sq_nonneg b)
    nlinarith [pow_nonneg ha 3]
  · have : b ^ 2 * a ≤ a ^ 2 * a :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb h 2) ha
    nlinarith [pow_nonneg hb 3]

lemma amgm (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v ^ 4 * u ^ 12 ≤ u ^ 16 + v ^ 6 * u ^ 10 := by
  have key : v ^ 4 * u ^ 2 ≤ u ^ 6 + v ^ 6 := by
    calc v ^ 4 * u ^ 2 = (v ^ 2) ^ 2 * u ^ 2 := by ring
      _ ≤ (u ^ 2) ^ 3 + (v ^ 2) ^ 3 := amgm0 (u ^ 2) (v ^ 2) (by positivity) (by positivity)
      _ = _ := by ring
  have h10 : 0 ≤ u ^ 10 := by positivity
  have := mul_le_mul_of_nonneg_right key h10
  calc v ^ 4 * u ^ 12 = v ^ 4 * u ^ 2 * u ^ 10 := by ring
    _ ≤ (u ^ 6 + v ^ 6) * u ^ 10 := this
    _ = _ := by ring

lemma poly_Y (R Y G u v z m : ℝ) (hu : 0 ≤ u) (hv : 1 ≤ v) (hz : 0 ≤ z) (hm0 : 0 ≤ m)
    (hRu : R = u ^ 4) (hm : m ≤ 129 * z) (hY : Y ≤ 16384 * m ^ 2 + 700 * v ^ 4 + 1)
    (hG1 : R ^ 2 ≤ G) (hG2 : z * u ^ 6 ≤ G) (hG3 : R ^ 2 + v ^ 3 * u ^ 5 ≤ G) :
    R ^ 2 * (R ^ 2 + Y * R) ≤ 300000000 * G ^ 2 := by
  subst hRu
  have hv0 : 0 ≤ v := by linarith
  have hG0 : 0 ≤ G := le_trans (sq_nonneg _) hG1
  have h12 : 0 ≤ u ^ 12 := by positivity
  have a1 : Y * u ^ 12 ≤ (16384 * m ^ 2 + 700 * v ^ 4 + 1) * u ^ 12 :=
    mul_le_mul_of_nonneg_right hY h12
  have a2 : m ^ 2 ≤ (129 * z) ^ 2 := pow_le_pow_left₀ hm0 hm 2
  have a2' : m ^ 2 * u ^ 12 ≤ (129 * z) ^ 2 * u ^ 12 := mul_le_mul_of_nonneg_right a2 h12
  have a3 : (z * u ^ 6) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by positivity) hG2 2
  have a4 := amgm u v hu hv0
  have a5 : (u ^ 8 + v ^ 3 * u ^ 5) ^ 2 ≤ G ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    calc u ^ 8 + v ^ 3 * u ^ 5 = (u ^ 4) ^ 2 + v ^ 3 * u ^ 5 := by ring
      _ ≤ G := hG3
  have a6 : 0 ≤ v ^ 3 * u ^ 13 := by positivity
  have a7 : u ^ 12 ≤ v ^ 4 * u ^ 12 := by
    have : 1 ≤ v ^ 4 := one_le_pow₀ hv
    nlinarith
  have a8 : ((u ^ 4) ^ 2) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by positivity) hG1 2
  have e : (u ^ 4) ^ 2 * ((u ^ 4) ^ 2 + Y * u ^ 4) = ((u ^ 4) ^ 2) ^ 2 + Y * u ^ 12 := by ring
  rw [e]
  nlinarith

lemma poly_X (R X N T u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hRu : R = u ^ 4) (hTv : T = v ^ 6)
    (hR : R = 0 ∨ 1 ≤ R) (hN : 0 ≤ N) (hX0 : 0 < X)
    (hX1 : v ^ 3 * u ≤ X) (hX2 : X ≤ 64 * N + v ^ 3 * u + 1) :
    R ^ 2 + X * R + T / X * u ^ 6 + v ^ 3 * u ^ 5 ≤ 64 * (R ^ 2 + N * R + v ^ 3 * u ^ 5) := by
  have hR0 : 0 ≤ R := by rw [hRu]; positivity
  have hXR : X * R ≤ (64 * N + v ^ 3 * u + 1) * R := mul_le_mul_of_nonneg_right hX2 hR0
  have hRR : R ≤ R ^ 2 := by
    rcases hR with h | h
    · rw [h]; norm_num
    · nlinarith
  have hT : T / X * u ^ 6 ≤ v ^ 3 * u ^ 5 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hX0, hTv]
    have h5 : 0 ≤ v ^ 3 * u ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left hX1 h5
    calc v ^ 6 * u ^ 6 = v ^ 3 * u ^ 5 * (v ^ 3 * u) := by ring
      _ ≤ v ^ 3 * u ^ 5 * X := this
  have e : (64 * N + v ^ 3 * u + 1) * R = 64 * N * R + v ^ 3 * u ^ 5 + R := by
    rw [hRu]; ring
  have h5 : 0 ≤ v ^ 3 * u ^ 5 := by positivity
  have h6 : 0 ≤ N * R := by positivity
  nlinarith

lemma bound_mono (s K K' τ B B' : ℝ) (h : s ≤ K * B) (hKK' : K ≤ K') (hτ : 1 ≤ τ)
    (hBB' : B ≤ B') (hK : 0 ≤ K) (hB : 0 ≤ B) : s ≤ K' * τ * B' := by
  have hK' : 0 ≤ K' := le_trans hK hKK'
  have h1 : K * B ≤ K' * B' := mul_le_mul hKK' hBB' hB hK'
  have h2 : 0 ≤ K' * B' := mul_nonneg hK' (le_trans hB hBB')
  nlinarith

lemma rpow_le_const_mul (x K T e : ℝ) (k : ℕ) (hx : 0 ≤ x) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (he : 0 ≤ e) (h : x ≤ K * T ^ k) : x ^ e ≤ K ^ e * (T ^ e) ^ k := by
  calc x ^ e ≤ (K * T ^ k) ^ e := Real.rpow_le_rpow hx h he
    _ = K ^ e * (T ^ k) ^ e := Real.mul_rpow hK (by positivity)
    _ = K ^ e * (T ^ e) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hT, ← Real.rpow_mul hT,
          mul_comm (k : ℝ) e]

lemma mvt_case (C0 : ℝ) (hC0 : 0 < C0)
    (hmvt : ∀ (A : Finset ℝ) (T : ℝ) (M : ℕ), IsSeparated 1 A →
      (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 0 ≤ T → 1 ≤ M → S A M ≤ C0 * A.card * (T + M + 1))
    (A : Finset ℝ) (T : ℝ) (N : ℕ) (hsep : IsSeparated 1 A)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) (hT : 0 ≤ T) (hN : 1 ≤ N) (hNT : T < N) :
    S A N ≤ 3 * C0 * (N * A.card) := by
  have h := hmvt A T N hsep hdiam hT hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hR : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  calc S A N ≤ _ := h
    _ ≤ C0 * A.card * (3 * N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = _ := by ring

/-! ### Case 1 -/
lemma case1 (e : ℝ) (he : 0 < e) : ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (X : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ X →
    300000000 * T ^ 2 ≤ (X : ℝ) ^ 3 →
    S A X ≤ C * (T ^ e) ^ 4 * ((A.card : ℝ) ^ 2 + X * A.card) := by
  obtain ⟨C0, hC0, hmvt⟩ := GuthMaynard.CitedLV.HB.mvt_bound
  obtain ⟨Cd, hCd, hdual⟩ := GuthMaynard.CitedLV.HB.dual e he
  obtain ⟨Cs, hCs, hsq⟩ := GuthMaynard.CitedLV.HB.square e he
  obtain ⟨Cm, hCm, hmono⟩ := GuthMaynard.CitedLV.HB.mono e he
  refine ⟨3 * C0 + (Cd ^ 2 * (Cs * Cm) + 2 * Cd), by positivity,
    fun A T X hsep hdiam hT hX hX3 => ?_⟩
  have hR : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ : 1 ≤ T ^ e := Real.one_le_rpow (by linarith) he.le
  have hτ4 : 1 ≤ (T ^ e) ^ 4 := one_le_pow₀ hτ
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hB : 0 ≤ (A.card : ℝ) ^ 2 + X * A.card := by positivity
  by_cases hXT : (X : ℝ) ≤ T
  · obtain ⟨hm1, hmx, hm1', hm200⟩ := M1_facts T X (by linarith) hX1 hXT
    set m := ⌈64 * (T / X + 1)⌉₊ with hmdef
    have hm2 : 16384 * (m : ℝ) ^ 2 ≤ X := m2_le m X T (by positivity) hX1 hT0.le hmx hX3
    have hM2X : 64 * (256 * m ^ 2) ≤ X := by
      have : ((64 * (256 * m ^ 2) : ℕ) : ℝ) ≤ X := by push_cast; linarith
      exact_mod_cast this
    have hM2one : 1 ≤ 256 * m ^ 2 := by have := Nat.one_le_pow 2 m hm1'; omega
    have hd := hdual A T X m hsep hdiam hT hX hXT hm1 hm200
    have hs := hsq A m (256 * m ^ 2) hm1' le_rfl
    have hmo := hmono A (256 * m ^ 2) X hM2one hM2X
    have hM2T : ((256 * m ^ 2 : ℕ) : ℝ) ≤ T := by
      have : ((256 * m ^ 2 : ℕ) : ℝ) ≤ X := by exact_mod_cast (by omega : 256 * m ^ 2 ≤ X)
      linarith
    have he1 : ((256 * m ^ 2 : ℕ) : ℝ) ^ e ≤ T ^ e :=
      Real.rpow_le_rpow (by positivity) hM2T he.le
    have he2 : (X : ℝ) ^ e ≤ T ^ e := Real.rpow_le_rpow (by positivity) hXT he.le
    have hp := chain1 (S A m) (S A (256 * m ^ 2)) (S A X) (T ^ e) (A.card : ℝ) Cs Cm
      _ _ hCs.le hCm.le (S_nonneg _ _) (S_nonneg _ _) (by positivity) (by positivity) hs hmo he1 he2
    have hd' : S A X ≤ Cd * T ^ e * (S A m + ((A.card : ℝ) ^ 2 + X * A.card)) := by
      calc _ ≤ _ := hd
        _ = _ := by ring
    have h := absorb1 (S A X) (S A m) (T ^ e) (A.card : ℝ) ((A.card : ℝ) ^ 2 + X * A.card) Cd
      (Cs * Cm) (S_nonneg _ _) hτ hR (by nlinarith) hCd (by positivity) hp hd'
    have h' : S A X ≤ (Cd ^ 2 * (Cs * Cm) + 2 * Cd) * ((T ^ e) ^ 4 * ((A.card : ℝ) ^ 2 + X * A.card)) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    have := bound_mono _ _ (3 * C0 + (Cd ^ 2 * (Cs * Cm) + 2 * Cd)) 1 _ _ h'
      (by linarith) le_rfl le_rfl (by positivity) (by positivity)
    calc S A X ≤ _ := this
      _ = _ := by ring
  · push_neg at hXT
    have h := mvt_case C0 hC0 hmvt A T X hsep hdiam hT0.le hX hXT
    have h' : S A X ≤ 3 * C0 * ((A.card : ℝ) ^ 2 + X * A.card) := by
      refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : (0 : ℝ) ≤ (A.card : ℝ) ^ 2 := by positivity
      linarith
    exact bound_mono _ _ _ _ _ _ h'
      (by have : 0 ≤ Cd ^ 2 * (Cs * Cm) + 2 * Cd := by positivity
          linarith) hτ4 le_rfl (by positivity) hB

/-! ### The bound (47') -/
lemma chain2 (p q s τ R Y G Cs Cm C1 Kc a b : ℝ) (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm)
    (hC1 : 0 ≤ C1) (hKc : 0 ≤ Kc) (hτ : 0 ≤ τ) (hq : 0 ≤ q) (hs0 : 0 ≤ s) (hR : 0 ≤ R)
    (hY : 0 ≤ Y) (ha0 : 0 ≤ a)
    (h1 : p ^ 2 ≤ Cs * a * R ^ 2 * q) (ha : a ≤ Kc * τ ^ 2) (h2 : q ≤ Cm * b * s)
    (hb : b ≤ Kc * τ ^ 2) (h3 : s ≤ C1 * τ ^ 4 * (R ^ 2 + Y * R))
    (hpoly : R ^ 2 * (R ^ 2 + Y * R) ≤ 300000000 * G ^ 2) :
    p ^ 2 ≤ (Cs * Cm * C1 * Kc ^ 2 * 300000000) * τ ^ 8 * G ^ 2 := by
  have hB : 0 ≤ R ^ 2 + Y * R := by positivity
  have hq' : q ≤ Cm * (Kc * τ ^ 2) * (C1 * τ ^ 4 * (R ^ 2 + Y * R)) := by
    refine le_trans h2 (mul_le_mul (mul_le_mul_of_nonneg_left hb hCm) h3 hs0 (by positivity))
  have h4 : Cs * a * R ^ 2 * q ≤
      Cs * (Kc * τ ^ 2) * R ^ 2 * (Cm * (Kc * τ ^ 2) * (C1 * τ ^ 4 * (R ^ 2 + Y * R))) := by
    apply mul_le_mul _ hq' hq (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hCs) (sq_nonneg R)
  have e : Cs * (Kc * τ ^ 2) * R ^ 2 * (Cm * (Kc * τ ^ 2) * (C1 * τ ^ 4 * (R ^ 2 + Y * R))) =
      (Cs * Cm * C1 * Kc ^ 2 * τ ^ 8) * (R ^ 2 * (R ^ 2 + Y * R)) := by ring
  have h5 := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ Cs * Cm * C1 * Kc ^ 2 * τ ^ 8 by positivity)
  calc p ^ 2 ≤ _ := le_trans h1 h4
    _ = _ := e
    _ ≤ _ := h5
    _ = _ := by ring

lemma bound47 (e : ℝ) (he : 0 < e) : ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N →
    S A N ≤ C * (T ^ e) ^ 5 * ((A.card : ℝ) ^ 2 + N * A.card +
      T / N * (A.card : ℝ) ^ (3 / 2 : ℝ) + T ^ (1 / 2 : ℝ) * (A.card : ℝ) ^ (5 / 4 : ℝ)) := by
  obtain ⟨C0, hC0, hmvt⟩ := GuthMaynard.CitedLV.HB.mvt_bound
  obtain ⟨Cd, hCd, hdual⟩ := GuthMaynard.CitedLV.HB.dual e he
  obtain ⟨Cs, hCs, hsq⟩ := GuthMaynard.CitedLV.HB.square e he
  obtain ⟨Cm, hCm, hmono⟩ := GuthMaynard.CitedLV.HB.mono e he
  obtain ⟨C1, hC1, hcase1⟩ := case1 e he
  set Kc : ℝ := (300000000 : ℝ) ^ e with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set K : ℝ := max 1 (Cs * Cm * C1 * Kc ^ 2 * 300000000) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKmax : Cs * Cm * C1 * Kc ^ 2 * 300000000 ≤ K := le_max_right _ _
  clear_value K
  refine ⟨3 * C0 + Cd * (K + 1), by positivity, fun A T N hsep hdiam hT hN => ?_⟩
  set R : ℝ := (A.card : ℝ) with hRdef
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ : 1 ≤ T ^ e := Real.one_le_rpow (by linarith) he.le
  have hτ0 : 0 ≤ T ^ e := by linarith
  have hτ5 : 1 ≤ (T ^ e) ^ 5 := one_le_pow₀ hτ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u := R ^ (1 / 4 : ℝ) with hu
  set v := T ^ (1 / 6 : ℝ) with hv
  have hu0 : 0 ≤ u := by positivity
  have hv1 : 1 ≤ v := Real.one_le_rpow (by linarith) (by norm_num)
  have hu4 : u ^ 4 = R := by rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hu5 : u ^ 5 = R ^ (5 / 4 : ℝ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hu6 : u ^ 6 = R ^ (3 / 2 : ℝ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hv6 : v ^ 6 = T := by rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hv3 : v ^ 3 = T ^ (1 / 2 : ℝ) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  clear_value u v
  set G := R ^ 2 + N * R + T / N * R ^ (3 / 2 : ℝ) + T ^ (1 / 2 : ℝ) * R ^ (5 / 4 : ℝ) with hG
  have hz0 : 0 ≤ T / N := by positivity
  have hG1' : 0 ≤ T / N * R ^ (3 / 2 : ℝ) := by rw [← hu6]; positivity
  have hG2' : 0 ≤ T ^ (1 / 2 : ℝ) * R ^ (5 / 4 : ℝ) := by rw [← hu5, ← hv3]; positivity
  have hNR : 0 ≤ N * R := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hGa : R ^ 2 + N * R ≤ G := by rw [hG]; linarith
  have hGb : T / N * u ^ 6 ≤ G := by rw [hG, hu6]; nlinarith [sq_nonneg R]
  have hGc : R ^ 2 + v ^ 3 * u ^ 5 ≤ G := by rw [hG, hv3, hu5]; linarith
  have hGd : R ^ 2 ≤ G := by linarith
  clear_value G
  by_cases hNT : (N : ℝ) ≤ T
  · obtain ⟨hm1, hmx, hm1', hm200⟩ := M1_facts T N (by linarith) hN1 hNT
    set m := ⌈64 * (T / N + 1)⌉₊ with hmdef
    clear_value m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmz : (m : ℝ) ≤ 129 * (T / N) := by
      rw [mul_div_assoc', le_div_iff₀ (by linarith)]; exact hmx
    have hmT : (m : ℝ) ≤ 129 * T := by
      have : (m : ℝ) ≤ m * N := le_mul_of_one_le_right hm0 hN1
      linarith
    set M₂ := 256 * m ^ 2 with hM₂
    have hM2one : 1 ≤ M₂ := by have := Nat.one_le_pow 2 m hm1'; omega
    clear_value M₂
    set Y := max (64 * M₂) ⌈700 * v ^ 4⌉₊ with hYdef
    have hYM : 64 * M₂ ≤ Y := le_max_left _ _
    have hY1 : 1 ≤ Y := by omega
    have hYv : 700 * v ^ 4 ≤ (Y : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right (64 * M₂) _)
    clear_value Y
    have hY3 : 300000000 * T ^ 2 ≤ (Y : ℝ) ^ 3 := by
      have h1 : (700 * v ^ 4) ^ 3 ≤ (Y : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hYv 3
      have h2 : T ^ 2 = v ^ 12 := by rw [← hv6]; ring
      have h4 : (700 * v ^ 4) ^ 3 = 343000000 * v ^ 12 := by ring
      rw [h2]; linarith [pow_nonneg (show (0:ℝ) ≤ v by linarith) 12]
    have hYup : (Y : ℝ) ≤ 16384 * (m : ℝ) ^ 2 + 700 * v ^ 4 + 1 := by
      rw [hYdef, Nat.cast_max]
      apply max_le
      · rw [hM₂]; push_cast; linarith [sq_nonneg (m : ℝ), pow_nonneg (show (0 : ℝ) ≤ v by linarith) 4]
      · have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 700 * v ^ 4 by positivity)
        linarith [sq_nonneg (m : ℝ), pow_nonneg (show (0 : ℝ) ≤ v by linarith) 4]
    have hYT : (Y : ℝ) ≤ 300000000 * T ^ 2 := by
      have h1 : (m : ℝ) ^ 2 ≤ (129 * T) ^ 2 := pow_le_pow_left₀ hm0 hmT 2
      have h2 : v ^ 4 ≤ T ^ 2 := by
        rw [← hv6]
        have : v ^ 4 ≤ v ^ 12 := pow_le_pow_right₀ hv1 (by norm_num)
        calc v ^ 4 ≤ v ^ 12 := this
          _ = _ := by ring
      have h3 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
      linarith
    have hYe : (Y : ℝ) ^ e ≤ Kc * (T ^ e) ^ 2 := by
      rw [hKc]
      exact rpow_le_const_mul _ _ _ _ 2 (by positivity) (by norm_num) hT0.le he.le hYT
    have hM2e : ((M₂ : ℕ) : ℝ) ^ e ≤ Kc * (T ^ e) ^ 2 := by
      refine le_trans (Real.rpow_le_rpow (by positivity) ?_ he.le) hYe
      exact_mod_cast (by omega : M₂ ≤ Y)
    have hd := hdual A T N m hsep hdiam hT hN hNT hm1 hm200
    have hs := hsq A m M₂ hm1' (le_of_eq hM₂.symm)
    have hmo := hmono A M₂ Y hM2one hYM
    have hc1 := hcase1 A T Y hsep hdiam hT hY1 hY3
    have hpoly := poly_Y R Y G u v (T / N) m hu0 hv1 hz0 hm0 hu4.symm hmz hYup
      hGd hGb hGc
    have hp := chain2 (S A m) (S A M₂) (S A Y) (T ^ e) R Y G Cs Cm C1 Kc _ _ hCs.le hCm.le
      hC1.le hKc0 hτ0 (S_nonneg _ _) (S_nonneg _ _) hR (Nat.cast_nonneg _) (by positivity)
      hs hM2e hmo hYe hc1 hpoly
    have hp' : S A m ^ 2 ≤ K * (T ^ e) ^ 8 * G ^ 2 := by
      refine le_trans hp (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        hKmax (by positivity)) (sq_nonneg _))
    have hd' : S A N ≤ Cd * T ^ e * (S A m + (R ^ 2 + N * R)) := by
      calc _ ≤ _ := hd
        _ = _ := by ring
    have h := absorb2 (S A N) (S A m) (T ^ e) G (R ^ 2 + N * R) K Cd hτ hG0 hGa
      hK1 hCd hp' hd'
    have h' : S A N ≤ (Cd * (K + 1)) * ((T ^ e) ^ 5 * G) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    have := bound_mono _ _ (3 * C0 + Cd * (K + 1)) 1 _ _ h' (by linarith) le_rfl le_rfl
      (by positivity) (by positivity)
    calc S A N ≤ _ := this
      _ = _ := by ring
  · push_neg at hNT
    have h := mvt_case C0 hC0 hmvt A T N hsep hdiam hT0.le hN hNT
    have h' : S A N ≤ 3 * C0 * G := by
      refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : 0 ≤ R ^ 2 := by positivity
      linarith
    exact bound_mono _ _ _ _ _ _ h'
      (by have : 0 ≤ Cd * (K + 1) := by positivity
          linarith) hτ5 le_rfl (by positivity) hG0

/-! ### `thm16` -/
theorem thm16 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N →
    S A N ≤ C * T ^ ε * ((A.card : ℝ) ^ 2 + N * A.card +
      T ^ (1 / 2 : ℝ) * (A.card : ℝ) ^ (5 / 4 : ℝ)) := by
  intro ε hε
  set e := ε / 6 with he_def
  have he : 0 < e := by positivity
  obtain ⟨C0, hC0, hmvt⟩ := GuthMaynard.CitedLV.HB.mvt_bound
  obtain ⟨Cm, hCm, hmono⟩ := GuthMaynard.CitedLV.HB.mono e he
  obtain ⟨C2, hC2, h47⟩ := bound47 e he
  refine ⟨3 * C0 + Cm * (67 : ℝ) ^ e * C2 * 64, by positivity,
    fun A T N hsep hdiam hT hN => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ : 1 ≤ T ^ e := Real.one_le_rpow (by linarith) he.le
  have hτ0 : 0 ≤ T ^ e := by linarith
  have hτ6 : 1 ≤ (T ^ e) ^ 6 := one_le_pow₀ hτ
  have hTε : T ^ ε = (T ^ e) ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, he_def]; norm_num
  rw [hTε]
  set R : ℝ := (A.card : ℝ) with hRdef
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hR01 : R = 0 ∨ 1 ≤ R := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · left; rw [hRdef, h]; simp
    · right; rw [hRdef]; exact_mod_cast h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u := R ^ (1 / 4 : ℝ) with hu
  set v := T ^ (1 / 6 : ℝ) with hv
  have hu0 : 0 ≤ u := by positivity
  have hv1 : 1 ≤ v := Real.one_le_rpow (by linarith) (by norm_num)
  have hv0 : 0 ≤ v := by linarith
  have hu4 : u ^ 4 = R := by rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hu5 : u ^ 5 = R ^ (5 / 4 : ℝ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hu6 : u ^ 6 = R ^ (3 / 2 : ℝ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR]; norm_num
  have hv6 : v ^ 6 = T := by rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hv3 : v ^ 3 = T ^ (1 / 2 : ℝ) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  clear_value u v
  set Gf := R ^ 2 + N * R + T ^ (1 / 2 : ℝ) * R ^ (5 / 4 : ℝ) with hGf
  have hNR : 0 ≤ N * R := by positivity
  have hG2' : 0 ≤ T ^ (1 / 2 : ℝ) * R ^ (5 / 4 : ℝ) := by rw [← hu5, ← hv3]; positivity
  have hG0 : 0 ≤ Gf := by positivity
  have hGN : N * R ≤ Gf := by rw [hGf]; nlinarith [sq_nonneg R]
  clear_value Gf
  by_cases hNT : (N : ℝ) ≤ T
  · have hcard := card_le A T hsep hdiam hT0.le
    have huv : u ≤ 2 * v ^ 3 := by
      have h1 : u ^ 4 ≤ (2 * v ^ 3) ^ 4 := by
        rw [hu4]
        have : v ^ 6 ≤ v ^ 12 := pow_le_pow_right₀ hv1 (by norm_num)
        have e2 : (2 * v ^ 3) ^ 4 = 16 * v ^ 12 := by ring
        rw [e2]; nlinarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    have hvu : v ^ 3 * u ≤ 2 * T := by
      rw [← hv6]; nlinarith [pow_nonneg hv0 3]
    set X := max (64 * N) ⌈v ^ 3 * u⌉₊ with hXdef
    have hXN : 64 * N ≤ X := le_max_left _ _
    have hX1 : 1 ≤ X := by omega
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
    have hXlo : v ^ 3 * u ≤ (X : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right (64 * N) _)
    clear_value X
    have hXup : (X : ℝ) ≤ 64 * N + v ^ 3 * u + 1 := by
      rw [hXdef, Nat.cast_max]
      apply max_le
      · push_cast; linarith [pow_nonneg hv0 3, mul_nonneg (pow_nonneg hv0 3) hu0]
      · have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ v ^ 3 * u by positivity)
        linarith
    have hXT : (X : ℝ) ≤ 67 * T ^ 1 := by rw [pow_one]; linarith
    have hXe : (X : ℝ) ^ e ≤ (67 : ℝ) ^ e * (T ^ e) ^ 1 :=
      rpow_le_const_mul _ _ _ _ 1 (by positivity) (by norm_num) hT0.le he.le hXT
    rw [pow_one] at hXe
    have hmo := hmono A N X hN hXN
    have h4 := h47 A T X hsep hdiam hT hX1
    have hpoly := poly_X R X N T u v hu0 hv0 hu4.symm hv6.symm hR01 (by linarith) hX0 hXlo hXup
    rw [hu6, hv3, hu5, ← hGf] at hpoly
    have h5 : S A X ≤ C2 * (T ^ e) ^ 5 * (64 * Gf) :=
      le_trans h4 (mul_le_mul_of_nonneg_left hpoly (by positivity))
    have h6 : S A N ≤ (Cm * (67 : ℝ) ^ e * C2 * 64) * ((T ^ e) ^ 6 * Gf) := by
      calc S A N ≤ Cm * (X : ℝ) ^ e * S A X := hmo
        _ ≤ Cm * ((67 : ℝ) ^ e * T ^ e) * (C2 * (T ^ e) ^ 5 * (64 * Gf)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hXe hCm.le) h5 (S_nonneg _ _)
            positivity
        _ = _ := by ring
    have := bound_mono _ _ (3 * C0 + Cm * (67 : ℝ) ^ e * C2 * 64) 1 _ _ h6 (by linarith) le_rfl
      le_rfl (by positivity) (by positivity)
    calc S A N ≤ _ := this
      _ = _ := by ring
  · push_neg at hNT
    have h := mvt_case C0 hC0 hmvt A T N hsep hdiam hT0.le hN hNT
    have h' : S A N ≤ 3 * C0 * Gf := by
      refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : 0 ≤ R ^ 2 := by positivity
      linarith
    have := bound_mono _ _ (3 * C0 + Cm * (67 : ℝ) ^ e * C2 * 64) _ _ _ h'
      (by have : 0 ≤ Cm * (67 : ℝ) ^ e * C2 * 64 := by positivity
          linarith) hτ6 le_rfl (by positivity) hG0
    exact this

end
end GuthMaynard.CitedLV.HB.PartT
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part T -/
alias thm16 := GuthMaynard.CitedLV.HB.PartT.thm16

end
end GuthMaynard.CitedLV.HB
end


open GuthMaynard in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * T ^ ε * ((A.card : ℝ) ^ 2 + N * A.card + T ^ (1 / 2 : ℝ) * (A.card : ℝ) ^ (5 / 4 : ℝ)) :=
  GuthMaynard.CitedLV.HB.thm16
