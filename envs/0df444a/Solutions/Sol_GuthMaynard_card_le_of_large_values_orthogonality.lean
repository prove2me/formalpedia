-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T19:58:31.197768+00:00
-- url     : https://prove2.me/submissions/f31c6cd5-bed6-42da-940f-45ae522032c6

import Definitions.Def_GuthMaynard
import Mathlib

section
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
end

section
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
end

section
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
end

section
section
namespace GuthMaynard.S1

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

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

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

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard

open S1

theorem chk_card_le_of_large_values_orthogonality :
    ∃ C : ℝ, ∀ (σ : ℝ) (N : ℕ), 1 ≤ N → ∀ T : ℝ, (N : ℝ) ≤ T → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (W.card : ℝ) ≤ C * T * (N : ℝ) ^ (1 - 2 * σ) := by
  obtain ⟨C₁, hC₁, hmv⟩ := disc_mvt
  refine ⟨3 * (2 + C₁), ?_⟩
  intro σ N hN T hNT b hb W hsep hWT hlarge
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 ≤ T := hN0.le.trans hNT
  have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc N (2 * N) := Finset.Ioc_subset_Icc_self
  have h1 := hmv N hN _ hsub b W T hT0 hsep hWT
  have hcard : (∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤ N := by
    calc (∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤ ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro n _
          have := hb n
          have h0 := norm_nonneg (b n)
          nlinarith
      _ = N := by simp [Nat.card_Ioc]; omega
  have hlow : (W.card : ℝ) * ((N : ℝ) ^ σ) ^ 2 ≤
      ∑ t ∈ W, ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
    calc (W.card : ℝ) * ((N : ℝ) ^ σ) ^ 2 = ∑ t ∈ W, ((N : ℝ) ^ σ) ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum; intro t ht
        have := hlarge t ht
        have h0 : 0 ≤ (N : ℝ) ^ σ := by positivity
        nlinarith
  have hpow : ((N : ℝ) ^ σ) ^ 2 = (N : ℝ) ^ (2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hpos : 0 < (N : ℝ) ^ (2 * σ) := by positivity
  have hS0 : 0 ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfac : 0 ≤ 3 * (T + 1 + C₁ * N) := by positivity
  have h2 : (W.card : ℝ) * (N : ℝ) ^ (2 * σ) ≤ 3 * (T + 1 + C₁ * N) * N := by
    rw [← hpow]
    exact (hlow.trans h1).trans (mul_le_mul_of_nonneg_left hcard hfac)
  have h3 : (3 * (T + 1 + C₁ * N) * N) ≤ 3 * (2 + C₁) * T * N := by
    nlinarith [mul_nonneg hC₁.le (sub_nonneg.mpr hNT)]
  have hexp : (N : ℝ) ^ (1 - 2 * σ) * (N : ℝ) ^ (2 * σ) = N := by
    rw [← Real.rpow_add hN0]; simp
  have : (W.card : ℝ) * (N : ℝ) ^ (2 * σ) ≤ (3 * (2 + C₁) * T * (N : ℝ) ^ (1 - 2 * σ)) * (N : ℝ) ^ (2 * σ) := by
    calc _ ≤ 3 * (2 + C₁) * T * N := h2.trans h3
      _ = _ := by rw [mul_assoc (3 * (2 + C₁) * T), hexp]
  exact le_of_mul_le_mul_right this hpos

alias card_le_of_large_values_orthogonality_dev := chk_card_le_of_large_values_orthogonality

end GuthMaynard

end
end

section
open GuthMaynard

theorem solution :
    ∃ C : ℝ, ∀ (σ : ℝ) (N : ℕ), 1 ≤ N → ∀ T : ℝ, (N : ℝ) ≤ T → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (W.card : ℝ) ≤ C * T * (N : ℝ) ^ (1 - 2 * σ) := by
  apply GuthMaynard.card_le_of_large_values_orthogonality_dev <;> assumption

end
