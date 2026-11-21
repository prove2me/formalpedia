-- Prove2me | solution 1 for LandauCriterion.sum_multiplicity_div_normSq_zeros_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-20T23:56:04.824472+00:00
-- url     : https://prove2.me/submissions/397c013c-f463-447a-8313-17a5bac6132e

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Under RH: `Σ_{ρ ∈ Z} m_ρ / |ρ|² ≤ 2 + γ - log 4π` for finite sets of nontrivial zeros

Proof: residue theorem for `ξ'/ξ · 1/(s(1-s))`-type kernels on a square, digamma bounds,
`2 ξ'(1)/ξ(1) = 2 + γ - log 4π` (see `LandauRH.zero_sum_le_Sstar`).
-/

namespace LandauMellin end LandauMellin
namespace ZetaAux end ZetaAux
namespace PsiOscillation end PsiOscillation
namespace VonKoch end VonKoch
namespace LandauRH end LandauRH

noncomputable section

-- ===== LandauMellin.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric

namespace LandauMellin

/-- `mellinK A k s = ∫_{x>1} A(x) (-log x)^k x^{-s-1} dx`; for `k = 0` this is the Mellin-type
transform `F(s) = ∫_{x>1} A(x) x^{-s-1} dx`, and `mellinK A k` is its `k`-th derivative. -/
def mellinK (A : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1)

lemma log_pow_le (k : ℕ) {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ k ≤ ((k:ℝ) / η) ^ k * x ^ η := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.one_le_rpow hx hη.le
  · have hk' : (0:ℝ) < k := by exact_mod_cast hk
    have hε : 0 < η / k := div_pos hη hk'
    have h1 : Real.log x ≤ x ^ (η / k) / (η / k) := Real.log_le_rpow_div (by linarith) hε
    have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hx0 : 0 ≤ x := by linarith
    calc Real.log x ^ k ≤ (x ^ (η / k) / (η / k)) ^ k := pow_le_pow_left₀ h0 h1 k
      _ = ((k:ℝ) / η) ^ k * x ^ η := by
        rw [div_pow, ← Real.rpow_natCast (x ^ (η / k)), ← Real.rpow_mul hx0,
          div_mul_cancel₀ η hk'.ne', div_eq_mul_inv, ← inv_pow, inv_div, mul_comm]

/-- Absolute convergence of the real Mellin integral `∫_{x>1} |A(x)| x^{-σ-1} dx`. -/
def ConvAbs (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => |A x| * x ^ (-σ - 1)) (Ioi 1)

/-- Domination: absolute convergence at `σ` gives integrability of
`|A(x)| (log x)^k x^{-σ'-1}` for every `σ' > σ`. -/
lemma integrableOn_log_pow {A : ℝ → ℝ} (hA : Measurable A)
    {σ σ' : ℝ} (hσ : σ < σ') (hc : ConvAbs A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => |A x| * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  have hη : 0 < σ' - σ := sub_pos.mpr hσ
  refine (hc.const_mul (((k:ℝ) / (σ' - σ)) ^ k)).mono'
    (((hA.abs.mul (Real.measurable_log.pow_const k)).mul
      (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  have hAx := abs_nonneg (A x)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have key := log_pow_le k hη hx'.le
  calc |A x| * Real.log x ^ k * x ^ (-σ' - 1)
      ≤ |A x| * (((k:ℝ) / (σ' - σ)) ^ k * x ^ (σ' - σ)) * x ^ (-σ' - 1) := by gcongr
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * (x ^ (σ' - σ) * x ^ (-σ' - 1))) := by ring
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * x ^ (-σ - 1)) := by
        rw [← Real.rpow_add hx0]; ring_nf

lemma norm_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    ‖(A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1)‖ =
      |A x| * Real.log x ^ k * x ^ (-z.re - 1) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp [abs_of_nonneg hlog]

lemma hasDerivAt_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun s : ℂ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1)) z := by
  have h1 : HasDerivAt (fun s : ℂ => -s - 1) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const 1
  have h2 := h1.const_cpow (c := (x:ℂ)) (Or.inl (by exact_mod_cast hx.ne'))
  have h3 := h2.const_mul ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k)
  refine h3.congr_deriv ?_
  rw [← Complex.ofReal_log hx.le]
  push_cast
  ring

lemma aestronglyMeasurable_integrand {A : ℝ → ℝ} (hA : Measurable A) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := by
  refine Measurable.aestronglyMeasurable ?_
  refine ((Complex.measurable_ofReal.comp hA).mul ?_).mul ?_
  · exact (Complex.measurable_ofReal.comp Real.measurable_log.neg).pow_const k
  · exact Complex.measurable_ofReal.pow_const _

lemma integrable_integrand {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    Integrable (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi 1)) := by
  have hI := integrableOn_log_pow hA (σ := (τ + s.re) / 2) (σ' := s.re) (by linarith)
    (hconv _ (by linarith)) k
  refine hI.mono' (aestronglyMeasurable_integrand hA k s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_integrand A k hx]

lemma hasDerivAt_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    HasDerivAt (mellinK A k) (mellinK A (k+1) s) s := by
  set δ := (s.re - τ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set σ₁ := s.re - δ with hσ₁
  have hτσ₁ : τ < σ₁ := by rw [hσ₁, hδ]; linarith
  have hbound := integrableOn_log_pow hA (σ := (τ + σ₁) / 2) (σ' := σ₁) (by linarith)
    (hconv _ (by linarith)) (k + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
    (F' := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1))
    (x₀ := s) (s := ball s δ)
    (bound := fun x => |A x| * Real.log x ^ (k + 1) * x ^ (-σ₁ - 1))
    (ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => aestronglyMeasurable_integrand hA k z)
    (integrable_integrand hA hconv k hs)
    (aestronglyMeasurable_integrand hA (k + 1) s) ?_ hbound ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    have hx' : (1:ℝ) < x := hx
    rw [norm_integrand A (k + 1) hx']
    have hzre : σ₁ ≤ z.re := by
      have h1 : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa using Complex.abs_re_le_norm (z - s)
      have h2 : ‖z - s‖ < δ := by simpa [dist_eq_norm] using hz
      have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      rw [hσ₁]; linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    exact hasDerivAt_integrand A k (by linarith [show (1:ℝ) < x from hx]) z

lemma differentiableOn_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) :
    DifferentiableOn ℂ (mellinK A k) {z : ℂ | τ < z.re} := fun _ hz =>
  (hasDerivAt_mellinK hA hconv k hz).differentiableAt.differentiableWithinAt

/-! ### Landau's theorem for Mellin transforms of nonnegative functions -/

end LandauMellin

end

-- ===== ZetaAux.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric
open scoped LSeries.notation

namespace ZetaAux

/-! ### The entire function `(s - 1) ζ(s)` -/

/-- `zetaMulSubOne s = (s - 1) ζ(s)`, extended by its limit `1` at `s = 1`. -/
def zetaMulSubOne (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s

lemma zetaMulSubOne_of_ne {s : ℂ} (hs : s ≠ 1) : zetaMulSubOne s = (s - 1) * riemannZeta s :=
  if_neg hs

lemma zetaMulSubOne_one : zetaMulSubOne 1 = 1 := if_pos rfl

lemma differentiable_zetaMulSubOne : Differentiable ℂ zetaMulSubOne := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaMulSubOne =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz using zetaMulSubOne_of_ne hz
    exact (((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq hev).differentiableWithinAt
  · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, zetaMulSubOne_one]
    refine riemannZeta_residue_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (zetaMulSubOne_of_ne hz).symm

lemma zetaMulSubOne_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : zetaMulSubOne s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, zetaMulSubOne_one]; exact one_ne_zero
  · rw [zetaMulSubOne_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

/-! ### `ζ(s) = s/(s-1) - s ∫_{x>1} {x} x^{-s-1} dx` and real zeros -/

lemma convAbs_fract {σ : ℝ} (hσ : 0 < σ) : LandauMellin.ConvAbs Int.fract σ := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hI.mono' ((measurable_fract.abs.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  have h0 : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) h0)]
  have : |Int.fract x| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le
  calc |Int.fract x| * x ^ (-σ - 1) ≤ 1 * x ^ (-σ - 1) := by gcongr
    _ = x ^ (-σ - 1) := one_mul _

lemma mellinK_fract_eq (s : ℂ) :
    LandauMellin.mellinK Int.fract 0 s =
      ∫ x in Ioi (1:ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  simp [LandauMellin.mellinK]

lemma zeta_eq_integral_fract {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * LandauMellin.mellinK Int.fract 0 s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1:ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1:ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp
  have h1 := LSeries_eq_mul_integral_of_nonneg (fun _ => (1:ℝ)) zero_le_one
    (by linarith : (1:ℝ) < s.re) hO (fun _ => zero_le_one)
  have hL : LSeries (fun n : ℕ => (((fun _ => (1:ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [hL] at h1
  rw [h1]
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  -- pointwise identity on `Ioi 1`
  have hpt : ∀ t ∈ Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((fun _ => (1:ℝ)) k : ℝ) : ℂ)) *
      (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    intro t ht
    have ht' : (1:ℝ) < t := ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < t).ne'
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [natCast_floor_eq_intCast_floor (by linarith), Int.self_sub_fract]
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, ofReal_one,
      mul_one]
    have hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by exact_mod_cast hfl
    rw [hfl', sub_mul, show -(s + 1) = -s - 1 by ring]
    congr 1
    rw [show -s - 1 = -s + (-1) by ring, cpow_add _ _ ht0, cpow_neg_one]
    field_simp
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint2 : IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi 1) := by
    have := LandauMellin.integrable_integrand (A := Int.fract) measurable_fract (τ := 0)
      (fun σ hσ => convAbs_fract hσ) 0 (s := s) (by linarith)
    simp only [pow_zero, mul_one] at this
    exact this
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hint1 hint2,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one, mellinK_fract_eq]
  simp only [ofReal_one, one_cpow]
  rw [show -s + 1 = -(s - 1) by ring]
  field_simp

/-- `(s - 1) ζ(s) = s - s (s - 1) ∫_{x>1} {x} x^{-s-1} dx` on the half-plane `Re s > 0`. -/
lemma zetaMulSubOne_eq_integral {s : ℂ} (hs : 0 < s.re) :
    zetaMulSubOne s = s - s * (s - 1) * LandauMellin.mellinK Int.fract 0 s := by
  have hJ : DifferentiableOn ℂ (LandauMellin.mellinK Int.fract 0) {z : ℂ | 0 < z.re} :=
    LandauMellin.differentiableOn_mellinK measurable_fract (fun σ hσ => convAbs_fract hσ) 0
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hR : DifferentiableOn ℂ (fun z => z - z * (z - 1) * LandauMellin.mellinK Int.fract 0 z)
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.sub differentiableOn_id ?_
    exact ((differentiableOn_id).mul (differentiableOn_id.sub_const 1)).mul hJ
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (differentiable_zetaMulSubOne.differentiableOn.analyticOnNhd hopen) (hR.analyticOnNhd hopen)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2:ℂ)) (by simp) ?_
  · exact heq hs
  · have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    rw [zetaMulSubOne_of_ne hz1, zeta_eq_integral_fract hz]
    have hs1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    field_simp

/-! ### Mellin transform of `ψ` -/

end ZetaAux

end

-- ===== Oscillation.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric

namespace PsiOscillation

open ZetaAux LandauMellin

/-! ### A holomorphic function satisfying `f' = P f` cannot vanish (unless it is locally `0`) -/

/-! ### The test function `A(x) = x^θ + ε (x - ψ(x))` -/

/-- `deriv ((s-1)ζ(s)) = ζ(s) + (s-1) ζ'(s)` for `s ≠ 1`. -/
lemma deriv_zetaMulSubOne {s : ℂ} (hs : s ≠ 1) :
    deriv zetaMulSubOne s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : zetaMulSubOne =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz using zetaMulSubOne_of_ne hz
  rw [hev.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]
  ring

/-! ### The core contradiction -/

/-! ### The oscillation theorems -/

/-! ### Consequences of the failure of the Riemann hypothesis -/

end PsiOscillation

end

-- ===== VK1Landau.lean =====
section

open Complex Metric Filter Topology Set

namespace VonKoch

/-! ### Borel–Carathéodory at a general center -/

lemma bc_center {H : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (ball c r)) (hre : ∀ w ∈ ball c r, (H w).re ≤ M) (hc : H c = 0)
    {w : ℂ} (hw : w ∈ ball c r) : ‖H w‖ ≤ 2 * M * ‖w - c‖ / (r - ‖w - c‖) := by
  set φ : ℂ → ℂ := fun z => H (z + c) with hφdef
  have hmem : ∀ z ∈ ball (0:ℂ) r, z + c ∈ ball c r := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    simpa using hz
  have hφ : DifferentiableOn ℂ φ (ball 0 r) := by
    intro z hz
    have h1 : DifferentiableAt ℂ H (z + c) :=
      hH.differentiableAt (isOpen_ball.mem_nhds (hmem z hz))
    exact (h1.comp z ((differentiableAt_id).add_const c)).differentiableWithinAt
  have hmaps : MapsTo φ (ball 0 r) {z | z.re ≤ M} := fun z hz => hre _ (hmem z hz)
  have hw' : w - c ∈ ball (0:ℂ) r := by
    rw [mem_ball, dist_eq_norm] at hw ⊢
    simpa using hw
  have key := Complex.borelCaratheodory hM hφ hmaps hr hw'
  simp only [hφdef, sub_add_cancel, zero_add, hc, norm_zero, zero_mul, zero_div,
    add_zero] at key
  exact key

/-! ### A normalized holomorphic logarithm of a nonvanishing function on a ball -/

lemma exists_log_on_ball {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (ball c r)) (hG0 : ∀ z ∈ ball c r, G z ≠ 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball c r) ∧ H c = 0 ∧
      (∀ z ∈ ball c r, HasDerivAt H (deriv G z / G z) z) ∧
      (∀ z ∈ ball c r, ‖G z‖ = ‖G c‖ * Real.exp (H z).re) := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hdiv : DifferentiableOn ℂ (fun z => deriv G z / G z) (ball c r) :=
    (hG.deriv isOpen_ball).div hG hG0
  obtain ⟨H₀, hH₀⟩ := hdiv.isExactOn_ball
  set H : ℂ → ℂ := fun z => H₀ z - H₀ c with hHdef
  have hH : ∀ z ∈ ball c r, HasDerivAt H (deriv G z / G z) z := fun z hz =>
    (hH₀ z hz).sub_const _
  have hHdiff : DifferentiableOn ℂ H (ball c r) := fun z hz =>
    (hH z hz).differentiableAt.differentiableWithinAt
  refine ⟨H, hHdiff, by simp [hHdef], hH, ?_⟩
  -- `G * exp (-H)` is constant on the ball
  set E : ℂ → ℂ := fun z => G z * Complex.exp (-H z) with hEdef
  have hEderiv : ∀ z ∈ ball c r, HasDerivAt E 0 z := by
    intro z hz
    have hGz : HasDerivAt G (deriv G z) z :=
      (hG.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hexp : HasDerivAt (fun w => Complex.exp (-H w))
        (Complex.exp (-H z) * (-(deriv G z / G z))) z :=
      ((hH z hz).neg).cexp
    have hGz0 := hG0 z hz
    refine (hGz.mul hexp).congr_deriv ?_
    field_simp
    ring
  have hEdiff : DifferentiableOn ℂ E (ball c r) := fun z hz =>
    (hEderiv z hz).differentiableAt.differentiableWithinAt
  have hEconst : ∀ z ∈ ball c r, E z = E c := by
    intro z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hEdiff
      (fun w hw => (hEderiv w hw).deriv) hz hc
  intro z hz
  have h1 : G z * Complex.exp (-H z) = G c * Complex.exp (-H c) := hEconst z hz
  have hHc : H c = 0 := by simp [hHdef]
  rw [hHc, neg_zero, Complex.exp_zero, mul_one] at h1
  have h2 : G z = G c * Complex.exp (H z) := by
    have := congrArg (fun w => w * Complex.exp (H z)) h1
    simp only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] at this
    exact this
  rw [h2, norm_mul, Complex.norm_exp]

/-! ### Landau's lemma: `f'/f` minus the nearby zeros is `O(log (B / |f c|))` -/

lemma divisor_eq_natOrder {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {u : ℂ} (hu : u ∈ U)
    (hu' : analyticOrderAt f u ≠ ⊤) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hu, ← Nat.cast_analyticOrderNatAt hu']
  simp

lemma analyticOrderNatAt_pos_iff {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u)
    (hu' : analyticOrderAt f u ≠ ⊤) : 0 < analyticOrderNatAt f u ↔ f u = 0 := by
  constructor
  · intro h
    by_contra hne
    have h0 : analyticOrderAt f u = 0 := hf.analyticOrderAt_eq_zero.mpr hne
    rw [← Nat.cast_analyticOrderNatAt hu'] at h0
    simp at h0
    omega
  · intro h
    by_contra hle
    have h0 : analyticOrderNatAt f u = 0 := by omega
    have : analyticOrderAt f u = 0 := by rw [← Nat.cast_analyticOrderNatAt hu', h0]; rfl
    exact (hf.analyticOrderAt_eq_zero.mp this) h

/-- **Landau's lemma.** For `f` holomorphic on `closedBall c R` with `f c ≠ 0` and `|f| ≤ B` on the
circle of radius `R`, the logarithmic derivative of `f` on `closedBall c a` equals the sum over the
zeros of `f` in `closedBall c r` of `m/(z-ρ)`, up to an error `O(log (B/|f c|) + 1)` whose constant
depends only on `r, R, a`. The number of these zeros is bounded by Jensen's inequality. -/
theorem landau_logDeriv {r R a : ℝ} (hr : 0 < r) (hrR : r < R) (ha : 0 < a) (har : a < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℂ → ℂ) (c : ℂ) (B : ℝ), 1 ≤ B →
      AnalyticOnNhd ℂ f (closedBall c R) → f c ≠ 0 → (∀ z ∈ sphere c R, ‖f z‖ ≤ B) →
      ∃ S : Finset ℂ, (∀ u ∈ S, u ∈ closedBall c r ∧ f u = 0) ∧
        (∀ u ∈ closedBall c r, f u = 0 → u ∈ S) ∧
        (∑ u ∈ S, (analyticOrderNatAt f u : ℝ)) ≤ Real.log (B / ‖f c‖) / Real.log (R / r) ∧
        ∀ z ∈ closedBall c a, f z ≠ 0 →
          ‖deriv f z / f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u)‖ ≤
            K * (Real.log (B / ‖f c‖) + 1) := by
  classical
  have hR : 0 < R := hr.trans hrR
  set δ : ℝ := (r - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  set κ : ℝ := max 0 (Real.log (r / (R - r))) / Real.log (R / r) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (le_max_left _ _) hlogRr.le
  refine ⟨2 * (a + δ) * (1 + κ) / δ ^ 2, by positivity, ?_⟩
  intro f c B hB hf hfc hfB
  set U : Set ℂ := closedBall c R with hU
  have hcU : c ∈ U := mem_closedBall_self hR.le
  have hconn : IsConnected U := ⟨nonempty_closedBall.mpr hR.le, (convex_closedBall c R).isPreconnected⟩
  -- `f` is not locally zero at any point of `U`
  have hord : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    rw [← hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hconn]
    refine ⟨⟨c, hcU⟩, ?_⟩
    rw [(hf c hcU).meromorphicOrderAt_eq, (hf c hcU).analyticOrderAt_eq_zero.mpr hfc]
    simp
  have hord' : ∀ u ∈ U, analyticOrderAt f u ≠ ⊤ := by
    intro u hu h
    apply hord ⟨u, hu⟩
    rw [(hf u hu).meromorphicOrderAt_eq, h]
    rfl
  have hfin : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.meromorphicOn.extract_zeros_poles hord hfin
  set D := MeromorphicOn.divisor f U with hDdef
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hmdef
  set Sall : Finset ℂ := hfin.toFinset with hSall
  have hSallU : ∀ u ∈ Sall, u ∈ U := fun u hu =>
    D.supportWithinDomain (by simpa [hSall] using hu)
  have hSall_iff : ∀ u ∈ U, u ∈ Sall ↔ f u = 0 := by
    intro u hu
    rw [hSall, Set.Finite.mem_toFinset, Function.mem_support, hDdef,
      divisor_eq_natOrder hf hu (hord' u hu), ← analyticOrderNatAt_pos_iff (hf u hu) (hord' u hu)]
    constructor
    · intro h; exact Nat.pos_of_ne_zero (by exact_mod_cast h)
    · intro h; exact_mod_cast h.ne'
  set S : Finset ℂ := Sall.filter (fun u => u ∈ closedBall c r) with hSdef
  set So : Finset ℂ := Sall.filter (fun u => u ∉ closedBall c r) with hSodef
  set P : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ m u with hPdef
  set Q : ℂ → ℂ := fun z => ∏ u ∈ So, (z - u) ^ m u with hQdef
  set G : ℂ → ℂ := fun z => Q z * g z with hGdef
  have hPdiff : Differentiable ℂ P := by rw [hPdef]; fun_prop
  have hQdiff : Differentiable ℂ Q := by rw [hQdef]; fun_prop
  -- the factorization holds codiscretely on `U`
  have hfactor : ∀ z, ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z = P z * G z := by
    intro z
    have hfs : Function.HasFiniteSupport (⇑D) := hfin
    rw [Pi.smul_apply', Function.FactorizedRational.finprod_eq_fun hfs, smul_eq_mul]
    beta_reduce
    have hsub : Function.mulSupport (fun u => (z - u) ^ D u) ⊆ (Sall : Set ℂ) := by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [hSall, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0, zpow_zero]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    have hcongr : ∏ u ∈ Sall, (z - u) ^ D u = ∏ u ∈ Sall, (z - u) ^ m u := by
      refine Finset.prod_congr rfl (fun u hu => ?_)
      rw [hDdef, divisor_eq_natOrder hf (hSallU u hu) (hord' u (hSallU u hu)), zpow_natCast]
    rw [hcongr, ← Finset.prod_filter_mul_prod_filter_not Sall (fun u => u ∈ closedBall c r)]
    simp only [hPdef, hQdef, hGdef, hSdef, hSodef]
    ring
  have hPGan : AnalyticOnNhd ℂ (fun z => P z * G z) U := by
    intro z hz
    exact (hPdiff.analyticAt z).mul ((hQdiff.analyticAt z).mul (hg z hz))
  have hEq : EqOn f (fun z => P z * G z) U := by
    refine hf.eqOn_of_preconnected_of_frequently_eq hPGan hconn.isPreconnected hcU ?_
    have hmem := (mem_codiscreteWithin.mp hfg) c hcU
    have h1 : (U \ {z | f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z})ᶜ ∈ 𝓝[≠] c :=
      (disjoint_principal_right.mp hmem)
    have h2 : U ∈ 𝓝[≠] c := mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds c hR)
    have h3 : ∀ᶠ z in 𝓝[≠] c, f z = P z * G z := by
      filter_upwards [h1, h2] with z hz1 hz2
      have : z ∈ {z | f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z} := by
        by_contra hcon; exact hz1 ⟨hz2, hcon⟩
      exact (show f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z from this).trans (hfactor z)
    exact h3.frequently
  -- basic facts about the zeros
  have hS_mem : ∀ u ∈ S, u ∈ closedBall c r ∧ f u = 0 := by
    intro u hu
    rw [hSdef, Finset.mem_filter] at hu
    exact ⟨hu.2, (hSall_iff u (hSallU u hu.1)).mp hu.1⟩
  have hS_all : ∀ u ∈ closedBall c r, f u = 0 → u ∈ S := by
    intro u hu hfu
    have huU : u ∈ U := closedBall_subset_closedBall hrR.le hu
    rw [hSdef, Finset.mem_filter]
    exact ⟨(hSall_iff u huU).mpr hfu, hu⟩
  set N : ℕ := ∑ u ∈ S, m u with hNdef
  -- Jensen: the number of zeros
  have hJensen : (∑ u ∈ S, (m u : ℝ)) ≤ Real.log (B / ‖f c‖) / Real.log (R / r) := by
    have hrabs : |r| = r := abs_of_pos hr
    have hRabs : |R| = R := abs_of_pos hR
    have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := B) (f := f)
      (by rw [hrabs]; exact hr) (by rw [hrabs, hRabs]; exact hrR) hB (by rw [hRabs]; exact hf) hfc
      (by rw [hRabs]; exact hfB)
    rw [hrabs] at hJ
    have hsub : Function.support (MeromorphicOn.divisor f (closedBall c r)) ⊆ (S : Set ℂ) := by
      intro u hu
      have huV : u ∈ closedBall c r := (MeromorphicOn.divisor f (closedBall c r)).supportWithinDomain hu
      have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
      have huU : u ∈ U := closedBall_subset_closedBall hrR.le huV
      rw [Function.mem_support, divisor_eq_natOrder hfr huV (hord' u huU)] at hu
      have hpos : 0 < m u := Nat.pos_of_ne_zero (by exact_mod_cast hu)
      exact hS_all u huV ((analyticOrderNatAt_pos_iff (hf u huU) (hord' u huU)).mp hpos)
    rw [finsum_eq_sum_of_support_subset _ hsub] at hJ
    have hcongr : ∑ u ∈ S, MeromorphicOn.divisor f (closedBall c r) u = ∑ u ∈ S, (m u : ℤ) := by
      refine Finset.sum_congr rfl (fun u hu => ?_)
      have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
      exact divisor_eq_natOrder hfr (hS_mem u hu).1 (hord' u (closedBall_subset_closedBall hrR.le
        (hS_mem u hu).1))
    rw [hcongr] at hJ
    push_cast at hJ
    exact hJ
  refine ⟨S, hS_mem, hS_all, hJensen, ?_⟩
  -- norm bounds for `P`
  have hnormP : ∀ z, ‖P z‖ = ∏ u ∈ S, ‖z - u‖ ^ m u := by
    intro z; simp [hPdef, norm_prod, norm_pow]
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hPsphere : ∀ z ∈ sphere c R, (R - r) ^ N ≤ ‖P z‖ := by
    intro z hz
    rw [hnormP, hNdef, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun u _ => by positivity)
    intro u hu
    apply pow_le_pow_left₀ hRr.le
    have h1 : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
    have h2 : ‖u - c‖ ≤ r := by
      have := (hS_mem u hu).1; rwa [mem_closedBall, dist_eq_norm] at this
    have h3 := norm_sub_norm_le (z - c) (u - c)
    rw [sub_sub_sub_cancel_right] at h3
    linarith
  have hPc : ‖P c‖ ≤ r ^ N := by
    rw [hnormP, hNdef, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun u _ => by positivity)
    intro u hu
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h2 := (hS_mem u hu).1
    rw [mem_closedBall, dist_eq_norm] at h2
    rwa [norm_sub_rev]
  have hfcPG : f c = P c * G c := hEq hcU
  have hPc0 : P c ≠ 0 := fun h => hfc (by rw [hfcPG, h, zero_mul])
  have hGc0 : G c ≠ 0 := fun h => hfc (by rw [hfcPG, h, mul_zero])
  have hGan : AnalyticOnNhd ℂ G U := fun z hz => (hQdiff.analyticAt z).mul (hg z hz)
  have hG0 : ∀ z ∈ closedBall c r, G z ≠ 0 := by
    intro z hz
    have hzU : z ∈ U := closedBall_subset_closedBall hrR.le hz
    apply mul_ne_zero
    · rw [hQdef]
      refine Finset.prod_ne_zero_iff.mpr (fun u hu => pow_ne_zero _ (sub_ne_zero.mpr ?_))
      rintro rfl
      rw [hSodef, Finset.mem_filter] at hu
      exact hu.2 hz
    · exact hg0 ⟨z, hzU⟩
  -- maximum modulus bounds
  have hfcB : ‖f c‖ ≤ B := by
    have hdc : DiffContOnCl ℂ f (ball c R) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c hR.ne']
      exact hf.differentiableOn
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rw [closure_ball c hR.ne']; exact hcU)
    intro z hz
    rw [frontier_ball c hR.ne'] at hz
    exact hfB z hz
  have hGbound : ∀ w ∈ closedBall c R, ‖G w‖ ≤ B / (R - r) ^ N := by
    have hdc : DiffContOnCl ℂ G (ball c R) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c hR.ne']
      exact hGan.differentiableOn
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball c hR.ne'])
    intro z hz
    rw [frontier_ball c hR.ne'] at hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    have hfz : f z = P z * G z := hEq hzU
    have hPz := hPsphere z hz
    have hpow : 0 < (R - r) ^ N := pow_pos hRr N
    rw [le_div_iff₀ hpow]
    calc ‖G z‖ * (R - r) ^ N ≤ ‖G z‖ * ‖P z‖ := by gcongr
      _ = ‖f z‖ := by rw [hfz, norm_mul (P z) (G z), mul_comm]
      _ ≤ B := hfB z hz
  -- the holomorphic logarithm of `G` on `ball c r`
  obtain ⟨H, hHdiff, hHc, hHderiv, hHnorm⟩ := exists_log_on_ball hr
    (hGan.differentiableOn.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)))
    (fun z hz => hG0 z (ball_subset_closedBall hz))
  set L : ℝ := Real.log (B / ‖f c‖) with hL
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hfc0]; linarith)
  have hNle : (N : ℝ) ≤ L / Real.log (R / r) := by
    rw [hNdef]; push_cast; exact hJensen
  -- `Re H ≤ L (1 + κ)` on the ball
  have hreH : ∀ w ∈ ball c r, (H w).re ≤ L * (1 + κ) := by
    intro w hw
    have hwR : w ∈ closedBall c R := closedBall_subset_closedBall hrR.le (ball_subset_closedBall hw)
    have hGc : ‖f c‖ / r ^ N ≤ ‖G c‖ := by
      rw [hfcPG, norm_mul, div_le_iff₀ (pow_pos hr N)]
      calc ‖P c‖ * ‖G c‖ ≤ r ^ N * ‖G c‖ := by gcongr
        _ = ‖G c‖ * r ^ N := by ring
    have hGc' : 0 < ‖G c‖ := norm_pos_iff.mpr hGc0
    have hexp : Real.exp (H w).re = ‖G w‖ / ‖G c‖ := by
      rw [hHnorm w hw]; field_simp
    have hratio : ‖G w‖ / ‖G c‖ ≤ (B / ‖f c‖) * (r / (R - r)) ^ N := by
      rw [div_le_iff₀ hGc']
      calc ‖G w‖ ≤ B / (R - r) ^ N := hGbound w hwR
        _ = (B / ‖f c‖) * (r / (R - r)) ^ N * (‖f c‖ / r ^ N) := by
          rw [div_pow]; field_simp
        _ ≤ (B / ‖f c‖) * (r / (R - r)) ^ N * ‖G c‖ := by gcongr
    have hlogbound : Real.log ((B / ‖f c‖) * (r / (R - r)) ^ N) ≤ L * (1 + κ) := by
      have hpos1 : 0 < B / ‖f c‖ := div_pos (by linarith) hfc0
      have hpos2 : 0 < r / (R - r) := div_pos hr hRr
      rw [Real.log_mul hpos1.ne' (pow_pos hpos2 N).ne', Real.log_pow, ← hL]
      have hmax : (N : ℝ) * Real.log (r / (R - r)) ≤ (N : ℝ) * max 0 (Real.log (r / (R - r))) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg N)
      have hmax2 : (N : ℝ) * max 0 (Real.log (r / (R - r))) ≤ L * κ := by
        rw [hκ, mul_div_assoc', mul_comm L, mul_div_assoc]
        calc (N : ℝ) * max 0 (Real.log (r / (R - r)))
            ≤ L / Real.log (R / r) * max 0 (Real.log (r / (R - r))) :=
              mul_le_mul_of_nonneg_right hNle (le_max_left _ _)
          _ = max 0 (Real.log (r / (R - r))) * (L / Real.log (R / r)) := by ring
      linarith
    have hpos : 0 < (B / ‖f c‖) * (r / (R - r)) ^ N := by positivity
    calc (H w).re = Real.log (Real.exp (H w).re) := (Real.log_exp _).symm
      _ = Real.log (‖G w‖ / ‖G c‖) := by rw [hexp]
      _ ≤ Real.log ((B / ‖f c‖) * (r / (R - r)) ^ N) := by
          apply Real.log_le_log (by rw [← hexp]; positivity) hratio
      _ ≤ L * (1 + κ) := hlogbound
  -- Borel–Carathéodory and the Cauchy estimate for `H`
  set M' : ℝ := L * (1 + κ) + 1 with hM'
  have hM'0 : 0 < M' := by positivity
  have hHbound : ∀ w ∈ ball c r, ‖H w‖ ≤ 2 * M' * ‖w - c‖ / (r - ‖w - c‖) := by
    intro w hw
    exact bc_center hM'0 hr hHdiff (fun w hw => (hreH w hw).trans (by linarith)) hHc hw
  intro z hz hfz
  have hzc : ‖z - c‖ ≤ a := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hzball : z ∈ ball c r := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hsub : closedBall z δ ⊆ ball c r := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    have := norm_add_le (w - z) (z - c)
    rw [sub_add_sub_cancel] at this
    rw [hδ] at hw
    linarith
  have hderivH : ‖deriv H z‖ ≤ 2 * M' * (a + δ) / δ / δ := by
    have hdc : DiffContOnCl ℂ H (ball z δ) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hδ0.ne']
      exact hHdiff.mono hsub
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ0 hdc (fun w hw => ?_)
    have hw' : w ∈ ball c r := hsub (sphere_subset_closedBall hw)
    have hwz : ‖w - z‖ = δ := by simpa [dist_eq_norm] using hw
    have hwc : ‖w - c‖ ≤ a + δ := by
      have := norm_add_le (w - z) (z - c)
      rw [sub_add_sub_cancel] at this
      linarith
    have hden : δ ≤ r - ‖w - c‖ := by rw [hδ] at hwc ⊢; linarith
    calc ‖H w‖ ≤ 2 * M' * ‖w - c‖ / (r - ‖w - c‖) := hHbound w hw'
      _ ≤ 2 * M' * (a + δ) / δ := by
          apply div_le_div₀ (by positivity) (by gcongr) hδ0 hden
  -- the logarithmic derivative identity
  have hzU : z ∈ U := closedBall_subset_closedBall hrR.le (ball_subset_closedBall hzball)
  have hfzPG : f z = P z * G z := hEq hzU
  have hPz0 : P z ≠ 0 := fun h => hfz (by rw [hfzPG, h, zero_mul])
  have hGz0 : G z ≠ 0 := fun h => hfz (by rw [hfzPG, h, mul_zero])
  have hevent : f =ᶠ[𝓝 z] fun w => P w * G w := by
    have hUn : U ∈ 𝓝 z := by
      apply closedBall_mem_nhds_of_mem
      rw [mem_ball, dist_eq_norm]
      linarith
    filter_upwards [hUn] with w hw using hEq hw
  have hlog : deriv f z / f z = (∑ u ∈ S, (m u : ℂ) / (z - u)) + deriv G z / G z := by
    have h1 : deriv f z / f z = logDeriv (fun w => P w * G w) z := by
      rw [← logDeriv_apply]; exact (logDeriv_congr_nhds hevent).eq_of_nhds
    have hGd : DifferentiableAt ℂ G z := (hGan z hzU).differentiableAt
    rw [h1, logDeriv_mul z hPz0 hGz0 (hPdiff z) hGd, logDeriv_apply G z]
    congr 1
    have hfac : ∀ u ∈ S, (z - u) ^ m u ≠ 0 := by
      intro u hu
      have := Finset.prod_ne_zero_iff.mp (show (∏ u ∈ S, (z - u) ^ m u) ≠ 0 from hPz0) u hu
      exact this
    rw [show P = fun w => ∏ u ∈ S, (w - u) ^ m u from rfl,
      logDeriv_prod hfac (fun u _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hzu : z - u ≠ 0 := by
      intro h; apply hfac u hu; rw [h, zero_pow]
      have := (hS_mem u hu).2
      exact (analyticOrderNatAt_pos_iff (hf u (closedBall_subset_closedBall hrR.le (hS_mem u hu).1))
        (hord' u (closedBall_subset_closedBall hrR.le (hS_mem u hu).1))).mpr this |>.ne'
    rw [logDeriv_fun_pow (by fun_prop) (m u), logDeriv_apply]
    simp only [deriv_sub_const, deriv_id'']
    field_simp
  have hderivHz : deriv H z = deriv G z / G z := (hHderiv z hzball).deriv
  calc ‖deriv f z / f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u)‖
      = ‖deriv H z‖ := by rw [hlog, hderivHz]; simp [hmdef]
    _ ≤ 2 * M' * (a + δ) / δ / δ := hderivH
    _ ≤ 2 * (a + δ) * (1 + κ) / δ ^ 2 * (L + 1) := by
        rw [div_div, ← sq]
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : M' ≤ (1 + κ) * (L + 1) := by rw [hM']; nlinarith
        calc 2 * M' * (a + δ) ≤ 2 * ((1 + κ) * (L + 1)) * (a + δ) := by gcongr
          _ = 2 * (a + δ) * (1 + κ) * (L + 1) := by ring

end VonKoch

end

-- ===== VK2Perron.lean =====
section

open Complex MeasureTheory Filter Topology Set

namespace VonKoch

open ArithmeticFunction

/-! ### Elementary bounds -/

/-! ### The Mellin transform of `(1 - u)₊` -/

/-! ### The Perron formula for `ψ₁` -/

end VonKoch

end

-- ===== VK3Rect.lean =====
section

open Complex MeasureTheory Filter Topology Set
open scoped Interval

namespace VonKoch

/-- The (counterclockwise) boundary integral over the rectangle `[x₁, x₂] × [y₁, y₂]`. -/
def rectInt (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  (∫ x in x₁..x₂, f (x + y₁ * I)) - (∫ x in x₁..x₂, f (x + y₂ * I)) +
    I * (∫ y in y₁..y₂, f (x₂ + y * I)) - I * (∫ y in y₁..y₂, f (x₁ + y * I))

/-- Continuity at every point of the boundary of the rectangle. -/
def BdryCont (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : Prop :=
  (∀ x ∈ uIcc x₁ x₂, ContinuousAt f (x + y₁ * I)) ∧ (∀ x ∈ uIcc x₁ x₂, ContinuousAt f (x + y₂ * I)) ∧
  (∀ y ∈ uIcc y₁ y₂, ContinuousAt f (x₂ + y * I)) ∧ (∀ y ∈ uIcc y₁ y₂, ContinuousAt f (x₁ + y * I))

section BdryCont

variable {f g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}

lemma intervalIntegrable_horiz {f : ℂ → ℂ} {x₁ x₂ y : ℝ}
    (h : ∀ x ∈ uIcc x₁ x₂, ContinuousAt f (x + y * I)) :
    IntervalIntegrable (fun x : ℝ => f (x + y * I)) volume x₁ x₂ := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  exact ((h x hx).comp (f := fun x : ℝ => (x : ℂ) + y * I)
    ((Complex.continuous_ofReal.add continuous_const).continuousAt)).continuousWithinAt

lemma intervalIntegrable_vert {f : ℂ → ℂ} {y₁ y₂ x : ℝ}
    (h : ∀ y ∈ uIcc y₁ y₂, ContinuousAt f (x + y * I)) :
    IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume y₁ y₂ := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  exact ((h y hy).comp (f := fun y : ℝ => (x : ℂ) + y * I)
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
    ).continuousWithinAt

lemma BdryCont.add (hf : BdryCont f x₁ x₂ y₁ y₂) (hg : BdryCont g x₁ x₂ y₁ y₂) :
    BdryCont (fun s => f s + g s) x₁ x₂ y₁ y₂ :=
  ⟨fun x hx => (hf.1 x hx).add (hg.1 x hx), fun x hx => (hf.2.1 x hx).add (hg.2.1 x hx),
    fun y hy => (hf.2.2.1 y hy).add (hg.2.2.1 y hy), fun y hy => (hf.2.2.2 y hy).add (hg.2.2.2 y hy)⟩

lemma BdryCont.sub (hf : BdryCont f x₁ x₂ y₁ y₂) (hg : BdryCont g x₁ x₂ y₁ y₂) :
    BdryCont (fun s => f s - g s) x₁ x₂ y₁ y₂ :=
  ⟨fun x hx => (hf.1 x hx).sub (hg.1 x hx), fun x hx => (hf.2.1 x hx).sub (hg.2.1 x hx),
    fun y hy => (hf.2.2.1 y hy).sub (hg.2.2.1 y hy), fun y hy => (hf.2.2.2 y hy).sub (hg.2.2.2 y hy)⟩

lemma BdryCont.const_mul (hf : BdryCont f x₁ x₂ y₁ y₂) (c : ℂ) :
    BdryCont (fun s => c * f s) x₁ x₂ y₁ y₂ :=
  ⟨fun x hx => continuousAt_const.mul (hf.1 x hx),
    fun x hx => continuousAt_const.mul (hf.2.1 x hx),
    fun y hy => continuousAt_const.mul (hf.2.2.1 y hy),
    fun y hy => continuousAt_const.mul (hf.2.2.2 y hy)⟩

lemma BdryCont.of_continuous (hf : Continuous f) : BdryCont f x₁ x₂ y₁ y₂ :=
  ⟨fun _ _ => hf.continuousAt, fun _ _ => hf.continuousAt, fun _ _ => hf.continuousAt,
    fun _ _ => hf.continuousAt⟩

lemma BdryCont.of_forall (hf : ∀ s : ℂ, s.re ∈ uIcc x₁ x₂ → s.im ∈ uIcc y₁ y₂ → ContinuousAt f s) :
    BdryCont f x₁ x₂ y₁ y₂ := by
  refine ⟨fun x hx => hf _ (by simpa using hx) (by simp), fun x hx => hf _ (by simpa using hx)
    (by simp), fun y hy => hf _ (by simp) (by simpa using hy),
    fun y hy => hf _ (by simp) (by simpa using hy)⟩

lemma BdryCont.of_bdry (hf : ∀ s : ℂ, s.re ∈ uIcc x₁ x₂ → s.im ∈ uIcc y₁ y₂ →
    (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) → ContinuousAt f s) :
    BdryCont f x₁ x₂ y₁ y₂ := by
  refine ⟨fun x hx => hf _ (by simpa using hx) (by simp) (by simp),
    fun x hx => hf _ (by simpa using hx) (by simp) (by simp),
    fun y hy => hf _ (by simp) (by simpa using hy) (by simp),
    fun y hy => hf _ (by simp) (by simpa using hy) (by simp)⟩

lemma rectInt_add (hf : BdryCont f x₁ x₂ y₁ y₂) (hg : BdryCont g x₁ x₂ y₁ y₂) :
    rectInt (fun s => f s + g s) x₁ x₂ y₁ y₂ = rectInt f x₁ x₂ y₁ y₂ + rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  rw [intervalIntegral.integral_add (intervalIntegrable_horiz hf.1) (intervalIntegrable_horiz hg.1),
    intervalIntegral.integral_add (intervalIntegrable_horiz hf.2.1)
      (intervalIntegrable_horiz hg.2.1),
    intervalIntegral.integral_add (intervalIntegrable_vert hf.2.2.1)
      (intervalIntegrable_vert hg.2.2.1),
    intervalIntegral.integral_add (intervalIntegrable_vert hf.2.2.2)
      (intervalIntegrable_vert hg.2.2.2)]
  ring

lemma rectInt_sub (hf : BdryCont f x₁ x₂ y₁ y₂) (hg : BdryCont g x₁ x₂ y₁ y₂) :
    rectInt (fun s => f s - g s) x₁ x₂ y₁ y₂ = rectInt f x₁ x₂ y₁ y₂ - rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  rw [intervalIntegral.integral_sub (intervalIntegrable_horiz hf.1) (intervalIntegrable_horiz hg.1),
    intervalIntegral.integral_sub (intervalIntegrable_horiz hf.2.1)
      (intervalIntegrable_horiz hg.2.1),
    intervalIntegral.integral_sub (intervalIntegrable_vert hf.2.2.1)
      (intervalIntegrable_vert hg.2.2.1),
    intervalIntegral.integral_sub (intervalIntegrable_vert hf.2.2.2)
      (intervalIntegrable_vert hg.2.2.2)]
  ring

lemma rectInt_const_mul (c : ℂ) :
    rectInt (fun s => c * f s) x₁ x₂ y₁ y₂ = c * rectInt f x₁ x₂ y₁ y₂ := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma BdryCont.sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, BdryCont (F i) x₁ x₂ y₁ y₂) :
    BdryCont (fun s => ∑ i ∈ S, F i s) x₁ x₂ y₁ y₂ := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BdryCont.of_continuous (f := fun _ => (0:ℂ)) continuous_const
  | insert i S hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i S)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

lemma rectInt_sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, BdryCont (F i) x₁ x₂ y₁ y₂) :
    rectInt (fun s => ∑ i ∈ S, F i s) x₁ x₂ y₁ y₂ = ∑ i ∈ S, rectInt (F i) x₁ x₂ y₁ y₂ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [rectInt]
  | insert i S hi ih =>
    simp_rw [Finset.sum_insert hi]
    rw [rectInt_add (hF i (Finset.mem_insert_self i S))
      (BdryCont.sum S fun j hj => hF j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]

lemma rectInt_congr (hfg : ∀ s : ℂ, s.re ∈ uIcc x₁ x₂ → s.im ∈ uIcc y₁ y₂ →
    (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) → f s = g s) :
    rectInt f x₁ x₂ y₁ y₂ = rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  have e1 : ∫ x in x₁..x₂, f (x + y₁ * I) = ∫ x in x₁..x₂, g (x + y₁ * I) :=
    intervalIntegral.integral_congr (fun x hx => hfg _ (by simpa using hx) (by simp) (by simp))
  have e2 : ∫ x in x₁..x₂, f (x + y₂ * I) = ∫ x in x₁..x₂, g (x + y₂ * I) :=
    intervalIntegral.integral_congr (fun x hx => hfg _ (by simpa using hx) (by simp) (by simp))
  have e3 : ∫ y in y₁..y₂, f (x₂ + y * I) = ∫ y in y₁..y₂, g (x₂ + y * I) :=
    intervalIntegral.integral_congr (fun y hy => hfg _ (by simp) (by simpa using hy) (by simp))
  have e4 : ∫ y in y₁..y₂, f (x₁ + y * I) = ∫ y in y₁..y₂, g (x₁ + y * I) :=
    intervalIntegral.integral_congr (fun y hy => hfg _ (by simp) (by simpa using hy) (by simp))
  rw [e1, e2, e3, e4]

/-- Cauchy–Goursat for rectangles. -/
lemma rectInt_eq_zero (hf : DifferentiableOn ℂ f ([[x₁, x₂]] ×ℂ [[y₁, y₂]])) :
    rectInt f x₁ x₂ y₁ y₂ = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ + y₁ * I)
    (x₂ + y₂ * I) (by simpa using hf)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at h
  rw [rectInt]
  exact h

end BdryCont

/-! ### `∮ ds / (s - a) = 2πi` -/

lemma integral_inv_of_slit {g : ℝ → ℂ} {g' : ℂ} {u₁ u₂ : ℝ} (hg : ∀ u, HasDerivAt g g' u)
    (hslit : ∀ u ∈ uIcc u₁ u₂, g u ∈ slitPlane) :
    ∫ u in u₁..u₂, g' / g u = Complex.log (g u₂) - Complex.log (g u₁) := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    exact (hg u).clog_real (hslit u hu)
  · apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div hcont.continuousOn (fun u hu => slitPlane_ne_zero (hslit u hu))

lemma log_sub_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log w - Complex.log (-w) = Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

lemma log_neg_sub_log_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) - Complex.log w = Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg hw]

lemma hasDerivAt_ofReal' (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := by
  simpa using (hasDerivAt_id u).ofReal_comp

/-- The residue theorem for `1/(s - a)` on a rectangle containing `a` in its interior. -/
theorem rectInt_inv {x₁ x₂ y₁ y₂ : ℝ} {a : ℂ} (h1 : x₁ < a.re) (h2 : a.re < x₂) (h3 : y₁ < a.im)
    (h4 : a.im < y₂) :
    rectInt (fun s => (s - a)⁻¹) x₁ x₂ y₁ y₂ = 2 * Real.pi * I := by
  unfold rectInt
  -- horizontal edges
  have hhor : ∀ y : ℝ, y ≠ a.im → ∫ x in x₁..x₂, ((x:ℂ) + y * I - a)⁻¹ =
      Complex.log (x₂ + y * I - a) - Complex.log (x₁ + y * I - a) := by
    intro y hy
    have := integral_inv_of_slit (g := fun x : ℝ => (x:ℂ) + y * I - a) (g' := 1) (u₁ := x₁)
      (u₂ := x₂) (fun u => ((hasDerivAt_ofReal' u).add_const ((y:ℂ) * I)).sub_const a)
      (fun u _ => mem_slitPlane_iff.mpr (Or.inr (by simpa [sub_eq_zero] using hy)))
    simpa [one_div] using this
  have hb := hhor y₁ h3.ne
  have ht := hhor y₂ h4.ne'
  -- right edge
  have hr : ∫ y in y₁..y₂, ((x₂:ℂ) + y * I - a)⁻¹ =
      -I * (Complex.log (x₂ + y₂ * I - a) - Complex.log (x₂ + y₁ * I - a)) := by
    have := integral_inv_of_slit (g := fun y : ℝ => (x₂:ℂ) + y * I - a) (g' := I) (u₁ := y₁)
      (u₂ := y₂) (fun u => (((hasDerivAt_ofReal' u).mul_const I).const_add (x₂:ℂ)).sub_const a
        |>.congr_deriv (one_mul I))
      (fun u _ => mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)))
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [← mul_div_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], one_div]
  -- left edge
  have hl : ∫ y in y₁..y₂, ((x₁:ℂ) + y * I - a)⁻¹ =
      -I * (Complex.log (-((x₁:ℂ) + y₂ * I - a)) - Complex.log (-((x₁:ℂ) + y₁ * I - a))) := by
    have := integral_inv_of_slit (g := fun y : ℝ => -((x₁:ℂ) + y * I - a)) (g' := -I) (u₁ := y₁)
      (u₂ := y₂) (fun u => ((((hasDerivAt_ofReal' u).mul_const I).const_add (x₁:ℂ)).sub_const a).neg
        |>.congr_deriv (by ring))
      (fun u _ => mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)))
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    have hne : (x₁:ℂ) + y * I - a ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    field_simp
    rw [I_sq, neg_neg]
  have hw2 : 0 < ((x₁:ℂ) + y₂ * I - a).im := by simp; linarith
  have hw1 : ((x₁:ℂ) + y₁ * I - a).im < 0 := by simp; linarith
  have e1 := log_sub_log_neg_of_im_pos hw2
  have e2 := log_neg_sub_log_of_im_neg hw1
  simp only
  rw [hb, ht, hr, hl]
  linear_combination e1 + e2 - (Complex.log (x₂ + y₂ * I - a) - Complex.log (x₂ + y₁ * I - a)
    - (Complex.log (-((x₁:ℂ) + y₂ * I - a)) - Complex.log (-((x₁:ℂ) + y₁ * I - a)))) * I_sq

/-- The residue theorem for `D(s)/(s - a)` with `D` holomorphic near the closed rectangle. -/
theorem rectInt_mul_inv {x₁ x₂ y₁ y₂ : ℝ} {a : ℂ} (h1 : x₁ < a.re) (h2 : a.re < x₂)
    (h3 : y₁ < a.im) (h4 : a.im < y₂) {D : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hrect : [[x₁, x₂]] ×ℂ [[y₁, y₂]] ⊆ V) (hD : DifferentiableOn ℂ D V) :
    rectInt (fun s => D s * (s - a)⁻¹) x₁ x₂ y₁ y₂ = 2 * Real.pi * I * D a := by
  have haV : a ∈ V := hrect (by
    rw [mem_reProdIm]
    exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨h1.le, h2.le⟩), Set.mem_uIcc.mpr (Or.inl ⟨h3.le, h4.le⟩)⟩)
  have hdsl : DifferentiableOn ℂ (dslope D a) V := (differentiableOn_dslope (hV.mem_nhds haV)).mpr hD
  have hbd : ∀ s : ℂ, (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) → s ≠ a := by
    rintro s hs rfl
    rcases hs with h | h | h | h <;> linarith
  have hmemV : ∀ s : ℂ, s.re ∈ uIcc x₁ x₂ → s.im ∈ uIcc y₁ y₂ → s ∈ V := fun s h1 h2 =>
    hrect (by rw [mem_reProdIm]; exact ⟨h1, h2⟩)
  have hcongr : rectInt (fun s => D s * (s - a)⁻¹) x₁ x₂ y₁ y₂ =
      rectInt (fun s => dslope D a s + D a * (s - a)⁻¹) x₁ x₂ y₁ y₂ := by
    refine rectInt_congr (fun s _ _ hs => ?_)
    have hsa : s - a ≠ 0 := sub_ne_zero.mpr (hbd s hs)
    rw [dslope_of_ne _ (hbd s hs), slope_def_field]
    field_simp
    ring
  have hc1 : BdryCont (dslope D a) x₁ x₂ y₁ y₂ :=
    BdryCont.of_forall fun s h1 h2 => (hdsl.differentiableAt (hV.mem_nhds (hmemV s h1 h2))).continuousAt
  have hc2 : BdryCont (fun s => D a * (s - a)⁻¹) x₁ x₂ y₁ y₂ :=
    BdryCont.of_bdry fun s _ _ hs =>
      continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (hbd s hs)))
  rw [hcongr, rectInt_add hc1 hc2, rectInt_const_mul, rectInt_inv h1 h2 h3 h4,
    rectInt_eq_zero (hdsl.mono hrect)]
  ring

end VonKoch

end

-- ===== VK4Zeta.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric

namespace VonKoch

open ZetaAux ArithmeticFunction

/-- `F(s) = -ζ'(s)/ζ(s)`, written via the entire function `h(s) = (s-1)ζ(s)`. -/
def Fh (s : ℂ) : ℂ := (s - 1)⁻¹ - deriv zetaMulSubOne s / zetaMulSubOne s

/-! ### Upper and lower bounds for `h(s) = (s-1)ζ(s)` -/

lemma norm_mellinK_fract_le {s : ℂ} (hs : 0 < s.re) :
    ‖LandauMellin.mellinK Int.fract 0 s‖ ≤ 1 / s.re := by
  rw [mellinK_fract_eq]
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  calc ‖∫ x in Ioi (1:ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ∫ x in Ioi (1:ℝ), x ^ (-s.re - 1) := by
        apply norm_integral_le_of_norm_le hint
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx' : (0:ℝ) < x := lt_trans zero_lt_one hx
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx']
        simp only [sub_re, neg_re, one_re]
        have h1 : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
          exact (Int.fract_lt_one x).le
        have h2 : 0 ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hx'.le _
        calc ‖((Int.fract x : ℝ) : ℂ)‖ * x ^ (-s.re - 1) ≤ 1 * x ^ (-s.re - 1) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = _ := one_mul _
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        have : -s.re - 1 + 1 = -s.re := by ring
        rw [this, div_neg, neg_div, neg_neg]

lemma norm_zetaMulSubOne_le {s : ℂ} (hs : 0 < s.re) :
    ‖zetaMulSubOne s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [zetaMulSubOne_eq_integral hs]
  calc ‖s - s * (s - 1) * LandauMellin.mellinK Int.fract 0 s‖
      ≤ ‖s‖ + ‖s * (s - 1) * LandauMellin.mellinK Int.fract 0 s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        rw [norm_mul, norm_mul]
        gcongr
        exact norm_mellinK_fract_le hs
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

lemma norm_ofReal_add_mul_I_le (σ t : ℝ) : ‖(σ : ℂ) + t * I‖ ≤ |σ| + |t| := by
  calc ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = |σ| + |t| := by simp

lemma norm_zetaMulSubOne_le_of_mem {t : ℝ} {z : ℂ} (hz : ‖z - (3/2 + t * I)‖ ≤ 11/8) :
    ‖zetaMulSubOne z‖ ≤ 9 * (|t| + 3) ^ 2 := by
  have hre : 1/8 ≤ z.re := by
    have h1 := Complex.abs_re_le_norm (z - (3/2 + t * I))
    simp at h1
    have h2 := (abs_le.mp (h1.trans hz)).1
    linarith
  have hz0 : 0 < z.re := by linarith
  have hc : ‖((3/2 : ℝ) : ℂ) + t * I‖ ≤ 3/2 + |t| := by
    have := norm_ofReal_add_mul_I_le (3/2) t
    rwa [abs_of_pos (by norm_num : (0:ℝ) < 3/2)] at this
  have hc1 : ‖((1/2 : ℝ) : ℂ) + t * I‖ ≤ 1/2 + |t| := by
    have := norm_ofReal_add_mul_I_le (1/2) t
    rwa [abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at this
  have hz1 : ‖z‖ ≤ |t| + 3 := by
    have := norm_le_norm_add_norm_sub' z (((3/2 : ℝ) : ℂ) + t * I)
    have e : z - (((3/2 : ℝ) : ℂ) + t * I) = z - (3/2 + t * I) := by push_cast; ring
    rw [e] at this
    linarith
  have hz2 : ‖z - 1‖ ≤ |t| + 3 := by
    have := norm_le_norm_add_norm_sub' (z - 1) (((1/2 : ℝ) : ℂ) + t * I)
    have e : z - 1 - (((1/2 : ℝ) : ℂ) + t * I) = z - (3/2 + t * I) := by push_cast; ring
    rw [e] at this
    linarith
  have ht : 0 ≤ |t| := abs_nonneg t
  calc ‖zetaMulSubOne z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := norm_zetaMulSubOne_le hz0
    _ ≤ (|t| + 3) + (|t| + 3) * (|t| + 3) / (1/8) := by
        gcongr
    _ ≤ 9 * (|t| + 3) ^ 2 := by
        rw [div_div_eq_mul_div, div_one]
        nlinarith

/-- `|h(3/2 + it)|` is bounded below uniformly in `t`. -/
lemma exists_lower_bound_zetaMulSubOne :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ ‖zetaMulSubOne (3/2 + t * I)‖ := by
  set M : ℝ := ∑' n, ‖LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) (3/2 : ℂ) n‖ with hM
  have key : ∀ t : ℝ, 1 ≤ ‖riemannZeta (3/2 + t * I)‖ * M := by
    intro t
    set s : ℂ := 3/2 + t * I with hs
    have hsre : 1 < s.re := by rw [hs]; simp; norm_num
    have h1 := LSeries_one_mul_Lseries_moebius hsre
    rw [LSeries_one_eq_riemannZeta hsre] at h1
    have hsum : Summable fun n => ‖LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ :=
      (LSeriesSummable_moebius_iff.mpr hsre).norm
    have h2 : ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖ ≤ M := by
      calc ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖
          ≤ ∑' n, ‖LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ :=
            norm_tsum_le_tsum_norm hsum
        _ = M := by
            rw [hM]
            congr 1; funext n
            rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
            simp [hs]
    calc (1:ℝ) = ‖riemannZeta s * LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖ := by
          rw [h1, norm_one]
      _ = ‖riemannZeta s‖ * ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖ := norm_mul _ _
      _ ≤ ‖riemannZeta s‖ * M := by gcongr
  have hMpos : 0 < M := by
    have h0 := key 0
    have hM0 : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
    rcases eq_or_lt_of_le hM0 with h | h
    · rw [← h, mul_zero] at h0; linarith
    · exact h
  refine ⟨1 / (2 * M), by positivity, fun t => ?_⟩
  set s : ℂ := 3/2 + t * I with hs
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hs] at this; simp at this; norm_num at this
  rw [zetaMulSubOne_of_ne hs1, norm_mul]
  have hsub : 1/2 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [hs] at this; simp at this; norm_num at this
    rw [hs]; linarith
  have hz := key t
  rw [← hs] at hz
  have hzpos : 1 / M ≤ ‖riemannZeta s‖ := by
    rw [div_le_iff₀ hMpos]; exact hz
  calc 1 / (2 * M) = (1/2) * (1 / M) := by field_simp
    _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := by
        apply mul_le_mul hsub hzpos (by positivity) (norm_nonneg _)

/-- `F = L(Λ, ·)` on the half-plane of absolute convergence. -/
lemma Fh_eq_LSeries {s : ℂ} (hs : 1 < s.re) : Fh s = LSeries (fun n => (Λ n : ℂ)) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, Fh,
    PsiOscillation.deriv_zetaMulSubOne hs1, zetaMulSubOne_of_ne hs1]
  field_simp
  ring

/-! ### Consequences of the Riemann hypothesis for the zeros of `h` -/

lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact (Real.exp_one_lt_d9.trans (by norm_num)).le

lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x :=
  one_le_log_three.trans (Real.log_le_log (by norm_num) hx)

lemma re_eq_half_of_zero (hRH : RiemannHypothesis) {u : ℂ} (hu : zetaMulSubOne u = 0)
    (hre : 0 < u.re) : u.re = 1 / 2 := by
  have hu1 : u ≠ 1 := by
    intro h; rw [h, zetaMulSubOne_one] at hu; exact one_ne_zero hu
  have hζ : riemannZeta u = 0 := by
    rw [zetaMulSubOne_of_ne hu1] at hu
    rcases mul_eq_zero.mp hu with h | h
    · exact absurd (sub_eq_zero.mp h) hu1
    · exact h
  refine hRH u hζ ?_ hu1
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp at this
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma analyticOrderAt_zetaMulSubOne_ne_top (u : ℂ) : analyticOrderAt zetaMulSubOne u ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ zetaMulSubOne univ := fun z _ =>
    differentiable_zetaMulSubOne.analyticAt z
  refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 2) (mem_univ _)
    (mem_univ _) ?_
  rw [(han 2 (mem_univ _)).analyticOrderAt_eq_zero.mpr
    (zetaMulSubOne_ne_zero_of_one_le_re (by norm_num))]
  simp

lemma one_le_order_of_zero {u : ℂ} (hu : zetaMulSubOne u = 0) :
    1 ≤ analyticOrderNatAt zetaMulSubOne u :=
  (analyticOrderNatAt_pos_iff (differentiable_zetaMulSubOne.analyticAt u)
    (analyticOrderAt_zetaMulSubOne_ne_top u)).mpr hu

/-- Landau's lemma for `h(s) = (s-1)ζ(s)` at the centers `3/2 + it`. -/
theorem landau_h : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ∃ S : Finset ℂ,
    (∀ u ∈ S, u ∈ closedBall ((3/2 : ℂ) + t * I) (13/10) ∧ zetaMulSubOne u = 0) ∧
    (∀ u ∈ closedBall ((3/2 : ℂ) + t * I) (13/10), zetaMulSubOne u = 0 → u ∈ S) ∧
    (∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℝ)) ≤ A * Real.log (|t| + 3) ∧
    ∀ z ∈ closedBall ((3/2 : ℂ) + t * I) (5/4), zetaMulSubOne z ≠ 0 →
      ‖deriv zetaMulSubOne z / zetaMulSubOne z -
        ∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℂ) / (z - u)‖ ≤
          A * Real.log (|t| + 3) := by
  obtain ⟨K, hK, hland⟩ := landau_logDeriv (r := 13/10) (R := 11/8) (a := 5/4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₀, hc₀, hlow⟩ := exists_lower_bound_zetaMulSubOne
  set A₀ : ℝ := |Real.log (9 / c₀)| + 2 with hA₀
  have hA₀pos : 0 < A₀ := by positivity
  have hlogRr : 0 < Real.log ((11/8 : ℝ) / (13/10)) := Real.log_pos (by norm_num)
  refine ⟨max (A₀ / Real.log ((11/8 : ℝ) / (13/10))) (K * (A₀ + 1)),
    lt_max_of_lt_left (div_pos hA₀pos hlogRr), fun t => ?_⟩
  set c : ℂ := (3/2 : ℂ) + t * I with hc
  set B : ℝ := 9 * (|t| + 3) ^ 2 with hBdef
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hB : 1 ≤ B := by rw [hBdef]; nlinarith
  have hf : AnalyticOnNhd ℂ zetaMulSubOne (closedBall c (11/8)) := fun z _ =>
    differentiable_zetaMulSubOne.analyticAt z
  have hfc : zetaMulSubOne c ≠ 0 := zetaMulSubOne_ne_zero_of_one_le_re (by rw [hc]; simp; norm_num)
  have hfB : ∀ z ∈ sphere c (11/8), ‖zetaMulSubOne z‖ ≤ B := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    exact norm_zetaMulSubOne_le_of_mem hz.le
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := hland zetaMulSubOne c B hB hf hfc hfB
  set ℓ := Real.log (|t| + 3) with hℓdef
  have hℓ : 1 ≤ ℓ := one_le_log_of_three_le (by linarith)
  have hL : Real.log (B / ‖zetaMulSubOne c‖) ≤ A₀ * ℓ := by
    have hpos : 0 < ‖zetaMulSubOne c‖ := norm_pos_iff.mpr hfc
    have h1 : B / ‖zetaMulSubOne c‖ ≤ B / c₀ :=
      div_le_div_of_nonneg_left (by positivity) hc₀ (hlow t)
    have h2 : Real.log (B / ‖zetaMulSubOne c‖) ≤ Real.log (B / c₀) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (B / c₀) = Real.log (9 / c₀) + 2 * ℓ := by
      rw [show B / c₀ = (9 / c₀) * (|t| + 3) ^ 2 by rw [hBdef]; ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have h4 : Real.log (9 / c₀) ≤ |Real.log (9 / c₀)| * ℓ :=
      le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hℓ)
    rw [hA₀]; nlinarith
  refine ⟨S, hS1, hS2, ?_, ?_⟩
  · calc (∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℝ))
        ≤ Real.log (B / ‖zetaMulSubOne c‖) / Real.log ((11/8 : ℝ) / (13/10)) := hS3
      _ ≤ A₀ * ℓ / Real.log ((11/8 : ℝ) / (13/10)) := div_le_div_of_nonneg_right hL hlogRr.le
      _ = (A₀ / Real.log ((11/8 : ℝ) / (13/10))) * ℓ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · intro z hz hz0
    calc _ ≤ K * (Real.log (B / ‖zetaMulSubOne c‖) + 1) := hS4 z hz hz0
      _ ≤ K * (A₀ * ℓ + ℓ) := by gcongr
      _ = (K * (A₀ + 1)) * ℓ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

lemma mem_closedBall_of_re_half {t : ℝ} {u : ℂ} (hre : u.re = 1 / 2) (him : |u.im - t| ≤ 4/5) :
    u ∈ closedBall ((3/2 : ℂ) + t * I) (13/10) := by
  rw [mem_closedBall, dist_eq_norm]
  have hsq : ‖u - ((3/2 : ℂ) + t * I)‖ ^ 2 ≤ (13/10) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, sub_im, add_im, mul_im, hre]
    have h1 : (u.im - t) ^ 2 ≤ (4/5) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
    norm_num at h1 ⊢
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

lemma re_pos_of_mem_S {t : ℝ} {u : ℂ} (hu : u ∈ closedBall ((3/2 : ℂ) + t * I) (13/10)) :
    0 < u.re := by
  rw [mem_closedBall, dist_eq_norm] at hu
  have h1 := Complex.abs_re_le_norm (u - ((3/2 : ℂ) + t * I))
  simp at h1
  have h2 := (abs_le.mp (h1.trans hu)).1
  linarith

lemma norm_sum_div_le {S : Finset ℂ} {z : ℂ} {d : ℝ} (hd : 0 < d)
    (hS : ∀ u ∈ S, d ≤ ‖z - u‖) (m : ℂ → ℕ) :
    ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ (∑ u ∈ S, (m u : ℝ)) / d := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (hS u hu)

/-- Under RH: for every `y` there is a height `T ∈ [y, y+1]` at distance `≥ δ` from all
ordinates of zeros, with `1/δ = O(log y)`. -/
theorem good_height (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, ∃ T ∈ Icc y (y + 1),
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 1 / δ ≤ A * Real.log (|y| + 4) ∧
    ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T| := by
  classical
  obtain ⟨A, hA, hland⟩ := landau_h
  refine ⟨8 * A + 4, by positivity, fun y => ?_⟩
  obtain ⟨S₁, hS₁1, hS₁2, hS₁3, -⟩ := hland y
  obtain ⟨S₂, hS₂1, hS₂2, hS₂3, -⟩ := hland (y + 1)
  set Z := S₁ ∪ S₂ with hZ
  set N : ℕ := Z.card with hN
  set δ : ℝ := 1 / (4 * ((N:ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hcard : ∀ S : Finset ℂ, (∀ u ∈ S, zetaMulSubOne u = 0) →
      (S.card : ℝ) ≤ ∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℝ) := by
    intro S hS
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    exact_mod_cast one_le_order_of_zero (hS u hu)
  have hNle : (N : ℝ) ≤ A * Real.log (|y| + 3) + A * Real.log (|y + 1| + 3) := by
    calc (N : ℝ) ≤ (S₁.card : ℝ) + S₂.card := by exact_mod_cast Finset.card_union_le S₁ S₂
      _ ≤ _ := add_le_add ((hcard S₁ fun u hu => (hS₁1 u hu).2).trans hS₁3)
          ((hcard S₂ fun u hu => (hS₂1 u hu).2).trans hS₂3)
  -- the bad set has measure `< 1`
  set Bad : Set ℝ := ⋃ u ∈ Z, Ioo (u.im - δ) (u.im + δ) with hBad
  have hmeas : volume Bad < volume (Icc y (y + 1)) := by
    have h1 : volume Bad ≤ ∑ u ∈ Z, volume (Ioo (u.im - δ) (u.im + δ)) :=
      measure_biUnion_finset_le Z _
    have h2 : ∑ u ∈ Z, volume (Ioo (u.im - δ) (u.im + δ)) = N * ENNReal.ofReal (2 * δ) := by
      simp only [Real.volume_Ioo, show ∀ a : ℝ, a + δ - (a - δ) = 2 * δ from fun a => by ring,
        Finset.sum_const, nsmul_eq_mul, hN]
    have h3 : (N : ENNReal) * ENNReal.ofReal (2 * δ) = ENNReal.ofReal (N * (2 * δ)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    rw [Real.volume_Icc, show y + 1 - y = 1 by ring]
    calc volume Bad ≤ ENNReal.ofReal (N * (2 * δ)) := by rw [← h3, ← h2]; exact h1
      _ < ENNReal.ofReal 1 := by
          rw [ENNReal.ofReal_lt_ofReal_iff one_pos, hδ]
          have : (0:ℝ) ≤ N := Nat.cast_nonneg N
          rw [show (N:ℝ) * (2 * (1 / (4 * ((N:ℝ) + 1)))) = N / (2 * (N + 1)) by field_simp; ring,
            div_lt_one (by positivity)]
          linarith
  have hnot : ¬ Icc y (y + 1) ⊆ Bad := fun h => absurd (measure_mono h) (not_le.mpr hmeas)
  obtain ⟨T, hT, hTB⟩ := not_subset.mp hnot
  refine ⟨T, hT, δ, hδ0, ?_, ?_, ?_⟩
  · rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0:ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  · have hl1 : Real.log (|y| + 3) ≤ Real.log (|y| + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hl2 : Real.log (|y + 1| + 3) ≤ Real.log (|y| + 4) :=
      Real.log_le_log (by positivity) (by
        have : |y + 1| ≤ |y| + 1 := by simpa using abs_add_le y 1
        linarith)
    have hl3 : 1 ≤ Real.log (|y| + 4) := one_le_log_of_three_le (by linarith [abs_nonneg y])
    rw [hδ, one_div_one_div]
    nlinarith
  · intro u hu hre
    by_contra hlt
    push Not at hlt
    have hhalf := re_eq_half_of_zero hRH hu hre
    by_cases huZ : u ∈ Z
    · apply hTB
      rw [hBad, mem_iUnion₂]
      refine ⟨u, huZ, ?_, ?_⟩ <;> [linarith [(abs_lt.mp hlt).2]; linarith [(abs_lt.mp hlt).1]]
    · have hδ4 : δ ≤ 1/4 := by
        rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (0:ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      have h1 : ¬ |u.im - y| ≤ 4/5 := fun h =>
        huZ (Finset.mem_union_left _ (hS₁2 u (mem_closedBall_of_re_half hhalf h) hu))
      have h2 : ¬ |u.im - (y + 1)| ≤ 4/5 := fun h =>
        huZ (Finset.mem_union_right _ (hS₂2 u (mem_closedBall_of_re_half hhalf h) hu))
      have hT1 := hT.1
      have hT2 := hT.2
      have hl := (abs_lt.mp hlt)
      rcases le_or_gt u.im (y + 1/2) with h | h
      · exact h1 (abs_le.mpr ⟨by linarith, by linarith⟩)
      · exact h2 (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Under RH, at a good height `T` the function `F` is `O(log T / δ)` on the horizontal segment. -/
theorem Fh_horizontal : ∃ A : ℝ, 0 < A ∧ ∀ T δ : ℝ, 1 ≤ |T| → 0 < δ →
    δ ≤ 1 → (∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) →
    ∀ σ ∈ Icc (1/4 : ℝ) (3/2), zetaMulSubOne (σ + T * I) ≠ 0 ∧
      ‖Fh (σ + T * I)‖ ≤ A * Real.log (|T| + 3) / δ := by
  obtain ⟨A, hA, hland⟩ := landau_h
  refine ⟨2 * A + 1, by positivity, fun T δ hT hδ hδ1 hgood σ hσ => ?_⟩
  obtain ⟨S, hS1, -, hS3, hS4⟩ := hland T
  set z : ℂ := σ + T * I with hz
  have hz0 : zetaMulSubOne z ≠ 0 := by
    intro h
    have := hgood z h (by rw [hz]; simp; linarith [hσ.1])
    rw [hz] at this; simp at this; linarith
  refine ⟨hz0, ?_⟩
  set ℓ := Real.log (|T| + 3) with hℓdef
  have hℓ : 1 ≤ ℓ := one_le_log_of_three_le (by linarith [abs_nonneg T])
  have hzball : z ∈ closedBall ((3/2 : ℂ) + T * I) (5/4) := by
    rw [mem_closedBall, dist_eq_norm, hz]
    have : (σ : ℂ) + T * I - (3/2 + T * I) = ((σ - 3/2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hdist : ∀ u ∈ S, δ ≤ ‖z - u‖ := by
    intro u hu
    have h1 := hgood u (hS1 u hu).2 (re_pos_of_mem_S (hS1 u hu).1)
    have h2 := Complex.abs_im_le_norm (z - u)
    rw [sub_im, hz] at h2
    simp at h2
    rw [abs_sub_comm] at h2
    linarith
  have hsum := norm_sum_div_le hδ hdist (fun u => analyticOrderNatAt zetaMulSubOne u)
  have hlog : ‖deriv zetaMulSubOne z / zetaMulSubOne z‖ ≤ A * ℓ + A * ℓ / δ := by
    have h1 := hS4 z hzball hz0
    calc ‖deriv zetaMulSubOne z / zetaMulSubOne z‖
        ≤ ‖deriv zetaMulSubOne z / zetaMulSubOne z -
            ∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℂ) / (z - u)‖ +
          ‖∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℂ) / (z - u)‖ := norm_le_norm_sub_add _ _
      _ ≤ A * ℓ + (A * ℓ) / δ := by
          gcongr
          exact hsum.trans (div_le_div_of_nonneg_right hS3 hδ.le)
  have hinv : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have h1 := Complex.abs_im_le_norm (z - 1)
    rw [hz] at h1; simp at h1
    exact inv_le_one_of_one_le₀ (hT.trans h1)
  have hAℓ : A * ℓ ≤ A * ℓ / δ := le_div_self (by positivity) hδ hδ1
  have h1ℓ : 1 ≤ ℓ / δ := hℓ.trans (le_div_self (by linarith) hδ hδ1)
  calc ‖Fh z‖ ≤ ‖(z - 1)⁻¹‖ + ‖deriv zetaMulSubOne z / zetaMulSubOne z‖ := norm_sub_le _ _
    _ ≤ 1 + (A * ℓ + A * ℓ / δ) := add_le_add hinv hlog
    _ ≤ (2 * A + 1) * ℓ / δ := by
        rw [show (2 * A + 1) * ℓ / δ = 2 * (A * ℓ / δ) + ℓ / δ by ring]
        linarith

end VonKoch

end

-- ===== VK5Explicit.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace VonKoch

open ZetaAux

/-! ### Factorization of an analytic function on a compact set -/

theorem factorization {f : ℂ → ℂ} {U : Set ℂ} (hUc : IsCompact U) (hUp : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) {c : ℂ} (hcU : U ∈ 𝓝 c) (hfc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (g : ℂ → ℂ), (∀ u ∈ Z, u ∈ U ∧ f u = 0) ∧ (∀ u ∈ U, f u = 0 → u ∈ Z) ∧
      AnalyticOnNhd ℂ g U ∧ (∀ u ∈ U, g u ≠ 0) ∧
      EqOn f (fun z => (∏ u ∈ Z, (z - u) ^ analyticOrderNatAt f u) * g z) U := by
  classical
  have hcU' : c ∈ U := mem_of_mem_nhds hcU
  have hconn : IsConnected U := ⟨⟨c, hcU'⟩, hUp⟩
  have hord : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    rw [← hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hconn]
    refine ⟨⟨c, hcU'⟩, ?_⟩
    rw [(hf c hcU').meromorphicOrderAt_eq, (hf c hcU').analyticOrderAt_eq_zero.mpr hfc]
    simp
  have hord' : ∀ u ∈ U, analyticOrderAt f u ≠ ⊤ := by
    intro u hu h
    apply hord ⟨u, hu⟩
    rw [(hf u hu).meromorphicOrderAt_eq, h]
    rfl
  have hfin : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport hUc
  obtain ⟨g, hg, hg0, hfg⟩ := hf.meromorphicOn.extract_zeros_poles hord hfin
  set D := MeromorphicOn.divisor f U with hDdef
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hmdef
  set Sall : Finset ℂ := hfin.toFinset with hSall
  have hSallU : ∀ u ∈ Sall, u ∈ U := fun u hu =>
    D.supportWithinDomain (by simpa [hSall] using hu)
  have hSall_iff : ∀ u ∈ U, u ∈ Sall ↔ f u = 0 := by
    intro u hu
    rw [hSall, Set.Finite.mem_toFinset, Function.mem_support, hDdef,
      divisor_eq_natOrder hf hu (hord' u hu), ← analyticOrderNatAt_pos_iff (hf u hu) (hord' u hu)]
    constructor
    · intro h; exact Nat.pos_of_ne_zero (by exact_mod_cast h)
    · intro h; exact_mod_cast h.ne'
  set P : ℂ → ℂ := fun z => ∏ u ∈ Sall, (z - u) ^ m u with hPdef
  have hPdiff : Differentiable ℂ P := by rw [hPdef]; fun_prop
  have hfactor : ∀ z, ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z = P z * g z := by
    intro z
    have hfs : Function.HasFiniteSupport (⇑D) := hfin
    rw [Pi.smul_apply', Function.FactorizedRational.finprod_eq_fun hfs, smul_eq_mul]
    beta_reduce
    have hsub : Function.mulSupport (fun u => (z - u) ^ D u) ⊆ (Sall : Set ℂ) := by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [hSall, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0, zpow_zero]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    have hcongr : ∏ u ∈ Sall, (z - u) ^ D u = ∏ u ∈ Sall, (z - u) ^ m u := by
      refine Finset.prod_congr rfl (fun u hu => ?_)
      rw [hDdef, divisor_eq_natOrder hf (hSallU u hu) (hord' u (hSallU u hu)), zpow_natCast]
    rw [hcongr]
  have hPGan : AnalyticOnNhd ℂ (fun z => P z * g z) U := by
    intro z hz
    exact (hPdiff.analyticAt z).mul (hg z hz)
  have hEq : EqOn f (fun z => P z * g z) U := by
    refine hf.eqOn_of_preconnected_of_frequently_eq hPGan hUp hcU' ?_
    have hmem := (mem_codiscreteWithin.mp hfg) c hcU'
    have h1 : (U \ {z | f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z})ᶜ ∈ 𝓝[≠] c :=
      (disjoint_principal_right.mp hmem)
    have h2 : U ∈ 𝓝[≠] c := mem_nhdsWithin_of_mem_nhds hcU
    have h3 : ∀ᶠ z in 𝓝[≠] c, f z = P z * g z := by
      filter_upwards [h1, h2] with z hz1 hz2
      have : z ∈ {z | f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z} := by
        by_contra hcon; exact hz1 ⟨hz2, hcon⟩
      exact (show f z = ((∏ᶠ u, (fun x => x - u) ^ D u) • g) z from this).trans (hfactor z)
    exact h3.frequently
  refine ⟨Sall, g, fun u hu => ⟨hSallU u hu, (hSall_iff u (hSallU u hu)).mp hu⟩,
    fun u hu hfu => (hSall_iff u hu).mpr hfu, hg, fun u hu => hg0 ⟨u, hu⟩, hEq⟩

/-- Logarithmic derivative of a factorization. -/
lemma logDeriv_factor {f g : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {s : ℂ}
    (hev : f =ᶠ[𝓝 s] fun z => (∏ u ∈ Z, (z - u) ^ m u) * g z) (hfs : f s ≠ 0)
    (hg : DifferentiableAt ℂ g s) :
    deriv f s / f s = (∑ u ∈ Z, (m u : ℂ) / (s - u)) + deriv g s / g s := by
  set P : ℂ → ℂ := fun z => ∏ u ∈ Z, (z - u) ^ m u with hPdef
  have hfsPG : f s = P s * g s := hev.eq_of_nhds
  have hPs0 : P s ≠ 0 := fun h => hfs (by rw [hfsPG, h, zero_mul])
  have hgs0 : g s ≠ 0 := fun h => hfs (by rw [hfsPG, h, mul_zero])
  have hPdiff : Differentiable ℂ P := by rw [hPdef]; fun_prop
  have h1 : deriv f s / f s = logDeriv (fun w => P w * g w) s := by
    rw [← logDeriv_apply]; exact (logDeriv_congr_nhds hev).eq_of_nhds
  rw [h1, logDeriv_mul s hPs0 hgs0 (hPdiff s) hg, logDeriv_apply g s]
  congr 1
  have hfac : ∀ u ∈ Z, (s - u) ^ m u ≠ 0 := by
    intro u hu
    exact Finset.prod_ne_zero_iff.mp (show (∏ u ∈ Z, (s - u) ^ m u) ≠ 0 from hPs0) u hu
  rw [show P = fun w => ∏ u ∈ Z, (w - u) ^ m u from rfl,
    logDeriv_prod hfac (fun u _ => by fun_prop)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [logDeriv_fun_pow (by fun_prop) (m u), logDeriv_apply]
  simp only [deriv_sub_const, deriv_id'']
  ring

/-! ### The explicit formula on a rectangle -/

lemma convex_Icc_reProdIm (a b c d : ℝ) : Convex ℝ (Icc a b ×ℂ Icc c d) := by
  have := convex_convexHull ℝ (Icc a b ×ℂ Icc c d)
  rwa [convexHull_reProdIm, (convex_Icc a b).convexHull_eq, (convex_Icc c d).convexHull_eq] at this

end VonKoch

end

-- ===== VK6Final.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace VonKoch

open ZetaAux ArithmeticFunction

/-! ### The difference kernel `D(s) = ((X+H)^{s+1} - X^{s+1}) / (s(s+1))` -/

/-! ### Continuity of `F` -/

/-! ### Perron's formula for the difference kernel -/

/-! ### Differencing `ψ₁` -/

/-! ### Bounds for the pieces of the contour -/

/-- `∑ Λ(n) n^{-3/2}`, a bound for `|F(3/2 + it)|`. -/
def MΛ : ℝ := ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3/2 : ℂ) n‖

lemma MΛ_nonneg : 0 ≤ MΛ := tsum_nonneg fun _ => norm_nonneg _

end VonKoch

end

-- ===== LF3Digamma.lean =====
section

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set

namespace LandauRH

/-! ### Locally uniform convergence of Euler's sequence `GammaSeq` -/

/-- `f_n(x) = (1 - x/n)^n` on `(0, n]`, zero elsewhere. -/
def fseq (n : ℕ) (x : ℝ) : ℝ := indicator (Ioc 0 (n : ℝ)) (fun x : ℝ => (1 - x / n) ^ n) x

lemma fseq_nonneg (n : ℕ) (x : ℝ) : 0 ≤ fseq n x := by
  unfold fseq
  by_cases hx : x ∈ Ioc 0 (n : ℝ)
  · rw [indicator_of_mem hx]
    have h1 : x / n ≤ 1 := div_le_one_of_le₀ hx.2 (by positivity)
    exact pow_nonneg (by linarith) n
  · rw [indicator_of_notMem hx]

lemma fseq_le_exp (n : ℕ) {x : ℝ} (hx : 0 < x) : fseq n x ≤ Real.exp (-x) := by
  unfold fseq
  by_cases hxn : x ∈ Ioc 0 (n : ℝ)
  · rw [indicator_of_mem hxn]
    exact Real.one_sub_div_pow_le_exp_neg hxn.2
  · rw [indicator_of_notMem hxn]; positivity

lemma tendsto_fseq {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => fseq n x) atTop (𝓝 (Real.exp (-x))) := by
  apply Tendsto.congr'
  · show ∀ᶠ n : ℕ in atTop, (1 - x / n) ^ n = fseq n x
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
    rw [Nat.ceil_le] at hn
    unfold fseq
    rw [indicator_of_mem (show x ∈ Ioc 0 (n:ℝ) from ⟨hx, hn⟩)]
  · convert Real.tendsto_one_add_div_pow_exp (-x) using 1
    ext1 n
    rw [neg_div, ← sub_eq_add_neg]

lemma measurable_fseq (n : ℕ) : Measurable (fseq n) := by
  unfold fseq
  exact Measurable.indicator (f := fun x : ℝ => (1 - x / n) ^ n) (by fun_prop) measurableSet_Ioc

lemma measurable_err (n : ℕ) (a b : ℝ) :
    Measurable (fun x : ℝ => |fseq n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1))) := by
  have h1 := measurable_fseq n
  have h2 : Measurable (fun x : ℝ => Real.exp (-x)) := by fun_prop
  exact ((h1.sub h2).abs).mul (by fun_prop)

lemma integrableOn_rpow_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) (Ioi 0) :=
  Real.GammaIntegral_convergent ha

lemma GammaSeq_eq_integral {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = ∫ x in Ioi (0:ℝ), ((fseq n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  rw [GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ n)]
  have : (fun x : ℝ => ((fseq n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
      indicator (Ioc 0 (n:ℝ)) (fun x : ℝ => (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) := by
    funext x
    unfold fseq
    by_cases hx : x ∈ Ioc 0 (n:ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  rw [this, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

/-- The error `‖GammaSeq s n - Γ(s)‖` is bounded uniformly on vertical strips. -/
lemma norm_GammaSeq_sub_Gamma_le {a b : ℝ} (ha : 0 < a) {s : ℂ} (hs1 : a ≤ s.re)
    (hs2 : s.re ≤ b) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq s n - Gamma s‖ ≤
      ∫ x in Ioi (0:ℝ), |fseq n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hs : 0 < s.re := lt_of_lt_of_le ha hs1
  have hb : 0 < b := lt_of_lt_of_le hs hs2
  rw [GammaSeq_eq_integral hs hn, Gamma_eq_integral hs, GammaIntegral]
  have hG := GammaIntegral_convergent hs
  have hbound : ∀ x ∈ Ioi (0:ℝ), ‖((fseq n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      Real.exp (-x) * x ^ (s.re - 1) := by
    intro x hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fseq_nonneg n x)]
    simp only [sub_re, one_re]
    exact mul_le_mul_of_nonneg_right (fseq_le_exp n hx) (Real.rpow_nonneg hx.le _)
  have hF : IntegrableOn (fun x : ℝ => ((fseq n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    refine Integrable.mono' (Real.GammaIntegral_convergent hs) ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      refine Measurable.mul ?_ ?_
      · exact Complex.measurable_ofReal.comp (measurable_fseq n)
      · exact (measurable_ofReal.pow_const _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hbound x hx
  rw [← integral_sub hF hG]
  have hdom : Integrable (fun x : ℝ => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
      (volume.restrict (Ioi 0)) := by
    have := (integrableOn_rpow_exp ha).add (integrableOn_rpow_exp hb)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  refine norm_integral_le_of_norm_le ?_ ?_
  · refine hdom.mono' ?_ ?_
    · exact (measurable_err n a b).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [abs_sub_comm, abs_of_nonneg (by linarith [fseq_le_exp n hx'])]
      linarith [fseq_nonneg n x]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (0:ℝ) < x := hx
    rw [← sub_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx']
    simp only [sub_re, one_re]
    rw [show ((fseq n x : ℝ) : ℂ) - ((Real.exp (-x) : ℝ) : ℂ) = ((fseq n x - Real.exp (-x) : ℝ) : ℂ)
      by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases le_or_gt x 1 with h | h
    · have : x ^ (s.re - 1) ≤ x ^ (a - 1) := Real.rpow_le_rpow_of_exponent_ge hx' h (by linarith)
      linarith [Real.rpow_nonneg hx'.le (b - 1)]
    · have : x ^ (s.re - 1) ≤ x ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
      linarith [Real.rpow_nonneg hx'.le (a - 1)]

lemma tendsto_err_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ), |fseq n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)))
      atTop (𝓝 0) := by
  have hdom : Integrable (fun x : ℝ => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
      (volume.restrict (Ioi 0)) := by
    have := (integrableOn_rpow_exp ha).add (integrableOn_rpow_exp hb)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have h := tendsto_integral_of_dominated_convergence
    (fun x : ℝ => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
    (F := fun (n : ℕ) (x : ℝ) => |fseq n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)))
    (f := fun _ => (0:ℝ)) (μ := volume.restrict (Ioi 0))
    (fun n => (measurable_err n a b).aestronglyMeasurable)
    hdom
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [abs_sub_comm, abs_of_nonneg (by linarith [fseq_le_exp n hx'])]
      linarith [fseq_nonneg n x])
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (0:ℝ) < x := hx
      have h1 := tendsto_fseq hx'
      have h2 : Tendsto (fun n : ℕ => |fseq n x - Real.exp (-x)|) atTop (𝓝 0) := by
        have := (h1.sub_const (Real.exp (-x))).abs
        simpa using this
      simpa using h2.mul_const (x ^ (a - 1) + x ^ (b - 1)))
  simpa using h

/-- Euler's sequence converges to `Γ` locally uniformly on the right half-plane. -/
theorem tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => GammaSeq s n) Gamma atTop
      {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set a := s₀.re / 2 with ha
  set b := s₀.re + 1 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  refine ⟨{s : ℂ | a < s.re ∧ s.re < b}, ?_, ?_⟩
  · apply mem_nhdsWithin_of_mem_nhds
    refine IsOpen.mem_nhds ?_ ⟨by linarith, by linarith⟩
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · have ht := tendsto_err_zero ha0 hb0
    filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
    intro s hs
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (norm_GammaSeq_sub_Gamma_le ha0 hs.1.le hs.2.le (by omega)) hn

/-! ### The limit formula `ψ(s) = lim (log n - ∑_{j ≤ n} 1/(s+j))` -/

lemma prod_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), (s + j) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun j _ h => ?_)
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma differentiableOn_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun s => GammaSeq s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold GammaSeq
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div ?_ ?_ (prod_ne_zero_of_re_pos hs' n)
  · exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hn')).mul_const _
  · exact DifferentiableAt.fun_finsetProd (fun j _ => by fun_prop)

lemma logDeriv_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z => GammaSeq z n) s =
      Complex.log n - ∑ j ∈ Finset.range (n + 1), 1 / (s + j) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hP := prod_ne_zero_of_re_pos hs n
  have hpow : (n : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hform : (fun z => GammaSeq z n) =
      fun z : ℂ => (n : ℂ) ^ z * (((Nat.factorial n : ℕ) : ℂ) /
        ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) := by
    funext z; unfold GammaSeq; ring
  set P : ℂ → ℂ := fun z => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ)) with hPdef
  have hPd : DifferentiableAt ℂ P s := DifferentiableAt.fun_finsetProd (fun j _ => by fun_prop)
  rw [hform, logDeriv_mul (f := fun z : ℂ => (n : ℂ) ^ z)
    (g := fun z : ℂ => ((Nat.factorial n : ℕ) : ℂ) / P z) s hpow (div_ne_zero hfac hP)
    (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hn'))
    (DifferentiableAt.div (differentiableAt_const _) hPd hP),
    logDeriv_div (f := fun _ : ℂ => ((Nat.factorial n : ℕ) : ℂ)) (g := P) s hfac hP
      (differentiableAt_const _) hPd,
    logDeriv_const, Pi.zero_apply, zero_sub]
  have h1 : logDeriv (fun z => (n : ℂ) ^ z) s = Complex.log n := by
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z => (n : ℂ) ^ z) ((n : ℂ) ^ s * Complex.log n) s := by
      have := (hasDerivAt_id s).const_cpow (c := (n : ℂ)) (Or.inl hn')
      simpa using this
    rw [hd.deriv]
    field_simp
  have h2 : logDeriv P s = ∑ j ∈ Finset.range (n + 1), 1 / (s + j) := by
    have hne : ∀ j ∈ Finset.range (n + 1), s + j ≠ 0 :=
      fun j hj => Finset.prod_ne_zero_iff.mp hP j hj
    rw [logDeriv_prod hne (fun j _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z : ℂ => z + j) 1 s := (hasDerivAt_id s).add_const _
    rw [hd.deriv]
  rw [h1, h2]
  ring

/-- **Gauss' limit formula** for the digamma function on the right half-plane. -/
theorem tendsto_digamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => Complex.log n - ∑ j ∈ Finset.range (n + 1), 1 / (s + j)) atTop
      (𝓝 (digamma s)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderiv := (tendstoLocallyUniformlyOn_GammaSeq.deriv
    (Eventually.mono (eventually_ge_atTop 1) (fun n hn => differentiableOn_GammaSeq (by omega)))
    hU).tendsto_at hs
  have hval := tendstoLocallyUniformlyOn_GammaSeq.tendsto_at hs
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hlim := hderiv.div hval hΓ
  rw [digamma_def, logDeriv_apply]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : n ≠ 0 := by omega
  rw [← logDeriv_GammaSeq hs hn', logDeriv_apply]
  rfl

/-! ### `ψ(s) = log s + O(1)` on the right half-plane -/

lemma norm_inv_sub_inv_le {s : ℂ} (hs : 0 < s.re) {j t : ℝ} (hj : 0 ≤ j) (hjt : j ≤ t)
    (ht : t ≤ j + 1) : ‖1 / (s + j) - 1 / (s + t)‖ ≤ 1 / ‖s + j‖ ^ 2 := by
  have hsj : s + j ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hst : s + t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hnorm : ‖s + j‖ ≤ ‖s + t‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    nlinarith
  have h1 : 1 / (s + j) - 1 / (s + t) = ((t - j : ℝ) : ℂ) / ((s + j) * (s + t)) := by
    field_simp; push_cast; ring
  rw [h1, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hp : 0 < ‖s + j‖ := norm_pos_iff.mpr hsj
  calc (t - j) / (‖s + j‖ * ‖s + t‖) ≤ 1 / (‖s + j‖ * ‖s + j‖) := by
        apply div_le_div₀ zero_le_one (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left hnorm hp.le
    _ = 1 / ‖s + j‖ ^ 2 := by ring

lemma sum_inv_sq_le (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (if j = 0 then (0:ℝ) else 1 / (j:ℝ) ^ 2) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
  have e : ∑ j ∈ Finset.range (n + 1), (if j = 0 then (0:ℝ) else 1 / (j:ℝ) ^ 2) =
      ∑ i ∈ Finset.Ioo 0 (n + 1), ((i:ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr
    · ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega
    · intro j _; rw [one_div]
  rw [e]
  have h2 : (2:ℝ) / ((0:ℕ) + 1) = 2 := by norm_num
  simpa using h

/-- The sum `∑_{j ≤ n} 1/(s+j)` differs from `log(s+n+1) - log s` by a bounded amount. -/
lemma norm_sum_sub_log_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖∑ j ∈ Finset.range (n + 1), 1 / (s + j) - (Complex.log (s + (n + 1 : ℕ)) - Complex.log s)‖
      ≤ 1 / ‖s‖ ^ 2 + 2 := by
  have hcont : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / (s + t)) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have hne : s + t ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact (continuousAt_const.div (continuousAt_const.add
      Complex.continuous_ofReal.continuousAt) hne).continuousWithinAt
  have hlog : ∫ t in (0:ℝ)..((n + 1 : ℕ) : ℝ), 1 / (s + t) =
      Complex.log (s + (n + 1 : ℕ)) - Complex.log s := by
    have := VonKoch.integral_inv_of_slit (g := fun t : ℝ => s + t) (g' := 1) (u₁ := 0)
      (u₂ := ((n + 1 : ℕ) : ℝ))
      (fun u => (VonKoch.hasDerivAt_ofReal' u).const_add s)
      (fun u hu => by
        have hu0 : 0 ≤ u := by
          rcases Set.mem_uIcc.mp hu with h | h <;> linarith [h.1, h.2]
        exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)))
    simpa using this
  have hsplit : ∫ t in (0:ℝ)..((n + 1 : ℕ) : ℝ), 1 / (s + t) =
      ∑ j ∈ Finset.range (n + 1), ∫ t in (j:ℝ)..((j + 1 : ℕ) : ℝ), 1 / (s + t) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (fun k _ => hcont _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    simp
  rw [← hlog, hsplit, ← Finset.sum_sub_distrib]
  calc ‖∑ j ∈ Finset.range (n + 1), (1 / (s + j) - ∫ t in (j:ℝ)..((j + 1 : ℕ) : ℝ), 1 / (s + t))‖
      ≤ ∑ j ∈ Finset.range (n + 1),
          ‖1 / (s + j) - ∫ t in (j:ℝ)..((j + 1 : ℕ) : ℝ), 1 / (s + t)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), 1 / ‖s + j‖ ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
        have e : 1 / (s + j) - ∫ t in (j:ℝ)..((j + 1 : ℕ) : ℝ), 1 / (s + t) =
            ∫ t in (j:ℝ)..((j + 1 : ℕ) : ℝ), (1 / (s + j) - 1 / (s + t)) := by
          rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont _ _ hj0 (by positivity)),
            intervalIntegral.integral_const]
          push_cast; simp
        rw [e]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (j:ℝ))
          (b := ((j + 1 : ℕ) : ℝ)) (C := 1 / ‖s + j‖ ^ 2)
          (f := fun t : ℝ => 1 / (s + j) - 1 / (s + t)) (fun t ht => by
            push_cast at ht
            rw [Set.uIoc_of_le (by linarith)] at ht
            exact norm_inv_sub_inv_le hs hj0 ht.1.le ht.2)
        push_cast at this
        rw [show |(j:ℝ) + 1 - j| = 1 by norm_num, mul_one] at this
        push_cast
        exact this
    _ ≤ ∑ j ∈ Finset.range (n + 1), (if j = 0 then 1 / ‖s‖ ^ 2 else 1 / (j:ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        split_ifs with hj
        · subst hj; simp
        · have hj' : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
          apply one_div_le_one_div_of_le (by positivity)
          apply pow_le_pow_left₀ hj'.le
          have := Complex.abs_re_le_norm (s + (j : ℂ))
          simp only [add_re, natCast_re] at this
          rw [abs_of_pos (by positivity)] at this
          linarith
    _ = 1 / ‖s‖ ^ 2 + ∑ j ∈ Finset.range (n + 1), (if j = 0 then (0:ℝ) else 1 / (j:ℝ) ^ 2) := by
        have e : ∀ j : ℕ, (if j = 0 then 1 / ‖s‖ ^ 2 else 1 / (j:ℝ) ^ 2) =
            (if j = 0 then 1 / ‖s‖ ^ 2 else 0) + (if j = 0 then (0:ℝ) else 1 / (j:ℝ) ^ 2) := by
          intro j; split_ifs <;> simp
        simp_rw [e]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (n + 1)) 0]
        simp
    _ ≤ 1 / ‖s‖ ^ 2 + 2 := by linarith [sum_inv_sq_le n]

/-- `‖ψ(s) - log s‖ ≤ 1/‖s‖² + 2` for `Re s > 0`. -/
theorem norm_digamma_sub_log_le {s : ℂ} (hs : 0 < s.re) :
    ‖digamma s - Complex.log s‖ ≤ 1 / ‖s‖ ^ 2 + 2 := by
  have hlim := tendsto_digamma hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  -- `log(s + n + 1) - log n → 0`
  have hratio : Tendsto (fun n : ℕ => (s + ((n + 1 : ℕ) : ℂ)) / (n : ℂ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (s + 1) / (n : ℂ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (s + 1)
    have h2 : Tendsto (fun n : ℕ => 1 + (s + 1) / (n : ℂ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
    push_cast; ring
  have hlog1 : Tendsto (fun n : ℕ => Complex.log ((s + ((n + 1 : ℕ) : ℂ)) / (n : ℂ))) atTop
      (𝓝 0) := by
    have := (continuousAt_clog (mem_slitPlane_iff.mpr (Or.inl (by norm_num)))).tendsto.comp hratio
    rw [Complex.log_one] at this
    exact this
  have hdiff : Tendsto (fun n : ℕ => Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log n) atTop
      (𝓝 0) := by
    refine hlog1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hne : (s + ((n + 1 : ℕ) : ℂ)) / (n : ℂ) ≠ 0 := by
      refine div_ne_zero ?_ hnC
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : Complex.log (s + ((n + 1 : ℕ) : ℂ)) =
        (Real.log n : ℂ) + Complex.log ((s + ((n + 1 : ℕ) : ℂ)) / (n : ℂ)) := by
      rw [← Complex.log_ofReal_mul hn0 hne]
      congr 1
      push_cast
      field_simp
    have h2 : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [h1, h2]
    ring
  -- conclude
  have hbound : ∀ n : ℕ, ‖(Complex.log n - ∑ j ∈ Finset.range (n + 1), 1 / (s + j)) -
      Complex.log s‖ ≤ ‖Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log n‖ +
        (1 / ‖s‖ ^ 2 + 2) := by
    intro n
    have h := norm_sum_sub_log_le hs n
    calc ‖(Complex.log n - ∑ j ∈ Finset.range (n + 1), 1 / (s + j)) - Complex.log s‖
        = ‖-(Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log n) -
            (∑ j ∈ Finset.range (n + 1), 1 / (s + j) -
              (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log s))‖ := by ring_nf
      _ ≤ ‖-(Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log n)‖ +
            ‖∑ j ∈ Finset.range (n + 1), 1 / (s + j) -
              (Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log s)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_neg]; gcongr
  have hlimL := (hlim.sub_const (Complex.log s)).norm
  have hlimR : Tendsto (fun n : ℕ => ‖Complex.log (s + ((n + 1 : ℕ) : ℂ)) - Complex.log n‖ +
      (1 / ‖s‖ ^ 2 + 2)) atTop (𝓝 (0 + (1 / ‖s‖ ^ 2 + 2))) := by
    have := hdiff.norm.add_const (1 / ‖s‖ ^ 2 + 2)
    simpa using this
  rw [zero_add] at hlimR
  exact le_of_tendsto_of_tendsto' hlimL hlimR hbound

/-- **Digamma bound**: `‖ψ(s)‖ ≤ log(‖s‖ + 2) + 24` for `Re s ≥ 1/4`. -/
theorem norm_digamma_le {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖digamma s‖ ≤ Real.log (‖s‖ + 2) + 24 := by
  have hs0 : 0 < s.re := by linarith
  have h1 := norm_digamma_sub_log_le hs0
  have hns : 1 / 4 ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hnpos : 0 < ‖s‖ := by linarith
  have hlog : ‖Complex.log s‖ ≤ Real.log (‖s‖ + 2) + Real.log 4 + Real.pi := by
    calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖s‖| + |Complex.arg s| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ (Real.log (‖s‖ + 2) + Real.log 4) + Real.pi := by
          gcongr
          · rw [abs_le]
            constructor
            · have : Real.log (1 / 4) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hns
              rw [one_div, Real.log_inv] at this
              have : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
              linarith
            · have : Real.log ‖s‖ ≤ Real.log (‖s‖ + 2) := Real.log_le_log hnpos (by linarith)
              have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
              linarith
          · exact Complex.abs_arg_le_pi s
  have hinv : 1 / ‖s‖ ^ 2 ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlog4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; linarith
  have hpi := Real.pi_lt_d2
  calc ‖digamma s‖ ≤ ‖digamma s - Complex.log s‖ + ‖Complex.log s‖ := norm_le_norm_sub_add _ _
    _ ≤ (1 / ‖s‖ ^ 2 + 2) + (Real.log (‖s‖ + 2) + Real.log 4 + Real.pi) := add_le_add h1 hlog
    _ ≤ Real.log (‖s‖ + 2) + 24 := by linarith

end LandauRH

end

-- ===== LF4Xi.lean =====
section

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace LandauRH

open ZetaAux VonKoch

/-! ### Riemann's `ξ` function -/

/-- `ξ(s) = (s (s - 1) Λ₀(s) + 1) / 2 = s (s - 1) π^{-s/2} Γ(s/2) ζ(s) / 2`. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

lemma differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  have := differentiable_completedZeta₀
  fun_prop

lemma xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma xi_one : xi 1 = 1 / 2 := by unfold xi; ring

lemma xi_zero : xi 0 = 1 / 2 := by unfold xi; ring

lemma xi_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    xi s = s * Gammaℝ s * zetaMulSubOne s / 2 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  by_cases hs1 : s = 1
  · subst hs1; rw [xi_one, zetaMulSubOne_one, Gammaℝ_one]; ring
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaMulSubOne_of_ne hs1, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold xi
  field_simp
  ring

lemma xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  rw [xi_eq_of_re_pos hs0]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hsne (Gammaℝ_ne_zero_of_re_pos hs0))
    (zetaMulSubOne_ne_zero_of_one_le_re hs)) two_ne_zero

lemma xi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp; linarith)

lemma xi_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : xi s = 0 ↔ zetaMulSubOne s = 0 := by
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rw [xi_eq_of_re_pos hs]
  constructor
  · intro h
    rcases mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right two_ne_zero) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hsne
      · exact absurd h (Gammaℝ_ne_zero_of_re_pos hs)
    · exact h
  · intro h; rw [h]; ring

/-- `ξ'(1 - s) = -ξ'(s)`. -/
lemma deriv_xi_one_sub (s : ℂ) : deriv xi (1 - s) = -deriv xi s := by
  have hc : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h1 : HasDerivAt (xi ∘ fun z : ℂ => 1 - z) (deriv xi (1 - s) * (-1)) s :=
    (differentiable_xi (1 - s)).hasDerivAt.comp s hc
  have h2 : (xi ∘ fun z : ℂ => 1 - z) = xi := funext fun z => xi_one_sub z
  rw [h2] at h1
  have := h1.deriv
  linear_combination this

/-- The logarithmic derivative of `ξ` is odd about `1/2`. -/
lemma logDeriv_xi_one_sub (s : ℂ) : deriv xi (1 - s) / xi (1 - s) = -(deriv xi s / xi s) := by
  rw [deriv_xi_one_sub, xi_one_sub, neg_div]

/-! ### `Γℝ'/Γℝ` and the logarithmic derivative of `ξ` on `Re s > 0` -/

lemma hasDerivAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gammaℝ (Gammaℝ s * (-(Real.log Real.pi) / 2 + digamma (s / 2) / 2)) s := by
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hΓ : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hs2
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdΓ : HasDerivAt (fun z : ℂ => Gamma (z / 2)) (deriv Gamma (s / 2) * (1 / 2)) s := by
    have hd : DifferentiableAt ℂ Gamma (s / 2) := by
      apply differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hd.hasDerivAt.comp s ((hasDerivAt_id s).div_const 2)
  have hdπ : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    simpa using this
  have h : HasDerivAt (fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (s / 2) +
        (Real.pi : ℂ) ^ (-s / 2) * (deriv Gamma (s / 2) * (1 / 2))) s := hdπ.mul hdΓ
  have e : Gammaℝ = (fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) := by
    funext z; rw [Gammaℝ_def]
  rw [e]
  refine h.congr_deriv ?_
  rw [digamma_def, logDeriv_apply, ← Complex.ofReal_log Real.pi_pos.le]
  field_simp

lemma logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    deriv Gammaℝ s / Gammaℝ s = -(Real.log Real.pi) / 2 + digamma (s / 2) / 2 := by
  rw [(hasDerivAt_Gammaℝ hs).deriv]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

lemma norm_logDeriv_Gammaℝ_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖deriv Gammaℝ s / Gammaℝ s‖ ≤ Real.log (‖s‖ + 2) / 2 + 13 := by
  have hs0 : 0 < s.re := by linarith
  rw [logDeriv_Gammaℝ hs0]
  have hd := norm_digamma_le (s := s / 2) (by simp; linarith)
  have hn : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; simp
  rw [hn] at hd
  have hlogπ : Real.log Real.pi < 2 := by
    have := Real.pi_lt_d2
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have h2 : (3.15 : ℝ) < Real.exp 2 := by
      have he := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    linarith
  have hlogπ0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hmono : Real.log (‖s‖ / 2 + 2) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith [norm_nonneg s])
  calc ‖-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖digamma (s / 2) / 2‖ := norm_add_le _ _
    _ = Real.log Real.pi / 2 + ‖digamma (s / 2)‖ / 2 := by
        rw [norm_div, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlogπ0]
        simp
    _ ≤ 1 + (Real.log (‖s‖ / 2 + 2) + 24) / 2 := by linarith
    _ ≤ Real.log (‖s‖ + 2) / 2 + 13 := by linarith

/-- On `Re s > 0`, away from zeros of `h`: `ξ'/ξ = 1/s + Γℝ'/Γℝ + h'/h`. -/
lemma logDeriv_xi_eq {s : ℂ} (hs : 0 < s.re) (hh : zetaMulSubOne s ≠ 0) :
    deriv xi s / xi s = 1 / s + deriv Gammaℝ s / Gammaℝ s +
      deriv zetaMulSubOne s / zetaMulSubOne s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : xi =ᶠ[𝓝 s] fun z => z * Gammaℝ z * zetaMulSubOne z / 2 := by
    filter_upwards [hU.mem_nhds hs] with z hz using xi_eq_of_re_pos hz
  have hGd : DifferentiableAt ℂ Gammaℝ s := (hasDerivAt_Gammaℝ hs).differentiableAt
  have hhd : DifferentiableAt ℂ zetaMulSubOne s := differentiable_zetaMulSubOne s
  have h1 : deriv xi s / xi s = logDeriv (fun z => z * Gammaℝ z * zetaMulSubOne z / 2) s := by
    rw [← logDeriv_apply]; exact (logDeriv_congr_nhds hev).eq_of_nhds
  have e : (fun z => z * Gammaℝ z * zetaMulSubOne z / 2) =
      fun z => (z * Gammaℝ z * zetaMulSubOne z) * (1 / 2 : ℂ) := by funext z; ring
  rw [h1, e, logDeriv_mul_const (f := fun z => z * Gammaℝ z * zetaMulSubOne z) s (1/2:ℂ)
    (by norm_num)]
  rw [logDeriv_mul (f := fun z => z * Gammaℝ z) (g := zetaMulSubOne) s (mul_ne_zero hs0 hG) hh
    (differentiableAt_id.mul hGd) hhd,
    logDeriv_mul (f := fun z => z) (g := Gammaℝ) s hs0 hG differentiableAt_id hGd]
  simp [logDeriv_apply]

/-! ### The value `2 ξ'/ξ(1) = 2 + γ - log 4π` -/

lemma hasDerivAt_zetaMulSubOne_one :
    HasDerivAt zetaMulSubOne (Real.eulerMascheroniConstant : ℂ) 1 := by
  have hd := (differentiable_zetaMulSubOne 1).hasDerivAt
  have h1 := hasDerivAt_iff_tendsto_slope.mp hd
  have h2 : Tendsto (slope zetaMulSubOne 1) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    refine tendsto_riemannZeta_sub_one_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [slope_def_field, zetaMulSubOne_of_ne hs1, zetaMulSubOne_one]
    field_simp
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hd

/-- `S★ = 2 + γ - log 4π`, the sum over zeros of `1/(ρ(1-ρ))`. -/
def Sstar : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

lemma two_logDeriv_xi_one : 2 * (deriv xi 1 / xi 1) = (Sstar : ℂ) := by
  rw [logDeriv_xi_eq (by norm_num) (by rw [zetaMulSubOne_one]; exact one_ne_zero),
    hasDerivAt_Gammaℝ_one.deriv, Gammaℝ_one, hasDerivAt_zetaMulSubOne_one.deriv,
    zetaMulSubOne_one, Sstar]
  have h4 : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; ring_nf
  rw [h4]
  push_cast
  ring

/-! ### Multiplicities and symmetry of the zeros -/

lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} := fun z hz =>
    (hasDerivAt_Gammaℝ hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hs)

lemma analyticOrderNatAt_xi {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt xi s = analyticOrderNatAt zetaMulSubOne s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hev : xi =ᶠ[𝓝 s] (fun z => z * Gammaℝ z / 2) * zetaMulSubOne := by
    filter_upwards [hU.mem_nhds hs] with z hz
    rw [xi_eq_of_re_pos hz, Pi.mul_apply]; ring
  have hc : AnalyticAt ℂ (fun z => z * Gammaℝ z / 2) s :=
    (analyticAt_id.mul (analyticAt_Gammaℝ hs)).div_const
  have hc0 : analyticOrderAt (fun z => z * Gammaℝ z / 2) s = 0 := by
    rw [hc.analyticOrderAt_eq_zero]
    exact div_ne_zero (mul_ne_zero hsne (Gammaℝ_ne_zero_of_re_pos hs)) two_ne_zero
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hc (differentiable_zetaMulSubOne.analyticAt s),
    hc0, zero_add]

/-- Under RH, the zeros of `h` in `Re s > 0` are symmetric under `s ↦ 1 - s`. -/
lemma zero_one_sub (hRH : RiemannHypothesis) {u : ℂ} (hu : zetaMulSubOne u = 0) (hre : 0 < u.re) :
    zetaMulSubOne (1 - u) = 0 ∧ 0 < (1 - u).re := by
  have hhalf := re_eq_half_of_zero hRH hu hre
  have hre' : 0 < (1 - u).re := by simp; linarith
  refine ⟨?_, hre'⟩
  rw [← xi_eq_zero_iff hre', xi_one_sub, xi_eq_zero_iff hre]
  exact hu

/-- Under RH, if `T` is a good height then so is `-T`. -/
lemma good_neg (hRH : RiemannHypothesis) {T δ : ℝ}
    (hgood : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) :
    ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - (-T)| := by
  intro u hu hre
  obtain ⟨h1, h2⟩ := zero_one_sub hRH hu hre
  have := hgood (1 - u) h1 h2
  rw [show (1 - u).im = -u.im by simp] at this
  rw [show u.im - -T = -(-u.im - T) by ring, abs_neg]
  exact this

/-! ### Bounds for `ξ'/ξ` -/

lemma norm_LSeries_vonMangoldt_le_of_re {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤ MΛ := by
  have hs1 : 1 < s.re := by linarith
  calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1).norm
    _ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3/2 : ℂ) n‖ := by
        refine Summable.tsum_le_tsum (fun n => ?_) (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1).norm
          (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)).norm
        exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
    _ = MΛ := rfl

/-- `‖ξ'/ξ(s)‖ ≤ log(‖s‖+2)/2 + 16 + MΛ` for `Re s ≥ 3/2`. -/
lemma norm_logDeriv_xi_right {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖deriv xi s / xi s‖ ≤ Real.log (‖s‖ + 2) / 2 + 16 + MΛ := by
  have hs0 : 0 < s.re := by linarith
  have hh : zetaMulSubOne s ≠ 0 := zetaMulSubOne_ne_zero_of_one_le_re (by linarith)
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [logDeriv_xi_eq hs0 hh]
  have hhh : deriv zetaMulSubOne s / zetaMulSubOne s = (s - 1)⁻¹ - Fh s := by
    unfold Fh; ring
  rw [hhh, Fh_eq_LSeries (by linarith)]
  have hns : 3 / 2 ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]; linarith
  have h2 : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have := Complex.abs_re_le_norm (s - 1)
    simp at this
    rw [inv_le_comm₀ (by linarith [abs_le.mp (le_refl |s.re - 1|)]) (by norm_num)]
    have : 1 / 2 ≤ |s.re - 1| := by rw [abs_of_pos (by linarith)]; linarith
    linarith
  have h3 := norm_logDeriv_Gammaℝ_le (s := s) (by linarith)
  have h4 := norm_LSeries_vonMangoldt_le_of_re hs
  calc ‖1 / s + deriv Gammaℝ s / Gammaℝ s +
        ((s - 1)⁻¹ - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s)‖
      ≤ ‖1 / s‖ + ‖deriv Gammaℝ s / Gammaℝ s‖ + (‖(s - 1)⁻¹‖ +
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
    _ ≤ 1 + (Real.log (‖s‖ + 2) / 2 + 13) + (2 + MΛ) := by gcongr
    _ = Real.log (‖s‖ + 2) / 2 + 16 + MΛ := by ring

/-- At a good height `T` and `1/2 ≤ Re s ≤ 3/2`. -/
lemma norm_logDeriv_xi_horiz {A₄ T δ : ℝ}
    (hA₄ : ∀ T δ : ℝ, 1 ≤ |T| → 0 < δ → δ ≤ 1 →
      (∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) →
      ∀ σ ∈ Icc (1/4 : ℝ) (3/2), zetaMulSubOne (σ + T * I) ≠ 0 ∧
        ‖Fh (σ + T * I)‖ ≤ A₄ * Real.log (|T| + 3) / δ)
    (hT : 1 ≤ |T|) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|)
    {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    ‖deriv xi (σ + T * I) / xi (σ + T * I)‖ ≤
      Real.log (‖(σ : ℂ) + T * I‖ + 2) / 2 + 15 + A₄ * Real.log (|T| + 3) / δ := by
  set s : ℂ := σ + T * I with hsdef
  obtain ⟨hh, hF⟩ := hA₄ T δ hT hδ hδ1 hgood σ ⟨by linarith, hσ2⟩
  have hs0 : 0 < s.re := by rw [hsdef]; simp; linarith
  rw [logDeriv_xi_eq hs0 hh]
  have hhh : deriv zetaMulSubOne s / zetaMulSubOne s = (s - 1)⁻¹ - Fh s := by
    unfold Fh; ring
  rw [hhh]
  have him : |s.im| = |T| := by rw [hsdef]; simp
  have h1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (by
      intro h; rw [h] at hs0; simp at hs0))]
    exact hT.trans (him ▸ Complex.abs_im_le_norm s)
  have h2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have := Complex.abs_im_le_norm (s - 1)
    rw [show (s - 1).im = s.im by simp, him] at this
    exact inv_le_one_of_one_le₀ (hT.trans this)
  have h3 := norm_logDeriv_Gammaℝ_le (s := s) (by rw [hsdef]; simpa using hσ1)
  calc ‖1 / s + deriv Gammaℝ s / Gammaℝ s + ((s - 1)⁻¹ - Fh s)‖
      ≤ ‖1 / s‖ + ‖deriv Gammaℝ s / Gammaℝ s‖ + (‖(s - 1)⁻¹‖ + ‖Fh s‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
    _ ≤ 1 + (Real.log (‖s‖ + 2) / 2 + 13) + (1 + A₄ * Real.log (|T| + 3) / δ) := by gcongr
    _ = Real.log (‖s‖ + 2) / 2 + 15 + A₄ * Real.log (|T| + 3) / δ := by ring

end LandauRH

end

-- ===== LF5ZeroSum.lean =====
section

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace LandauRH

open ZetaAux VonKoch

/-! ### The residue theorem for `f'/f · (s - a)⁻¹` on a rectangle -/

theorem rect_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x₁ x₂ y₁ y₂ ε : ℝ}
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hε : 0 < ε)
    (hzeros : ∀ u : ℂ, u.re ∈ Icc (x₁ - ε) (x₂ + ε) → u.im ∈ Icc (y₁ - ε) (y₂ + ε) → f u = 0 →
      x₁ < u.re ∧ u.re < x₂ ∧ y₁ < u.im ∧ u.im < y₂)
    {c : ℂ} (hc1 : x₁ < c.re) (hc2 : c.re < x₂) (hc3 : y₁ < c.im) (hc4 : c.im < y₂)
    (hfc : f c ≠ 0) :
    ∃ Z : Finset ℂ, (∀ u ∈ Z, f u = 0 ∧ x₁ < u.re ∧ u.re < x₂ ∧ y₁ < u.im ∧ u.im < y₂) ∧
      (∀ u : ℂ, x₁ < u.re → u.re < x₂ → y₁ < u.im → u.im < y₂ → f u = 0 → u ∈ Z) ∧
      ∀ a : ℂ, x₁ < a.re → a.re < x₂ → y₁ < a.im → a.im < y₂ → f a ≠ 0 →
        rectInt (fun s => deriv f s / f s * (s - a)⁻¹) x₁ x₂ y₁ y₂ =
          2 * Real.pi * I * (deriv f a / f a +
            ∑ u ∈ Z, (analyticOrderNatAt f u : ℂ) / (u - a)) := by
  classical
  set U : Set ℂ := Icc (x₁ - ε) (x₂ + ε) ×ℂ Icc (y₁ - ε) (y₂ + ε) with hU
  have hUc : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  have hUp : IsPreconnected U := (convex_Icc_reProdIm _ _ _ _).isPreconnected
  set V : Set ℂ := Ioo (x₁ - ε) (x₂ + ε) ×ℂ Ioo (y₁ - ε) (y₂ + ε) with hV
  have hVo : IsOpen V := isOpen_Ioo.reProdIm isOpen_Ioo
  have hVU : V ⊆ U := reProdIm_subset_iff.mpr (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hrectV : ∀ s : ℂ, s.re ∈ Icc x₁ x₂ → s.im ∈ Icc y₁ y₂ → s ∈ V := by
    intro s h1 h2
    rw [hV, mem_reProdIm]
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  have hcV : c ∈ V := hrectV c ⟨hc1.le, hc2.le⟩ ⟨hc3.le, hc4.le⟩
  have hfU : AnalyticOnNhd ℂ f U := fun z _ => hf.analyticAt z
  obtain ⟨Z, g, hZ1, hZ2, hg, hg0, hEq⟩ := factorization hUc hUp hfU
    (mem_of_superset (hVo.mem_nhds hcV) hVU) hfc
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  have hZloc : ∀ u ∈ Z, f u = 0 ∧ x₁ < u.re ∧ u.re < x₂ ∧ y₁ < u.im ∧ u.im < y₂ := by
    intro u hu
    obtain ⟨huU, h0⟩ := hZ1 u hu
    rw [hU, mem_reProdIm] at huU
    exact ⟨h0, hzeros u huU.1 huU.2 h0⟩
  have hZall : ∀ u : ℂ, x₁ < u.re → u.re < x₂ → y₁ < u.im → u.im < y₂ → f u = 0 → u ∈ Z := by
    intro u h1 h2 h3 h4 h0
    exact hZ2 u (hVU (hrectV u ⟨h1.le, h2.le⟩ ⟨h3.le, h4.le⟩)) h0
  refine ⟨Z, hZloc, hZall, fun a ha1 ha2 ha3 ha4 hfa => ?_⟩
  -- `G = g'/g` is holomorphic on `V`
  set G : ℂ → ℂ := fun s => deriv g s / g s with hG
  have hGd : DifferentiableOn ℂ G V := by
    intro s hs
    have hgs := hg s (hVU hs)
    exact (hgs.deriv.differentiableAt.div hgs.differentiableAt
      (hg0 s (hVU hs))).differentiableWithinAt
  have hrectsub : [[x₁, x₂]] ×ℂ [[y₁, y₂]] ⊆ V := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le hx.le, uIcc_of_le hy.le] at hs
    exact hrectV s hs.1 hs.2
  -- the logarithmic derivative on the closed rectangle
  have hlogd : ∀ s : ℂ, s.re ∈ Icc x₁ x₂ → s.im ∈ Icc y₁ y₂ → f s ≠ 0 →
      deriv f s / f s = (∑ u ∈ Z, (m u : ℂ) / (s - u)) + G s := by
    intro s h1 h2 hfs
    have hsV := hrectV s h1 h2
    have hev : f =ᶠ[𝓝 s] fun z => (∏ u ∈ Z, (z - u) ^ m u) * g z := by
      filter_upwards [hVo.mem_nhds hsV] with z hz using hEq (hVU hz)
    exact logDeriv_factor hev hfs (hg s (hVU hsV)).differentiableAt
  -- boundary points avoid the zeros and `a`
  have hbd : ∀ s : ℂ, (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) →
      ∀ b : ℂ, x₁ < b.re → b.re < x₂ → y₁ < b.im → b.im < y₂ → s ≠ b := by
    rintro s hs b h1 h2 h3 h4 rfl
    rcases hs with h | h | h | h <;> linarith
  have hfbd : ∀ s : ℂ, s.re ∈ Icc x₁ x₂ → s.im ∈ Icc y₁ y₂ →
      (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) → f s ≠ 0 := by
    intro s h1 h2 hs h0
    obtain ⟨g1, g2, g3, g4⟩ := hzeros s ⟨by linarith [h1.1], by linarith [h1.2]⟩
      ⟨by linarith [h2.1], by linarith [h2.2]⟩ h0
    exact hbd s hs s g1 g2 g3 g4 rfl
  have hua : ∀ u ∈ Z, u ≠ a := by
    intro u hu h; rw [h] at hu; exact hfa (hZloc a hu).1
  -- decomposition on the boundary
  set Φ : ℂ → ℂ := fun s => (∑ u ∈ Z, (m u : ℂ) * (u - a)⁻¹ * ((s - u)⁻¹ - (s - a)⁻¹)) +
    G s * (s - a)⁻¹ with hΦ
  have hcongr : rectInt (fun s => deriv f s / f s * (s - a)⁻¹) x₁ x₂ y₁ y₂ =
      rectInt Φ x₁ x₂ y₁ y₂ := by
    refine rectInt_congr (fun s h1 h2 hs => ?_)
    rw [uIcc_of_le hx.le] at h1
    rw [uIcc_of_le hy.le] at h2
    have hfs := hfbd s h1 h2 hs
    rw [hlogd s h1 h2 hfs, hΦ]
    have hsa : s - a ≠ 0 := sub_ne_zero.mpr (hbd s hs a ha1 ha2 ha3 ha4)
    simp only
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    obtain ⟨-, g1, g2, g3, g4⟩ := hZloc u hu
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr (hbd s hs u g1 g2 g3 g4)
    have hua' : u - a ≠ 0 := sub_ne_zero.mpr (hua u hu)
    field_simp
    ring
  -- continuity on the boundary
  have hc_inv : ∀ b : ℂ, x₁ < b.re → b.re < x₂ → y₁ < b.im → b.im < y₂ →
      BdryCont (fun s => (s - b)⁻¹) x₁ x₂ y₁ y₂ := by
    intro b h1 h2 h3 h4
    exact BdryCont.of_bdry fun s _ _ hs =>
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hbd s hs b h1 h2 h3 h4))
  have hcu : ∀ u ∈ Z, BdryCont (fun s => (m u : ℂ) * (u - a)⁻¹ * ((s - u)⁻¹ - (s - a)⁻¹))
      x₁ x₂ y₁ y₂ := by
    intro u hu
    obtain ⟨-, g1, g2, g3, g4⟩ := hZloc u hu
    exact ((hc_inv u g1 g2 g3 g4).sub (hc_inv a ha1 ha2 ha3 ha4)).const_mul _
  have hcG : BdryCont (fun s => G s * (s - a)⁻¹) x₁ x₂ y₁ y₂ := by
    refine BdryCont.of_bdry fun s h1 h2 hs => ?_
    rw [uIcc_of_le hx.le] at h1
    rw [uIcc_of_le hy.le] at h2
    exact ((hGd.differentiableAt (hVo.mem_nhds (hrectV s h1 h2))).continuousAt).mul
      ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (hbd s hs a ha1 ha2 ha3 ha4)))
  rw [hcongr, hΦ, rectInt_add (BdryCont.sum Z hcu) hcG, rectInt_sum Z hcu]
  have hterm : ∀ u ∈ Z, rectInt (fun s => (m u : ℂ) * (u - a)⁻¹ * ((s - u)⁻¹ - (s - a)⁻¹))
      x₁ x₂ y₁ y₂ = 0 := by
    intro u hu
    obtain ⟨-, g1, g2, g3, g4⟩ := hZloc u hu
    rw [rectInt_const_mul, rectInt_sub (hc_inv u g1 g2 g3 g4) (hc_inv a ha1 ha2 ha3 ha4),
      rectInt_inv g1 g2 g3 g4, rectInt_inv ha1 ha2 ha3 ha4]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, zero_add,
    rectInt_mul_inv ha1 ha2 ha3 ha4 hVo hrectsub hGd]
  -- `G a = f'/f(a) - ∑ m/(a - u)`
  have hGa : G a = deriv f a / f a - ∑ u ∈ Z, (m u : ℂ) / (a - u) := by
    rw [hlogd a ⟨ha1.le, ha2.le⟩ ⟨ha3.le, ha4.le⟩ hfa]; ring
  rw [hGa]
  have hneg : ∑ u ∈ Z, (m u : ℂ) / (a - u) = -∑ u ∈ Z, (m u : ℂ) / (u - a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hua' : u - a ≠ 0 := sub_ne_zero.mpr (hua u hu)
    have hau : a - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (hua u hu))
    field_simp
    ring
  rw [hneg]
  ring

/-- A trivial bound for a rectangle integral. -/
lemma norm_rectInt_le {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ M : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hM : ∀ s : ℂ, s.re ∈ Icc x₁ x₂ → s.im ∈ Icc y₁ y₂ →
      (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) → ‖f s‖ ≤ M) :
    ‖rectInt f x₁ x₂ y₁ y₂‖ ≤ 2 * M * (x₂ - x₁) + 2 * M * (y₂ - y₁) := by
  unfold rectInt
  have hh : ∀ y : ℝ, (y = y₁ ∨ y = y₂) → ‖∫ x in x₁..x₂, f (x + y * I)‖ ≤ M * (x₂ - x₁) := by
    intro y hy'
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂) (C := M)
      (f := fun x : ℝ => f (x + y * I)) (fun x hx' => by
        rw [uIoc_of_le hx] at hx'
        refine hM _ (by simp; exact ⟨hx'.1.le, hx'.2⟩) (by
          simp; rcases hy' with h | h <;> rw [h] <;> [exact ⟨le_rfl, hy⟩; exact ⟨hy, le_rfl⟩])
          (by rcases hy' with h | h <;> simp [h]))
    rwa [abs_of_nonneg (by linarith)] at this
  have hv : ∀ x : ℝ, (x = x₁ ∨ x = x₂) → ‖∫ y in y₁..y₂, f (x + y * I)‖ ≤ M * (y₂ - y₁) := by
    intro x hx'
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y₁) (b := y₂) (C := M)
      (f := fun y : ℝ => f (x + y * I)) (fun y hy'' => by
        rw [uIoc_of_le hy] at hy''
        refine hM _ (by
          simp; rcases hx' with h | h <;> rw [h] <;> [exact ⟨le_rfl, hx⟩; exact ⟨hx, le_rfl⟩])
          (by simp; exact ⟨hy''.1.le, hy''.2⟩)
          (by rcases hx' with h | h <;> simp [h]))
    rwa [abs_of_nonneg (by linarith)] at this
  have e1 := hh y₁ (Or.inl rfl)
  have e2 := hh y₂ (Or.inr rfl)
  have e3 := hv x₂ (Or.inr rfl)
  have e4 := hv x₁ (Or.inl rfl)
  have n3 : ‖I * ∫ y in y₁..y₂, f (x₂ + y * I)‖ = ‖∫ y in y₁..y₂, f (x₂ + y * I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have n4 : ‖I * ∫ y in y₁..y₂, f (x₁ + y * I)‖ = ‖∫ y in y₁..y₂, f (x₁ + y * I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  calc ‖(∫ x in x₁..x₂, f (x + y₁ * I)) - (∫ x in x₁..x₂, f (x + y₂ * I)) +
        I * (∫ y in y₁..y₂, f (x₂ + y * I)) - I * (∫ y in y₁..y₂, f (x₁ + y * I))‖
      ≤ ‖(∫ x in x₁..x₂, f (x + y₁ * I)) - (∫ x in x₁..x₂, f (x + y₂ * I)) +
          I * (∫ y in y₁..y₂, f (x₂ + y * I))‖ + ‖I * (∫ y in y₁..y₂, f (x₁ + y * I))‖ :=
        norm_sub_le _ _
    _ ≤ ‖∫ x in x₁..x₂, f (x + y₁ * I)‖ + ‖∫ x in x₁..x₂, f (x + y₂ * I)‖ +
          ‖I * (∫ y in y₁..y₂, f (x₂ + y * I))‖ + ‖I * (∫ y in y₁..y₂, f (x₁ + y * I))‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * M * (x₂ - x₁) + 2 * M * (y₂ - y₁) := by rw [n3, n4]; linarith

/-! ### `ξ'/ξ` on the boundary of the square `[1 - T, T] × [-T, T]` -/

lemma norm_logDeriv_xi_square (hRH : RiemannHypothesis) {A₄ : ℝ}
    (hA₄ : ∀ T δ : ℝ, 1 ≤ |T| → 0 < δ → δ ≤ 1 →
      (∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) →
      ∀ σ ∈ Icc (1/4 : ℝ) (3/2), zetaMulSubOne (σ + T * I) ≠ 0 ∧
        ‖Fh (σ + T * I)‖ ≤ A₄ * Real.log (|T| + 3) / δ)
    (hA₄0 : 0 ≤ A₄) {T δ : ℝ} (hT : 2 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgood : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) :
    ∀ s : ℂ, s.re ∈ Icc (1 - T) T → s.im ∈ Icc (-T) T →
      (s.re = 1 - T ∨ s.re = T ∨ s.im = -T ∨ s.im = T) →
      ‖deriv xi s / xi s‖ ≤ Real.log (2 * T + 2) / 2 + 31 + MΛ + A₄ * Real.log (T + 3) / δ := by
  have hM := MΛ_nonneg
  have hgood' := good_neg hRH hgood
  have hlogT : 0 ≤ A₄ * Real.log (T + 3) / δ := by
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    positivity
  -- the case `1/2 ≤ Re s`
  have hright : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ∈ Icc (1 - T) T → s.im ∈ Icc (-T) T →
      (s.re = 1 - T ∨ s.re = T ∨ s.im = -T ∨ s.im = T) →
      ‖deriv xi s / xi s‖ ≤ Real.log (2 * T + 2) / 2 + 31 + MΛ + A₄ * Real.log (T + 3) / δ := by
    intro s hs1 h1 h2 hs
    have hns : ‖s‖ ≤ 2 * T := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ T + T := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
          · rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
        _ = 2 * T := by ring
    have hlog : Real.log (‖s‖ + 2) ≤ Real.log (2 * T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rcases le_or_gt (3 / 2) s.re with hs32 | hs32
    · have := norm_logDeriv_xi_right hs32
      linarith
    · -- then `s` lies on a horizontal side
      have him : s.im = -T ∨ s.im = T := by
        rcases hs with h | h | h | h
        · linarith
        · linarith
        · exact Or.inl h
        · exact Or.inr h
      have hsform : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
      rcases him with h | h
      · rw [hsform, h]
        have := norm_logDeriv_xi_horiz hA₄ (T := -T) (δ := δ)
          (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) hδ hδ1 hgood' hs1 hs32.le
        rw [abs_neg, abs_of_pos (by linarith)] at this
        have hlog' : Real.log (‖(s.re : ℂ) + ((-T : ℝ) : ℂ) * I‖ + 2) ≤ Real.log (2 * T + 2) := by
          have e : (s.re : ℂ) + ((-T : ℝ) : ℂ) * I = s := by
            rw [← h]; exact (Complex.re_add_im s)
          rw [e]; exact hlog
        push_cast at this hlog' ⊢
        linarith
      · rw [hsform, h]
        have := norm_logDeriv_xi_horiz hA₄ (T := T) (δ := δ)
          (by rw [abs_of_pos (by linarith)]; linarith) hδ hδ1 hgood hs1 hs32.le
        rw [abs_of_pos (by linarith)] at this
        have hlog' : Real.log (‖(s.re : ℂ) + (T : ℂ) * I‖ + 2) ≤ Real.log (2 * T + 2) := by
          have e : (s.re : ℂ) + (T : ℂ) * I = s := by
            rw [← h]; exact (Complex.re_add_im s)
          rw [e]; exact hlog
        linarith
  intro s h1 h2 hs
  rcases le_or_gt (1 / 2) s.re with hs1 | hs1
  · exact hright s hs1 h1 h2 hs
  · have e := logDeriv_xi_one_sub (1 - s)
    rw [sub_sub_cancel] at e
    rw [e, norm_neg]
    refine hright (1 - s) (by simp; linarith) ?_ ?_ ?_
    · simp; constructor <;> linarith [h1.1, h1.2]
    · simp; constructor <;> linarith [h2.1, h2.2]
    · simp
      rcases hs with h | h | h | h
      · right; left; linarith
      · left; linarith
      · right; right; right; linarith
      · right; right; left; linarith

lemma log_le_four_rpow {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 4 * x ^ (1/4 : ℝ) := by
  have := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ x) (by norm_num : (0:ℝ) < 1/4)
  linarith [this, show x ^ (1/4 : ℝ) / (1/4) = 4 * x ^ (1/4 : ℝ) by ring]

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 16 * x ^ (1/2 : ℝ) := by
  have h1 := log_le_four_rpow hx
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  calc Real.log x ^ 2 ≤ (4 * x ^ (1/4 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * x ^ (1/2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1/4 : ℝ)), ← Real.rpow_mul (by linarith)]
        norm_num

lemma mul_conj_of_re_half {u : ℂ} (hu : u.re = 1 / 2) : u * (1 - u) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : 1 - u = (starRingEnd ℂ) u := by
    apply Complex.ext <;> simp [hu]; norm_num
  rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The square contour: for a good height `T`, the zero sum inside `[1-T,T]×[-T,T]` is at most
`S★` plus an explicit error. -/
lemma square_bound (hRH : RiemannHypothesis) {A₄ : ℝ}
    (hhor : ∀ T δ : ℝ, 1 ≤ |T| → 0 < δ → δ ≤ 1 →
      (∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) →
      ∀ σ ∈ Icc (1/4 : ℝ) (3/2), zetaMulSubOne (σ + T * I) ≠ 0 ∧
        ‖Fh (σ + T * I)‖ ≤ A₄ * Real.log (|T| + 3) / δ)
    (hA₄ : 0 < A₄) {T δ : ℝ} (hT2 : 2 ≤ T) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hgood : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) :
    ∃ ZT : Finset ℂ, (∀ u : ℂ, 1 - T < u.re → u.re < T → -T < u.im → u.im < T → xi u = 0 →
      u ∈ ZT) ∧
      ∑ u ∈ ZT, (analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 ≤ Sstar +
        16 * (Real.log (2 * T + 2) / 2 + 31 + MΛ + A₄ * Real.log (T + 3) / δ) / (T - 1) /
          (2 * Real.pi) := by
  classical
  have hM := MΛ_nonneg
  have hgood' := good_neg hRH hgood
  -- the zeros of `ξ` near the square
  have hzeros : ∀ u : ℂ, u.re ∈ Icc (1 - T - δ / 2) (T + δ / 2) →
      u.im ∈ Icc (-T - δ / 2) (T + δ / 2) → xi u = 0 →
      1 - T < u.re ∧ u.re < T ∧ -T < u.im ∧ u.im < T := by
    intro u h1 h2 h0
    have hre0 : 0 < u.re := by
      by_contra hc; push Not at hc; exact xi_ne_zero_of_re_nonpos hc h0
    have hre1 : u.re < 1 := by
      by_contra hc; push Not at hc; exact xi_ne_zero_of_one_le_re hc h0
    have hh0 : zetaMulSubOne u = 0 := (xi_eq_zero_iff hre0).mp h0
    have hhalf := re_eq_half_of_zero hRH hh0 hre0
    have g1 := hgood u hh0 hre0
    have g2 := hgood' u hh0 hre0
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · by_contra hc; push Not at hc
      have : |u.im - -T| ≤ δ / 2 := abs_le.mpr ⟨by linarith [h2.1], by linarith⟩
      linarith
    · by_contra hc; push Not at hc
      have : |u.im - T| ≤ δ / 2 := abs_le.mpr ⟨by linarith, by linarith [h2.2]⟩
      linarith
  obtain ⟨ZT, hZT1, hZT2, hform⟩ := rect_logDeriv differentiable_xi (x₁ := 1 - T) (x₂ := T)
    (y₁ := -T) (y₂ := T) (ε := δ / 2) (by linarith) (by linarith) (by positivity) hzeros
    (c := 1) (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by rw [xi_one]; norm_num)
  have hI0 := hform 0 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by rw [xi_zero]; norm_num)
  have hI1 := hform 1 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by rw [xi_one]; norm_num)
  -- the combined rectangle integral
  set F : ℂ → ℂ := fun s => deriv xi s / xi s with hF
  have hbdne : ∀ s : ℂ, (s.re = 1 - T ∨ s.re = T ∨ s.im = -T ∨ s.im = T) →
      s.re ∈ uIcc (1 - T) T → s.im ∈ uIcc (-T) T → xi s ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 := by
    intro s hs h1 h2
    rw [uIcc_of_le (by linarith)] at h1
    rw [uIcc_of_le (by linarith)] at h2
    refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
    · obtain ⟨g1, g2, g3, g4⟩ := hzeros s ⟨by linarith [h1.1], by linarith [h1.2]⟩
        ⟨by linarith [h2.1], by linarith [h2.2]⟩ h0
      rcases hs with h | h | h | h <;> linarith
    · rw [h0] at hs; simp at hs; rcases hs with h | h | h | h <;> linarith
    · rw [h0] at hs; simp at hs; rcases hs with h | h | h | h <;> linarith
  have hcF : ∀ a : ℂ, (a = 0 ∨ a = 1) → BdryCont (fun s => F s * (s - a)⁻¹) (1 - T) T (-T) T := by
    intro a ha
    refine BdryCont.of_bdry fun s h1 h2 hs => ?_
    obtain ⟨hx, hs0, hs1⟩ := hbdne s hs h1 h2
    have hsa : s - a ≠ 0 := by
      rcases ha with rfl | rfl
      · simpa using hs0
      · exact sub_ne_zero.mpr hs1
    exact (((differentiable_xi.analyticAt s).deriv.continuousAt).div
      (differentiable_xi s).continuousAt hx).mul
      ((continuousAt_id.sub continuousAt_const).inv₀ hsa)
  have hsub := rectInt_sub (hcF 0 (Or.inl rfl)) (hcF 1 (Or.inr rfl))
  set E := rectInt (fun s => F s * (s - 0)⁻¹ - F s * (s - 1)⁻¹) (1 - T) T (-T) T with hE
  have hF0 : deriv xi 0 / xi 0 = -(deriv xi 1 / xi 1) := by
    have := logDeriv_xi_one_sub 1; simpa using this
  -- zeros in the square lie on the critical line
  have hZTre : ∀ u ∈ ZT, u.re = 1 / 2 ∧ zetaMulSubOne u = 0 := by
    intro u hu
    obtain ⟨h0, -, -, -, -⟩ := hZT1 u hu
    have hre0 : 0 < u.re := by
      by_contra hc; push Not at hc; exact xi_ne_zero_of_re_nonpos hc h0
    have hh0 : zetaMulSubOne u = 0 := (xi_eq_zero_iff hre0).mp h0
    exact ⟨re_eq_half_of_zero hRH hh0 hre0, hh0⟩
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hkey : (∑ u ∈ ZT, (analyticOrderNatAt xi u : ℂ) / (u * (1 - u))) =
      2 * (deriv xi 1 / xi 1) + E / (2 * Real.pi * I) := by
    have hE' : E = 2 * Real.pi * I * (deriv xi 0 / xi 0 +
        ∑ u ∈ ZT, (analyticOrderNatAt xi u : ℂ) / (u - 0)) -
        2 * Real.pi * I * (deriv xi 1 / xi 1 + ∑ u ∈ ZT, (analyticOrderNatAt xi u : ℂ) / (u - 1)) := by
      rw [hsub, ← hI0, ← hI1]
    rw [hE', hF0]
    have hterm : ∀ u ∈ ZT, (analyticOrderNatAt xi u : ℂ) / (u - 0) -
        (analyticOrderNatAt xi u : ℂ) / (u - 1) = (analyticOrderNatAt xi u : ℂ) / (u * (1 - u)) := by
      intro u hu
      have hre := (hZTre u hu).1
      have hu0 : u ≠ 0 := by intro h; rw [h] at hre; simp at hre
      have hu1 : u - 1 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hu1' : 1 - u ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring
    rw [← Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    field_simp
    ring
  -- real form
  have hreal : ∀ u ∈ ZT, (analyticOrderNatAt xi u : ℂ) / (u * (1 - u)) =
      (((analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 : ℝ) : ℂ) := by
    intro u hu
    rw [mul_conj_of_re_half (hZTre u hu).1]
    push_cast; ring
  rw [Finset.sum_congr rfl hreal, two_logDeriv_xi_one, ← Complex.ofReal_sum] at hkey
  have hsumle : ∑ u ∈ ZT, (analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 ≤
      Sstar + ‖E‖ / (2 * Real.pi) := by
    have h1 := congrArg Complex.re hkey
    rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at h1
    rw [h1]
    have h2 : (E / (2 * Real.pi * I)).re ≤ ‖E / (2 * Real.pi * I)‖ := Complex.re_le_norm _
    have h3 : ‖E / (2 * Real.pi * I)‖ = ‖E‖ / (2 * Real.pi) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp
    linarith
  -- the bound for `E`
  set B : ℝ := Real.log (2 * T + 2) / 2 + 31 + MΛ + A₄ * Real.log (T + 3) / δ with hB
  have hFbd := norm_logDeriv_xi_square hRH hhor hA₄.le hT2 hδ (by linarith) hgood
  have hEbd : ‖E‖ ≤ 16 * B / (T - 1) := by
    have hT1 : 0 < T - 1 := by linarith
    have hM : ∀ s : ℂ, s.re ∈ Icc (1 - T) T → s.im ∈ Icc (-T) T →
        (s.re = 1 - T ∨ s.re = T ∨ s.im = -T ∨ s.im = T) →
        ‖F s * (s - 0)⁻¹ - F s * (s - 1)⁻¹‖ ≤ B / (T - 1) ^ 2 := by
      intro s h1 h2 hs
      have hns : T - 1 ≤ ‖s‖ := by
        rcases hs with h | h | h | h
        · have := Complex.abs_re_le_norm s; rw [h, abs_of_neg (by linarith)] at this; linarith
        · have := Complex.abs_re_le_norm s; rw [h, abs_of_pos (by linarith)] at this; linarith
        · have := Complex.abs_im_le_norm s; rw [h, abs_neg, abs_of_pos (by linarith)] at this
          linarith
        · have := Complex.abs_im_le_norm s; rw [h, abs_of_pos (by linarith)] at this; linarith
      have hns1 : T - 1 ≤ ‖s - 1‖ := by
        rcases hs with h | h | h | h
        · have := Complex.abs_re_le_norm (s - 1)
          simp only [sub_re, one_re] at this
          rw [h, abs_of_neg (by linarith)] at this; linarith
        · have := Complex.abs_re_le_norm (s - 1)
          simp only [sub_re, one_re] at this
          rw [h, abs_of_pos (by linarith)] at this; linarith
        · have := Complex.abs_im_le_norm (s - 1)
          simp only [sub_im, one_im, sub_zero] at this
          rw [h, abs_neg, abs_of_pos (by linarith)] at this; linarith
        · have := Complex.abs_im_le_norm (s - 1)
          simp only [sub_im, one_im, sub_zero] at this
          rw [h, abs_of_pos (by linarith)] at this; linarith
      have hs0 : s ≠ 0 := fun h => by rw [h] at hns; simp at hns; linarith
      have hs1 : s - 1 ≠ 0 := fun h => by rw [h] at hns1; simp at hns1; linarith
      have e : F s * (s - 0)⁻¹ - F s * (s - 1)⁻¹ = -(F s) / (s * (s - 1)) := by
        rw [sub_zero]; field_simp; ring
      rw [e, norm_div, norm_neg, norm_mul]
      have hF := hFbd s h1 h2 hs
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hF
      calc ‖F s‖ / (‖s‖ * ‖s - 1‖) ≤ B / ((T - 1) * (T - 1)) := by
            apply div_le_div₀ hB0 hF (by positivity)
            exact mul_le_mul hns hns1 hT1.le (norm_nonneg _)
        _ = B / (T - 1) ^ 2 := by ring
    have hR := norm_rectInt_le (by linarith : 1 - T ≤ T) (by linarith : -T ≤ T) hM
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hFbd (T : ℂ) (by simp; linarith)
      (by simp; linarith) (Or.inr (Or.inl (by simp))))
    calc ‖E‖ ≤ 2 * (B / (T - 1) ^ 2) * (T - (1 - T)) + 2 * (B / (T - 1) ^ 2) * (T - -T) := hR
      _ = B * (8 * T - 2) / (T - 1) ^ 2 := by ring
      _ ≤ 16 * B / (T - 1) := by
          rw [div_le_div_iff₀ (by positivity) hT1]
          have : (8 * T - 2) * (T - 1) ≤ 16 * (T - 1) ^ 2 := by nlinarith
          nlinarith
  refine ⟨ZT, hZT2, hsumle.trans ?_⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have := div_le_div_of_nonneg_right hEbd hpi.le
  linarith only [this]

/-- **The zero sum** (under RH): `∑_ρ m_ρ / |ρ|² ≤ 2 + γ - log 4π` over any finite set of zeros. -/
theorem zero_sum_le_Sstar (hRH : RiemannHypothesis) (Z : Finset ℂ)
    (hZ : ∀ u ∈ Z, zetaMulSubOne u = 0 ∧ 0 < u.re) :
    ∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖ ^ 2 ≤ Sstar := by
  classical
  obtain ⟨A₃, hA₃, hgoodh⟩ := good_height hRH
  obtain ⟨A₄, hA₄, hhor⟩ := Fh_horizontal
  have hM := MΛ_nonneg
  set C₁ : ℝ := 8 + 31 + MΛ + 16 * A₃ * A₄ with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set Y₀ : ℝ := ∑ u ∈ Z, |u.im| with hY₀
  have hY₀0 : 0 ≤ Y₀ := Finset.sum_nonneg (fun u _ => abs_nonneg _)
  have hYu : ∀ u ∈ Z, |u.im| ≤ Y₀ := fun u hu =>
    Finset.single_le_sum (f := fun v : ℂ => |v.im|) (fun v _ => abs_nonneg v.im) hu
  apply le_of_forall_pos_lt_add
  intro ε hε
  set y : ℝ := Y₀ + 3 + (48 * C₁ / ε) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  obtain ⟨T, hT, δ, hδ, hδ4, hδA, hgood⟩ := hgoodh y
  have hTy : y ≤ T := hT.1
  have hT2 : 2 ≤ T := by nlinarith [sq_nonneg (48 * C₁ / ε)]
  have hTY : Y₀ + 3 ≤ T := by nlinarith [sq_nonneg (48 * C₁ / ε)]
  obtain ⟨ZT, hZT2, hsum⟩ := square_bound hRH hhor hA₄ hT2 hδ hδ4 hgood
  clear_value C₁ Y₀ y
  set B : ℝ := Real.log (2 * T + 2) / 2 + 31 + MΛ + A₄ * Real.log (T + 3) / δ with hB
  clear_value B
  -- `B ≤ C₁ (T + 4)^{1/2}`
  have hT4 : (1:ℝ) ≤ T + 4 := by linarith
  have hsq : 1 ≤ (T + 4) ^ (1/2 : ℝ) := Real.one_le_rpow hT4 (by norm_num)
  have hlogT4 : 0 ≤ Real.log (T + 4) := Real.log_nonneg hT4
  have h1δ : 1 / δ ≤ A₃ * Real.log (T + 4) := by
    refine hδA.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA₃.le)
    rw [abs_of_nonneg hy0]; linarith
  have hBle : B ≤ C₁ * (T + 4) ^ (1/2 : ℝ) := by
    have e1 : Real.log (2 * T + 2) / 2 ≤ 4 * (T + 4) ^ (1/2 : ℝ) := by
      have h2 : Real.log (2 * T + 2) ≤ 2 * Real.log (T + 4) := by
        have e : 2 * Real.log (T + 4) = Real.log ((T + 4) ^ 2) := by
          rw [Real.log_pow]; norm_num
        rw [e]
        exact Real.log_le_log (by positivity) (by nlinarith)
      have h4 := log_le_four_rpow hT4
      have : (T + 4) ^ (1/4 : ℝ) ≤ (T + 4) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT4 (by norm_num)
      linarith
    have e2 : A₄ * Real.log (T + 3) / δ ≤ 16 * A₃ * A₄ * (T + 4) ^ (1/2 : ℝ) := by
      have hl3 : Real.log (T + 3) ≤ Real.log (T + 4) := Real.log_le_log (by linarith) (by linarith)
      have hl30 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
      calc A₄ * Real.log (T + 3) / δ = A₄ * Real.log (T + 3) * (1 / δ) := by ring
        _ ≤ A₄ * Real.log (T + 4) * (A₃ * Real.log (T + 4)) := by gcongr
        _ = A₃ * A₄ * Real.log (T + 4) ^ 2 := by ring
        _ ≤ A₃ * A₄ * (16 * (T + 4) ^ (1/2 : ℝ)) := by gcongr; exact log_sq_le hT4
        _ = 16 * A₃ * A₄ * (T + 4) ^ (1/2 : ℝ) := by ring
    have e3 : 31 + MΛ ≤ (31 + MΛ) * (T + 4) ^ (1/2 : ℝ) :=
      le_mul_of_one_le_right (by positivity) hsq
    have hsq0 : 0 ≤ (T + 4) ^ (1/2 : ℝ) := by positivity
    calc B ≤ 4 * (T + 4) ^ (1/2 : ℝ) + (31 + MΛ) * (T + 4) ^ (1/2 : ℝ) +
          16 * A₃ * A₄ * (T + 4) ^ (1/2 : ℝ) := by linarith only [e1, e2, e3, hB]
      _ = (4 + 31 + MΛ + 16 * A₃ * A₄) * (T + 4) ^ (1/2 : ℝ) := by ring
      _ ≤ C₁ * (T + 4) ^ (1/2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hsq0
  -- the error is small
  have hsqrt : 48 * C₁ / ε ≤ (T + 4) ^ (1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    linarith only [hy, hTy, hY₀0]
  have herr : 16 * B / (T - 1) / (2 * Real.pi) < ε := by
    have hT1 : 0 < T - 1 := by linarith
    have hpos : 0 < (T + 4) ^ (1/2 : ℝ) := by positivity
    have hsq2 : (T + 4) ^ (1/2 : ℝ) * (T + 4) ^ (1/2 : ℝ) = T + 4 := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h1 : 16 * B / (T - 1) ≤ 96 * C₁ / (T + 4) ^ (1/2 : ℝ) := by
      rw [div_le_div_iff₀ hT1 hpos]
      calc 16 * B * (T + 4) ^ (1/2 : ℝ)
          ≤ 16 * (C₁ * (T + 4) ^ (1/2 : ℝ)) * (T + 4) ^ (1/2 : ℝ) := by gcongr
        _ = 16 * C₁ * ((T + 4) ^ (1/2 : ℝ) * (T + 4) ^ (1/2 : ℝ)) := by ring
        _ = 16 * C₁ * (T + 4) := by rw [hsq2]
        _ ≤ 96 * C₁ * (T - 1) := by
            have := mul_nonneg (by linarith only [hT2] : (0:ℝ) ≤ 80 * T - 160) hC₁0.le
            linarith only [this]
    have h2 : 96 * C₁ / (T + 4) ^ (1/2 : ℝ) ≤ 2 * ε := by
      rw [div_le_iff₀ hpos]
      calc 96 * C₁ = 2 * ε * (48 * C₁ / ε) := by field_simp; ring
        _ ≤ 2 * ε * (T + 4) ^ (1/2 : ℝ) := by gcongr
    have hpi3 : 6 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [div_lt_iff₀ (by positivity)]
    calc 16 * B / (T - 1) ≤ 2 * ε := h1.trans h2
      _ < ε * (2 * Real.pi) := by
          have := mul_lt_mul_of_pos_left (show (2:ℝ) < 2 * Real.pi by linarith only [hpi3]) hε
          linarith only [this]
  -- `Z ⊆ ZT`
  have hZsub : Z ⊆ ZT := by
    intro u hu
    obtain ⟨hh, hre⟩ := hZ u hu
    have hhalf := re_eq_half_of_zero hRH hh hre
    have hxi : xi u = 0 := (xi_eq_zero_iff hre).mpr hh
    have him := hYu u hu
    exact hZT2 u (by rw [hhalf]; linarith only [hT2]) (by rw [hhalf]; linarith only [hT2])
      (by linarith only [(abs_le.mp him).1, hTY]) (by linarith only [(abs_le.mp him).2, hTY]) hxi
  have hmult : ∀ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖ ^ 2 =
      (analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 := by
    intro u hu; rw [analyticOrderNatAt_xi (hZ u hu).2]
  calc ∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖ ^ 2
      = ∑ u ∈ Z, (analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 := Finset.sum_congr rfl hmult
    _ ≤ ∑ u ∈ ZT, (analyticOrderNatAt xi u : ℝ) / ‖u‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hZsub (fun _ _ _ => by positivity)
    _ ≤ Sstar + 16 * B / (T - 1) / (2 * Real.pi) := hsum
    _ < Sstar + ε := by linarith only [herr]

end LandauRH

end

-- ===== Bridge.lean =====
section

set_option autoImplicit false

open Complex Filter Topology

namespace LandauRH

open ZetaAux

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
    (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

lemma analyticOrderAt_zetaMulSubOne {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt zetaMulSubOne s = analyticOrderAt riemannZeta s := by
  have hev : zetaMulSubOne =ᶠ[𝓝 s] (fun z : ℂ => z - 1) * riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz using zetaMulSubOne_of_ne hz
  have ha : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha (analyticAt_riemannZeta hs)]
  have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr hs))
  rw [h0, zero_add]

lemma analyticOrderNatAt_zetaMulSubOne {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt zetaMulSubOne s = analyticOrderNatAt riemannZeta s := by
  simp only [analyticOrderNatAt, analyticOrderAt_zetaMulSubOne hs]

lemma zetaMulSubOne_eq_zero_iff {s : ℂ} : zetaMulSubOne s = 0 ↔ s ≠ 1 ∧ riemannZeta s = 0 := by
  constructor
  · intro h
    have hs : s ≠ 1 := by
      rintro rfl; rw [zetaMulSubOne_one] at h; exact one_ne_zero h
    refine ⟨hs, ?_⟩
    rw [zetaMulSubOne_of_ne hs] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hs)
  · rintro ⟨hs, h⟩
    rw [zetaMulSubOne_of_ne hs, h, mul_zero]

end LandauRH


end

end

/-- Under RH, the weighted zero sum is bounded by `2 + γ - log 4π`. -/
theorem solution (hRH : RiemannHypothesis) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 0 < ρ.re) :
    ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hne : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h => riemannZeta_one_ne_zero (h ▸ (hZ ρ hρ).1)
  have h := LandauRH.zero_sum_le_Sstar hRH Z (fun ρ hρ =>
    ⟨LandauRH.zetaMulSubOne_eq_zero_iff.mpr ⟨hne ρ hρ, (hZ ρ hρ).1⟩, (hZ ρ hρ).2⟩)
  have e : ∑ ρ ∈ Z, (analyticOrderNatAt ZetaAux.zetaMulSubOne ρ : ℝ) / ‖ρ‖ ^ 2 =
      ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 :=
    Finset.sum_congr rfl (fun ρ hρ => by rw [LandauRH.analyticOrderNatAt_zetaMulSubOne (hne ρ hρ)])
  rw [← e]
  exact h
