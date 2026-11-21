-- Prove2me | solution 1 for LandauCriterion.psi_error_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-20T19:43:28.192774+00:00
-- url     : https://prove2.me/submissions/af6f4d11-139e-41ce-b643-70975f96f6bd

/-
  von Koch's theorem: under the Riemann hypothesis,
      |ψ(x) - x| ≤ C √x (log x)²   for all x ≥ 2.

  Proof outline (all steps are proved below; no external axioms):
  * `VonKoch.perron`        : Perron's formula for the Riesz mean ψ₁(x) = Σ Λ(n)(x-n)₊, via Mellin
                              inversion of (1-u)₊ (whose Mellin transform is 1/(s(s+1))).
  * `VonKoch.landau_logDeriv`: Landau's lemma (Jensen + Borel–Carathéodory + Cauchy estimate):
                              f'/f minus the nearby zeros is O(log(B/|f(c)|)).
  * `VonKoch.rectInt_inv`, `VonKoch.rectInt_mul_inv` : residue theorem on rectangles.
  * `VonKoch.landau_h`, `zero_count`, `Fh_quarter_bound`, `good_height`, `Fh_horizontal`,
    `zero_sum` : consequences for h(s) = (s-1)ζ(s) (under RH: zeros with Re > 0 lie on Re = 1/2).
  * `VonKoch.rect_explicit` : ∮ F(s) D(s) ds = 2πi (D(1) - Σ_ρ m_ρ D(ρ)) on [1/4, 3/2] × [-T₂, T₁],
                              F = -ζ'/ζ.
  * `VonKoch.main_estimate` : ψ₁(X+H) - ψ₁(X) = XH + H²/2 + O(H √X log² X).
  * `VonKoch.psi_error`     : differencing with H = √x.
-/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Order.Group.Lattice


noncomputable section

section

open Complex MeasureTheory Filter Topology Set Metric


namespace LandauMellin

/-- `mellinK A k s = ∫_{x>1} A(x) (-log x)^k x^{-s-1} dx`; for `k = 0` this is the Mellin-type
transform `F(s) = ∫_{x>1} A(x) x^{-s-1} dx`, and `mellinK A k` is its `k`-th derivative. -/
def mellinK (A : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1)

/-- Convergence of the real Mellin integral `∫_{x>1} A(x) x^{-σ-1} dx`. -/
def Conv (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => A x * x ^ (-σ - 1)) (Ioi 1)

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

lemma conv_mono {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ}
    (h : Conv A σ) (hσ : σ ≤ σ') : Conv A σ' := by
  refine h.mono' ((hA.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 x hx') (Real.rpow_nonneg (by linarith) _))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (hA0 x hx')

/-- Absolute convergence of the real Mellin integral `∫_{x>1} |A(x)| x^{-σ-1} dx`. -/
def ConvAbs (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => |A x| * x ^ (-σ - 1)) (Ioi 1)

lemma convAbs_of_conv {A : ℝ → ℝ} (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ : ℝ} (h : Conv A σ) :
    ConvAbs A σ := by
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

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

lemma integrableOn_log_pow_of_nonneg {A : ℝ → ℝ} (hA : Measurable A)
    (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ} (hσ : σ < σ') (hc : Conv A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => A x * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  refine IntegrableOn.congr_fun (integrableOn_log_pow hA hσ (convAbs_of_conv hA0 hc) k)
    (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

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

lemma iteratedDeriv_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) :
    ∀ s : ℂ, τ < s.re → iteratedDeriv k (mellinK A 0) s = mellinK A k s := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | τ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : iteratedDeriv k (mellinK A 0) =ᶠ[𝓝 s] mellinK A k := by
      filter_upwards [hopen.mem_nhds hs] with z hz using ih z hz
    rw [hev.deriv_eq]
    exact (hasDerivAt_mellinK hA hconv k hs).deriv

lemma differentiableOn_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) :
    DifferentiableOn ℂ (mellinK A k) {z : ℂ | τ < z.re} := fun _ hz =>
  (hasDerivAt_mellinK hA hconv k hz).differentiableAt.differentiableWithinAt

end LandauMellin

end

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

end ZetaAux

end

section

open Complex Filter Topology

namespace PsiOscillation

open ZetaAux

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

end PsiOscillation

end

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

section

open Complex MeasureTheory Filter Topology Set


namespace VonKoch

open ArithmeticFunction

/-- The Riesz mean `ψ₁(x) = ∑_n Λ(n) (x - n)₊`. -/
def psi1 (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * max (x - n) 0

/-- The kernel `x^{s+1} / (s (s+1))`. -/
def kerX (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ (s + 1) / (s * (s + 1))

/-! ### Elementary bounds -/

lemma normSq_le_norm_mul {s : ℂ} (hs : 0 ≤ s.re) : ‖s‖ ^ 2 ≤ ‖s * (s + 1)‖ := by
  rw [norm_mul, sq]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, one_re, add_im, one_im, add_zero]
  nlinarith

lemma norm_sq_eq (σ t : ℝ) : ‖(σ : ℂ) + t * I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

lemma norm_kerX_le {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖kerX x (σ + t * I)‖ ≤ x ^ (σ + 1) / (σ ^ 2 + t ^ 2) := by
  have hpos : 0 < σ ^ 2 + t ^ 2 := by positivity
  rw [kerX, norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, one_re]
  apply div_le_div_of_nonneg_left (by positivity) hpos
  rw [← norm_sq_eq]
  exact normSq_le_norm_mul (by simp; exact hσ.le)

lemma integrable_inv_sq_add_sq {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by
  have h := (integrable_inv_one_add_sq.comp_div (show σ ≠ 0 from hσ.ne')).const_mul (σ ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [div_pow]
  field_simp

lemma continuous_kerX_vert {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => kerX x (σ + t * I) := by
  have hden : ∀ t : ℝ, ((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) ≠ 0 := by
    intro t h
    rcases mul_eq_zero.mp h with h | h
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  unfold kerX
  refine Continuous.div ?_ (by fun_prop) hden
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hx.ne'

lemma integrable_kerX_vert {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun t : ℝ => kerX x (σ + t * I) := by
  refine ((integrable_inv_sq_add_sq hσ).const_mul (x ^ (σ + 1))).mono'
    (continuous_kerX_vert hx hσ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [← div_eq_mul_inv]
  exact norm_kerX_le hx hσ t

/-! ### The Mellin transform of `(1 - u)₊` -/

/-- `f(u) = (1 - u)₊`. -/
def wedge (u : ℝ) : ℂ := ((max (1 - u) 0 : ℝ) : ℂ)

lemma wedge_eq_on (u : ℝ) (hu : u ∈ Ioi (0:ℝ)) :
    wedge u = (indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ)) u -
      (indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1:ℂ) : ℝ → ℂ)) u := by
  have hu' : (0:ℝ) < u := hu
  by_cases h1 : u ≤ 1
  · have hmem : u ∈ Ioc (0:ℝ) 1 := ⟨hu', h1⟩
    rw [indicator_of_mem hmem, indicator_of_mem hmem, wedge, max_eq_left (by linarith)]
    simp
  · have hmem : u ∉ Ioc (0:ℝ) 1 := fun h => h1 h.2
    rw [indicator_of_notMem hmem, indicator_of_notMem hmem, wedge, max_eq_right (by linarith)]
    simp

lemma hasMellin_wedge {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent wedge s ∧ mellin wedge s = 1 / (s * (s + 1)) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1:ℂ) (s := s) (by simp; linarith)
  have h3 := hasMellin_sub h1.1 h2.1
  have hcongr : ∀ t ∈ Ioi (0:ℝ), (t : ℂ) ^ (s - 1) • wedge t =
      (t : ℂ) ^ (s - 1) • ((indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ)) t -
        (indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1:ℂ) : ℝ → ℂ)) t) := by
    intro t ht; rw [wedge_eq_on t ht]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  constructor
  · exact (integrableOn_congr_fun hcongr measurableSet_Ioi).mpr h3.1
  · have : mellin wedge s = mellin (fun t => (indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ)) t -
        (indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1:ℂ) : ℝ → ℂ)) t) s :=
      setIntegral_congr_fun measurableSet_Ioi hcongr
    rw [this, h3.2, h1.2, h2.2]
    field_simp
    ring

lemma continuous_wedge : Continuous wedge := by
  unfold wedge; fun_prop

/-- Mellin inversion for `(1 - u)₊`: for `y > 0`,
`(1/2Real.pi) ∫ y^{-(σ+it)} / ((σ+it)(σ+it+1)) dt = (1 - y)₊`. -/
lemma mellinInv_wedge {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi)) • ∫ t : ℝ, (y : ℂ) ^ (-((σ:ℂ) + t * I)) *
      (1 / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) = wedge y := by
  have hre : ∀ t : ℝ, 0 < ((σ:ℂ) + t * I).re := fun t => by simp [hσ]
  have hint : VerticalIntegrable (mellin wedge) σ := by
    unfold VerticalIntegrable
    have hcongr : (fun t : ℝ => mellin wedge (σ + t * I)) =
        fun t : ℝ => kerX 1 (σ + t * I) := by
      funext t
      rw [(hasMellin_wedge (hre t)).2, kerX]
      simp
    rw [hcongr]
    exact integrable_kerX_vert one_pos hσ
  have h := mellinInv_mellin_eq σ wedge hy (hasMellin_wedge (by simpa using hσ)).1 hint
    continuous_wedge.continuousAt
  rw [← h, mellinInv]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [(hasMellin_wedge (hre t)).2]

/-- One term of the Perron formula: for `n ≥ 1` and `x > 0`,
`∫ n^{-s} x^{s+1}/(s(s+1)) dt = 2Real.pi (x - n)₊` on the line `Re s = σ > 0`. -/
lemma perron_term {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∫ t : ℝ, (n : ℂ) ^ (-((σ:ℂ) + t * I)) * kerX x (σ + t * I) =
      2 * Real.pi * ((max (x - n) 0 : ℝ) : ℂ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hy : 0 < (n:ℝ) / x := div_pos hn0 hx
  have h := mellinInv_wedge hσ hy
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpt : ∀ t : ℝ, (n : ℂ) ^ (-((σ:ℂ) + t * I)) * kerX x (σ + t * I) =
      (x : ℂ) * ((((n:ℝ) / x : ℝ) : ℂ) ^ (-((σ:ℂ) + t * I)) *
        (1 / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))) := by
    intro t
    have hdiv : ((((n:ℝ) / x : ℝ)) : ℂ) = (((n:ℝ)) : ℂ) * (((x⁻¹ : ℝ)) : ℂ) := by
      rw [div_eq_mul_inv, ofReal_mul]
    have hxinv : ((x : ℂ))⁻¹ = (((x⁻¹ : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiv, mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr hx.le)]
    rw [← hxinv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)]
    rw [kerX, cpow_neg (x : ℂ), inv_inv, cpow_add _ _ hx0, cpow_one]
    simp only [ofReal_natCast]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul]
  have h2 : ∫ t : ℝ, ((((n:ℝ) / x : ℝ)) : ℂ) ^ (-((σ:ℂ) + t * I)) *
      (1 / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) = 2 * Real.pi * wedge ((n:ℝ) / x) := by
    rw [← h, Complex.real_smul]
    have : (2 * (Real.pi:ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    generalize (∫ t : ℝ, ((((n:ℝ) / x : ℝ)) : ℂ) ^ (-((σ:ℂ) + t * I)) *
      (1 / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))) = J
    push_cast
    field_simp
  rw [h2, wedge]
  have : x * max (1 - n / x) 0 = max (x - n) 0 := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hx.ne']
  rw [← this]
  push_cast
  ring

/-! ### The Perron formula for `ψ₁` -/

lemma psi1_eq_tsum (x : ℝ) :
    ∑' n : ℕ, (Λ n : ℝ) * max (x - n) 0 = psi1 x := by
  rw [psi1]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have : x < n := by
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    linarith
  rw [max_eq_right (by linarith), mul_zero]

/-- **Perron's formula** for `ψ₁` on the line `Re s = σ > 1`. -/
theorem perron {σ : ℝ} (hσ : 1 < σ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, LSeries (fun n => (Λ n : ℂ)) (σ + t * I) * kerX x (σ + t * I) =
      2 * Real.pi * psi1 x := by
  have hσ0 : 0 < σ := by linarith
  set F : ℕ → ℝ → ℂ := fun n t => LSeries.term (fun n => (Λ n : ℂ)) (σ + t * I) n *
    kerX x (σ + t * I) with hFdef
  have hterm : ∀ n : ℕ, ∀ t : ℝ, LSeries.term (fun n => (Λ n : ℂ)) (σ + t * I) n =
      (Λ n : ℂ) * (n : ℂ) ^ (-((σ:ℂ) + t * I)) := by
    intro n t
    exact LSeries.term_def₀ (by simp) _ n
  have hnormterm : ∀ n : ℕ, ∀ t : ℝ, ‖LSeries.term (fun n => (Λ n : ℂ)) (σ + t * I) n‖ =
      ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖ := by
    intro n t
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have hc : Continuous fun t : ℝ => LSeries.term (fun n => (Λ n : ℂ)) (σ + t * I) n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]; exact continuous_const
      · simp_rw [hterm n]
        refine continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl ?_))
        exact_mod_cast hn
    refine ((integrable_kerX_vert hx hσ0).norm.const_mul
      ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖).mono'
      (hc.mul (continuous_kerX_vert hx hσ0)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [hFdef]; dsimp only
    rw [norm_mul, hnormterm]
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    have hnorm : ∀ n, ∫ t, ‖F n t‖ =
        ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖ * ∫ t : ℝ, ‖kerX x (σ + t * I)‖ := by
      intro n
      have : (fun t : ℝ => ‖F n t‖) = fun t : ℝ => ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖ *
          ‖kerX x (σ + t * I)‖ := by
        funext t
        rw [hFdef]; dsimp only
        rw [norm_mul, hnormterm]
      rw [this, integral_const_mul]
    simp_rw [hnorm]
    exact (LSeriesSummable_vonMangoldt (by simpa using hσ)).norm.mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFint hsum
  have hL : ∀ t : ℝ, LSeries (fun n => (Λ n : ℂ)) (σ + t * I) * kerX x (σ + t * I) =
      ∑' n, F n t := by
    intro t
    rw [LSeries, hFdef]
    dsimp only
    rw [tsum_mul_right]
  simp_rw [hL]
  rw [← hswap]
  have hval : ∀ n : ℕ, ∫ t, F n t = 2 * Real.pi * (((Λ n : ℝ) * max (x - n) 0 : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hFdef]
    · rw [hFdef]; dsimp only
      simp_rw [hterm n, mul_assoc]
      rw [integral_const_mul, perron_term hσ0 hx hn]
      push_cast; ring
  simp_rw [hval]
  rw [tsum_mul_left, ← ofReal_tsum, psi1_eq_tsum]

end VonKoch

end

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
  exact ((h x hx).comp (f := fun x : ℝ => (x : ℂ) + y * I) (by fun_prop)).continuousWithinAt

lemma intervalIntegrable_vert {f : ℂ → ℂ} {y₁ y₂ x : ℝ}
    (h : ∀ y ∈ uIcc y₁ y₂, ContinuousAt f (x + y * I)) :
    IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume y₁ y₂ := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  exact ((h y hy).comp (f := fun y : ℝ => (x : ℂ) + y * I) (by fun_prop)).continuousWithinAt

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

lemma norm_LSeries_vonMangoldt_le (t : ℝ) :
    ‖LSeries (fun n => (Λ n : ℂ)) (3/2 + t * I)‖ ≤
      ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3/2 : ℂ) n‖ := by
  have hsre : 1 < ((3/2 : ℂ) + t * I).re := by simp; norm_num
  calc ‖LSeries (fun n => (Λ n : ℂ)) (3/2 + t * I)‖
      ≤ ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3/2 + t * I) n‖ :=
        norm_tsum_le_tsum_norm (LSeriesSummable_vonMangoldt hsre).norm
    _ = _ := by
        congr 1; funext n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
        simp

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

/-- Zeros in a window of height `8/5` (counted with multiplicity) number `O(log t)`. -/
theorem zero_count (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ∀ W : Finset ℂ,
    (∀ u ∈ W, zetaMulSubOne u = 0 ∧ 0 < u.re ∧ |u.im - t| ≤ 4/5) →
    (∑ u ∈ W, (analyticOrderNatAt zetaMulSubOne u : ℝ)) ≤ A * Real.log (|t| + 3) := by
  obtain ⟨A, hA, hland⟩ := landau_h
  refine ⟨A, hA, fun t W hW => ?_⟩
  obtain ⟨S, -, hS2, hS3, -⟩ := hland t
  have hsub : W ⊆ S := by
    intro u hu
    obtain ⟨h0, hre, him⟩ := hW u hu
    exact hS2 u (mem_closedBall_of_re_half (re_eq_half_of_zero hRH h0 hre) him) h0
  calc (∑ u ∈ W, (analyticOrderNatAt zetaMulSubOne u : ℝ))
      ≤ ∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ A * Real.log (|t| + 3) := hS3

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

/-- Under RH, `|F(1/4 + it)| = O(log t)`. -/
theorem Fh_quarter_bound (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
    zetaMulSubOne (1/4 + t * I) ≠ 0 ∧ ‖Fh (1/4 + t * I)‖ ≤ A * Real.log (|t| + 3) := by
  obtain ⟨A, hA, hland⟩ := landau_h
  refine ⟨5 * A + 2, by positivity, fun t => ?_⟩
  obtain ⟨S, hS1, -, hS3, hS4⟩ := hland t
  set z : ℂ := 1/4 + t * I with hz
  have hz0 : zetaMulSubOne z ≠ 0 := by
    intro h
    have := re_eq_half_of_zero hRH h (by rw [hz]; simp)
    rw [hz] at this; norm_num at this
  refine ⟨hz0, ?_⟩
  set ℓ := Real.log (|t| + 3) with hℓdef
  have hℓ : 1 ≤ ℓ := one_le_log_of_three_le (by linarith [abs_nonneg t])
  have hzball : z ∈ closedBall ((3/2 : ℂ) + t * I) (5/4) := by
    rw [mem_closedBall, dist_eq_norm, hz]
    have : (1/4 : ℂ) + t * I - (3/2 + t * I) = ((-5/4 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real]; norm_num
  have hdist : ∀ u ∈ S, 1/4 ≤ ‖z - u‖ := by
    intro u hu
    have hre := re_eq_half_of_zero hRH (hS1 u hu).2 (re_pos_of_mem_S (hS1 u hu).1)
    have h1 := Complex.abs_re_le_norm (z - u)
    rw [sub_re, hre, hz] at h1
    simp at h1; norm_num at h1
    linarith
  have hsum := norm_sum_div_le (by norm_num : (0:ℝ) < 1/4) hdist
    (fun u => analyticOrderNatAt zetaMulSubOne u)
  have hlog : ‖deriv zetaMulSubOne z / zetaMulSubOne z‖ ≤ 5 * A * ℓ := by
    have h1 := hS4 z hzball hz0
    calc ‖deriv zetaMulSubOne z / zetaMulSubOne z‖
        ≤ ‖deriv zetaMulSubOne z / zetaMulSubOne z -
            ∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℂ) / (z - u)‖ +
          ‖∑ u ∈ S, (analyticOrderNatAt zetaMulSubOne u : ℂ) / (z - u)‖ := norm_le_norm_sub_add _ _
      _ ≤ A * ℓ + (A * ℓ) / (1/4) := by
          gcongr
          exact hsum.trans (div_le_div_of_nonneg_right hS3 (by norm_num))
      _ = 5 * A * ℓ := by ring
  have hinv : ‖(z - 1)⁻¹‖ ≤ 4/3 := by
    rw [norm_inv]
    have h1 := Complex.abs_re_le_norm (z - 1)
    rw [hz] at h1; simp at h1; norm_num at h1
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖Fh z‖ ≤ ‖(z - 1)⁻¹‖ + ‖deriv zetaMulSubOne z / zetaMulSubOne z‖ := norm_sub_le _ _
    _ ≤ 4/3 + 5 * A * ℓ := add_le_add hinv hlog
    _ ≤ (5 * A + 2) * ℓ := by nlinarith

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

lemma sum_range_inv_succ_le (K : ℕ) :
    ∑ j ∈ Finset.range K, 1 / ((j:ℝ) + 1) ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  have e : ((harmonic K : ℚ) : ℝ) = ∑ j ∈ Finset.range K, 1 / ((j:ℝ) + 1) := by
    simp [harmonic, one_div]
  rw [← e]
  exact h

/-- Under RH, `∑_{|γ| ≤ Y} m_ρ / |ρ| = O(log² Y)`. -/
theorem zero_sum (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 < A ∧ ∀ Y : ℝ, 0 ≤ Y →
    ∀ Z : Finset ℂ, (∀ u ∈ Z, zetaMulSubOne u = 0 ∧ 0 < u.re ∧ |u.im| ≤ Y) →
    (∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖) ≤ A * Real.log (Y + 4) ^ 2 := by
  classical
  obtain ⟨A₁, hA₁, hcount⟩ := zero_count hRH
  refine ⟨16 * A₁, by positivity, fun Y hY Z hZ => ?_⟩
  set m : ℂ → ℝ := fun u => (analyticOrderNatAt zetaMulSubOne u : ℝ) with hm
  set k : ℂ → ℕ := fun u => ⌊|u.im|⌋₊ with hk
  set K : ℕ := ⌊Y⌋₊ + 1 with hK
  set ℓ := Real.log (Y + 4) with hℓdef
  have hℓ : 1 ≤ ℓ := one_le_log_of_three_le (by linarith)
  have hmaps : ∀ u ∈ Z, k u ∈ Finset.range K := by
    intro u hu
    rw [Finset.mem_range, hK, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hZ u hu).2.2
  have hm0 : ∀ u, 0 ≤ m u := fun u => Nat.cast_nonneg _
  have hfiber : ∀ j ∈ Finset.range K,
      ∑ u ∈ Z with k u = j, m u / ‖u‖ ≤ 8 * A₁ * ℓ / ((j:ℝ) + 1) := by
    intro j hj
    have hjY : (j:ℝ) ≤ Y := by
      rw [Finset.mem_range, hK, Nat.lt_succ_iff] at hj
      exact (Nat.cast_le.mpr hj).trans (Nat.floor_le hY)
    set Zj := Z.filter (fun u => k u = j) with hZj
    have hmem : ∀ u ∈ Zj, u ∈ Z ∧ (j:ℝ) ≤ |u.im| ∧ |u.im| < j + 1 := by
      intro u hu
      rw [hZj, Finset.mem_filter] at hu
      have hku : ⌊|u.im|⌋₊ = j := hu.2
      refine ⟨hu.1, ?_, ?_⟩
      · rw [← hku]; exact Nat.floor_le (abs_nonneg _)
      · rw [← hku]; exact Nat.lt_floor_add_one _
    have hnorm : ∀ u ∈ Zj, ((j:ℝ) + 1) / 4 ≤ ‖u‖ := by
      intro u hu
      obtain ⟨huZ, h1, -⟩ := hmem u hu
      have hre := re_eq_half_of_zero hRH (hZ u huZ).1 (hZ u huZ).2.1
      have h2 := Complex.abs_im_le_norm u
      have h3 := Complex.abs_re_le_norm u
      rw [hre] at h3
      norm_num at h3
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hsum_m : ∑ u ∈ Zj, m u ≤ 2 * A₁ * ℓ := by
      rw [← Finset.sum_filter_add_sum_filter_not Zj (fun u => 0 ≤ u.im) m]
      have hlog : Real.log (|(j:ℝ) + 1/2| + 3) ≤ ℓ := by
        apply Real.log_le_log (by positivity)
        rw [abs_of_nonneg (by positivity)]
        linarith
      have hpos : ∑ u ∈ Zj with 0 ≤ u.im, m u ≤ A₁ * ℓ := by
        refine (hcount ((j:ℝ) + 1/2) _ fun u hu => ?_).trans (by gcongr)
        rw [Finset.mem_filter] at hu
        obtain ⟨huZ, h1, h2⟩ := hmem u hu.1
        rw [abs_of_nonneg hu.2] at h1 h2
        refine ⟨(hZ u huZ).1, (hZ u huZ).2.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      have hneg : ∑ u ∈ Zj with ¬ 0 ≤ u.im, m u ≤ A₁ * ℓ := by
        refine (hcount (-((j:ℝ) + 1/2)) _ fun u hu => ?_).trans ?_
        · rw [Finset.mem_filter] at hu
          obtain ⟨huZ, h1, h2⟩ := hmem u hu.1
          rw [abs_of_neg (not_le.mp hu.2)] at h1 h2
          refine ⟨(hZ u huZ).1, (hZ u huZ).2.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
        · rw [abs_neg]; gcongr
      linarith
    have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    calc ∑ u ∈ Zj, m u / ‖u‖ ≤ ∑ u ∈ Zj, m u * (4 / ((j:ℝ) + 1)) := by
          refine Finset.sum_le_sum fun u hu => ?_
          rw [div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (hm0 u)
          rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (hnorm u hu)) (by positivity)]
          rw [inv_div]
          exact hnorm u hu
      _ = (∑ u ∈ Zj, m u) * (4 / ((j:ℝ) + 1)) := by rw [Finset.sum_mul]
      _ ≤ (2 * A₁ * ℓ) * (4 / ((j:ℝ) + 1)) := by gcongr
      _ = 8 * A₁ * ℓ / ((j:ℝ) + 1) := by ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hK1 : Real.log K ≤ ℓ := by
    apply Real.log_le_log (by rw [hK]; positivity)
    rw [hK]; push_cast
    linarith [Nat.floor_le hY]
  calc ∑ j ∈ Finset.range K, ∑ u ∈ Z with k u = j, m u / ‖u‖
      ≤ ∑ j ∈ Finset.range K, 8 * A₁ * ℓ / ((j:ℝ) + 1) := Finset.sum_le_sum hfiber
    _ = 8 * A₁ * ℓ * ∑ j ∈ Finset.range K, 1 / ((j:ℝ) + 1) := by
        rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ 8 * A₁ * ℓ * (1 + ℓ) := by
        gcongr
        exact (sum_range_inv_succ_le K).trans (by linarith)
    _ ≤ 16 * A₁ * ℓ ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg hA₁.le (by linarith : (0:ℝ) ≤ ℓ))
          (by linarith : (0:ℝ) ≤ ℓ - 1)]

end VonKoch

end

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

/-- **Explicit formula on a rectangle** (under RH): for `D` holomorphic on `Re s > 0`,
`∮ F(s) D(s) ds = 2πi (D(1) - ∑_ρ m_ρ D(ρ))` over the boundary of `[1/4, 3/2] × [-T₂, T₁]`,
where `T₁, -T₂` are at distance `≥ δ` from all ordinates of zeros. -/
theorem rect_explicit (hRH : RiemannHypothesis) {T₁ T₂ δ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hgood : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T₁| ∧ δ ≤ |u.im + T₂|)
    {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D {s : ℂ | 0 < s.re}) :
    ∃ Z : Finset ℂ, (∀ u ∈ Z, zetaMulSubOne u = 0 ∧ u.re = 1/2 ∧ -T₂ < u.im ∧ u.im < T₁) ∧
      rectInt (fun s => Fh s * D s) (1/4) (3/2) (-T₂) T₁ =
        2 * Real.pi * I * (D 1 - ∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℂ) * D u) := by
  classical
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set U : Set ℂ := Icc (1/4 - ε) (3/2 + ε) ×ℂ Icc (-T₂ - ε) (T₁ + ε) with hU
  have hUc : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  have hUp : IsPreconnected U := (convex_Icc_reProdIm _ _ _ _).isPreconnected
  have hint : ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/2) → s.im ∈ Icc (-T₂) T₁ → U ∈ 𝓝 s := by
    intro s h1 h2
    refine mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ?_)
      (reProdIm_subset_iff.mpr (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    rw [mem_reProdIm]
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  have h1U : U ∈ 𝓝 (1:ℂ) := hint 1 (by simp; norm_num) (by simp; constructor <;> linarith)
  have hf : AnalyticOnNhd ℂ zetaMulSubOne U := fun z _ => differentiable_zetaMulSubOne.analyticAt z
  obtain ⟨Z, g, hZ1, hZ2, hg, hg0, hEq⟩ := factorization hUc hUp hf h1U
    (by rw [zetaMulSubOne_one]; exact one_ne_zero)
  set m : ℂ → ℕ := fun u => analyticOrderNatAt zetaMulSubOne u with hm
  -- location of the zeros
  have hZloc : ∀ u ∈ Z, zetaMulSubOne u = 0 ∧ u.re = 1/2 ∧ -T₂ < u.im ∧ u.im < T₁ := by
    intro u hu
    obtain ⟨huU, h0⟩ := hZ1 u hu
    rw [hU, mem_reProdIm] at huU
    have hre0 : 0 < u.re := by linarith [huU.1.1]
    obtain ⟨g1, g2⟩ := hgood u h0 hre0
    refine ⟨h0, re_eq_half_of_zero hRH h0 hre0, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have : |u.im + T₂| ≤ ε := abs_le.mpr ⟨by linarith [huU.2.1], by linarith⟩
      linarith
    · by_contra hc
      push Not at hc
      have : |u.im - T₁| ≤ ε := abs_le.mpr ⟨by linarith, by linarith [huU.2.2]⟩
      linarith
  -- the boundary avoids the zeros and `1`
  have hbdry_ne : ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/2) → s.im ∈ Icc (-T₂) T₁ →
      (s.re = 1/4 ∨ s.re = 3/2 ∨ s.im = -T₂ ∨ s.im = T₁) → zetaMulSubOne s ≠ 0 := by
    intro s h1 h2 hs h0
    have hre0 : 0 < s.re := by linarith [h1.1]
    have hhalf := re_eq_half_of_zero hRH h0 hre0
    obtain ⟨g1, g2⟩ := hgood s h0 hre0
    rcases hs with hs | hs | hs | hs
    · rw [hs] at hhalf; norm_num at hhalf
    · rw [hs] at hhalf; norm_num at hhalf
    · rw [hs] at g2; simp at g2; linarith
    · rw [hs] at g1; simp at g1; linarith
  have hZin : ∀ u ∈ Z, 1/4 < u.re ∧ u.re < 3/2 ∧ -T₂ < u.im ∧ u.im < T₁ := by
    intro u hu
    obtain ⟨-, h1, h2, h3⟩ := hZloc u hu
    exact ⟨by rw [h1]; norm_num, by rw [h1]; norm_num, h2, h3⟩
  -- the decomposition on the boundary
  have hV : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hrectV : [[(1/4 : ℝ), 3/2]] ×ℂ [[-T₂, T₁]] ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hs
    show 0 < s.re
    linarith [hs.1.1]
  have hrectU : [[(1/4 : ℝ), 3/2]] ×ℂ [[-T₂, T₁]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hs
    rw [hU, mem_reProdIm]
    exact ⟨⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩, ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩⟩
  set Φ : ℂ → ℂ := fun s => D s * (s - 1)⁻¹ -
    (∑ u ∈ Z, (m u : ℂ) * (D s * (s - u)⁻¹)) - (deriv g s / g s) * D s with hΦ
  have hcongr : rectInt (fun s => Fh s * D s) (1/4) (3/2) (-T₂) T₁ =
      rectInt Φ (1/4) (3/2) (-T₂) T₁ := by
    refine rectInt_congr (fun s h1 h2 hs => ?_)
    rw [uIcc_of_le (by norm_num)] at h1
    rw [uIcc_of_le (by linarith)] at h2
    have hs0 := hbdry_ne s h1 h2 hs
    have hsU := hint s h1 h2
    have hev : zetaMulSubOne =ᶠ[𝓝 s] fun z => (∏ u ∈ Z, (z - u) ^ m u) * g z := by
      filter_upwards [hsU] with z hz using hEq hz
    have hgd : DifferentiableAt ℂ g s := (hg s (mem_of_mem_nhds hsU)).differentiableAt
    have hlog := logDeriv_factor hev hs0 hgd
    simp only [Fh, hΦ]
    rw [hlog]
    have hsum : ∑ u ∈ Z, (m u : ℂ) * (D s * (s - u)⁻¹) = (∑ u ∈ Z, (m u : ℂ) / (s - u)) * D s := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun u _ => by ring)
    rw [hsum]
    ring
  -- continuity on the boundary
  have hDdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ D s := fun s hs =>
    hD.differentiableAt (hV.mem_nhds hs)
  have hbd_ne_pt : ∀ a : ℂ, 1/4 < a.re → a.re < 3/2 → -T₂ < a.im → a.im < T₁ →
      ∀ s : ℂ, (s.re = 1/4 ∨ s.re = 3/2 ∨ s.im = -T₂ ∨ s.im = T₁) → s ≠ a := by
    rintro a h1 h2 h3 h4 s hs rfl
    rcases hs with h | h | h | h <;> linarith
  have h1in : 1/4 < (1:ℂ).re ∧ (1:ℂ).re < 3/2 ∧ -T₂ < (1:ℂ).im ∧ (1:ℂ).im < T₁ := by
    simp; refine ⟨by norm_num, by norm_num, hT₂, hT₁⟩
  have hBa : ∀ a : ℂ, 1/4 < a.re → a.re < 3/2 → -T₂ < a.im → a.im < T₁ →
      BdryCont (fun s => D s * (s - a)⁻¹) (1/4) (3/2) (-T₂) T₁ := by
    intro a h1 h2 h3 h4
    refine BdryCont.of_bdry fun s hs1 _ hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs1
    exact (hDdiff s (by linarith [hs1.1])).continuousAt.mul
      ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (hbd_ne_pt a h1 h2 h3 h4 s hs)))
  have hB1 := hBa 1 h1in.1 h1in.2.1 h1in.2.2.1 h1in.2.2.2
  have hBu : ∀ u ∈ Z, BdryCont (fun s => (m u : ℂ) * (D s * (s - u)⁻¹)) (1/4) (3/2) (-T₂) T₁ :=
    fun u hu => (hBa u (hZin u hu).1 (hZin u hu).2.1 (hZin u hu).2.2.1 (hZin u hu).2.2.2).const_mul _
  have hgD : ∀ s ∈ [[(1/4 : ℝ), 3/2]] ×ℂ [[-T₂, T₁]],
      DifferentiableAt ℂ (fun s => deriv g s / g s * D s) s := by
    intro s hs
    have hsU := hrectU hs
    have hgs := hg s hsU
    exact (hgs.deriv.differentiableAt.div hgs.differentiableAt (hg0 s hsU)).mul
      (hDdiff s (hrectV hs))
  have hBg : BdryCont (fun s => deriv g s / g s * D s) (1/4) (3/2) (-T₂) T₁ :=
    BdryCont.of_forall fun s h1 h2 => (hgD s (by rw [mem_reProdIm]; exact ⟨h1, h2⟩)).continuousAt
  refine ⟨Z, hZloc, ?_⟩
  rw [hcongr, hΦ, rectInt_sub (hB1.sub (BdryCont.sum Z hBu)) hBg,
    rectInt_sub hB1 (BdryCont.sum Z hBu), rectInt_sum Z hBu,
    rectInt_mul_inv h1in.1 h1in.2.1 h1in.2.2.1 h1in.2.2.2 hV hrectV hD,
    rectInt_eq_zero (fun s hs => (hgD s hs).differentiableWithinAt)]
  have hres : ∀ u ∈ Z, rectInt (fun s => (m u : ℂ) * (D s * (s - u)⁻¹)) (1/4) (3/2) (-T₂) T₁ =
      2 * Real.pi * I * ((m u : ℂ) * D u) := by
    intro u hu
    rw [rectInt_const_mul, rectInt_mul_inv (hZin u hu).1 (hZin u hu).2.1 (hZin u hu).2.2.1
      (hZin u hu).2.2.2 hV hrectV hD]
    ring
  rw [Finset.sum_congr rfl hres, ← Finset.mul_sum]
  ring

end VonKoch

end

section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval


namespace VonKoch

open ZetaAux ArithmeticFunction

/-! ### The difference kernel `D(s) = ((X+H)^{s+1} - X^{s+1}) / (s(s+1))` -/

def Dk (X H : ℝ) (s : ℂ) : ℂ := kerX (X + H) s - kerX X s

lemma Dk_eq_integral (X H : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Dk X H s = (∫ x in X..X + H, (x : ℂ) ^ s) / s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [integral_cpow (Or.inl (by linarith : -1 < s.re)), Dk, kerX, kerX]
  push_cast
  field_simp

lemma norm_Dk_le {X H : ℝ} (hX : 0 < X) (hH : 0 < H) {s : ℂ} (hs : 0 < s.re) :
    ‖Dk X H s‖ ≤ H * (X + H) ^ s.re / ‖s‖ := by
  rw [Dk_eq_integral X H hs, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := X) (b := X + H)
    (f := fun x : ℝ => (x : ℂ) ^ s) (C := (X + H) ^ s.re) (fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      have hx0 : 0 < x := lt_trans hX hx.1
      rw [norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_rpow hx0.le hx.2 hs.le)
  rw [show X + H - X = H by ring, abs_of_pos hH] at h
  linarith

lemma norm_Dk_le_sq {X H : ℝ} (hX : 1 ≤ X) (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 3/2)
    (t : ℝ) : ‖Dk X H (σ + t * I)‖ ≤ 2 * (X + H) ^ (5/2 : ℝ) / (σ ^ 2 + t ^ 2) := by
  have h1 := norm_kerX_le (by linarith : 0 < X + H) hσ t
  have h2 := norm_kerX_le (by linarith : 0 < X) hσ t
  have hpos : 0 < σ ^ 2 + t ^ 2 := by positivity
  have e1 : (X + H) ^ (σ + 1) ≤ (X + H) ^ (5/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have e2 : X ^ (σ + 1) ≤ (X + H) ^ (5/2 : ℝ) :=
    (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  calc ‖Dk X H (σ + t * I)‖ ≤ ‖kerX (X + H) (σ + t * I)‖ + ‖kerX X (σ + t * I)‖ :=
        norm_sub_le _ _
    _ ≤ (X + H) ^ (σ + 1) / (σ ^ 2 + t ^ 2) + X ^ (σ + 1) / (σ ^ 2 + t ^ 2) := add_le_add h1 h2
    _ ≤ (X + H) ^ (5/2 : ℝ) / (σ ^ 2 + t ^ 2) + (X + H) ^ (5/2 : ℝ) / (σ ^ 2 + t ^ 2) := by
        gcongr
    _ = 2 * (X + H) ^ (5/2 : ℝ) / (σ ^ 2 + t ^ 2) := by ring

lemma differentiableAt_kerX {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (kerX x) s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold kerX
  refine DifferentiableAt.div ?_ (by fun_prop) (mul_ne_zero hs0 hs1)
  refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hx.ne'

lemma differentiableOn_Dk {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    DifferentiableOn ℂ (Dk X H) {s : ℂ | 0 < s.re} := fun s hs =>
  ((differentiableAt_kerX (by linarith) hs).sub (differentiableAt_kerX hX hs)).differentiableWithinAt

lemma Dk_one (X H : ℝ) : Dk X H 1 = ((X * H + H ^ 2 / 2 : ℝ) : ℂ) := by
  simp only [Dk, kerX]
  rw [show (1:ℂ) + 1 = ((2:ℕ) : ℂ) by norm_num, cpow_natCast, cpow_natCast]
  push_cast
  ring

/-! ### Continuity of `F` -/

lemma continuousAt_Fh {s : ℂ} (hs1 : s ≠ 1) (hs0 : zetaMulSubOne s ≠ 0) : ContinuousAt Fh s := by
  have han := differentiable_zetaMulSubOne.analyticAt s
  unfold Fh
  exact ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs1)).sub
    (han.deriv.continuousAt.div han.continuousAt hs0)

lemma continuous_Fh_vert {σ : ℝ} (hσ : 1 < σ) : Continuous fun t : ℝ => Fh (σ + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h0 : zetaMulSubOne ((σ : ℂ) + t * I) ≠ 0 :=
    zetaMulSubOne_ne_zero_of_one_le_re (by simp; linarith)
  exact ContinuousAt.comp (f := fun t : ℝ => (σ:ℂ) + t * I) (continuousAt_Fh hs1 h0) (by fun_prop)

/-! ### Perron's formula for the difference kernel -/

lemma perron_Fh {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, Fh ((3/2 : ℝ) + t * I) * kerX x ((3/2 : ℝ) + t * I) = 2 * Real.pi * psi1 x := by
  rw [← perron (by norm_num : (1:ℝ) < 3/2) hx]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [Fh_eq_LSeries (by simp; norm_num)]

lemma integrable_Fh_kerX {x : ℝ} (hx : 0 < x) :
    Integrable fun t : ℝ => Fh ((3/2 : ℝ) + t * I) * kerX x ((3/2 : ℝ) + t * I) := by
  set M₁ := ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3/2 : ℂ) n‖
  refine ((integrable_kerX_vert hx (by norm_num : (0:ℝ) < 3/2)).norm.const_mul M₁).mono'
    ((continuous_Fh_vert (by norm_num)).mul (continuous_kerX_vert hx (by norm_num))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  gcongr
  rw [Fh_eq_LSeries (by simp; norm_num)]
  have := norm_LSeries_vonMangoldt_le t
  simpa using this

lemma perron_Dk {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    ∫ t : ℝ, Fh ((3/2 : ℝ) + t * I) * Dk X H ((3/2 : ℝ) + t * I) =
      2 * Real.pi * ((psi1 (X + H) - psi1 X : ℝ) : ℂ) := by
  simp only [Dk, mul_sub]
  rw [integral_sub (integrable_Fh_kerX (by linarith)) (integrable_Fh_kerX hX),
    perron_Fh (by linarith), perron_Fh hX]
  push_cast
  ring

/-! ### Differencing `ψ₁` -/

lemma psi1_eq_sum_range {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x < N) :
    psi1 x = ∑ n ∈ Finset.range N, Λ n * max (x - n) 0 := by
  rw [psi1]
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_range] at hn ⊢
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    have h2 : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hn
    have : (n : ℝ) < N := by linarith
    exact_mod_cast this
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    have : x < n := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      have h2 := Nat.lt_floor_add_one x
      linarith
    rw [max_eq_right (by linarith), mul_zero]

lemma psi_eq_sum_range {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x < N) :
    Chebyshev.psi x = ∑ n ∈ Finset.range N, if (n:ℝ) ≤ x then Λ n else 0 := by
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, zero_le, true_and]
  rw [Nat.le_floor_iff hx]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have : (n:ℝ) < N := lt_of_le_of_lt h hN
    exact_mod_cast this
  · intro h; exact h.2

lemma psi1_diff_ge {X H : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) :
    H * Chebyshev.psi X ≤ psi1 (X + H) - psi1 X := by
  set N := ⌊X + H⌋₊ + 1
  have hN : X + H < N := by
    have := Nat.lt_floor_add_one (X + H)
    simp only [N]; push_cast; linarith
  rw [psi1_eq_sum_range (by linarith) hN, psi1_eq_sum_range hX (by linarith),
    psi_eq_sum_range hX (by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  split_ifs with h
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · push Not at h
    have : max (X - n) 0 = 0 := max_eq_right (by linarith)
    rw [mul_zero, ← mul_sub, this, sub_zero]
    exact mul_nonneg hΛ (le_max_right _ _)

lemma psi1_diff_le {X H : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) :
    psi1 (X + H) - psi1 X ≤ H * Chebyshev.psi (X + H) := by
  set N := ⌊X + H⌋₊ + 1
  have hN : X + H < N := by
    have := Nat.lt_floor_add_one (X + H)
    simp only [N]; push_cast; linarith
  rw [psi1_eq_sum_range (by linarith) hN, psi1_eq_sum_range hX (by linarith),
    psi_eq_sum_range (by linarith) hN, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  rw [← mul_sub]
  split_ifs with h
  · rw [mul_comm H]
    apply mul_le_mul_of_nonneg_left _ hΛ
    rcases le_or_gt (n:ℝ) X with h' | h'
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
  · push Not at h
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp

/-! ### Bounds for the pieces of the contour -/

/-- `∑ Λ(n) n^{-3/2}`, a bound for `|F(3/2 + it)|`. -/
def MΛ : ℝ := ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3/2 : ℂ) n‖

lemma MΛ_nonneg : 0 ≤ MΛ := tsum_nonneg fun _ => norm_nonneg _

lemma norm_Fh_vert_le (t : ℝ) : ‖Fh ((3/2 : ℝ) + t * I)‖ ≤ MΛ := by
  rw [Fh_eq_LSeries (by simp; norm_num)]
  have := norm_LSeries_vonMangoldt_le t
  simpa [MΛ] using this

lemma integral_inv_sq_add_sq {Y : ℝ} (hY : 0 < Y) :
    ∫ t : ℝ, (Y ^ 2 + t ^ 2)⁻¹ = Real.pi / Y := by
  have h1 : (fun t : ℝ => (Y ^ 2 + t ^ 2)⁻¹) = fun t : ℝ => (Y ^ 2)⁻¹ * (1 + (t / Y) ^ 2)⁻¹ := by
    funext t
    field_simp
  rw [h1, integral_const_mul, Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) Y,
    integral_univ_inv_one_add_sq, abs_of_pos hY, smul_eq_mul]
  field_simp

/-- The tails of the vertical line integral on `Re s = 3/2`. -/
lemma tail_bound {X H : ℝ} (hX : 1 ≤ X) (hH : 0 < H) {Y₀ T₁ T₂ : ℝ} (hY₀ : 0 < Y₀)
    (hT₁ : Y₀ ≤ T₁) (hT₂ : Y₀ ≤ T₂) :
    ‖(∫ t : ℝ, Fh ((3/2:ℝ) + t * I) * Dk X H ((3/2:ℝ) + t * I)) -
      ∫ t in (-T₂)..T₁, Fh ((3/2:ℝ) + t * I) * Dk X H ((3/2:ℝ) + t * I)‖ ≤
      4 * MΛ * (X + H) ^ (5/2 : ℝ) * Real.pi / Y₀ := by
  set g : ℝ → ℂ := fun t => Fh ((3/2:ℝ) + t * I) * Dk X H ((3/2:ℝ) + t * I) with hg
  have hgint : Integrable g := by
    have := (integrable_Fh_kerX (x := X + H) (by linarith)).sub (integrable_Fh_kerX (x := X)
      (by linarith))
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [hg, Dk, mul_sub, Pi.sub_apply]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl measurableSet_Ioc hgint,
    add_sub_cancel_left]
  set K : ℝ := 4 * MΛ * (X + H) ^ (5/2 : ℝ) with hK
  have hK0 : 0 ≤ K := by
    have := MΛ_nonneg
    positivity
  have hGint : Integrable fun t : ℝ => K * (Y₀ ^ 2 + t ^ 2)⁻¹ :=
    (integrable_inv_sq_add_sq hY₀).const_mul K
  have hbound : ∀ t ∈ (Ioc (-T₂) T₁)ᶜ, ‖g t‖ ≤ K * (Y₀ ^ 2 + t ^ 2)⁻¹ := by
    intro t ht
    have ht' : Y₀ ^ 2 ≤ t ^ 2 := by
      rw [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · nlinarith
      · nlinarith
    rw [hg, norm_mul]
    have h1 := norm_Fh_vert_le t
    have h2 := norm_Dk_le_sq hX hH (by norm_num : (0:ℝ) < 3/2) le_rfl t
    have h3 : 2 * (X + H) ^ (5/2 : ℝ) / ((3/2 : ℝ) ^ 2 + t ^ 2) ≤
        4 * (X + H) ^ (5/2 : ℝ) * (Y₀ ^ 2 + t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, mul_assoc 4]
      have hp : 0 < (X + H) ^ (5/2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      rw [show 4 * ((X + H) ^ (5/2 : ℝ) * (Y₀ ^ 2 + t ^ 2)⁻¹) =
        2 * (X + H) ^ (5/2 : ℝ) * (2 * (Y₀ ^ 2 + t ^ 2)⁻¹) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [show 2 * (Y₀ ^ 2 + t ^ 2)⁻¹ = ((Y₀ ^ 2 + t ^ 2) / 2)⁻¹ by field_simp]
      apply inv_anti₀ (by positivity)
      nlinarith
    calc ‖Fh ((3/2:ℝ) + t * I)‖ * ‖Dk X H ((3/2:ℝ) + t * I)‖
        ≤ MΛ * (4 * (X + H) ^ (5/2 : ℝ) * (Y₀ ^ 2 + t ^ 2)⁻¹) :=
          mul_le_mul h1 (h2.trans h3) (norm_nonneg _) MΛ_nonneg
      _ = K * (Y₀ ^ 2 + t ^ 2)⁻¹ := by rw [hK]; ring
  calc ‖∫ t in (Ioc (-T₂) T₁)ᶜ, g t‖ ≤ ∫ t in (Ioc (-T₂) T₁)ᶜ, K * (Y₀ ^ 2 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le hGint.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with t ht using hbound t ht
    _ ≤ ∫ t : ℝ, K * (Y₀ ^ 2 + t ^ 2)⁻¹ :=
        setIntegral_le_integral hGint (Eventually.of_forall fun t => by positivity)
    _ = K * (Real.pi / Y₀) := by rw [integral_const_mul, integral_inv_sq_add_sq hY₀]
    _ = 4 * MΛ * (X + H) ^ (5/2 : ℝ) * Real.pi / Y₀ := by rw [hK]; ring

/-- A horizontal edge. -/
lemma horiz_bound {X H : ℝ} (hX : 1 ≤ X) (hH : 0 < H) {T B : ℝ} (hT : T ≠ 0)
    (hB : ∀ σ ∈ Icc (1/4:ℝ) (3/2), ‖Fh (σ + T * I)‖ ≤ B) :
    ‖∫ x in (1/4:ℝ)..(3/2), Fh (x + T * I) * Dk X H (x + T * I)‖ ≤
      B * (2 * (X + H) ^ (5/2:ℝ) / T ^ 2) * (5/4) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (1/4) ⟨le_rfl, by norm_num⟩)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1/4:ℝ)) (b := 3/2)
    (f := fun x : ℝ => Fh (x + T * I) * Dk X H (x + T * I))
    (C := B * (2 * (X + H) ^ (5/2:ℝ) / T ^ 2)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      rw [norm_mul]
      apply mul_le_mul (hB x ⟨hx.1.le, hx.2⟩) _ (norm_nonneg _) hB0
      refine (norm_Dk_le_sq hX hH (by linarith [hx.1]) hx.2 T).trans ?_
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg x])
  rw [show |(3/2:ℝ) - 1/4| = 5/4 by norm_num] at h
  exact h

lemma arsinh_le_log {T : ℝ} (hT : 0 ≤ T) : Real.arsinh T ≤ Real.log (2 * T + 1) := by
  rw [Real.arsinh]
  apply Real.log_le_log (by positivity)
  have : √(1 + T ^ 2) ≤ T + 1 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

lemma integral_inv_sqrt_one_add_sq (a b : ℝ) :
    ∫ y in a..b, (√(1 + y ^ 2))⁻¹ = Real.arsinh b - Real.arsinh a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => Real.hasDerivAt_arsinh y)
  apply Continuous.intervalIntegrable
  refine Continuous.inv₀ (by fun_prop) (fun y => ?_)
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

/-- The left edge `Re s = 1/4`. -/
lemma left_bound {X H : ℝ} (hX : 1 ≤ X) (hH : 0 < H) {A₂ T₁ T₂ T : ℝ} (hA₂ : 0 < A₂)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hT₁T : T₁ ≤ T) (hT₂T : T₂ ≤ T)
    (hF : ∀ t : ℝ, ‖Fh (1/4 + t * I)‖ ≤ A₂ * Real.log (|t| + 3)) :
    ‖∫ y in (-T₂)..T₁, Fh ((1/4:ℝ) + y * I) * Dk X H ((1/4:ℝ) + y * I)‖ ≤
      8 * A₂ * Real.log (T + 3) * H * (X + H) ^ (1/4:ℝ) * Real.log (2 * T + 1) := by
  have hT : 0 ≤ T := hT₁.trans hT₁T
  set K : ℝ := 4 * A₂ * Real.log (T + 3) * H * (X + H) ^ (1/4:ℝ) with hK
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ K := by positivity
  have h1 : ‖∫ y in (-T₂)..T₁, Fh ((1/4:ℝ) + y * I) * Dk X H ((1/4:ℝ) + y * I)‖ ≤
      ∫ y in (-T₂)..T₁, K * (√(1 + y ^ 2))⁻¹ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Eventually.of_forall fun y hy => ?_
      have hy' : |y| ≤ T := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      rw [norm_mul]
      have hs : 0 < ((1/4:ℝ) + y * I : ℂ).re := by simp
      have hD := norm_Dk_le (by linarith : (0:ℝ) < X) hH hs
      have hre : ((1/4:ℝ) + y * I : ℂ).re = 1/4 := by simp
      rw [hre] at hD
      have hnorm : √(1 + y ^ 2) / 4 ≤ ‖((1/4:ℝ) : ℂ) + y * I‖ := by
        rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left (by positivity)]
        rw [show (‖((1/4:ℝ) : ℂ) + y * I‖ * 4) ^ 2 = 16 * ‖((1/4:ℝ) : ℂ) + y * I‖ ^ 2 by ring,
          norm_sq_eq]
        nlinarith
      have hsq : 0 < √(1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hF' : ‖Fh ((1/4:ℝ) + y * I)‖ ≤ A₂ * Real.log (T + 3) := by
        have := hF y
        rw [show ((1/4 : ℝ) : ℂ) = 1/4 by push_cast; ring]
        refine this.trans ?_
        gcongr
      have hD' : ‖Dk X H ((1/4:ℝ) + y * I)‖ ≤ H * (X + H) ^ (1/4:ℝ) * (4 * (√(1 + y ^ 2))⁻¹) := by
        refine hD.trans ?_
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show 4 * (√(1 + y ^ 2))⁻¹ = (√(1 + y ^ 2) / 4)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) hnorm
      calc ‖Fh ((1/4:ℝ) + y * I)‖ * ‖Dk X H ((1/4:ℝ) + y * I)‖
          ≤ (A₂ * Real.log (T + 3)) * (H * (X + H) ^ (1/4:ℝ) * (4 * (√(1 + y ^ 2))⁻¹)) :=
            mul_le_mul hF' hD' (norm_nonneg _) (by positivity)
        _ = K * (√(1 + y ^ 2))⁻¹ := by rw [hK]; ring
    · apply Continuous.intervalIntegrable
      refine continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun y => ?_))
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_one_add_sq, Real.arsinh_neg] at h1
  have h2 : Real.arsinh T₁ + Real.arsinh T₂ ≤ 2 * Real.log (2 * T + 1) := by
    have a1 := (Real.arsinh_le_arsinh.mpr hT₁T).trans (arsinh_le_log hT)
    have a2 := (Real.arsinh_le_arsinh.mpr hT₂T).trans (arsinh_le_log hT)
    linarith
  calc _ ≤ K * (Real.arsinh T₁ - -Real.arsinh T₂) := h1
    _ = K * (Real.arsinh T₁ + Real.arsinh T₂) := by ring
    _ ≤ K * (2 * Real.log (2 * T + 1)) := mul_le_mul_of_nonneg_left h2 hK0
    _ = _ := by rw [hK]; ring

/-- The sum over zeros. -/
lemma zero_term_bound {X H : ℝ} (hX : 0 < X) (hH : 0 < H) {Z : Finset ℂ}
    (hZ : ∀ u ∈ Z, u.re = 1/2) :
    ‖∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℂ) * Dk X H u‖ ≤
      H * (X + H) ^ (1/2:ℝ) * ∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
  have hre : 0 < u.re := by rw [hZ u hu]; norm_num
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (by intro h; rw [h] at hre; simp at hre)
  rw [norm_mul, Complex.norm_natCast]
  have := norm_Dk_le hX hH hre
  rw [hZ u hu] at this
  calc (analyticOrderNatAt zetaMulSubOne u : ℝ) * ‖Dk X H u‖
      ≤ (analyticOrderNatAt zetaMulSubOne u : ℝ) * (H * (X + H) ^ (1/2:ℝ) / ‖u‖) :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = H * (X + H) ^ (1/2:ℝ) * ((analyticOrderNatAt zetaMulSubOne u : ℝ) / ‖u‖) := by ring

lemma log_le_three_log {X y : ℝ} (_hX : 4 ≤ X) (hy : 0 < y) (hyX : y ≤ X ^ 3) :
    Real.log y ≤ 3 * Real.log X := by
  rw [show (3:ℝ) * Real.log X = Real.log (X ^ 3) by rw [Real.log_pow]; norm_num]
  exact Real.log_le_log hy hyX

/-- **Main estimate** (under RH): `ψ₁(X+H) - ψ₁(X) = XH + H²/2 + O(H √X log² X)`. -/
theorem main_estimate (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ X H : ℝ, 4 ≤ X → 1 ≤ H →
    H ≤ X → |psi1 (X + H) - psi1 X - (X * H + H ^ 2 / 2)| ≤
      C * (H * Real.sqrt X * Real.log X ^ 2) := by
  obtain ⟨A₂, hA₂, hF2⟩ := Fh_quarter_bound hRH
  obtain ⟨A₃, hA₃, hgood⟩ := good_height hRH
  obtain ⟨A₄, hA₄, hhor⟩ := Fh_horizontal
  obtain ⟨A₅, hA₅, hzs⟩ := zero_sum hRH
  have hM := MΛ_nonneg
  set C : ℝ := 18 * A₅ + (32 * Real.pi * MΛ + 144 * A₂ + 360 * A₃ * A₄) / (2 * Real.pi) with hC
  refine ⟨C, by positivity, fun X H hX hH hHX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := one_le_log_of_three_le (by linarith)
  set sX := Real.sqrt X with hsX
  have hsX0 : 0 < sX := Real.sqrt_pos.mpr hX0
  have hsXsq : sX ^ 2 = X := Real.sq_sqrt hX0.le
  -- elementary bounds for powers of `X + H`
  have hW : X + H ≤ 2 * X := by linarith
  have hW1 : (X + H) ^ (1/2:ℝ) ≤ 2 * sX := by
    rw [← Real.sqrt_eq_rpow, hsX]
    calc Real.sqrt (X + H) ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hW
      _ = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
      _ ≤ 2 * Real.sqrt X := by
          gcongr
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hW2 : (X + H) ^ (1/4:ℝ) ≤ 2 * sX :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans hW1
  have hW3 : (X + H) ^ (5/2:ℝ) ≤ 8 * X ^ 2 * sX := by
    rw [show (5/2:ℝ) = (2:ℕ) + 1/2 by norm_num, Real.rpow_add (by linarith), Real.rpow_natCast]
    have h1 : (X + H) ^ 2 ≤ 4 * X ^ 2 := by
      calc (X + H) ^ 2 ≤ (2 * X) ^ 2 := pow_le_pow_left₀ (by linarith) hW 2
        _ = 4 * X ^ 2 := by ring
    calc (X + H) ^ 2 * (X + H) ^ (1/2:ℝ) ≤ (4 * X ^ 2) * (2 * sX) :=
          mul_le_mul h1 hW1 (by positivity) (by positivity)
      _ = 8 * X ^ 2 * sX := by ring
  -- good heights
  obtain ⟨T₁, hT₁, δ₁, hδ₁, hδ₁4, hδ₁A, hgood₁⟩ := hgood (X ^ 2)
  obtain ⟨T₂', hT₂', δ₂, hδ₂, hδ₂4, hδ₂A, hgood₂⟩ := hgood (-(X ^ 2) - 1)
  set T₂ := -T₂' with hT₂def
  have hT₁a : X ^ 2 ≤ T₁ := hT₁.1
  have hT₁b : T₁ ≤ X ^ 2 + 1 := hT₁.2
  have hT₂a : X ^ 2 ≤ T₂ := by rw [hT₂def]; linarith [hT₂'.2]
  have hT₂b : T₂ ≤ X ^ 2 + 1 := by rw [hT₂def]; linarith [hT₂'.1]
  have hX2 : 16 ≤ X ^ 2 := by
    calc (16:ℝ) = 4 ^ 2 := by norm_num
      _ ≤ X ^ 2 := pow_le_pow_left₀ (by norm_num) hX 2
  have hX3' : 4 * X ^ 2 ≤ X ^ 3 := by
    have := mul_le_mul_of_nonneg_right hX (sq_nonneg X)
    rw [show X ^ 3 = X * X ^ 2 by ring]; exact this
  set δ := min δ₁ δ₂ with hδdef
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have hδ4 : δ ≤ 1/4 := (min_le_left _ _).trans hδ₁4
  have hlog5 : Real.log (X ^ 2 + 5) ≤ 3 * L :=
    log_le_three_log hX (by positivity) (by linarith)
  have hδA : 1 / δ ≤ A₃ * (3 * L) := by
    rcases min_choice δ₁ δ₂ with h | h
    · rw [← hδdef] at h
      rw [h]
      refine hδ₁A.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hlog5) hA₃.le)
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by positivity)]; linarith
    · rw [← hδdef] at h
      rw [h]
      refine hδ₂A.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hlog5) hA₃.le)
      apply le_of_eq; congr 1
      rw [abs_of_neg (by linarith)]; ring
  have hgoodδ : ∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re →
      δ ≤ |u.im - T₁| ∧ δ ≤ |u.im + T₂| := by
    intro u hu hre
    refine ⟨(min_le_left _ _).trans (hgood₁ u hu hre), (min_le_right _ _).trans ?_⟩
    have := hgood₂ u hu hre
    have e : u.im + T₂ = u.im - T₂' := by rw [hT₂def]; ring
    rw [e]; exact this
  -- the explicit formula on the rectangle
  obtain ⟨Z, hZ, hrect⟩ := rect_explicit hRH (by linarith) (by linarith) hδ0 hδ4 hgoodδ
    (differentiableOn_Dk hX0 hH0)
  set Bot := ∫ x in (1/4:ℝ)..(3/2), Fh (x + ((-T₂ : ℝ) : ℂ) * I) * Dk X H (x + ((-T₂ : ℝ) : ℂ) * I)
    with hBot
  set Top := ∫ x in (1/4:ℝ)..(3/2), Fh (x + T₁ * I) * Dk X H (x + T₁ * I) with hTop
  set Right := ∫ y in (-T₂)..T₁, Fh ((3/2:ℝ) + y * I) * Dk X H ((3/2:ℝ) + y * I) with hRight
  set Left := ∫ y in (-T₂)..T₁, Fh ((1/4:ℝ) + y * I) * Dk X H ((1/4:ℝ) + y * I) with hLeft
  set ZS := ∑ u ∈ Z, (analyticOrderNatAt zetaMulSubOne u : ℂ) * Dk X H u with hZS
  set Full := ∫ t : ℝ, Fh ((3/2:ℝ) + t * I) * Dk X H ((3/2:ℝ) + t * I) with hFull
  have hFullv : Full = 2 * Real.pi * ((psi1 (X + H) - psi1 X : ℝ) : ℂ) := perron_Dk hX0 hH0
  set R := Full - Right with hR
  have hrect' : Bot - Top + I * Right - I * Left = 2 * Real.pi * I * (Dk X H 1 - ZS) := hrect
  rw [Dk_one] at hrect'
  set a : ℝ := psi1 (X + H) - psi1 X - (X * H + H ^ 2 / 2) with ha
  have key : ((2 * Real.pi * a : ℝ) : ℂ) = -(2 * Real.pi) * ZS + R + Left + I * Bot - I * Top := by
    rw [ha]
    push_cast at hFullv hrect' ⊢
    linear_combination (-I) * hrect' - hR - hFullv + (Right - Left + 2 * (Real.pi : ℂ) * ZS -
      2 * (Real.pi : ℂ) * (X : ℂ) * (H : ℂ) - (Real.pi : ℂ) * (H : ℂ) ^ 2) * I_sq
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : 2 * Real.pi * |a| ≤ 2 * Real.pi * ‖ZS‖ + ‖R‖ + ‖Left‖ + ‖Bot‖ + ‖Top‖ := by
    have h1 : ‖((2 * Real.pi * a : ℝ) : ℂ)‖ = 2 * Real.pi * |a| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hpi]
    rw [← h1, key]
    have h2 : ‖-(2 * (Real.pi : ℂ)) * ZS‖ = 2 * Real.pi * ‖ZS‖ := by
      rw [norm_mul, norm_neg, show (2 * (Real.pi:ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    have e1 := norm_sub_le (-(2 * (Real.pi:ℂ)) * ZS + R + Left + I * Bot) (I * Top)
    have e2 := norm_add_le (-(2 * (Real.pi:ℂ)) * ZS + R + Left) (I * Bot)
    have e3 := norm_add_le (-(2 * (Real.pi:ℂ)) * ZS + R) Left
    have e4 := norm_add_le (-(2 * (Real.pi:ℂ)) * ZS) R
    have e5 : ‖I * Bot‖ = ‖Bot‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have e6 : ‖I * Top‖ = ‖Top‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    linarith
  set P := H * sX * L ^ 2 with hP
  have hHL : 1 ≤ H * L ^ 2 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hL1)
  have hP1 : sX ≤ P := by
    calc sX = sX * 1 := (mul_one _).symm
      _ ≤ sX * (H * L ^ 2) := mul_le_mul_of_nonneg_left hHL hsX0.le
      _ = P := by rw [hP]; ring
  have hX3 : 4 * X ^ 2 ≤ X ^ 3 := by
    have := mul_le_mul_of_nonneg_right hX (sq_nonneg X)
    rw [show X ^ 3 = X * X ^ 2 by ring]; exact this
  have h16 : 16 * X ^ 2 ≤ X ^ 4 := by
    have := mul_le_mul_of_nonneg_right hX2 (sq_nonneg X)
    rw [show X ^ 4 = X ^ 2 * X ^ 2 by ring]; exact this
  -- the sum over zeros
  have hZSb : 2 * Real.pi * ‖ZS‖ ≤ 36 * Real.pi * A₅ * P := by
    have hZre : ∀ u ∈ Z, u.re = 1/2 := fun u hu => (hZ u hu).2.1
    have h1 := zero_term_bound hX0 hH0 hZre
    have hZY : ∀ u ∈ Z, zetaMulSubOne u = 0 ∧ 0 < u.re ∧ |u.im| ≤ X ^ 2 + 1 := by
      intro u hu
      obtain ⟨h0, hre, h1, h2⟩ := hZ u hu
      exact ⟨h0, by rw [hre]; norm_num, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have h2 := hzs (X ^ 2 + 1) (by positivity) Z hZY
    have h3 : Real.log (X ^ 2 + 1 + 4) ≤ 3 * L := by
      rw [show X ^ 2 + 1 + 4 = X ^ 2 + 5 by ring]; exact hlog5
    have h4 : Real.log (X ^ 2 + 1 + 4) ^ 2 ≤ 9 * L ^ 2 := by
      have h0 : 0 ≤ Real.log (X ^ 2 + 1 + 4) := Real.log_nonneg (by linarith [sq_nonneg X])
      calc Real.log (X ^ 2 + 1 + 4) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ h0 h3 2
        _ = 9 * L ^ 2 := by ring
    have h5 : ‖ZS‖ ≤ H * (X + H) ^ (1/2:ℝ) * (A₅ * Real.log (X ^ 2 + 1 + 4) ^ 2) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc 2 * Real.pi * ‖ZS‖
        ≤ 2 * Real.pi * (H * (X + H) ^ (1/2:ℝ) * (A₅ * Real.log (X ^ 2 + 1 + 4) ^ 2)) := by
          gcongr
      _ ≤ 2 * Real.pi * (H * (2 * sX) * (A₅ * (9 * L ^ 2))) := by gcongr
      _ = 36 * Real.pi * A₅ * P := by rw [hP]; ring
  -- the tails
  have hRb : ‖R‖ ≤ 32 * Real.pi * MΛ * P := by
    have h1 := tail_bound (by linarith : (1:ℝ) ≤ X) hH0 (by positivity : (0:ℝ) < X ^ 2) hT₁a hT₂a
    have h2 : 4 * MΛ * (X + H) ^ (5/2:ℝ) * Real.pi / X ^ 2 ≤ 32 * Real.pi * MΛ * sX := by
      rw [div_le_iff₀ (by positivity)]
      calc 4 * MΛ * (X + H) ^ (5/2:ℝ) * Real.pi ≤ 4 * MΛ * (8 * X ^ 2 * sX) * Real.pi := by
            gcongr
        _ = 32 * Real.pi * MΛ * sX * X ^ 2 := by ring
    calc ‖R‖ ≤ 4 * MΛ * (X + H) ^ (5/2:ℝ) * Real.pi / X ^ 2 := h1
      _ ≤ 32 * Real.pi * MΛ * sX := h2
      _ ≤ 32 * Real.pi * MΛ * P := by gcongr
  -- the left edge
  have hLb : ‖Left‖ ≤ 144 * A₂ * P := by
    have h1 := left_bound (by linarith : (1:ℝ) ≤ X) hH0 hA₂ (by linarith : (0:ℝ) ≤ T₁)
      (by linarith : (0:ℝ) ≤ T₂) hT₁b hT₂b (fun t => (hF2 t).2)
    have h2 : Real.log (X ^ 2 + 1 + 3) ≤ 3 * L :=
      log_le_three_log hX (by positivity) (by linarith)
    have h3 : Real.log (2 * (X ^ 2 + 1) + 1) ≤ 3 * L :=
      log_le_three_log hX (by positivity) (by linarith)
    have h2' : 0 ≤ Real.log (X ^ 2 + 1 + 3) := Real.log_nonneg (by linarith)
    have h3' : 0 ≤ Real.log (2 * (X ^ 2 + 1) + 1) := Real.log_nonneg (by linarith)
    calc ‖Left‖ ≤ 8 * A₂ * Real.log (X ^ 2 + 1 + 3) * H * (X + H) ^ (1/4:ℝ) *
          Real.log (2 * (X ^ 2 + 1) + 1) := h1
      _ ≤ 8 * A₂ * (3 * L) * H * (2 * sX) * (3 * L) := by gcongr
      _ = 144 * A₂ * P := by rw [hP]; ring
  -- the horizontal edges
  have hB : ∀ T : ℝ, X ^ 2 ≤ |T| → |T| ≤ X ^ 2 + 1 →
      (∀ u : ℂ, zetaMulSubOne u = 0 → 0 < u.re → δ ≤ |u.im - T|) →
      ‖∫ x in (1/4:ℝ)..(3/2), Fh (x + T * I) * Dk X H (x + T * I)‖ ≤ 180 * A₃ * A₄ * P := by
    intro T hT1 hT2 hgoodT
    have hT0 : T ≠ 0 := by intro h; rw [h, abs_zero] at hT1; linarith
    have hBd : ∀ σ ∈ Icc (1/4:ℝ) (3/2), ‖Fh (σ + T * I)‖ ≤ A₄ * (3 * L) * (A₃ * (3 * L)) := by
      intro σ hσ
      have h1 := (hhor T δ (by linarith) hδ0 (by linarith) hgoodT σ hσ).2
      have h2 : Real.log (|T| + 3) ≤ 3 * L :=
        log_le_three_log hX (by positivity) (by linarith)
      have h2' : 0 ≤ Real.log (|T| + 3) := Real.log_nonneg (by linarith [abs_nonneg T])
      calc ‖Fh (σ + T * I)‖ ≤ A₄ * Real.log (|T| + 3) / δ := h1
        _ = A₄ * Real.log (|T| + 3) * (1 / δ) := by ring
        _ ≤ A₄ * (3 * L) * (A₃ * (3 * L)) := by gcongr
    have h1 := horiz_bound (by linarith : (1:ℝ) ≤ X) hH0 hT0 hBd
    have hT2' : X ^ 4 ≤ T ^ 2 := by
      rw [← sq_abs, show X ^ 4 = (X ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg X) hT1 2
    have h2 : 2 * (X + H) ^ (5/2:ℝ) / T ^ 2 ≤ sX := by
      rw [div_le_iff₀ (by positivity)]
      calc 2 * (X + H) ^ (5/2:ℝ) ≤ 2 * (8 * X ^ 2 * sX) := by gcongr
        _ = sX * (16 * X ^ 2) := by ring
        _ ≤ sX * T ^ 2 := mul_le_mul_of_nonneg_left (h16.trans hT2') hsX0.le
    have hA34 : 0 ≤ A₄ * (3 * L) * (A₃ * (3 * L)) := by positivity
    calc _ ≤ A₄ * (3 * L) * (A₃ * (3 * L)) * (2 * (X + H) ^ (5/2:ℝ) / T ^ 2) * (5/4) := h1
      _ ≤ A₄ * (3 * L) * (A₃ * (3 * L)) * sX * (5/4) := by gcongr
      _ ≤ 180 * A₃ * A₄ * P := by
          rw [hP]
          have h0 : 0 ≤ A₃ * A₄ * L ^ 2 * sX := by positivity
          rw [show A₄ * (3 * L) * (A₃ * (3 * L)) * sX * (5/4) = (45/4) * (A₃ * A₄ * L ^ 2 * sX) by
            ring, show 180 * A₃ * A₄ * (H * sX * L ^ 2) = (180 * H) * (A₃ * A₄ * L ^ 2 * sX) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) h0
  have hTopb : ‖Top‖ ≤ 180 * A₃ * A₄ * P :=
    hB T₁ (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
      (fun u hu hre => (hgoodδ u hu hre).1)
  have hBotb : ‖Bot‖ ≤ 180 * A₃ * A₄ * P :=
    hB (-T₂) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      (fun u hu hre => by have := (hgoodδ u hu hre).2; rwa [sub_neg_eq_add])
  -- conclusion
  have hfinal : 2 * Real.pi * |a| ≤ 2 * Real.pi * (C * P) := by
    have : 2 * Real.pi * (C * P) =
        36 * Real.pi * A₅ * P + 32 * Real.pi * MΛ * P + 144 * A₂ * P + 360 * A₃ * A₄ * P := by
      rw [hC]; field_simp; ring
    rw [this]
    linarith
  exact le_of_mul_le_mul_left hfinal hpi

/-- **von Koch's theorem**: under RH, `ψ(x) = x + O(√x log² x)`. -/
theorem psi_error (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨C₀, hC₀, hmain⟩ := main_estimate hRH
  refine ⟨max 256 (C₀ + 1), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hψ0 := Chebyshev.psi_nonneg x
  by_cases hx16 : x < 16
  · -- small `x`
    have hlog2 : 0.69 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hL2 : 0.69 < L := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hx)
    have hs1 : 1 ≤ s := by rw [hs, Real.le_sqrt (by norm_num) hx0.le]; linarith
    have hψ : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx0.le
    have hlog4 : Real.log 4 < 1.4 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9
      push_cast; linarith
    have h1 : |Chebyshev.psi x - x| ≤ 6.4 * x := by
      rw [abs_le]; constructor <;> nlinarith
    have h2 : 6.4 * x ≤ 256 * s * L ^ 2 := by
      have hL2' : 0.4761 ≤ L ^ 2 := by nlinarith
      nlinarith
    calc |Chebyshev.psi x - x| ≤ 256 * s * L ^ 2 := h1.trans h2
      _ ≤ max 256 (C₀ + 1) * s * L ^ 2 := by
          gcongr
          exact le_max_left _ _
  · push Not at hx16
    have hs4 : 4 ≤ s := by rw [hs, Real.le_sqrt (by norm_num) hx0.le]; linarith
    have hL1 : 1 ≤ L := one_le_log_of_three_le (by linarith)
    -- upper bound, with `X = x`, `H = √x`
    have hup : Chebyshev.psi x ≤ x + s / 2 + C₀ * s * L ^ 2 := by
      have h1 := psi1_diff_ge hx0.le hs0.le
      have h2 := hmain x s (by linarith) (by linarith) (by nlinarith)
      rw [abs_le] at h2
      have h3 : s * Chebyshev.psi x ≤ s * (x + s / 2 + C₀ * s * L ^ 2) := by
        have e : C₀ * (s * Real.sqrt x * Real.log x ^ 2) = s * (C₀ * s * L ^ 2) := by
          rw [← hs, ← hL]; ring
        rw [e] at h2
        nlinarith [h2.2]
      exact le_of_mul_le_mul_left h3 hs0
    -- lower bound, with `X = x - √x`, `H = √x`
    have hlow : x - s / 2 - C₀ * s * L ^ 2 ≤ Chebyshev.psi x := by
      set X := x - s with hXdef
      have hX4 : 4 ≤ X := by rw [hXdef]; nlinarith
      have hXx : X + s = x := by rw [hXdef]; ring
      have h1 := psi1_diff_le (by linarith : 0 ≤ X) hs0.le
      rw [hXx] at h1
      have h2 := hmain X s hX4 (by linarith) (by rw [hXdef]; nlinarith)
      rw [hXx, abs_le] at h2
      have hsqX : Real.sqrt X ≤ s := Real.sqrt_le_sqrt (by linarith)
      have hlogX : Real.log X ≤ L := Real.log_le_log (by linarith) (by linarith)
      have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
      have h3 : s * Real.sqrt X * Real.log X ^ 2 ≤ s * s * L ^ 2 := by
        have : Real.log X ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogX0 hlogX 2
        have h0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
        calc s * Real.sqrt X * Real.log X ^ 2 ≤ s * s * L ^ 2 := by gcongr
          _ = s * s * L ^ 2 := rfl
      have h4 : s * (x - s / 2 - C₀ * s * L ^ 2) ≤ s * Chebyshev.psi x := by
        have e : s * (x - s / 2 - C₀ * s * L ^ 2) = X * s + s ^ 2 / 2 - C₀ * (s * s * L ^ 2) := by
          rw [hXdef, ← hss]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left h3 hC₀.le
        linarith [h2.1]
      exact le_of_mul_le_mul_left h4 hs0
    have hfin : |Chebyshev.psi x - x| ≤ (C₀ + 1) * s * L ^ 2 := by
      have hsL : s / 2 ≤ s * L ^ 2 := by
        have : 1 ≤ L ^ 2 := one_le_pow₀ hL1
        nlinarith
      rw [abs_le]; constructor <;> nlinarith
    calc |Chebyshev.psi x - x| ≤ (C₀ + 1) * s * L ^ 2 := hfin
      _ ≤ max 256 (C₀ + 1) * s * L ^ 2 := by
          gcongr
          exact le_max_right _ _

end VonKoch

end

end


/-- **Milestone** `LandauCriterion.psi_error_of_riemannHypothesis` (von Koch, 1901): under the
Riemann hypothesis, `|ψ(x) - x| ≤ C √x (log x)²` for all `x ≥ 2`. -/
theorem solution (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 :=
  VonKoch.psi_error hRH
