-- Prove2me | solution 1 for LandauCriterion.psi_oscillation_of_not_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-20T18:03:32.118751+00:00
-- url     : https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7

/-
  Landau's oscillation theorem for the Chebyshev function ψ.

  If the Riemann hypothesis fails, then there is `b ∈ (1/2, 1)` such that for every `ε > 0`
  both `ψ(x) - x > x^{b-ε}` and `ψ(x) - x < -x^{b-ε}` hold for arbitrarily large `x`
  (`ψ(x) - x = Ω_±(x^{b-ε})`); the same holds for `θ`.

  Contents:
  * `LandauMellin.landau` : Landau's theorem for Mellin transforms of nonnegative functions
    (the abscissa of convergence is a singularity of the analytic continuation).
  * `ZetaAux.riemannZeta_ne_zero_of_mem_Ioo` : `ζ(σ) ≠ 0` for real `0 < σ < 1`.
  * `ZetaAux.integral_psi_mul_cpow` : `∫_{x>1} ψ(x) x^{-s-1} dx = -ζ'(s)/(s ζ(s))`, `Re s > 1`.
  * `PsiOscillation.frequently_rpow_lt_psi_sub`, `...frequently_psi_sub_lt_neg_rpow` :
    the Ω± statements for any zero `ρ` with `0 < Re ρ < 1` and any `θ < Re ρ`.
  * `PsiOscillation.exists_zero_of_not_RH` : `¬RH → ∃ ρ, ζ ρ = 0 ∧ 1/2 < Re ρ < 1`.
  * `PsiOscillation.psi_oscillation_of_not_RH`, `PsiOscillation.theta_oscillation_of_not_RH`.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Order.Group.Lattice

open Complex MeasureTheory Filter Topology Set Metric

noncomputable section

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

/-! ### Landau's theorem for Mellin transforms of nonnegative functions -/

/-- At a real point, `mellinK A k a` is (the coercion of) a real integral. -/
lemma mellinK_ofReal (A : ℝ → ℝ) (k : ℕ) (a : ℝ) :
    mellinK A k (a : ℂ) =
      (((-1:ℝ) ^ k * ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1) : ℝ) : ℂ) := by
  rw [mellinK, ← integral_const_mul, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0:ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  rw [show (-(a:ℂ) - 1) = ((-a - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx0]
  push_cast
  ring

/-- Monotone convergence step: summability of the (nonnegative) Taylor coefficients at `a`,
evaluated at distance `t`, gives convergence of the Mellin integral at `a - t`. -/
lemma conv_of_summable {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x)
    {a t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ k : ℕ, IntegrableOn (fun x => A x * Real.log x ^ k * x ^ (-a - 1)) (Ioi 1))
    (hsum : Summable (fun k : ℕ => t ^ k / k.factorial *
        ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1))) :
    Conv A (a - t) := by
  set f : ℕ → ℝ → ℝ := fun k x => t ^ k / k.factorial * (A x * Real.log x ^ k * x ^ (-a - 1))
    with hf
  have hf_nonneg : ∀ k, ∀ x ∈ Ioi (1:ℝ), 0 ≤ f k x := by
    intro k x hx
    have hx' : (1:ℝ) < x := hx
    have := hA0 x hx'
    have := Real.log_nonneg hx'.le
    simp only [hf]
    positivity
  have hpt : ∀ x ∈ Ioi (1:ℝ), HasSum (fun k => f k x) (A x * x ^ (-(a - t) - 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have he := NormedSpace.expSeries_div_hasSum_exp (t * Real.log x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have h2 := he.mul_left (A x * x ^ (-a - 1))
    have e1 : (fun k => f k x) =
        (fun i => A x * x ^ (-a - 1) * ((t * Real.log x) ^ i / i.factorial)) := by
      funext k
      simp only [hf]
      rw [mul_pow]
      ring
    have e2 : A x * x ^ (-(a - t) - 1) = A x * x ^ (-a - 1) * Real.exp (t * Real.log x) := by
      rw [show -(a - t) - 1 = (-a - 1) + t by ring, Real.rpow_add hx0,
        Real.rpow_def_of_pos hx0 t]
      ring_nf
    rw [e1, e2]
    exact h2
  have hmeas : AEStronglyMeasurable (fun x => A x * x ^ (-(a - t) - 1))
      (volume.restrict (Ioi 1)) :=
    (hA.mul (measurable_id.pow_const _)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 1)] (fun x => A x * x ^ (-(a - t) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (1:ℝ) < x := hx
    have := hA0 x hx'
    have : 0 ≤ x := by linarith
    positivity
  have hfint : ∀ k, IntegrableOn (f k) (Ioi 1) := fun k => (hint k).const_mul _
  have hfmeas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (f k x)) (volume.restrict (Ioi 1)) :=
    fun k => (hfint k).aemeasurable.ennreal_ofReal
  have hIk : ∀ k, ∫ x in Ioi (1:ℝ), f k x =
      t ^ k / k.factorial * ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1) := by
    intro k; simp only [hf]; rw [integral_const_mul]
  have hInn : ∀ k, 0 ≤ ∫ x in Ioi (1:ℝ), f k x := fun k =>
    setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)
  have hsum' : Summable (fun k => ∫ x in Ioi (1:ℝ), f k x) := by
    simp_rw [hIk]; exact hsum
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
  calc ∫⁻ x in Ioi 1, ENNReal.ofReal (A x * x ^ (-(a - t) - 1))
      = ∫⁻ x in Ioi 1, ∑' k, ENNReal.ofReal (f k x) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        rw [← (hpt x hx).tsum_eq,
          ENNReal.ofReal_tsum_of_nonneg (fun k => hf_nonneg k x hx) (hpt x hx).summable]
    _ = ∑' k, ∫⁻ x in Ioi 1, ENNReal.ofReal (f k x) := lintegral_tsum hfmeas
    _ = ∑' k, ENNReal.ofReal (∫ x in Ioi 1, f k x) := by
        congr 1; funext k
        rw [ofReal_integral_eq_lintegral_ofReal (hfint k)]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hf_nonneg k x hx
    _ = ENNReal.ofReal (∑' k, ∫ x in Ioi 1, f k x) :=
        (ENNReal.ofReal_tsum_of_nonneg hInn hsum').symm
    _ < ⊤ := ENNReal.ofReal_lt_top

lemma norm_sub_ofReal_re (z : ℂ) : ‖z - (z.re : ℂ)‖ = |z.im| := by
  have : z - (z.re : ℂ) = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Landau's theorem** for Mellin transforms of nonnegative functions.
Let `A ≥ 0` on `(1, ∞)` with `∫_{x>1} A(x) x^{-σ-1} dx < ∞` for `σ > c`. If the transform
`F(s) = ∫_{x>1} A(x) x^{-s-1} dx` agrees on `Re s > c` with a function `G` that is holomorphic
on an open set containing the half-plane `Re s > c` and the real half-line `(σ₀, ∞)`, then the
integral converges for every real `σ > σ₀`. -/
theorem landau {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x)
    {σ₀ c : ℝ} (hc : ∀ σ, c < σ → Conv A σ)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hUc : ∀ s : ℂ, c < s.re → s ∈ U) (hUr : ∀ σ : ℝ, σ₀ < σ → (σ : ℂ) ∈ U)
    (hFG : ∀ s : ℂ, c < s.re → mellinK A 0 s = G s) :
    ∀ σ, σ₀ < σ → Conv A σ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨σ₁, hσ₁, hnot⟩ := hcon
  set S : Set ℝ := {σ | Conv A σ} with hS
  have hlow : ∀ σ ∈ S, σ₁ ≤ σ := fun σ hσ => by
    by_contra h; push Not at h; exact hnot (conv_mono hA hA0 hσ h.le)
  have hSbdd : BddBelow S := ⟨σ₁, hlow⟩
  have hSne : S.Nonempty := ⟨c + 1, hc _ (by linarith)⟩
  set τ := sInf S with hτ
  have hσ₁τ : σ₁ ≤ τ := le_csInf hSne hlow
  have hτc : τ ≤ c := by
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    exact (csInf_le hSbdd (show c + ε / 2 ∈ S from hc _ (by linarith))).trans_lt (by linarith)
  have hright : ∀ σ, τ < σ → Conv A σ := fun σ hσ => by
    obtain ⟨σ', hσ'S, hσ'lt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact conv_mono hA hA0 hσ'S hσ'lt.le
  have hleft : ∀ σ, σ < τ → ¬ Conv A σ := fun σ hσ hS' =>
    absurd (csInf_le hSbdd hS') (not_le.mpr hσ)
  have hσ₀τ : σ₀ < τ := lt_of_lt_of_le hσ₁ hσ₁τ
  -- the compact segment `K` and a uniform width `δ`
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc ((σ₀ + τ) / 2) (c + 1) with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hUr x (by linarith [hx.1])
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hU hKU
  set r := min δ 1 / 3 with hr
  have hr0 : 0 < r := by positivity
  have hrδ : r ≤ δ / 3 := by rw [hr]; gcongr; exact min_le_left _ _
  have hr1 : r ≤ 1 / 3 := by rw [hr]; gcongr; exact min_le_right _ _
  set a : ℝ := τ + r with ha
  have haK : (a : ℂ) ∈ K := ⟨a, ⟨by linarith, by linarith⟩, rfl⟩
  have hGball : DifferentiableOn ℂ G (ball (a : ℂ) δ) :=
    hG.mono ((ball_subset_thickening haK δ).trans hthick)
  -- the region `W` on which `F = G`
  set W₁ : Set ℂ := {z | τ < z.re} ∩ ({z | z.re < c + 1} ∩ ({z | -δ < z.im} ∩ {z | z.im < δ}))
    with hW₁
  set W : Set ℂ := W₁ ∪ {z | c < z.re} with hW
  have hWU : W ⊆ U := by
    rintro z (⟨h1, h2, h3, h4⟩ | h)
    · apply hthick
      rw [mem_thickening_iff]
      refine ⟨(z.re : ℂ), ⟨z.re, ⟨by simp only [Set.mem_setOf_eq] at h1; linarith,
        by simp only [Set.mem_setOf_eq] at h2; linarith⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_ofReal_re]
      simp only [Set.mem_setOf_eq] at h3 h4
      exact abs_lt.mpr ⟨h3, h4⟩
    · exact hUc z h
  have hWopen : IsOpen W := by
    refine IsOpen.union ?_ (isOpen_lt continuous_const Complex.continuous_re)
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hz₀W₁ : ((c + 1/2 : ℝ) : ℂ) ∈ W₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Set.mem_setOf_eq, ofReal_re, ofReal_im] <;> linarith
  have hz₀W₂ : ((c + 1/2 : ℝ) : ℂ) ∈ {z : ℂ | c < z.re} := by
    simp only [Set.mem_setOf_eq, ofReal_re]; linarith
  have hWconn : IsPreconnected W := by
    refine IsPreconnected.union ((c + 1/2 : ℝ) : ℂ) hz₀W₁ hz₀W₂ ?_
      (convex_halfSpace_re_gt c).isPreconnected
    exact ((convex_halfSpace_re_gt τ).inter ((convex_halfSpace_re_lt (c + 1)).inter
      ((convex_halfSpace_im_gt (-δ)).inter (convex_halfSpace_im_lt δ)))).isPreconnected
  have hright' : ∀ σ, τ < σ → ConvAbs A σ := fun σ hσ => convAbs_of_conv hA0 (hright σ hσ)
  have hFdiff := differentiableOn_mellinK hA hright' 0
  have hWsub : W ⊆ {z : ℂ | τ < z.re} := by
    rintro z (⟨h1, _, _⟩ | h)
    · exact h1
    · exact lt_of_le_of_lt hτc h
  have hFW : EqOn (mellinK A 0) G W := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hFdiff.mono hWsub).analyticOnNhd hWopen) ((hG.mono hWU).analyticOnNhd hWopen) hWconn
      (z₀ := ((c + 1/2 : ℝ) : ℂ)) (Or.inr hz₀W₂) ?_
    have : {z : ℂ | c < z.re} ∈ 𝓝 (((c + 1/2 : ℝ) : ℂ)) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀W₂
    filter_upwards [this] with z hz using hFG z hz
  have hballW : ball (a : ℂ) r ⊆ W := by
    intro z hz
    left
    have hz' : ‖z - a‖ < r := by simpa [dist_eq_norm] using hz
    have h1 : |z.re - a| < r :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - a)) hz'
    have h2 : |z.im| < r :=
      lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (z - a)) hz'
    have h1' := abs_lt.mp h1
    have h2' := abs_lt.mp h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Set.mem_setOf_eq] <;> linarith
  have hev : mellinK A 0 =ᶠ[𝓝 (a : ℂ)] G := by
    filter_upwards [ball_mem_nhds (a : ℂ) hr0] with z hz using hFW (hballW hz)
  -- Taylor expansion of `G` at `a`, evaluated at `a - 2r`
  have hzmem : ((a - 2 * r : ℝ) : ℂ) ∈ ball (a : ℂ) δ := by
    rw [mem_ball, dist_eq_norm,
      show ((a - 2 * r : ℝ) : ℂ) - (a : ℂ) = ((-(2 * r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball hGball hzmem
  set I : ℕ → ℝ := fun n => ∫ x in Ioi (1:ℝ), A x * Real.log x ^ n * x ^ (-a - 1) with hI
  have hterm : ∀ n : ℕ, (n.factorial : ℂ)⁻¹ • (((a - 2 * r : ℝ) : ℂ) - (a : ℂ)) ^ n •
      iteratedDeriv n G (a : ℂ) = (((2 * r) ^ n / n.factorial * I n : ℝ) : ℂ) := by
    intro n
    have hare : τ < (a : ℂ).re := by simp only [ofReal_re]; linarith
    rw [← hev.iteratedDeriv_eq n, iteratedDeriv_mellinK hA hright' n (a : ℂ) hare,
      mellinK_ofReal, show ((a - 2 * r : ℝ) : ℂ) - (a : ℂ) = ((-(2 * r) : ℝ) : ℂ) by
        push_cast; ring]
    simp only [smul_eq_mul]
    rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; ring,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have h1 : ((-1:ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow]
    have e : ∀ X : ℝ, ((n.factorial : ℝ))⁻¹ * ((-1) ^ n * (2 * r) ^ n * ((-1) ^ n * X)) =
        (2 * r) ^ n / n.factorial * X := by
      intro X
      calc _ = ((n.factorial : ℝ))⁻¹ * (2 * r) ^ n * X * ((-1) ^ n * (-1) ^ n) := by ring
        _ = _ := by rw [h1]; ring
    exact e _
  have hsum : Summable (fun n : ℕ => (2 * r) ^ n / n.factorial * I n) := by
    have := htaylor.summable
    simp_rw [hterm] at this
    exact Complex.summable_ofReal.mp this
  have hconv := conv_of_summable hA hA0 (a := a) (t := 2 * r) (by positivity)
    (fun k => integrableOn_log_pow_of_nonneg hA hA0 (σ := (τ + a) / 2) (σ' := a) (by linarith)
      (hright _ (by linarith)) k) hsum
  exact hleft (a - 2 * r) (by linarith) hconv

end LandauMellin


open Complex MeasureTheory Filter Topology Set Metric

noncomputable section

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

/-- `(σ - 1) ζ(σ) > 0` for real `0 < σ < 1`; in particular `ζ(σ) ≠ 0` there. -/
lemma zetaMulSubOne_ne_zero_of_pos {σ : ℝ} (hσ : 0 < σ) : zetaMulSubOne σ ≠ 0 := by
  rcases lt_or_ge σ 1 with h1 | h1
  · rw [zetaMulSubOne_eq_integral (by simpa using hσ), LandauMellin.mellinK_ofReal]
    set J := ∫ x in Ioi (1:ℝ), Int.fract x * Real.log x ^ 0 * x ^ (-σ - 1) with hJ
    have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun x hx => by
      have : (0:ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
      have := Int.fract_nonneg x
      positivity)
    have hpos : 0 < σ - σ * (σ - 1) * ((-1) ^ 0 * J) := by
      have : 0 ≤ σ * (1 - σ) * J := by
        apply mul_nonneg (mul_nonneg hσ.le (by linarith)) hJ0
      nlinarith
    intro h
    have h' : ((σ - σ * (σ - 1) * ((-1) ^ 0 * J) : ℝ) : ℂ) = 0 := by
      push_cast; push_cast at h; linear_combination h
    exact hpos.ne' (by exact_mod_cast h')
  · exact zetaMulSubOne_ne_zero_of_one_le_re (by simpa using h1)

/-- The Riemann zeta function has no zeros on the real interval `(0, 1)`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  intro h
  apply zetaMulSubOne_ne_zero_of_pos h0
  rw [zetaMulSubOne_of_ne (by intro h'; have := congrArg Complex.re h'; simp at this; linarith),
    h, mul_zero]

/-! ### Mellin transform of `ψ` -/

lemma sum_Icc_vonMangoldt (t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) =
      (Chebyshev.psi t : ℂ) := by
  rw [Chebyshev.psi, ofReal_sum]
  rfl

lemma psi_isBigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
    =O[atTop] fun n : ℕ => (n : ℝ) ^ (1:ℝ) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  have h : ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k = Chebyshev.psi n := by
    rw [Chebyshev.psi, Nat.floor_natCast]; rfl
  rw [h, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _), Real.rpow_one,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

/-- `∫_{x>1} ψ(x) x^{-s-1} dx = -ζ'(s) / (s ζ(s))` for `Re s > 1`. -/
theorem integral_psi_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-s - 1) =
      -deriv riemannZeta s / (s * riemannZeta s) := by
  have h1 := LSeries_eq_mul_integral_of_nonneg (fun n => ArithmeticFunction.vonMangoldt n)
    zero_le_one hs psi_isBigO (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  simp_rw [sum_Icc_vonMangoldt] at h1
  rw [h2] at h1
  rw [show (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-s - 1)) =
    fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)) by
      funext x; rw [show -s - 1 = -(s + 1) by ring]]
  rw [eq_div_iff (mul_ne_zero hs0 hζ)]
  have : (∫ x in Ioi (1:ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      (-deriv riemannZeta s / riemannZeta s) / s := by
    rw [h1]; field_simp
  rw [this]
  field_simp

end ZetaAux


open Complex MeasureTheory Filter Topology Set Metric

noncomputable section

namespace PsiOscillation

open ZetaAux LandauMellin

/-! ### A holomorphic function satisfying `f' = P f` cannot vanish (unless it is locally `0`) -/

lemma ne_zero_of_deriv_eq_mul {f P : ℂ → ℂ} {ρ : ℂ} {V : Set ℂ} (hV : IsOpen V) (hρ : ρ ∈ V)
    (hf : AnalyticAt ℂ f ρ) (hP : ContinuousAt P ρ)
    (hfP : ∀ z ∈ V, deriv f z = P z * f z) (hnz : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0) : f ρ ≠ 0 := by
  intro h0
  obtain ⟨n, g, hg, hgρ, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hn : n ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [pow_zero, one_smul] at this
    exact hgρ (this ▸ h0)
  have hgev : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hfg' : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n * g z := by
    filter_upwards [hfg] with z hz; rw [hz, smul_eq_mul]
  have hderiv : ∀ᶠ z in 𝓝 ρ,
      deriv f z = (n : ℂ) * (z - ρ) ^ (n - 1) * g z + (z - ρ) ^ n * deriv g z := by
    filter_upwards [hfg'.deriv, hgev] with z hz hgz
    rw [hz]
    have h1 : HasDerivAt (fun z => (z - ρ) ^ n) ((n : ℂ) * (z - ρ) ^ (n - 1) * 1) z :=
      ((hasDerivAt_id z).sub_const ρ).pow n
    have h2 : HasDerivAt (fun z => (z - ρ) ^ n * g z)
        ((n : ℂ) * (z - ρ) ^ (n - 1) * 1 * g z + (z - ρ) ^ n * deriv g z) z :=
      h1.mul hgz.differentiableAt.hasDerivAt
    rw [h2.deriv]
    ring
  have hrel : ∀ᶠ z in 𝓝 ρ, deriv f z = P z * ((z - ρ) ^ n * g z) := by
    filter_upwards [hfg', hV.mem_nhds hρ] with z hz hzV
    rw [hfP z hzV, hz]
  have hpunct : ∀ᶠ z in 𝓝[≠] ρ,
      (n : ℂ) * g z - (z - ρ) * (P z * g z - deriv g z) = 0 := by
    filter_upwards [nhdsWithin_le_nhds (hderiv.and hrel), self_mem_nhdsWithin] with z hz hzρ
    obtain ⟨h1, h2⟩ := hz
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    have hpow : (z - ρ) ^ n = (z - ρ) ^ (n - 1) * (z - ρ) := by
      rw [← pow_succ]; congr 1; omega
    have key : (z - ρ) ^ (n - 1) * ((n : ℂ) * g z - (z - ρ) * (P z * g z - deriv g z)) = 0 := by
      rw [hpow] at h1 h2
      linear_combination h1.symm.trans h2
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (pow_ne_zero _ hzρ')
    · exact h
  have hcont : ContinuousAt (fun z => (n : ℂ) * g z - (z - ρ) * (P z * g z - deriv g z)) ρ := by
    have hgc : ContinuousAt g ρ := hg.continuousAt
    have hg'c : ContinuousAt (deriv g) ρ := hg.deriv.continuousAt
    exact (continuousAt_const.mul hgc).sub
      ((continuousAt_id.sub continuousAt_const).mul ((hP.mul hgc).sub hg'c))
  have hlim : (n : ℂ) * g ρ - (ρ - ρ) * (P ρ * g ρ - deriv g ρ) = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hpunct.mono fun z hz => hz.symm))
  rw [sub_self, zero_mul, sub_zero] at hlim
  rcases mul_eq_zero.mp hlim with h | h
  · exact hn (by exact_mod_cast h)
  · exact hgρ h

/-! ### The test function `A(x) = x^θ + ε (x - ψ(x))` -/

/-- `Aθ θ ε x = x^θ + ε (x - ψ(x))`. -/
def Aθ (θ ε : ℝ) (x : ℝ) : ℝ := x ^ θ + ε * (x - Chebyshev.psi x)

lemma measurable_Aθ (θ ε : ℝ) : Measurable (Aθ θ ε) := by
  unfold Aθ
  exact (measurable_id.pow_const θ).add
    (measurable_const.mul (measurable_id.sub Chebyshev.psi_mono.measurable))

/-- The Chebyshev constant used below. -/
def cψ : ℝ := Real.log 4 + 4

lemma cψ_pos : 0 < cψ := by
  unfold cψ; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith

lemma abs_Aθ_le {θ ε : ℝ} (hθ : θ ≤ 1) (hε : |ε| ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    |Aθ θ ε x| ≤ (2 + cψ) * x := by
  unfold Aθ
  have hx0 : 0 ≤ x := by linarith
  have h1 : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ
      _ = x := Real.rpow_one x
  have h2 : 0 ≤ x ^ θ := Real.rpow_nonneg hx0 θ
  have hψ0 := Chebyshev.psi_nonneg x
  have hψ : Chebyshev.psi x ≤ cψ * x := Chebyshev.psi_le_const_mul_self hx0
  have h3 : |x - Chebyshev.psi x| ≤ x + Chebyshev.psi x := by
    rw [abs_le]; constructor <;> linarith
  calc |x ^ θ + ε * (x - Chebyshev.psi x)|
      ≤ |x ^ θ| + |ε * (x - Chebyshev.psi x)| := abs_add_le _ _
    _ = x ^ θ + |ε| * |x - Chebyshev.psi x| := by rw [abs_of_nonneg h2, abs_mul]
    _ ≤ x + 1 * (x + Chebyshev.psi x) := by gcongr
    _ ≤ (2 + cψ) * x := by nlinarith

/-- `∫_{x>1} (x^θ + ε(x - ψ x)) x^{-s-1} dx = 1/(s-θ) + ε/(s-1) + ε ζ'(s)/(s ζ(s))`. -/
lemma mellinK_Aθ {θ ε : ℝ} (hθ : θ < 1) {s : ℂ} (hs : 1 < s.re) :
    mellinK (Aθ θ ε) 0 s = 1 / (s - θ) + ε / (s - 1) + ε * (deriv riemannZeta s /
      (s * riemannZeta s)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hsθ : s - θ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hpt : ∀ x ∈ Ioi (1:ℝ), (Aθ θ ε x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ 0 * (x : ℂ) ^ (-s - 1) =
      (x : ℂ) ^ ((θ : ℂ) - s - 1) + (ε : ℂ) * (x : ℂ) ^ (-s) -
        (ε : ℂ) * ((Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    unfold Aθ
    rw [pow_zero, mul_one]
    rw [Complex.ofReal_add, Complex.ofReal_cpow hx0.le]
    rw [show (θ : ℂ) - s - 1 = (θ : ℂ) + (-s - 1) by ring, cpow_add _ _ hxc,
      show -s = 1 + (-s - 1) by ring, cpow_add _ _ hxc, cpow_one]
    push_cast
    ring_nf
  have hi1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((θ : ℂ) - s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hi2 : IntegrableOn (fun x : ℝ => (ε : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).const_mul _
  have hi3 : IntegrableOn (fun x : ℝ => (ε : ℂ) * ((Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-s - 1)))
      (Ioi 1) := by
    refine Integrable.const_mul ?_ _
    have hI : IntegrableOn (fun x : ℝ => cψ * x ^ (-s.re)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hI.mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp Chebyshev.psi_mono.measurable).mul
        (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := by linarith
      rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Real.norm_eq_abs,
        abs_of_nonneg (Chebyshev.psi_nonneg x)]
      have hψ := Chebyshev.psi_le_const_mul_self hx0.le
      have : x ^ (-s - 1).re = x ^ (-s.re) * x⁻¹ := by
        rw [show (-s - 1).re = -s.re + (-1) by simp; ring, Real.rpow_add hx0, Real.rpow_neg_one]
      rw [this]
      have hxp : 0 < x ^ (-s.re) := Real.rpow_pos_of_pos hx0 _
      calc Chebyshev.psi x * (x ^ (-s.re) * x⁻¹) ≤ (cψ * x) * (x ^ (-s.re) * x⁻¹) := by
            gcongr; exact hψ
        _ = cψ * x ^ (-s.re) := by field_simp
  have hi12 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((θ : ℂ) - s - 1) + (ε : ℂ) * (x : ℂ) ^ (-s))
      (Ioi 1) := hi1.add hi2
  rw [mellinK, setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hi12 hi3,
    integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one, ZetaAux.integral_psi_mul_cpow hs]
  simp only [ofReal_one, one_cpow]
  rw [show (θ : ℂ) - s - 1 + 1 = -(s - θ) by ring, show -s + 1 = -(s - 1) by ring]
  field_simp
  ring

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

theorem core {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < ρ.re) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ᶠ x in atTop, 0 ≤ Aθ θ ε x) : False := by
  have hθ1 : θ < 1 := lt_trans hθ hρ1
  have hεabs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hε2 : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp h
  set X₀ := max X₁ 1 with hX₀def
  have hX₀ : ∀ x, X₀ ≤ x → 0 ≤ Aθ θ ε x := fun x hx => hX₁ x (le_trans (le_max_left _ _) hx)
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  set A := Aθ θ ε with hAdef
  have hA : Measurable A := measurable_Aθ θ ε
  set A₁ : ℝ → ℝ := fun x => if X₀ < x then A x else 0 with hA₁def
  set A₂ : ℝ → ℝ := fun x => if X₀ < x then 0 else A x with hA₂def
  have hA₁ : Measurable A₁ := Measurable.ite measurableSet_Ioi hA measurable_const
  have hA₂ : Measurable A₂ := Measurable.ite measurableSet_Ioi measurable_const hA
  have hA₁0 : ∀ x, 1 < x → 0 ≤ A₁ x := by
    intro x _
    simp only [hA₁def]
    split_ifs with hx
    · exact hX₀ x hx.le
    · exact le_refl 0
  have hsplit : ∀ x, A x = A₁ x + A₂ x := by
    intro x; simp only [hA₁def, hA₂def]; split_ifs <;> ring
  -- convergence of the pieces
  have hconvA₁ : ∀ σ, 1 < σ → Conv A₁ σ := by
    intro σ hσ
    have hI : IntegrableOn (fun x : ℝ => (2 + cψ) * x ^ (-σ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hI.mono' ((hA₁.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (1:ℝ) < x := hx
    have hx0 : (0:ℝ) < x := by linarith
    have hb : |A₁ x| ≤ (2 + cψ) * x := by
      simp only [hA₁def]
      split_ifs
      · exact abs_Aθ_le hθ1.le hεabs hx'.le
      · simp; have := cψ_pos; nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc |A₁ x| * x ^ (-σ - 1) ≤ (2 + cψ) * x * x ^ (-σ - 1) := by gcongr
      _ = (2 + cψ) * x ^ (-σ) := by
        rw [mul_assoc, show -σ - 1 = -σ + (-1) by ring, Real.rpow_add hx0, Real.rpow_neg_one]
        field_simp
  have hconvA₂ : ∀ σ, ConvAbs A₂ σ := by
    intro σ
    have hsplitI : Ioi (1:ℝ) = Ioc 1 X₀ ∪ Ioi X₀ := (Ioc_union_Ioi_eq_Ioi hX₀1).symm
    unfold ConvAbs
    rw [hsplitI]
    refine IntegrableOn.union ?_ ?_
    · refine Measure.integrableOn_of_bounded (M := (2 + cψ) * X₀ * X₀ ^ (|σ| + 1))
        (by simp) ((hA₂.abs.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx0 : (0:ℝ) < x := by linarith
      have hA2x : A₂ x = A x := by simp only [hA₂def]; rw [if_neg (not_lt.mpr hx2)]
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), hA2x]
      have hb := abs_Aθ_le hθ1.le hεabs hx1.le
      have hpow : x ^ (-σ - 1) ≤ X₀ ^ (|σ| + 1) := by
        calc x ^ (-σ - 1) ≤ x ^ (|σ| + 1) :=
              Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [neg_abs_le σ])
          _ ≤ X₀ ^ (|σ| + 1) :=
              Real.rpow_le_rpow hx0.le hx2 (by positivity)
      have hc := cψ_pos
      calc |A x| * x ^ (-σ - 1) ≤ ((2 + cψ) * X₀) * X₀ ^ (|σ| + 1) := by
            apply mul_le_mul (hb.trans (by gcongr)) hpow (Real.rpow_nonneg hx0.le _)
              (by positivity)
        _ = (2 + cψ) * X₀ * X₀ ^ (|σ| + 1) := by ring
    · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
      have hx' : X₀ < x := hx
      simp only [hA₂def, if_pos hx', abs_zero, zero_mul]
  -- the entire correction term `E`
  set E : ℂ → ℂ := mellinK A₂ 0 with hEdef
  have hEdiff : Differentiable ℂ E := by
    intro s
    have := differentiableOn_mellinK hA₂ (τ := s.re - 1) (fun σ _ => hconvA₂ σ) 0
    exact this.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp))
  -- `mellinK A₁ 0 = mellinK A 0 - E` on `Re s > 1`
  have hconvAbsA₁ : ∀ σ, 1 < σ → ConvAbs A₁ σ := fun σ hσ => convAbs_of_conv hA₁0 (hconvA₁ σ hσ)
  have hsplitM : ∀ s : ℂ, 1 < s.re → mellinK A 0 s = mellinK A₁ 0 s + E s := by
    intro s hs
    have i1 := integrable_integrand hA₁ hconvAbsA₁ 0 hs
    have i2 := integrable_integrand hA₂ (τ := 1) (fun σ _ => hconvA₂ σ) 0 hs
    rw [hEdef, mellinK, mellinK, mellinK, ← integral_add i1 i2]
    congr 1
    funext x
    rw [hsplit x]
    push_cast
    ring
  -- the holomorphic continuation `G`
  set h := zetaMulSubOne with hhdef
  have hdiff_h : Differentiable ℂ h := differentiable_zetaMulSubOne
  have hdiff_h' : Differentiable ℂ (deriv h) := by
    have := (hdiff_h.differentiableOn (s := univ)).deriv isOpen_univ
    exact fun z => (this z (mem_univ z)).differentiableAt (univ_mem)
  set G : ℂ → ℂ := fun s => 1 / (s - θ) + ε * (1 / s + deriv h s / (s * h s)) - E s with hGdef
  set U : Set ℂ := {s | s ≠ 0} ∩ ({s | s ≠ (θ : ℂ)} ∩ {s | h s ≠ 0}) with hUdef
  have hUopen : IsOpen U :=
    isOpen_compl_singleton.inter (isOpen_compl_singleton.inter
      (isOpen_compl_singleton.preimage hdiff_h.continuous))
  have hGdiff : DifferentiableOn ℂ G U := by
    intro s hs
    obtain ⟨hs0, hsθ, hsh⟩ := hs
    have hs0' : s ≠ 0 := hs0
    have hsθ' : s - θ ≠ 0 := sub_ne_zero.mpr hsθ
    have hsh' : s * h s ≠ 0 := mul_ne_zero hs0' hsh
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub (DifferentiableAt.add ?_ ?_) (hEdiff s)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _) hsθ'
    · refine (differentiableAt_const _).mul (DifferentiableAt.add ?_ ?_)
      · exact (differentiableAt_const _).div differentiableAt_id hs0'
      · exact (hdiff_h' s).div (differentiableAt_id.mul (hdiff_h s)) hsh'
  have hUc : ∀ s : ℂ, 1 < s.re → s ∈ U := by
    intro s hs
    refine ⟨?_, ?_, ?_⟩
    · intro h0; rw [h0] at hs; simp at hs; linarith
    · intro h0; rw [h0] at hs; simp at hs; linarith
    · exact zetaMulSubOne_ne_zero_of_one_le_re hs.le
  have hUr : ∀ σ : ℝ, θ < σ → (σ : ℂ) ∈ U := by
    intro σ hσ
    refine ⟨?_, ?_, ?_⟩
    · intro h0; simp only [ofReal_eq_zero] at h0; linarith
    · intro h0; simp only [ofReal_inj] at h0; linarith
    · exact zetaMulSubOne_ne_zero_of_pos (by linarith)
  have hFG : ∀ s : ℂ, 1 < s.re → mellinK A₁ 0 s = G s := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h1; rw [h1] at hs; simp at hs
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have e1 := hsplitM s hs
    rw [hAdef, mellinK_Aθ hθ1 hs] at e1
    simp only [hGdef, hhdef]
    rw [deriv_zetaMulSubOne hs1, zetaMulSubOne_of_ne hs1]
    have : mellinK A₁ 0 s = 1 / (s - θ) + ε / (s - 1) +
        ε * (deriv riemannZeta s / (s * riemannZeta s)) - E s := by
      rw [e1]; ring
    rw [this]
    field_simp
    ring
  -- Landau's theorem: the Mellin integral of `A₁` converges for every `σ > θ`
  have hland := landau hA₁ hA₁0 (σ₀ := θ) (c := 1) hconvA₁ hUopen hGdiff hUc hUr hFG
  have hconvAbs' : ∀ σ, θ < σ → ConvAbs A₁ σ := fun σ hσ => convAbs_of_conv hA₁0 (hland σ hσ)
  have hF₁diff : DifferentiableOn ℂ (mellinK A₁ 0) {z : ℂ | θ < z.re} :=
    differentiableOn_mellinK hA₁ hconvAbs' 0
  -- `h' = P h` on `Re s > θ`
  set P : ℂ → ℂ := fun s => s * ε * (mellinK A₁ 0 s + E s - 1 / (s - θ)) - 1 with hPdef
  set V : Set ℂ := {z : ℂ | θ < z.re} with hVdef
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hPdiff : DifferentiableOn ℂ P V := by
    intro s hs
    have hsθ' : s - θ ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; simp [hVdef] at hs; linarith
    have hF : DifferentiableAt ℂ (mellinK A₁ 0) s := hF₁diff.differentiableAt (hVopen.mem_nhds hs)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub_const ?_ _
    refine (differentiableAt_id.mul_const _).mul ?_
    exact (hF.add (hEdiff s)).sub ((differentiableAt_const _).div (differentiableAt_id.sub_const _)
      hsθ')
  have hPh : ∀ s ∈ V, deriv h s = P s * h s := by
    have hL : DifferentiableOn ℂ (deriv h) V := hdiff_h'.differentiableOn
    have hR : DifferentiableOn ℂ (fun s => P s * h s) V := hPdiff.mul hdiff_h.differentiableOn
    have h2V : (2:ℂ) ∈ V := by simp [hVdef]; linarith
    have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hL.analyticOnNhd hVopen) (hR.analyticOnNhd hVopen) (convex_halfSpace_re_gt θ).isPreconnected
      h2V ?_
    · exact fun s hs => heq hs
    · have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [this] with s hs
      have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
      have hhs : h s ≠ 0 := zetaMulSubOne_ne_zero_of_one_le_re hs.le
      have hsθ' : s - θ ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      simp only [hPdef]
      rw [hFG s hs]
      simp only [hGdef]
      field_simp
      linear_combination (-(deriv h s * s - deriv h s * θ + s * h s - θ * h s)) * hε2
  -- contradiction at the zero `ρ`
  have hρV : ρ ∈ V := by simp [hVdef]; linarith
  have hρ1' : ρ ≠ 1 := by intro h1; rw [h1] at hρ1; simp at hρ1
  have hhρ : h ρ = 0 := by rw [hhdef, zetaMulSubOne_of_ne hρ1', hρ, mul_zero]
  have hnz : ¬ ∀ᶠ z in 𝓝 ρ, h z = 0 := by
    intro hev
    have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (hdiff_h.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ ρ) hev
    exact zetaMulSubOne_ne_zero_of_one_le_re (s := 2) (by norm_num) (this (mem_univ 2))
  exact ne_zero_of_deriv_eq_mul hVopen hρV (hdiff_h.analyticAt ρ)
    (hPdiff.differentiableAt (hVopen.mem_nhds hρV)).continuousAt hPh hnz hhρ

/-! ### The oscillation theorems -/

/-- **Landau's oscillation theorem (Ω₊).** If `ζ(ρ) = 0` with `0 < Re ρ < 1`, then for every
`θ < Re ρ` we have `ψ(x) - x > x^θ` for arbitrarily large `x`. -/
theorem frequently_rpow_lt_psi_sub {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {θ : ℝ} (hθ : θ < ρ.re) :
    ∃ᶠ x in atTop, x ^ θ < Chebyshev.psi x - x := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set θ' := max θ (ρ.re / 2) with hθ'
  have hθ'0 : 0 < θ' := lt_max_of_lt_right (by linarith)
  have hθ'ρ : θ' < ρ.re := max_lt hθ (by linarith)
  apply core hρ hρ1 hθ'0 hθ'ρ (Or.inl rfl)
  filter_upwards [hcon, eventually_ge_atTop 1] with x hx hx1
  have : Chebyshev.psi x - x ≤ x ^ θ' :=
    (not_lt.mp hx).trans (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
  simp only [Aθ]
  linarith

/-- **Landau's oscillation theorem (Ω₋).** If `ζ(ρ) = 0` with `0 < Re ρ < 1`, then for every
`θ < Re ρ` we have `ψ(x) - x < -x^θ` for arbitrarily large `x`. -/
theorem frequently_psi_sub_lt_neg_rpow {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {θ : ℝ} (hθ : θ < ρ.re) :
    ∃ᶠ x in atTop, Chebyshev.psi x - x < -x ^ θ := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set θ' := max θ (ρ.re / 2) with hθ'
  have hθ'0 : 0 < θ' := lt_max_of_lt_right (by linarith)
  have hθ'ρ : θ' < ρ.re := max_lt hθ (by linarith)
  apply core hρ hρ1 hθ'0 hθ'ρ (Or.inr rfl)
  filter_upwards [hcon, eventually_ge_atTop 1] with x hx hx1
  have h1 : -x ^ θ ≤ Chebyshev.psi x - x := not_lt.mp hx
  have h2 : x ^ θ ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  simp only [Aθ]
  linarith

/-! ### Consequences of the failure of the Riemann hypothesis -/

/-- A zero of `ζ` with real part `≤ 0` is a trivial zero (or `ζ` does not vanish there). -/
lemma re_pos_of_zero {s : ℂ} (hs0 : riemannZeta s = 0)
    (hstriv : ∀ n : ℕ, s ≠ -2 * (n + 1)) : 0 < s.re := by
  by_contra h
  push Not at h
  have hsne0 : s ≠ 0 := by
    intro h0; rw [h0, riemannZeta_zero] at hs0; norm_num at hs0
  set s' := 1 - s with hs'
  have hs're : 1 ≤ s'.re := by simp [hs']; linarith
  have hnotint : ∀ n : ℕ, s' ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs'1 : s' ≠ 1 := by
    intro h1; apply hsne0; rw [hs'] at h1; linear_combination -h1
  have hfe := riemannZeta_one_sub hnotint hs'1
  rw [show 1 - s' = s by simp [hs'], hs0] at hfe
  have hζ' : riemannZeta s' ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs're
  have hΓ : Gamma s' ≠ 0 := Complex.Gamma_ne_zero hnotint
  have h2π : (2 * (Real.pi : ℂ)) ^ (-s') ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    rintro ⟨h, _⟩
    have : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    exact this h
  have hcos : Complex.cos (Real.pi * s' / 2) = 0 := by
    have h' := hfe.symm
    simp only [mul_eq_zero, two_ne_zero, false_or, hΓ, hζ', or_false] at h'
    rcases h' with h' | h'
    · exact absurd h' h2π
    · exact h'
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs'k : s' = 2 * k + 1 := by
    apply mul_left_cancel₀ hπ
    linear_combination 2 * hk
  have hsk : s = -2 * k := by
    have : s = 1 - s' := by simp [hs']
    rw [this, hs'k]; ring
  have hkre : s.re = -2 * k := by rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    have : ((-2 * k : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
    have : -2 * k ≤ 0 := by exact_mod_cast this
    linarith
  rcases eq_or_lt_of_le hk0 with hk | hk
  · apply hsne0; rw [hsk, ← hk]; simp
  · apply hstriv (k - 1).toNat
    rw [hsk]
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by linarith)
    have : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast this
    rw [this]; ring

/-- If the Riemann hypothesis fails, then `ζ` has a zero `ρ` with `1/2 < Re ρ < 1`. -/
theorem exists_zero_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 := by
  unfold RiemannHypothesis at hRH
  push Not at hRH
  obtain ⟨s, hs0, hstriv, hs1, hshalf⟩ := hRH
  have hlt1 : s.re < 1 := by
    by_contra h; push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hs0
  have hgt0 : 0 < s.re := re_pos_of_zero hs0 hstriv
  rcases lt_or_gt_of_ne hshalf with hlt | hgt
  · refine ⟨1 - s, ?_, by simp; linarith, by simp; linarith⟩
    have hnotint : ∀ n : ℕ, s ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      simp only [neg_re, natCast_re] at this
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [riemannZeta_one_sub hnotint hs1, hs0, mul_zero]
  · exact ⟨s, hs0, hgt, hlt1⟩

/-- **Oscillation of `ψ` when the Riemann hypothesis fails.** If RH fails, there is `b > 1/2`
(the real part of a zero of `ζ` in the critical strip) such that for every `ε > 0`,
`ψ(x) - x > x^{b-ε}` and `ψ(x) - x < -x^{b-ε}` both hold for arbitrarily large `x`;
that is, `ψ(x) - x = Ω_±(x^{b-ε})`. -/
theorem psi_oscillation_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ b : ℝ, 1 / 2 < b ∧ b < 1 ∧ ∀ ε : ℝ, 0 < ε →
      (∃ᶠ x in atTop, x ^ (b - ε) < Chebyshev.psi x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.psi x - x < -x ^ (b - ε)) := by
  obtain ⟨ρ, hρ, hρ1, hρ2⟩ := exists_zero_of_not_RH hRH
  refine ⟨ρ.re, hρ1, hρ2, fun ε hε => ⟨?_, ?_⟩⟩
  · exact frequently_rpow_lt_psi_sub hρ (by linarith) hρ2 (by linarith)
  · exact frequently_psi_sub_lt_neg_rpow hρ (by linarith) hρ2 (by linarith)


/-! ### The same oscillation for `θ` -/

/-- For `1/2 < α` and `β < α`, eventually `x^β + 2√x log x < x^α`. -/
lemma eventually_rpow_add_sqrt_mul_log_lt {α β : ℝ} (hα : 1 / 2 < α) (hβ : β < α) :
    ∀ᶠ x in atTop, x ^ β + 2 * Real.sqrt x * Real.log x < x ^ α := by
  set δ := (α - 1 / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set γ := max β (1 / 2 + δ) with hγ
  have hγα : γ < α := max_lt hβ (by rw [hδ]; linarith)
  set K := 1 + 2 / δ with hK
  have htend := tendsto_rpow_atTop (sub_pos.mpr hγα)
  filter_upwards [htend.eventually_gt_atTop K, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have h1 : x ^ β ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have h2 : 2 * Real.sqrt x * Real.log x ≤ (2 / δ) * x ^ γ := by
    have e : x ^ (1 / 2 : ℝ) * x ^ δ = x ^ (1 / 2 + δ) := (Real.rpow_add hx0 _ _).symm
    have h3 : x ^ (1 / 2 + δ) ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
    calc 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * (x ^ δ / δ) := by gcongr
      _ = (2 / δ) * (x ^ (1 / 2 : ℝ) * x ^ δ) := by rw [Real.sqrt_eq_rpow]; ring
      _ = (2 / δ) * x ^ (1 / 2 + δ) := by rw [e]
      _ ≤ (2 / δ) * x ^ γ := by gcongr
  have h4 : K * x ^ γ < x ^ α := by
    have e : x ^ α = x ^ (α - γ) * x ^ γ := by rw [← Real.rpow_add hx0]; ring_nf
    rw [e]
    exact mul_lt_mul_of_pos_right hx (Real.rpow_pos_of_pos hx0 _)
  calc x ^ β + 2 * Real.sqrt x * Real.log x ≤ x ^ γ + (2 / δ) * x ^ γ := add_le_add h1 h2
    _ = K * x ^ γ := by rw [hK]; ring
    _ < x ^ α := h4

/-- **Oscillation of `θ` when the Riemann hypothesis fails.** -/
theorem theta_oscillation_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ b : ℝ, 1 / 2 < b ∧ b < 1 ∧ ∀ ε : ℝ, 0 < ε →
      (∃ᶠ x in atTop, x ^ (b - ε) < Chebyshev.theta x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.theta x - x < -x ^ (b - ε)) := by
  obtain ⟨ρ, hρ, hρ1, hρ2⟩ := exists_zero_of_not_RH hRH
  refine ⟨ρ.re, hρ1, hρ2, fun ε hε => ⟨?_, ?_⟩⟩
  · set ε' := min ε (ρ.re - 1 / 2) / 2 with hε'
    have hm : 0 < min ε (ρ.re - 1 / 2) := lt_min hε (by linarith)
    have hε'0 : 0 < ε' := div_pos hm two_pos
    have hε'ε : ε' < ε := by
      have := min_le_left ε (ρ.re - 1 / 2); rw [hε']; linarith
    have hα : 1 / 2 < ρ.re - ε' := by
      have := min_le_right ε (ρ.re - 1 / 2); rw [hε']; linarith
    have hfreq := frequently_rpow_lt_psi_sub hρ (by linarith) hρ2 (θ := ρ.re - ε')
      (by linarith)
    have hev := eventually_rpow_add_sqrt_mul_log_lt hα (β := ρ.re - ε) (by linarith)
    refine (hfreq.and_eventually (hev.and (eventually_ge_atTop 1))).mono ?_
    rintro x ⟨h1, h2, hx1⟩
    have h3 := (abs_le.mp (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1)).2
    linarith
  · refine (frequently_psi_sub_lt_neg_rpow hρ (by linarith) hρ2 (θ := ρ.re - ε)
      (by linarith)).mono ?_
    intro x hx
    have := Chebyshev.theta_le_psi x
    linarith


/-! ### The classical form with `Θ = sup {Re ρ}` -/

/-- `Θ = sup {Re ρ : ζ(ρ) = 0, Re ρ > 0}`, the supremum of the real parts of the nontrivial
zeros of `ζ`. -/
def zetaZeroReSup : ℝ :=
  sSup {σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re = σ}

/-- **Landau's oscillation theorem, classical form.** If RH fails, then `Θ > 1/2` and for every
`ε > 0`, `ψ(x) - x = Ω_±(x^{Θ-ε})`. -/
theorem psi_oscillation_zetaZeroReSup (hRH : ¬ RiemannHypothesis) :
    1 / 2 < zetaZeroReSup ∧ ∀ ε : ℝ, 0 < ε →
      (∃ᶠ x in atTop, x ^ (zetaZeroReSup - ε) < Chebyshev.psi x - x) ∧
      (∃ᶠ x in atTop, Chebyshev.psi x - x < -x ^ (zetaZeroReSup - ε)) := by
  set S : Set ℝ := {σ : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re = σ} with hS
  have hlt1 : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 := by
    intro ρ hρ
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  have hbdd : BddAbove S := ⟨1, by rintro σ ⟨ρ, hρ, -, rfl⟩; exact (hlt1 ρ hρ).le⟩
  obtain ⟨ρ₀, hρ₀, hρ₀1, hρ₀2⟩ := exists_zero_of_not_RH hRH
  have hmem : ρ₀.re ∈ S := ⟨ρ₀, hρ₀, by linarith, rfl⟩
  have hΘ : ρ₀.re ≤ zetaZeroReSup := le_csSup hbdd hmem
  refine ⟨lt_of_lt_of_le hρ₀1 hΘ, fun ε hε => ?_⟩
  obtain ⟨σ, ⟨ρ, hρ, hρ0, rfl⟩, hσ⟩ :=
    exists_lt_of_lt_csSup ⟨_, hmem⟩ (show zetaZeroReSup - ε < zetaZeroReSup by linarith)
  exact ⟨frequently_rpow_lt_psi_sub hρ hρ0 (hlt1 ρ hρ) hσ,
    frequently_psi_sub_lt_neg_rpow hρ hρ0 (hlt1 ρ hρ) hσ⟩

end PsiOscillation

/-- **Milestone** `LandauCriterion.psi_oscillation_of_not_riemannHypothesis`:
if RH fails, there are `β > 1/2` and `c > 0` such that for every `ε > 0`,
`ψ(x) - x ≥ c x^{β-ε}` and `ψ(x) - x ≤ -c x^{β-ε}` both hold for arbitrarily large `x`.
We take `c = 1` and `β = Re ρ` for a zero `ρ` of `ζ` with `1/2 < Re ρ < 1`. -/
theorem solution (h : ¬ RiemannHypothesis) :
    ∃ β c : ℝ, 1 / 2 < β ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      (Filter.Frequently (fun x : ℝ => c * x ^ (β - ε) ≤ Chebyshev.psi x - x) Filter.atTop) ∧
      (Filter.Frequently (fun x : ℝ => Chebyshev.psi x - x ≤ -c * x ^ (β - ε)) Filter.atTop) := by
  obtain ⟨b, hb, -, hosc⟩ := PsiOscillation.psi_oscillation_of_not_RH h
  refine ⟨b, 1, hb, one_pos, fun ε hε => ⟨?_, ?_⟩⟩
  · exact (hosc ε hε).1.mono fun x hx => by rw [one_mul]; exact hx.le
  · exact (hosc ε hε).2.mono fun x hx => by rw [neg_mul, one_mul]; exact hx.le
