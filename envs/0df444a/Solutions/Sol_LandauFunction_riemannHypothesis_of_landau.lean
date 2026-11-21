-- Prove2me | solution 1 for LandauFunction.riemannHypothesis_of_landau
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-20T23:56:06.07058+00:00
-- url     : https://prove2.me/submissions/079eacc0-fc10-4c11-bf05-c41e94b63dbc

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

/-!
# `log g(n) < √(Li⁻¹ n)` for all large `n` ⇒ RH

Primorials give `∫₂ˣ w(t)(θ(t) - t) dt < c₂`, hence `A(x) = 2x√x + c₂ - ∫₂ˣ w(ψ - t) ≥ 0`;
Landau's theorem for Mellin transforms of nonnegative functions (with primitives on a zero-free
half-strip) continues `∫ A(x) x^{-s-1} dx` to `Re s > 3/2`; an ODE trick then forces
`h' = P h` near any zero `ρ₀` of `ζ` with `Re ρ₀ > 1/2`, a contradiction.
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
      refine ⟨(z.re : ℂ), ⟨z.re, ⟨by simp only [mem_ofPred_eq] at h1; linarith,
        by simp only [mem_ofPred_eq] at h2; linarith⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_ofReal_re]
      simp only [mem_ofPred_eq] at h3 h4
      exact abs_lt.mpr ⟨h3, h4⟩
    · exact hUc z h
  have hWopen : IsOpen W := by
    refine IsOpen.union ?_ (isOpen_lt continuous_const Complex.continuous_re)
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hz₀W₁ : ((c + 1/2 : ℝ) : ℂ) ∈ W₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mem_ofPred_eq, ofReal_re, ofReal_im] <;> linarith
  have hz₀W₂ : ((c + 1/2 : ℝ) : ℂ) ∈ {z : ℂ | c < z.re} := by
    simp only [mem_ofPred_eq, ofReal_re]; linarith
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
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mem_ofPred_eq] <;> linarith
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

end

-- ===== Oscillation.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric

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

/-- The Chebyshev constant used below. -/
def cψ : ℝ := Real.log 4 + 4

lemma cψ_pos : 0 < cψ := by
  unfold cψ; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith

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

end PsiOscillation

end

-- ===== LF7Comb.lean =====
section

set_option autoImplicit false

open Finset

namespace LandauRH

/-! ### The additive function `ℓ(m) = ∑_{p^a ‖ m} p^a` -/

/-! ### The bound `log g(n) ≤ λ n + M(λ)` -/

lemma log_div_self_antitone {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a := by
  have := Real.log_div_self_antitoneOn (show a ∈ Set.Ici (Real.exp 1) from ha)
    (show b ∈ Set.Ici (Real.exp 1) from ha.trans hab) hab
  simpa using this

/-! ### Primorials -/

lemma lcm_primes_eq_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : s.lcm id = ∏ p ∈ s, p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [lcm_insert, prod_insert ha, ih (fun p hp => hs p (mem_insert_of_mem hp))]
    have hap : a.Prime := hs a (mem_insert_self a s)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      have hpp : p.Prime := hs p (mem_insert_of_mem hp)
      exact (Nat.coprime_primes hap hpp).mpr (fun h => ha (h ▸ hp))
    simp only [id]
    exact hcop.lcm_eq_mul

/-- `g(∑_{p ≤ x} p) ≥ ∏_{p ≤ x} p`. -/
theorem prod_primes_le_landau (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ≤ LandauFunction.landau (∑ p ∈ s, p) := by
  classical
  set n := ∑ p ∈ s, p
  have hex : ∃ σ : Equiv.Perm (Fin n), σ.cycleType = s.val := by
    rw [Equiv.Perm.exists_with_cycleType_iff]
    refine ⟨?_, fun a ha => (hs a ha).two_le⟩
    rw [Fintype.card_fin]
    simp [n]
  obtain ⟨σ, hσ⟩ := hex
  have hord : orderOf σ = ∏ p ∈ s, p := by
    rw [← Equiv.Perm.lcm_cycleType, hσ, ← lcm_primes_eq_prod s hs, Finset.lcm_def]
    simp
  rw [← hord]
  exact Finset.le_sup (f := fun σ => orderOf σ) (Finset.mem_univ σ)

end LandauRH

end

-- ===== LF7Li.lean =====
section

set_option autoImplicit false

open Set Filter Topology

namespace LandauRH

open LandauFunction

lemma continuousOn_one_div_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Ioi 1) := by
  intro t ht
  have ht' : (1:ℝ) < t := ht
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos ht').ne').continuousWithinAt

lemma intervalIntegrable_one_div_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_one_div_log.mono (fun t ht => ?_)
  rcases mem_uIcc.mp ht with h | h
  · show 1 < t; linarith [h.1]
  · show 1 < t; linarith [h.1]

lemma hasDerivAt_logIntegral {y : ℝ} (hy : 1 < y) :
    HasDerivAt logIntegral (1 / Real.log y) y := by
  unfold logIntegral
  apply intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_one_div_log
    (by norm_num) hy)
  · exact (continuousOn_one_div_log.stronglyMeasurableAtFilter isOpen_Ioi y hy)
  · exact (continuousOn_one_div_log y hy).continuousAt (isOpen_Ioi.mem_nhds hy)

lemma logIntegral_two : logIntegral 2 = 0 := by simp [logIntegral]

lemma continuousOn_logIntegral : ContinuousOn logIntegral (Ioi 1) := fun y hy =>
  (hasDerivAt_logIntegral hy).continuousAt.continuousWithinAt

lemma logIntegral_strictMonoOn : StrictMonoOn logIntegral (Ici 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 2)
  · exact continuousOn_logIntegral.mono (fun t ht => by show 1 < t; linarith [mem_Ici.mp ht])
  · intro y hy
    rw [interior_Ici] at hy
    have hy' : (2:ℝ) < y := hy
    rw [(hasDerivAt_logIntegral (by linarith)).deriv]
    exact div_pos one_pos (Real.log_pos (by linarith))

lemma logIntegral_ge {y : ℝ} (hy : 2 ≤ y) : (y - 2) / Real.log y ≤ logIntegral y := by
  unfold logIntegral
  have h := intervalIntegral.integral_mono_on (a := (2:ℝ)) (b := y) (g := fun t => 1 / Real.log t)
    (f := fun _ => 1 / Real.log y) hy intervalIntegrable_const
    (intervalIntegrable_one_div_log (by norm_num) (by linarith)) (fun t ht => by
      apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
      exact Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  rw [div_eq_mul_one_div]
  linarith

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr hx), Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  linarith

/-- `Li(Li⁻¹(n)) = n` and `Li⁻¹(n) ≥ 2` for `n ≥ 0`. -/
theorem logIntegral_logIntegralInv {n : ℝ} (hn : 0 ≤ n) :
    logIntegral (logIntegralInv n) = n ∧ 2 ≤ logIntegralInv n := by
  set S : Set ℝ := {x : ℝ | 2 ≤ x ∧ n ≤ logIntegral x} with hS
  have hbdd : BddBelow S := ⟨2, fun x hx => hx.1⟩
  -- nonempty
  set x₁ : ℝ := (4 * n + 8) ^ 2 with hx₁
  have hx₁64 : 64 ≤ x₁ := by rw [hx₁]; nlinarith
  have hsq : Real.sqrt x₁ = 4 * n + 8 := by rw [hx₁]; exact Real.sqrt_sq (by linarith)
  have hne : S.Nonempty := by
    refine ⟨x₁, by linarith, ?_⟩
    have h1 := logIntegral_ge (y := x₁) (by linarith)
    have h2 := log_le_two_sqrt (x := x₁) (by linarith)
    rw [hsq] at h2
    have hlog : 0 < Real.log x₁ := Real.log_pos (by linarith)
    have h3 : n ≤ (x₁ - 2) / Real.log x₁ := by
      rw [le_div_iff₀ hlog]
      nlinarith
    linarith
  -- closed
  have hclosed : IsClosed S := by
    have hc : ContinuousOn logIntegral (Ici 2) :=
      continuousOn_logIntegral.mono (fun t ht => by show 1 < t; linarith [mem_Ici.mp ht])
    have := hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Ici (a := n))
    convert this using 1
    ext x; simp [hS, and_comm]
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  refine ⟨?_, hmem.1⟩
  have hge : n ≤ logIntegral (sInf S) := hmem.2
  by_contra hne'
  have hgt : n < logIntegral (sInf S) := lt_of_le_of_ne hge (Ne.symm hne')
  have h2 : 2 < sInf S := by
    rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h, logIntegral_two] at hgt; linarith
    · exact h
  -- by continuity there is a smaller point of `S`
  have hcont : ContinuousAt logIntegral (sInf S) :=
    (hasDerivAt_logIntegral (by linarith)).continuousAt
  have hev : ∀ᶠ z in 𝓝 (sInf S), n < logIntegral z := hcont.eventually (lt_mem_nhds hgt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set z := sInf S - min (ε / 2) ((sInf S - 2) / 2) with hz
  have hzlt : z < sInf S := by
    have : 0 < min (ε / 2) ((sInf S - 2) / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hz2 : 2 ≤ z := by
    have : min (ε / 2) ((sInf S - 2) / 2) ≤ (sInf S - 2) / 2 := min_le_right _ _
    linarith
  have hzS : z ∈ S := by
    refine ⟨hz2, (hball ?_).le⟩
    rw [Real.dist_eq, abs_lt]
    have : min (ε / 2) ((sInf S - 2) / 2) ≤ ε / 2 := min_le_left _ _
    have : 0 < min (ε / 2) ((sInf S - 2) / 2) := lt_min (by linarith) (by linarith)
    constructor <;> linarith
  have := csInf_le hbdd hzS
  linarith

/-- If `2 ≤ a < Li⁻¹(n)` then `Li(a) < n`. -/
lemma logIntegral_lt_of_lt_logIntegralInv {n a : ℝ} (hn : 0 ≤ n) (ha : 2 ≤ a)
    (hlt : a < logIntegralInv n) : logIntegral a < n := by
  obtain ⟨h1, h2⟩ := logIntegral_logIntegralInv hn
  have := logIntegral_strictMonoOn (show a ∈ Ici 2 from ha) (show logIntegralInv n ∈ Ici 2 from h2)
    hlt
  rwa [h1] at this

/-- `d/dx Li(x²) = x / log x`. -/
lemma hasDerivAt_logIntegral_sq {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => logIntegral (t ^ 2)) (x / Real.log x) x := by
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt logIntegral (1 / Real.log (x ^ 2)) (x ^ 2) := hasDerivAt_logIntegral hx2
  have h : HasDerivAt (fun t : ℝ => logIntegral (t ^ 2)) (1 / Real.log (x ^ 2) * (2 * x)) x :=
    HasDerivAt.comp (h := fun t : ℝ => t ^ 2) x h1 hp
  convert h using 1
  have hlog : Real.log (x ^ 2) = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [hlog]
  field_simp

end LandauRH

end

-- ===== LF7Q.lean =====
section

set_option autoImplicit false

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction

/-! ### The weight `W(t) = t / log t` and its derivatives -/

/-- `W(t) = t / log t`. -/
def Wf (t : ℝ) : ℝ := t / Real.log t

/-- `w = W' = (log t - 1) / log² t`. -/
def wf (t : ℝ) : ℝ := (Real.log t - 1) / Real.log t ^ 2

lemma hasDerivAt_Wf {t : ℝ} (ht : 1 < t) : HasDerivAt Wf (wf t) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have h : HasDerivAt (fun x => x / Real.log x)
      ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t :=
    (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
  have e : (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2 = wf t := by
    simp only [wf]; field_simp
  rw [e] at h
  exact h

lemma continuousOn_log_Ioi : ContinuousOn Real.log (Ioi 1) :=
  Real.continuousOn_log.mono (fun t (ht : 1 < t) => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith)

lemma log_ne_zero_of_one_lt {t : ℝ} (ht : 1 < t) : Real.log t ≠ 0 := (Real.log_pos ht).ne'

lemma continuousOn_wf : ContinuousOn wf (Ioi 1) := by
  refine ContinuousOn.div (continuousOn_log_Ioi.sub continuousOn_const)
    (continuousOn_log_Ioi.pow 2) (fun t ht => pow_ne_zero 2 (log_ne_zero_of_one_lt ht))

lemma uIcc_subset_Ioi {a b : ℝ} (ha : 1 < a) (hb : 1 < b) : uIcc a b ⊆ Ioi 1 := by
  intro t ht
  have := ht.1
  simp only [mem_Ioi]
  exact lt_of_lt_of_le (lt_inf_iff.mpr ⟨ha, hb⟩) this

lemma intervalIntegrable_of_Ioi {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 1)) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) : IntervalIntegrable f volume a b :=
  (hf.mono (uIcc_subset_Ioi ha hb)).intervalIntegrable

/-! ### `ψ₁` is continuous -/

/-! ### Identity 1: `R_W(x) = ψ₁(x) w(x) - ∫₂ˣ ψ₁ w'` -/

/-! ### Identity 2 -/

/-! ### Elementary bounds -/

lemma log_gt_069 {t : ℝ} (ht : 2 ≤ t) : 0.69 < Real.log t :=
  lt_of_lt_of_le (lt_trans (by norm_num) Real.log_two_gt_d9) (Real.log_le_log (by norm_num) ht)

lemma rpow_three_halves_eq {t : ℝ} (ht : 0 < t) : t ^ (3/2:ℝ) = t * Real.sqrt t := by
  rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add ht, Real.rpow_one, Real.sqrt_eq_rpow]

end LandauRH

end

-- ===== LF7G.lean =====
section

set_option autoImplicit false

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction

/-! ### `θ(t) = t + O(√t log² t)` under RH -/

/-! ### Abel summation against `θ` -/

/-- `c(k) = log k` if `k` is prime, `0` otherwise. -/
def cθ (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

lemma sum_cθ_eq_theta (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cθ k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]; rfl

lemma abel_theta {f f' : ℝ → ℝ} {b : ℝ} (hb : 2 ≤ b)
    (hf : ∀ t ∈ Icc 2 b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc 2 b)) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k * cθ k =
      f b * Chebyshev.theta b - ∫ t in (2:ℝ)..b, f' t * Chebyshev.theta t := by
  have hderiv : EqOn (deriv f) f' (Icc 2 b) := fun t ht => (hf t ht).deriv
  have hint : IntegrableOn (deriv f) (Icc 2 b) :=
    (hf'.integrableOn_Icc).congr_fun hderiv.symm measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ cθ (by simp [cθ]) (by simp [cθ]) b
    (fun t ht => (hf t ht).differentiableAt) hint
  rw [h, sum_cθ_eq_theta, integral_of_le hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [sum_cθ_eq_theta, hderiv (Ioc_subset_Icc_self ht)]

lemma intervalIntegrable_mul_theta {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (uIcc a b)) :
    IntervalIntegrable (fun t => g t * Chebyshev.theta t) volume a b :=
  (Chebyshev.theta_mono.intervalIntegrable).continuousOn_mul hg

/-! ### The prime-square sum `P₂ = ∑_{p ≤ √x} (log p - λ p²/2)` -/

/-! ### The `j = 2` part of `M(x)` -/

/-! ### Decomposition of `λ R_W(x)` into prime powers -/

/-! ### The `k ≥ 3` terms -/

/-! ### The `j ≥ 3` part of `M(x)` -/

/-! ### Assembly: lower bound for `G = λ R_W(x) - M(x)` -/

end LandauRH

end

-- ===== LF8a.lean =====
section

set_option autoImplicit false

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction

/-! ### Partial summation for `∑_{p ≤ x} p` -/

lemma sum_primes_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (p:ℝ) =
      Wf x * Chebyshev.theta x - ∫ t in (2:ℝ)..x, wf t * Chebyshev.theta t := by
  have h := abel_theta (f := Wf) (f' := wf) hx (fun t ht => hasDerivAt_Wf (by linarith [ht.1]))
    (continuousOn_wf.mono (fun t ht => by simp only [mem_Ioi]; linarith [ht.1]))
  rw [← h, Finset.sum_filter]
  have hset : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    ext k; simp only [Finset.mem_range, Finset.mem_Icc]; omega
  rw [hset]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k.Prime
  · rw [if_pos hk, cθ, if_pos hk, Wf]
    have hl : Real.log k ≠ 0 := log_ne_zero_of_one_lt (by exact_mod_cast hk.one_lt)
    field_simp
  · rw [if_neg hk, cθ, if_neg hk, mul_zero]

/-- `Ψ₂(x) = x W(x) - ∫₂ˣ t w(t) dt - Li(x²)` is constant. -/
def Psi2 (x : ℝ) : ℝ := x * Wf x - (∫ t in (2:ℝ)..x, t * wf t) - logIntegral (x ^ 2)

lemma continuousOn_id_mul_wf : ContinuousOn (fun t : ℝ => t * wf t) (Ioi 1) :=
  continuousOn_id.mul continuousOn_wf

lemma hasDerivAt_Psi2 {x : ℝ} (hx : 1 < x) : HasDerivAt Psi2 0 x := by
  have h1 : HasDerivAt (fun t => t * Wf t) (1 * Wf x + x * wf x) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_Wf hx)
  have h2 : HasDerivAt (fun u => ∫ t in (2:ℝ)..u, t * wf t) (x * wf x) x :=
    integral_hasDerivAt_right (intervalIntegrable_of_Ioi continuousOn_id_mul_wf (by norm_num) hx)
      (continuousOn_id_mul_wf.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      (continuousOn_id_mul_wf.continuousAt (Ioi_mem_nhds hx))
  have h3 := hasDerivAt_logIntegral_sq hx
  have h := (h1.sub h2).sub h3
  have e : 1 * Wf x + x * wf x - x * wf x - x / Real.log x = 0 := by rw [Wf]; ring
  rw [e] at h
  exact h

lemma Psi2_eq {x : ℝ} (hx : 2 ≤ x) : Psi2 x = Psi2 2 := by
  have h := integral_eq_sub_of_hasDerivAt (f := Psi2) (f' := fun _ => (0:ℝ)) (a := 2) (b := x)
    (fun t ht => hasDerivAt_Psi2 (uIcc_subset_Ioi (by norm_num) (by linarith) ht))
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- `c₂ = Ψ₂(2)`. -/
def c2 : ℝ := Psi2 2

/-- `J_θ(x) = ∫₂ˣ w(t) (θ(t) - t) dt`. -/
def Jtheta (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, wf t * (Chebyshev.theta t - t)

/-- `J_ψ(x) = ∫₂ˣ w(t) (ψ(t) - t) dt`. -/
def Jpsi (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, wf t * (Chebyshev.psi t - t)

lemma intervalIntegrable_wf_mul_sub {f : ℝ → ℝ} (hf : Monotone f) {a b : ℝ} (ha : 1 < a)
    (hb : 1 < b) : IntervalIntegrable (fun t => wf t * (f t - t)) volume a b := by
  have h1 : IntervalIntegrable (fun t => wf t * f t) volume a b :=
    hf.intervalIntegrable.continuousOn_mul (continuousOn_wf.mono (uIcc_subset_Ioi ha hb))
  have h2 : IntervalIntegrable (fun t => wf t * t) volume a b :=
    intervalIntegrable_of_Ioi (continuousOn_wf.mul continuousOn_id) ha hb
  have := h1.sub h2
  convert this using 1
  funext t
  ring

lemma sum_primes_identity {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (p:ℝ) =
      Wf x * (Chebyshev.theta x - x) + logIntegral (x ^ 2) + c2 - Jtheta x := by
  have h1x : (1:ℝ) < x := by linarith
  rw [sum_primes_eq_abel hx]
  have hP := Psi2_eq hx
  rw [Psi2] at hP
  have hI1 : IntervalIntegrable (fun t => wf t * Chebyshev.theta t) volume 2 x :=
    intervalIntegrable_mul_theta (continuousOn_wf.mono (uIcc_subset_Ioi (by norm_num) h1x))
  have hI2 : IntervalIntegrable (fun t : ℝ => t * wf t) volume 2 x :=
    intervalIntegrable_of_Ioi continuousOn_id_mul_wf (by norm_num) h1x
  have hJ : Jtheta x =
      (∫ t in (2:ℝ)..x, wf t * Chebyshev.theta t) - ∫ t in (2:ℝ)..x, t * wf t := by
    rw [Jtheta, ← integral_sub hI1 hI2]
    refine integral_congr (fun t _ => ?_)
    ring
  rw [hJ, c2]
  linarith

/-! ### Convexity-type inequality for `Li(y²)` -/

lemma Wf_monotoneOn : MonotoneOn Wf (Ici (Real.exp 1)) := by
  intro a ha b hb hab
  have ha' : Real.exp 1 ≤ a := ha
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha'
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla : 1 ≤ Real.log a := by rw [Real.le_log_iff_exp_le ha0]; exact ha'
  have hlb : 1 ≤ Real.log b := by rw [Real.le_log_iff_exp_le hb0]; exact ha'.trans hab
  have h := log_div_self_antitone ha' hab
  rw [div_le_div_iff₀ hb0 ha0] at h
  rw [Wf, Wf, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

lemma continuousOn_Wf : ContinuousOn Wf (Ioi 1) :=
  continuousOn_id.div continuousOn_log_Ioi (fun t ht => log_ne_zero_of_one_lt ht)

lemma Li_sq_sub_ge {a b : ℝ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (b - a) * Wf a ≤ logIntegral (b ^ 2) - logIntegral (a ^ 2) := by
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hftc : ∫ t in a..b, Wf t = logIntegral (b ^ 2) - logIntegral (a ^ 2) :=
    integral_eq_sub_of_hasDerivAt
      (f := fun t => logIntegral (t ^ 2)) (fun t ht =>
        hasDerivAt_logIntegral_sq (uIcc_subset_Ioi (by linarith) (by linarith) ht))
      (intervalIntegrable_of_Ioi continuousOn_Wf (by linarith) (by linarith))
  rw [← hftc]
  rcases le_total a b with hab | hab
  · have h := integral_mono_on hab intervalIntegrable_const
      (intervalIntegrable_of_Ioi continuousOn_Wf (by linarith) (by linarith))
      (fun t ht => Wf_monotoneOn (show a ∈ Ici (Real.exp 1) from he.trans ha)
        (show t ∈ Ici (Real.exp 1) from he.trans (ha.trans ht.1)) ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  · have h := integral_mono_on hab
      (intervalIntegrable_of_Ioi continuousOn_Wf (by linarith) (by linarith))
      intervalIntegrable_const
      (fun t ht => Wf_monotoneOn (show t ∈ Ici (Real.exp 1) from he.trans (hb.trans ht.1))
        (show a ∈ Ici (Real.exp 1) from he.trans ha) ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    rw [intervalIntegral.integral_symm]
    linarith

/-! ### The primorial argument -/

lemma eventually_theta_ge (M : ℝ) : ∀ᶠ x : ℝ in atTop, M ≤ Chebyshev.theta x := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes ⌈Real.exp M⌉₊
  rw [eventually_atTop]
  refine ⟨p, fun x hx => ?_⟩
  have h1 : Chebyshev.theta p ≤ Chebyshev.theta x := Chebyshev.theta_mono hx
  have h2 : Real.log p ≤ Chebyshev.theta p := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    refine Finset.single_le_sum (f := fun q : ℕ => Real.log q) (fun q hq => ?_) ?_
    · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hp.pos, le_rfl⟩, hp⟩
  have h3 : M ≤ Real.log p := by
    have : Real.exp M ≤ p := Nat.ceil_le.mp hp1
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hp.pos)]; exact this
  linarith

theorem Jtheta_lt_of_landau
    (H : ∀ᶠ n : ℕ in atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n)) :
    ∀ᶠ x : ℝ in atTop, Jtheta x < c2 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp H
  filter_upwards [eventually_theta_ge (max 3 N₀), eventually_ge_atTop 3] with x hθ hx3
  set S := (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime with hS
  set n := ∑ p ∈ S, p with hn
  have hθS : Chebyshev.theta x = ∑ p ∈ S, Real.log p := by
    rw [Chebyshev.theta]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [hS, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h1⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have hθn : Chebyshev.theta x ≤ (n:ℝ) := by
    rw [hθS, hn, Nat.cast_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp0 : (0:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    have := Real.log_le_sub_one_of_pos hp0
    linarith
  have h3θ : 3 ≤ Chebyshev.theta x := (le_max_left _ _).trans hθ
  have hnN : N₀ ≤ n := by
    have : (N₀:ℝ) ≤ n := (le_max_right _ _).trans (hθ.trans hθn)
    exact_mod_cast this
  have hg := hN₀ n hnN
  have hprod := prod_primes_le_landau S (fun p hp => (Finset.mem_filter.mp hp).2)
  have hlog : Chebyshev.theta x ≤ Real.log (landau n) := by
    rw [hθS, ← Real.log_prod (fun p hp => by
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero)]
    have hpos : (0:ℝ) < ∏ p ∈ S, (p:ℝ) := Finset.prod_pos (fun p hp => by
      exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
    refine Real.log_le_log hpos ?_
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  have hlt : Chebyshev.theta x < Real.sqrt (logIntegralInv n) := lt_of_le_of_lt hlog hg
  have hsq : Chebyshev.theta x ^ 2 < logIntegralInv n :=
    (Real.lt_sqrt (by linarith)).mp hlt
  have hLi : logIntegral (Chebyshev.theta x ^ 2) < n :=
    logIntegral_lt_of_lt_logIntegralInv (Nat.cast_nonneg n) (by nlinarith) hsq
  have hid := sum_primes_identity (by linarith : (2:ℝ) ≤ x)
  rw [← hS, ← Nat.cast_sum, ← hn] at hid
  have hconv := Li_sq_sub_ge hx3 h3θ
  linarith

lemma Jpsi_le {x : ℝ} (hx : 2 ≤ x) : Jpsi x ≤ Jtheta x + 2 * x * Real.sqrt x := by
  have h1x : (1:ℝ) < x := by linarith
  have hIψ := intervalIntegrable_wf_mul_sub Chebyshev.psi_mono (by norm_num : (1:ℝ) < 2) h1x
  have hIθ := intervalIntegrable_wf_mul_sub Chebyshev.theta_mono (by norm_num : (1:ℝ) < 2) h1x
  have hdiff : Jpsi x - Jtheta x =
      ∫ t in (2:ℝ)..x, (wf t * (Chebyshev.psi t - t) - wf t * (Chebyshev.theta t - t)) := by
    rw [Jpsi, Jtheta, ← integral_sub hIψ hIθ]
  have hbound : ∫ t in (2:ℝ)..x, (wf t * (Chebyshev.psi t - t) - wf t * (Chebyshev.theta t - t)) ≤
      ∫ t in (2:ℝ)..x, 2 * Real.sqrt x := by
    refine integral_mono_on hx (hIψ.sub hIθ) intervalIntegrable_const (fun t ht => ?_)
    have ht2 := ht.1
    have hl := log_gt_069 ht2
    have hl0 : 0 < Real.log t := by linarith
    have h1 := Chebyshev.theta_le_psi t
    have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1:ℝ) ≤ t)
    have hw : wf t ≤ 1 / Real.log t := by
      rw [wf, div_le_div_iff₀ (by positivity) hl0]; nlinarith
    have e : wf t * (Chebyshev.psi t - t) - wf t * (Chebyshev.theta t - t) =
        wf t * (Chebyshev.psi t - Chebyshev.theta t) := by ring
    rw [e]
    have hd0 : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by linarith
    have a1 : wf t * (Chebyshev.psi t - Chebyshev.theta t) ≤
        1 / Real.log t * (Chebyshev.psi t - Chebyshev.theta t) :=
      mul_le_mul_of_nonneg_right hw hd0
    have a2 : 1 / Real.log t * (Chebyshev.psi t - Chebyshev.theta t) ≤
        1 / Real.log t * (2 * Real.sqrt t * Real.log t) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have a3 : 1 / Real.log t * (2 * Real.sqrt t * Real.log t) = 2 * Real.sqrt t := by
      field_simp
    have a4 : Real.sqrt t ≤ Real.sqrt x := Real.sqrt_le_sqrt ht.2
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith

/-- `A(x) = 2 x √x + c₂ - J_ψ(x)`. -/
def Afun (x : ℝ) : ℝ := 2 * x * Real.sqrt x + c2 - Jpsi x

theorem Afun_nonneg_of_landau
    (H : ∀ᶠ n : ℕ in atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n)) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ Afun x := by
  filter_upwards [Jtheta_lt_of_landau H, eventually_ge_atTop 2] with x h1 h2
  have := Jpsi_le h2
  rw [Afun]
  linarith

end LandauRH

end

-- ===== LF8b.lean =====
section

set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction LandauMellin PsiOscillation ZetaAux

/-! ### The derivative `a = A'` -/

/-- `a(t) = 3√t - w(t)(ψ(t) - t)`. -/
def aFun (t : ℝ) : ℝ := 3 * Real.sqrt t - wf t * (Chebyshev.psi t - t)

lemma psi_eventually_eq {x : ℝ} (hx0 : 0 < x) (hx : ∀ n : ℕ, x ≠ n) :
    ∀ᶠ y in 𝓝 x, Chebyshev.psi y = Chebyshev.psi x := by
  set m := ⌊x⌋₊ with hm
  have h1 : (m:ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx0.le) (fun h => hx m h.symm)
  have h2 : x < m + 1 := Nat.lt_floor_add_one x
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  rw [Chebyshev.psi_eq_psi_coe_floor y, Chebyshev.psi_eq_psi_coe_floor x]
  congr 2
  rw [← hm]
  apply Nat.floor_eq_iff (by linarith [hy.1, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]) |>.mpr
  exact ⟨hy.1.le, hy.2⟩

lemma continuousAt_psi_of_ne {x : ℝ} (hx0 : 0 < x) (hx : ∀ n : ℕ, x ≠ n) :
    ContinuousAt Chebyshev.psi x :=
  continuousAt_const.congr ((psi_eventually_eq hx0 hx).mono fun _ hy => hy.symm)

lemma measurable_wf_psi : Measurable (fun t => wf t * (Chebyshev.psi t - t)) := by
  have hw : Measurable wf := by
    unfold wf; fun_prop
  exact hw.mul (Chebyshev.psi_mono.measurable.sub measurable_id)

lemma hasDerivAt_Jpsi {x : ℝ} (hx : 2 < x) (hxn : ∀ n : ℕ, x ≠ n) :
    HasDerivAt Jpsi (wf x * (Chebyshev.psi x - x)) x := by
  have h1x : (1:ℝ) < x := by linarith
  have hcont : ContinuousAt (fun t => wf t * (Chebyshev.psi t - t)) x :=
    (continuousOn_wf.continuousAt (Ioi_mem_nhds h1x)).mul
      ((continuousAt_psi_of_ne (by linarith) hxn).sub continuousAt_id)
  exact integral_hasDerivAt_right
    (intervalIntegrable_wf_mul_sub Chebyshev.psi_mono (by norm_num) h1x)
    measurable_wf_psi.aestronglyMeasurable.stronglyMeasurableAtFilter hcont

lemma hasDerivAt_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => 2 * t * Real.sqrt t) (3 * Real.sqrt x) x := by
  have h := ((hasDerivAt_id' x).const_mul 2).mul (Real.hasDerivAt_sqrt hx.ne')
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have e : 2 * 1 * Real.sqrt x + 2 * x * (1 / (2 * Real.sqrt x)) = 3 * Real.sqrt x := by
    field_simp
    rw [Real.sq_sqrt hx.le]
    ring
  rw [e] at h
  exact h

lemma hasDerivAt_Afun {x : ℝ} (hx : 2 < x) (hxn : ∀ n : ℕ, x ≠ n) :
    HasDerivAt Afun (aFun x) x := by
  have h := ((hasDerivAt_two_mul_sqrt (by linarith : (0:ℝ) < x)).add_const c2).sub
    (hasDerivAt_Jpsi hx hxn)
  exact h

lemma continuousOn_Jpsi {R : ℝ} (hR : 2 ≤ R) : ContinuousOn Jpsi (Icc 2 R) := by
  have h := continuousOn_primitive_interval' (μ := volume) (a := 2)
    (intervalIntegrable_wf_mul_sub Chebyshev.psi_mono (by norm_num : (1:ℝ) < 2)
      (by linarith : (1:ℝ) < R)) (by rw [uIcc_of_le hR]; exact ⟨le_rfl, hR⟩)
  rw [uIcc_of_le hR] at h
  exact h

lemma continuousOn_Afun {R : ℝ} (hR : 2 ≤ R) : ContinuousOn Afun (Icc 2 R) := by
  have h1 : Continuous (fun t : ℝ => 2 * t * Real.sqrt t + c2) := by fun_prop
  exact h1.continuousOn.sub (continuousOn_Jpsi hR)

/-! ### Elementary bounds -/

lemma abs_psi_sub_le {t : ℝ} (ht : 0 ≤ t) : |Chebyshev.psi t - t| ≤ cψ * t := by
  have h1 := Chebyshev.psi_le_const_mul_self ht
  have h2 := Chebyshev.psi_nonneg t
  have hc : (1:ℝ) ≤ cψ := by
    unfold cψ; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  rw [abs_le]; constructor
  · nlinarith
  · unfold cψ at hc ⊢; linarith

lemma abs_wf_le {t : ℝ} (ht : 2 ≤ t) : |wf t| ≤ 1 := by
  have hl := log_gt_069 ht
  rw [wf, abs_div, abs_of_pos (by positivity : 0 < Real.log t ^ 2), div_le_one (by positivity),
    abs_le]
  constructor <;> nlinarith

lemma abs_aFun_le {t : ℝ} (ht : 2 ≤ t) : |aFun t| ≤ (3 + cψ) * t := by
  have h1 := abs_psi_sub_le (by linarith : (0:ℝ) ≤ t)
  have h2 := abs_wf_le ht
  have hs : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h3 : |wf t * (Chebyshev.psi t - t)| ≤ cψ * t := by
    rw [abs_mul]
    calc |wf t| * |Chebyshev.psi t - t| ≤ 1 * (cψ * t) :=
          mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
      _ = cψ * t := one_mul _
  rw [aFun]
  calc |3 * Real.sqrt t - wf t * (Chebyshev.psi t - t)|
      ≤ |3 * Real.sqrt t| + |wf t * (Chebyshev.psi t - t)| := abs_sub _ _
    _ ≤ 3 * t + cψ * t := by rw [abs_of_nonneg (by positivity)]; linarith
    _ = (3 + cψ) * t := by ring

lemma abs_Jpsi_le {x : ℝ} (hx : 2 ≤ x) : |Jpsi x| ≤ cψ * x ^ 2 := by
  have h1x : (1:ℝ) < x := by linarith
  rw [Jpsi]
  have h := norm_integral_le_of_norm_le_const (a := 2) (b := x) (C := cψ * x)
    (f := fun t => wf t * (Chebyshev.psi t - t)) (fun t ht => by
      rw [uIoc_of_le hx] at ht
      have ht2 : 2 ≤ t := ht.1.le
      rw [Real.norm_eq_abs, abs_mul]
      calc |wf t| * |Chebyshev.psi t - t| ≤ 1 * (cψ * t) :=
            mul_le_mul (abs_wf_le ht2) (abs_psi_sub_le (by linarith)) (abs_nonneg _)
              (by norm_num)
        _ ≤ cψ * x := by have := cψ_pos; nlinarith [ht.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 2)] at h
  have := cψ_pos
  nlinarith

lemma abs_Afun_le {x : ℝ} (hx : 2 ≤ x) : |Afun x| ≤ (2 + |c2| + cψ) * x ^ 2 := by
  have h1 := abs_Jpsi_le hx
  have hs : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hx1 : 1 ≤ x ^ 2 := by nlinarith
  rw [Afun]
  calc |2 * x * Real.sqrt x + c2 - Jpsi x| ≤ |2 * x * Real.sqrt x| + |c2| + |Jpsi x| := by
        have := abs_sub (2 * x * Real.sqrt x + c2) (Jpsi x)
        have := abs_add_le (2 * x * Real.sqrt x) c2
        linarith
    _ ≤ 2 * x ^ 2 + |c2| * x ^ 2 + cψ * x ^ 2 := by
        rw [abs_of_nonneg (by positivity)]
        have : |c2| ≤ |c2| * x ^ 2 := le_mul_of_one_le_right (abs_nonneg _) hx1
        nlinarith
    _ = (2 + |c2| + cψ) * x ^ 2 := by ring

/-! ### Cut-off functions and absolute convergence -/

/-- Cut-off at `X₀`: `f(x)` for `x > X₀`, `0` otherwise. -/
def cut (X₀ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := if X₀ < x then f x else 0

lemma measurable_cut {X₀ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) : Measurable (cut X₀ f) :=
  Measurable.ite measurableSet_Ioi hf measurable_const

lemma convAbs_of_le {f : ℝ → ℝ} (hf : Measurable f) {C p σ : ℝ} (hσ : p < σ)
    (hb : ∀ x : ℝ, 1 < x → |f x| ≤ C * x ^ p) : ConvAbs f σ := by
  have hI : IntegrableOn (fun x : ℝ => C * x ^ (p - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine hI.mono' ((hf.abs.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  have hx0 : (0:ℝ) < x := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc |f x| * x ^ (-σ - 1) ≤ C * x ^ p * x ^ (-σ - 1) :=
        mul_le_mul_of_nonneg_right (hb x hx') (Real.rpow_nonneg hx0.le _)
    _ = C * x ^ (p - σ - 1) := by
        rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf

lemma cut_bound {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {f : ℝ → ℝ} {C p : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : ℝ, 2 ≤ x → |f x| ≤ C * x ^ p) : ∀ x : ℝ, 1 < x → |cut X₀ f x| ≤ C * x ^ p := by
  intro x hx
  unfold cut
  split_ifs with h
  · exact hb x (by linarith)
  · rw [abs_zero]; exact mul_nonneg hC (Real.rpow_nonneg (by linarith) _)

lemma continuousOn_Afun_Ioi : ContinuousOn Afun (Ioi 2) := fun x hx => by
  have hx' : (2:ℝ) < x := hx
  exact ((continuousOn_Afun (R := x + 1) (by linarith)).continuousAt
    (Icc_mem_nhds hx' (by linarith))).continuousWithinAt

lemma measurable_cut_of_continuousOn {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 2)) : Measurable (cut X₀ f) := by
  have : cut X₀ f = (Ioi X₀).piecewise f 0 := by
    funext x; simp only [cut, Set.piecewise, mem_Ioi, Pi.zero_apply]
  rw [this]
  exact ContinuousOn.measurable_piecewise (hf.mono (Ioi_subset_Ioi hX₀)) continuousOn_const
    measurableSet_Ioi

lemma measurable_aFun : Measurable aFun := by
  unfold aFun
  exact (measurable_const.mul Real.continuous_sqrt.measurable).sub measurable_wf_psi

/-! ### Mellin transforms of cut-off functions -/

lemma setIntegral_Ioi_one_cut {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (g : ℝ → ℂ) :
    ∫ x in Ioi (1:ℝ), (if X₀ < x then g x else 0) = ∫ x in Ioi X₀, g x := by
  have : (fun x => if X₀ < x then g x else 0) = (Ioi X₀).indicator g := by
    funext x; simp only [Set.indicator_apply, mem_Ioi]
  rw [this, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_of_le_right hX₀]

lemma mellinK_cut {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (f : ℝ → ℝ) (k : ℕ) (s : ℂ) :
    mellinK (cut X₀ f) k s =
      ∫ x in Ioi X₀, (f x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1) := by
  rw [mellinK, ← setIntegral_Ioi_one_cut hX₀]
  congr 1; funext x
  unfold cut; split_ifs <;> simp

lemma norm_cpow_of_pos {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx z

/-- Integrability on `(X₀, ∞)` of `g(x) x^{-z}` when `|g(x)| ≤ C x^p` and `p - Re z < -1`. -/
lemma integrableOn_mul_cpow {X₀ : ℝ} (hX₀ : 0 < X₀) {g : ℝ → ℝ} (hg : AEStronglyMeasurable g
    (volume.restrict (Ioi X₀))) {C p : ℝ} {z : ℂ} (hp : p - z.re < -1)
    (hb : ∀ x : ℝ, X₀ < x → |g x| ≤ C * x ^ p) :
    IntegrableOn (fun x : ℝ => (g x : ℂ) * (x : ℂ) ^ (-z)) (Ioi X₀) := by
  have hI : IntegrableOn (fun x : ℝ => C * x ^ (p - z.re)) (Ioi X₀) :=
    (integrableOn_Ioi_rpow_of_lt hp hX₀).const_mul _
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (g x : ℂ) * (x : ℂ) ^ (-z))
      (volume.restrict (Ioi X₀)) := by
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hg).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := lt_trans hX₀ hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).continuousWithinAt
  refine hI.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : X₀ < x := hx
  have hx0 : (0:ℝ) < x := lt_trans hX₀ hx'
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_of_pos hx0]
  calc |g x| * x ^ (-z).re ≤ C * x ^ p * x ^ (-z).re :=
        mul_le_mul_of_nonneg_right (hb x hx') (Real.rpow_nonneg hx0.le _)
    _ = C * x ^ (p - z.re) := by
        rw [mul_assoc, ← Real.rpow_add hx0, neg_re, ← sub_eq_add_neg]

/-- **Integration by parts**: `s ∫_{X₀}^∞ A x^{-s-1} = A(X₀) X₀^{-s} + ∫_{X₀}^∞ a x^{-s}`. -/
theorem mellin_ibp {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {s : ℂ} (hs : 2 < s.re) :
    s * mellinK (cut X₀ Afun) 0 s =
      (Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) + mellinK (cut X₀ (fun x => x * aFun x)) 0 s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hX₀0 : (0:ℝ) < X₀ := by linarith
  rw [mellinK_cut (by linarith), mellinK_cut (by linarith)]
  simp only [pow_zero, mul_one]
  set fA : ℝ → ℂ := fun x => (Afun x : ℂ) * (x : ℂ) ^ (-s - 1) with hfA
  set fa : ℝ → ℂ := fun x => (aFun x : ℂ) * (x : ℂ) ^ (-s) with hfa
  have hfa' : ∀ x ∈ Ioi X₀, ((x * aFun x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = fa x := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans hX₀0 hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    simp only [hfa]
    rw [show -s = 1 + (-s - 1) by ring, cpow_add _ _ hxc, cpow_one]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hfa']
  have hIA : IntegrableOn fA (Ioi X₀) := by
    have := integrableOn_mul_cpow hX₀0 (g := Afun) (C := 2 + |c2| + cψ) (p := 2) (z := s + 1)
      ((continuousOn_Afun_Ioi.mono (Ioi_subset_Ioi hX₀)).aestronglyMeasurable measurableSet_Ioi)
      (by simp; linarith) (fun x hx => by
        have := abs_Afun_le (by linarith : (2:ℝ) ≤ x)
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; exact this)
    simpa only [hfA, neg_add'] using this
  have hIa : IntegrableOn fa (Ioi X₀) := by
    have := integrableOn_mul_cpow hX₀0 (g := aFun) (C := 3 + cψ) (p := 1) (z := s)
      measurable_aFun.aestronglyMeasurable (by linarith) (fun x hx => by
        rw [Real.rpow_one]; exact abs_aFun_le (by linarith))
    simpa only [hfa] using this
  -- FTC on `[X₀, R]`
  have hFTC : ∀ R : ℝ, X₀ ≤ R → ∫ x in X₀..R, (fA x - fa x / s) =
      -(Afun R : ℂ) * (R : ℂ) ^ (-s) / s - (-(Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s) := by
    intro R hR
    refine integral_eq_of_hasDerivAt_off_countable_of_le
      (fun x => -(Afun x : ℂ) * (x : ℂ) ^ (-s) / s) (fun x => fA x - fa x / s) hR
      (Set.countable_range (Nat.cast : ℕ → ℝ)) ?_ ?_ ?_
    · have h1 : ContinuousOn (fun x => (Afun x : ℂ)) (Icc X₀ R) :=
        Complex.continuous_ofReal.comp_continuousOn
          ((continuousOn_Afun (by linarith : (2:ℝ) ≤ R)).mono (Icc_subset_Icc_left hX₀))
      have h2 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Icc X₀ R) := fun x hx =>
        (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (by linarith [hx.1] : x ≠ 0))).continuousWithinAt
      exact ((h1.neg).mul h2).div_const s
    · rintro x ⟨hx, hxn⟩
      have hxn' : ∀ n : ℕ, x ≠ n := fun n h => hxn ⟨n, h.symm⟩
      have hx0 : (0:ℝ) < x := by linarith [hx.1]
      have hA : HasDerivAt (fun y : ℝ => (Afun y : ℂ)) (aFun x : ℂ) x :=
        (hasDerivAt_Afun (by linarith [hx.1]) hxn').ofReal_comp
      have hA' : HasDerivAt (fun y : ℝ => -(Afun y : ℂ)) (-(aFun x : ℂ)) x := hA.neg
      have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
        hasDerivAt_ofReal_cpow_const hx0.ne' (neg_ne_zero.mpr hs0)
      have h : HasDerivAt (fun y : ℝ => -(Afun y : ℂ) * (y : ℂ) ^ (-s) / s)
          ((-(aFun x : ℂ) * (x : ℂ) ^ (-s) + -(Afun x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) / s) x :=
        (hA'.mul hp).div_const s
      have e : fA x - fa x / s =
          (-(aFun x : ℂ) * (x : ℂ) ^ (-s) + -(Afun x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) / s := by
        simp only [hfA, hfa]; field_simp; ring
      rw [e]; exact h
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
      exact (hIA.mono_set Ioc_subset_Ioi_self).sub
        ((hIa.mono_set Ioc_subset_Ioi_self).div_const s)
  have hlim1 : Tendsto (fun R => ∫ x in X₀..R, (fA x - fa x / s)) atTop
      (𝓝 (∫ x in Ioi X₀, (fA x - fa x / s))) :=
    intervalIntegral_tendsto_integral_Ioi X₀ (hIA.sub (hIa.div_const s)) tendsto_id
  have hint : ∫ x in Ioi X₀, (fA x - fa x / s) =
      (∫ x in Ioi X₀, fA x) - (∫ x in Ioi X₀, fa x) / s := by
    rw [integral_sub hIA (hIa.div_const s), MeasureTheory.integral_div]
  have hA0 : Tendsto (fun R : ℝ => (Afun R : ℂ) * (R : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hσ : 0 < s.re - 2 := by linarith
    have hT := (tendsto_rpow_neg_atTop hσ).const_mul (2 + |c2| + cψ)
    rw [mul_zero] at hT
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [eventually_ge_atTop 2] with R hR
    have hR0 : (0:ℝ) < R := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_of_pos hR0]
    calc |Afun R| * R ^ (-s).re ≤ ((2 + |c2| + cψ) * R ^ 2) * R ^ (-s).re :=
          mul_le_mul_of_nonneg_right (abs_Afun_le hR) (Real.rpow_nonneg hR0.le _)
      _ = (2 + |c2| + cψ) * R ^ (-(s.re - 2)) := by
          rw [mul_assoc, show R ^ 2 = R ^ (2:ℝ) by norm_cast, ← Real.rpow_add hR0]
          congr 2; simp only [neg_re]; ring
  have hlim2 : Tendsto (fun R : ℝ => -(Afun R : ℂ) * (R : ℂ) ^ (-s) / s -
      (-(Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s)) atTop
      (𝓝 (0 - (-(Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s))) := by
    have := (hA0.neg.div_const s).sub_const (-(Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s)
    rw [neg_zero, zero_div] at this
    refine this.congr (fun R => ?_)
    ring
  have hlim1' : Tendsto (fun R : ℝ => -(Afun R : ℂ) * (R : ℂ) ^ (-s) / s -
      (-(Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s)) atTop
      (𝓝 (∫ x in Ioi X₀, (fA x - fa x / s))) :=
    hlim1.congr' (by filter_upwards [eventually_ge_atTop X₀] with R hR; exact hFTC R hR)
  have heq := tendsto_nhds_unique hlim1' hlim2
  rw [hint] at heq
  have h2 : (∫ x in Ioi X₀, fA x) - (∫ x in Ioi X₀, fa x) / s =
      (Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) / s := by rw [heq]; ring
  field_simp at h2
  linear_combination h2

/-! ### The functions entering `∫ a(t) log² t t^{-s} dt` -/

/-- `e₂(t) = t √t`. -/
def e2F (t : ℝ) : ℝ := t * Real.sqrt t

/-- `φ(t) = t (ψ(t) - t)`. -/
def phiF (t : ℝ) : ℝ := t * (Chebyshev.psi t - t)

/-- `t a(t)`. -/
def aF (t : ℝ) : ℝ := t * aFun t

lemma measurable_e2F : Measurable e2F := by unfold e2F; fun_prop

lemma measurable_phiF : Measurable phiF := by
  unfold phiF; exact measurable_id.mul (Chebyshev.psi_mono.measurable.sub measurable_id)

lemma measurable_aF : Measurable aF := by unfold aF; exact measurable_id.mul measurable_aFun

lemma convAbs_cut_aF {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {σ : ℝ} (hσ : 2 < σ) : ConvAbs (cut X₀ aF) σ := by
  refine convAbs_of_le (measurable_cut measurable_aF) (C := 3 + cψ) (p := 2) hσ
    (cut_bound hX₀ (by have := cψ_pos; linarith) (fun x hx => ?_))
  rw [aF, abs_mul, abs_of_nonneg (by linarith), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  have := abs_aFun_le hx
  nlinarith

lemma convAbs_cut_e2F {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {σ : ℝ} (hσ : 3 / 2 < σ) :
    ConvAbs (cut X₀ e2F) σ := by
  refine convAbs_of_le (measurable_cut measurable_e2F) (C := 1) (p := 3 / 2) hσ
    (cut_bound hX₀ zero_le_one (fun x hx => ?_))
  have hx0 : 0 < x := by linarith
  rw [e2F, abs_of_nonneg (by positivity), one_mul, rpow_three_halves_eq hx0]

lemma convAbs_cut_phiF {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {σ : ℝ} (hσ : 2 < σ) :
    ConvAbs (cut X₀ phiF) σ := by
  refine convAbs_of_le (measurable_cut measurable_phiF) (C := cψ) (p := 2) hσ
    (cut_bound hX₀ cψ_pos.le (fun x hx => ?_))
  rw [phiF, abs_mul, abs_of_nonneg (by linarith), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  have := abs_psi_sub_le (by linarith : (0:ℝ) ≤ x)
  nlinarith

lemma convAbs_cut_Afun {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {σ : ℝ} (hσ : 2 < σ) :
    ConvAbs (cut X₀ Afun) σ := by
  refine convAbs_of_le (measurable_cut_of_continuousOn hX₀ continuousOn_Afun_Ioi)
    (C := 2 + |c2| + cψ) (p := 2) hσ
    (cut_bound hX₀ (by have := cψ_pos; positivity) (fun x hx => ?_))
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  exact abs_Afun_le hx

/-- `x a(x) log² x = 3 e₂(x) log² x - φ(x) log x + φ(x)`, integrated. -/
theorem mellin_decomp {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {s : ℂ} (hs : 2 < s.re) :
    mellinK (cut X₀ aF) 2 s = 3 * mellinK (cut X₀ e2F) 2 s + mellinK (cut X₀ phiF) 1 s +
      mellinK (cut X₀ phiF) 0 s := by
  have i1 := integrable_integrand (measurable_cut measurable_e2F) (τ := 2)
    (fun σ hσ => convAbs_cut_e2F hX₀ (by linarith)) 2 hs
  have i2 := integrable_integrand (measurable_cut measurable_phiF) (τ := 2)
    (fun σ hσ => convAbs_cut_phiF hX₀ hσ) 1 hs
  have i3 := integrable_integrand (measurable_cut measurable_phiF) (τ := 2)
    (fun σ hσ => convAbs_cut_phiF hX₀ hσ) 0 hs
  have i12 : Integrable (fun x : ℝ => 3 * ((cut X₀ e2F x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ 2 *
      (x : ℂ) ^ (-s - 1)) + (cut X₀ phiF x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ 1 * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi 1)) := (i1.const_mul 3).add i2
  rw [mellinK, mellinK, mellinK, mellinK, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add (i1.const_mul 3) i2,
    ← MeasureTheory.integral_add i12 i3]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx1 : (1:ℝ) < x := hx
  have hL : Real.log x ≠ 0 := log_ne_zero_of_one_lt hx1
  unfold cut
  split_ifs with h
  · have key : aF x * (-Real.log x) ^ 2 = 3 * (e2F x * (-Real.log x) ^ 2) +
        phiF x * (-Real.log x) ^ 1 + phiF x * (-Real.log x) ^ 0 := by
      simp only [aF, aFun, e2F, phiF, wf]
      field_simp
      ring
    have := congrArg (fun r : ℝ => (r : ℂ) * (x : ℂ) ^ (-s - 1)) key
    push_cast at this ⊢
    linear_combination this
  · simp

/-! ### The Mellin transform of `φ(t) = t(ψ(t) - t)` -/

lemma integrableOn_psi_cpow {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by
  have := integrableOn_mul_cpow zero_lt_one (g := Chebyshev.psi) (C := cψ) (p := 1) (z := w + 1)
    Chebyshev.psi_mono.measurable.aestronglyMeasurable (by simp; linarith) (fun x hx => by
      rw [Real.rpow_one, abs_of_nonneg (Chebyshev.psi_nonneg x)]
      exact Chebyshev.psi_le_const_mul_self (by linarith))
  simpa only [neg_add'] using this

theorem mellinK_phiF {s : ℂ} (hs : 2 < s.re) :
    mellinK phiF 0 s = -deriv zetaMulSubOne (s - 1) / ((s - 1) * zetaMulSubOne (s - 1)) -
      1 / (s - 1) := by
  set w := s - 1 with hw
  have hwre : 1 < w.re := by simp [hw]; linarith
  have hw1 : w ≠ 1 := by intro h; rw [h] at hwre; simp at hwre
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre; linarith
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre.le
  have hpt : ∀ x ∈ Ioi (1:ℝ), (phiF x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ 0 * (x : ℂ) ^ (-s - 1) =
      (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-w - 1) - (x : ℂ) ^ (1 - s) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    rw [pow_zero, mul_one, phiF, hw, show -(s - 1) - 1 = 1 + (-s - 1) by ring,
      show (1:ℂ) - s = 2 + (-s - 1) by ring, cpow_add _ _ hxc, cpow_add _ _ hxc, cpow_one,
      show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, cpow_natCast]
    push_cast
    ring
  have hi1 := integrableOn_psi_cpow hwre
  have hi2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (1 - s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  rw [mellinK, setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hi1 hi2,
    integral_psi_mul_cpow hwre, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  rw [deriv_zetaMulSubOne hw1, zetaMulSubOne_of_ne hw1]
  simp only [ofReal_one, one_cpow]
  have h2s : (1:ℂ) - s + 1 = -(w - 1) := by rw [hw]; ring
  rw [h2s]
  field_simp
  ring

/-- Complementary cut-off: `f(x)` for `x ≤ X₀`, `0` otherwise. -/
def cutc (X₀ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := if X₀ < x then 0 else f x

lemma measurable_cutc {X₀ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) : Measurable (cutc X₀ f) :=
  Measurable.ite (measurableSet_Ioi (a := X₀)) measurable_const hf

lemma convAbs_cutc_phiF {X₀ : ℝ} (hX₀ : 1 ≤ X₀) (σ : ℝ) : ConvAbs (cutc X₀ phiF) σ := by
  set p := min (σ - 1) 0 with hp
  have hpσ : p < σ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hp0 : p ≤ 0 := min_le_right _ _
  have hX₀0 : 0 < X₀ := by linarith
  refine convAbs_of_le (measurable_cutc measurable_phiF)
    (C := cψ * X₀ ^ 2 * X₀ ^ (-p)) hpσ (fun x hx => ?_)
  simp only [cutc]
  split_ifs with h
  · rw [abs_zero]; exact mul_nonneg (by have := cψ_pos; positivity)
      (Real.rpow_nonneg (by linarith) _)
  · push Not at h
    have hx0 : 0 < x := by linarith
    have h1 : |phiF x| ≤ cψ * X₀ ^ 2 := by
      rw [phiF, abs_mul, abs_of_nonneg hx0.le]
      have hab := abs_psi_sub_le hx0.le
      have hc := cψ_pos
      calc x * |Chebyshev.psi x - x| ≤ x * (cψ * x) := mul_le_mul_of_nonneg_left hab hx0.le
        _ = cψ * (x * x) := by ring
        _ ≤ cψ * X₀ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          nlinarith
    have h2 : X₀ ^ p ≤ x ^ p := Real.rpow_le_rpow_of_nonpos hx0 h hp0
    have h3 : 1 ≤ X₀ ^ (-p) * x ^ p := by
      have : X₀ ^ (-p) * X₀ ^ p = 1 := by
        rw [← Real.rpow_add hX₀0]; simp
      have h4 : 0 ≤ X₀ ^ (-p) := Real.rpow_nonneg hX₀0.le _
      nlinarith
    have hc : 0 ≤ cψ * X₀ ^ 2 := by have := cψ_pos; positivity
    calc |phiF x| ≤ cψ * X₀ ^ 2 * 1 := by linarith
      _ ≤ cψ * X₀ ^ 2 * (X₀ ^ (-p) * x ^ p) := mul_le_mul_of_nonneg_left h3 hc
      _ = cψ * X₀ ^ 2 * X₀ ^ (-p) * x ^ p := by ring

/-- `Φ̃(s) = -h'(s-1)/((s-1)h(s-1)) - 1/(s-1) - E(s)`, the continuation of `∫_{X₀}^∞ (ψ-t) t^{-s}`. -/
def Phit (X₀ : ℝ) (s : ℂ) : ℂ :=
  -deriv zetaMulSubOne (s - 1) / ((s - 1) * zetaMulSubOne (s - 1)) - 1 / (s - 1) -
    mellinK (cutc X₀ phiF) 0 s

theorem mellinK_cut_phiF_eq {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {s : ℂ} (hs : 2 < s.re) :
    mellinK (cut X₀ phiF) 0 s = Phit X₀ s := by
  have i1 := integrable_integrand (measurable_cut measurable_phiF) (τ := 2)
    (fun σ hσ => convAbs_cut_phiF hX₀ hσ) 0 hs
  have i2 := integrable_integrand (measurable_cutc (X₀ := X₀) measurable_phiF) (τ := 0) (fun σ _ => convAbs_cutc_phiF (by linarith) σ) 0
    (by linarith : (0:ℝ) < s.re)
  have hsum : mellinK phiF 0 s = mellinK (cut X₀ phiF) 0 s + mellinK (cutc X₀ phiF) 0 s := by
    rw [mellinK, mellinK, mellinK, ← MeasureTheory.integral_add i1 i2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    unfold cut cutc
    split_ifs <;> simp
  rw [Phit, ← mellinK_phiF hs, hsum]
  ring

end LandauRH

end

-- ===== LF8c.lean =====
section

set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory Metric
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction LandauMellin PsiOscillation ZetaAux

/-! ### A zero-free half-strip around `(1/2, ∞)` -/

lemma exists_zeroFree_strip : ∃ η : ℝ, 0 < η ∧
    ∀ w : ℂ, 1 / 2 < w.re → |w.im| < η → zetaMulSubOne w ≠ 0 := by
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (1/2) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hU : IsOpen {w : ℂ | zetaMulSubOne w ≠ 0} :=
    isOpen_compl_singleton.preimage differentiable_zetaMulSubOne.continuous
  have hKU : K ⊆ {w : ℂ | zetaMulSubOne w ≠ 0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact zetaMulSubOne_ne_zero_of_pos (by linarith [hx.1])
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, fun w hw hwi => ?_⟩
  rcases le_or_gt 1 w.re with h1 | h1
  · exact zetaMulSubOne_ne_zero_of_one_le_re h1
  · have hmem : w ∈ thickening δ K := by
      rw [mem_thickening_iff]
      refine ⟨(w.re : ℂ), ⟨w.re, ⟨hw.le, h1.le⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_ofReal_re]
      exact hwi
    exact hsub hmem

/-! ### Primitives on a half-strip -/

/-- The half-strip `{a < Re z, |Im z| < η}`. -/
def hstrip (a η : ℝ) : Set ℂ := {z : ℂ | a < z.re ∧ |z.im| < η}

lemma isOpen_hstrip (a η : ℝ) : IsOpen (hstrip a η) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

lemma convex_hstrip (a η : ℝ) : Convex ℝ (hstrip a η) := by
  have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt a
  have h2 : Convex ℝ {z : ℂ | |z.im| < η} := by
    have : {z : ℂ | |z.im| < η} = {z : ℂ | z.im < η} ∩ {z : ℂ | -η < z.im} := by
      ext z; simp only [mem_setOf_eq, mem_inter_iff, abs_lt]; tauto
    rw [this]
    exact (convex_halfSpace_im_lt η).inter (convex_halfSpace_im_gt (-η))
  exact h1.inter h2

lemma abs_le_of_mem_uIcc {y u v : ℝ} (hy : y ∈ uIcc u v) : |y| ≤ max |u| |v| := by
  rcases Set.mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le_max_abs_abs h1 h2
  · rw [max_comm]; exact abs_le_max_abs_abs h1 h2

lemma lt_of_mem_uIcc {a y u v : ℝ} (hy : y ∈ uIcc u v) (hu : a < u) (hv : a < v) : a < y :=
  lt_of_lt_of_le (lt_inf_iff.mpr ⟨hu, hv⟩) hy.1

lemma ii_horiz {f : ℂ → ℂ} {a η : ℝ} (hf : ContinuousOn f (hstrip a η)) {b : ℝ} (hb : |b| < η)
    {u v : ℝ} (hu : a < u) (hv : a < v) :
    IntervalIntegrable (fun x : ℝ => f (x + b * I)) volume u v := by
  refine ContinuousOn.intervalIntegrable ?_
  refine hf.comp (Continuous.continuousOn (by fun_prop)) (fun x hx => ?_)
  refine ⟨by simpa using lt_of_mem_uIcc hx hu hv, by simpa using hb⟩

lemma ii_vert {f : ℂ → ℂ} {a η : ℝ} (hf : ContinuousOn f (hstrip a η)) {r : ℝ} (hr : a < r)
    {u v : ℝ} (hu : |u| < η) (hv : |v| < η) :
    IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume u v := by
  refine ContinuousOn.intervalIntegrable ?_
  refine hf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ?_)
  have hyab := abs_le_of_mem_uIcc hy
  refine ⟨by simpa using hr, by simpa using lt_of_le_of_lt hyab (max_lt hu hv)⟩

lemma wedge_add {f : ℂ → ℂ} {a η c : ℝ} (hc : a < c) (hf : DifferentiableOn ℂ f (hstrip a η))
    {z w : ℂ} (hz : z ∈ hstrip a η) (hw : w ∈ hstrip a η) :
    wedgeIntegral (c : ℂ) w f = wedgeIntegral (c : ℂ) z f + wedgeIntegral z w f := by
  have hcont := hf.continuousOn
  have hcons : IsConservativeOn f (hstrip a η) := hf.isConservativeOn
  have h0 : |(0:ℝ)| < η := by rw [abs_zero]; exact lt_of_le_of_lt (abs_nonneg _) hz.2
  -- the rectangle with corners `z.re` and `w.re + z.im I`
  have hrect : Rectangle (z.re : ℂ) ((w.re : ℂ) + (z.im : ℂ) * I) ⊆ hstrip a η := by
    intro u hu
    rw [Rectangle, mem_reProdIm] at hu
    simp only [ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_im, zero_add, add_zero, mul_im] at hu
    obtain ⟨hu1, hu2⟩ := hu
    exact ⟨lt_of_mem_uIcc hu1 hz.1 hw.1, lt_of_le_of_lt (abs_le_of_mem_uIcc hu2) (max_lt h0 hz.2)⟩
  have key := hcons _ _ hrect
  simp only [wedgeIntegral, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_zero, add_im, zero_add, add_zero, zero_mul, sub_self, ofReal_zero, mul_im] at key ⊢
  -- additivity of the one-dimensional integrals
  have e1 : (∫ x : ℝ in c..w.re, f (x + 0 * I)) =
      (∫ x : ℝ in c..z.re, f (x + 0 * I)) + ∫ x : ℝ in z.re..w.re, f (x + 0 * I) :=
    (intervalIntegral.integral_add_adjacent_intervals (ii_horiz hcont h0 hc hz.1)
      (ii_horiz hcont h0 hz.1 hw.1)).symm
  have e2 : (∫ y : ℝ in (0:ℝ)..w.im, f (w.re + y * I)) =
      (∫ y : ℝ in (0:ℝ)..z.im, f (w.re + y * I)) + ∫ y : ℝ in z.im..w.im, f (w.re + y * I) :=
    (intervalIntegral.integral_add_adjacent_intervals (ii_vert hcont hw.1 h0 hz.2)
      (ii_vert hcont hw.1 hz.2 hw.2)).symm
  rw [intervalIntegral.integral_symm z.re w.re, intervalIntegral.integral_symm 0 z.im] at key
  simp only [zero_mul, add_zero, smul_eq_mul] at key e1 e2 ⊢
  rw [e1, e2]
  linear_combination key

/-- **Primitive on a half-strip** via wedge integrals from a real base point. -/
theorem hasDerivAt_wedge_hstrip {f : ℂ → ℂ} {a η c : ℝ} (hc : a < c)
    (hf : DifferentiableOn ℂ f (hstrip a η)) {z : ℂ} (hz : z ∈ hstrip a η) :
    HasDerivAt (fun w => wedgeIntegral (c : ℂ) w f) (f z) z := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_hstrip a η) z hz
  have hloc : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
    (hf.mono hball).isConservativeOn.hasDerivAt_wedgeIntegral (hf.continuousOn.mono hball)
      (mem_ball_self hρ)
  have hev : (fun w => wedgeIntegral (c : ℂ) z f + wedgeIntegral z w f) =ᶠ[𝓝 z]
      (fun w => wedgeIntegral (c : ℂ) w f) := by
    filter_upwards [(isOpen_hstrip a η).mem_nhds hz] with w hw
    exact (wedge_add hc hf hz hw).symm
  exact (hloc.const_add _).congr_of_eventuallyEq hev.symm

/-! ### Holomorphy of the comparison function `H` -/

/-- `H(s) = 3 E₂''(s) + Φ̃'(s) + Φ̃(s)`. -/
def Hfun (X₀ : ℝ) (s : ℂ) : ℂ :=
  3 * mellinK (cut X₀ e2F) 2 s + deriv (Phit X₀) s + Phit X₀ s

/-- Region where `Φ̃` is holomorphic. -/
def OmegaP : Set ℂ := {s | s ≠ 1 ∧ zetaMulSubOne (s - 1) ≠ 0}

lemma isOpen_OmegaP : IsOpen OmegaP :=
  isOpen_compl_singleton.inter (isOpen_compl_singleton.preimage
    (differentiable_zetaMulSubOne.continuous.comp (continuous_id.sub continuous_const)))

lemma differentiable_deriv_zetaMulSubOne : Differentiable ℂ (deriv zetaMulSubOne) := by
  have := (differentiable_zetaMulSubOne.differentiableOn (s := univ)).deriv isOpen_univ
  exact fun z => (this z (mem_univ z)).differentiableAt univ_mem

lemma differentiable_mellinK_cutc_phiF {X₀ : ℝ} (hX₀ : 1 ≤ X₀) :
    Differentiable ℂ (mellinK (cutc X₀ phiF) 0) := by
  intro s
  have := differentiableOn_mellinK (measurable_cutc (X₀ := X₀) measurable_phiF) (τ := s.re - 1)
    (fun σ _ => convAbs_cutc_phiF hX₀ σ) 0
  exact this.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simp))

lemma differentiableOn_Phit {X₀ : ℝ} (hX₀ : 1 ≤ X₀) : DifferentiableOn ℂ (Phit X₀) OmegaP := by
  rintro s ⟨hs1, hsh⟩
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
  have h1 : DifferentiableAt ℂ (fun z => deriv zetaMulSubOne (z - 1)) s := by
    have := (differentiable_deriv_zetaMulSubOne (s - 1)).comp s hsub
    exact this
  have h1' : DifferentiableAt ℂ (fun z => zetaMulSubOne (z - 1)) s := by
    have := (differentiable_zetaMulSubOne (s - 1)).comp s hsub
    exact this
  have h2 : DifferentiableAt ℂ (fun z => (z - 1) * zetaMulSubOne (z - 1)) s := hsub.mul h1'
  apply DifferentiableAt.differentiableWithinAt
  unfold Phit
  exact ((h1.neg.div h2 (mul_ne_zero hs1' hsh)).sub
    ((differentiableAt_const _).div hsub hs1')).sub (differentiable_mellinK_cutc_phiF hX₀ s)

lemma differentiableOn_Hfun {X₀ : ℝ} (hX₀ : 2 ≤ X₀) :
    DifferentiableOn ℂ (Hfun X₀) (OmegaP ∩ {s | 3 / 2 < s.re}) := by
  have hE : DifferentiableOn ℂ (mellinK (cut X₀ e2F) 2) {s : ℂ | 3 / 2 < s.re} :=
    differentiableOn_mellinK (measurable_cut measurable_e2F) (fun σ hσ => convAbs_cut_e2F hX₀ hσ) 2
  have hP := differentiableOn_Phit (X₀ := X₀) (by linarith)
  have hP' := hP.deriv isOpen_OmegaP
  unfold Hfun
  exact (((hE.mono inter_subset_right).const_mul 3).add (hP'.mono inter_subset_left)).add
    (hP.mono inter_subset_left)

lemma deriv_mellinK_cut_phiF {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {s : ℂ} (hs : 2 < s.re) :
    mellinK (cut X₀ phiF) 1 s = deriv (Phit X₀) s := by
  have hd := hasDerivAt_mellinK (measurable_cut measurable_phiF) (τ := 2)
    (fun σ hσ => convAbs_cut_phiF hX₀ hσ) 0 hs
  have hev : mellinK (cut X₀ phiF) 0 =ᶠ[𝓝 s] Phit X₀ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact mellinK_cut_phiF_eq hX₀ hz
  rw [← hev.deriv_eq, hd.deriv]

lemma mellinK_aF_two_eq {X₀ : ℝ} (hX₀ : 2 ≤ X₀) {s : ℂ} (hs : 2 < s.re) :
    mellinK (cut X₀ aF) 2 s = Hfun X₀ s := by
  rw [mellin_decomp hX₀ hs, Hfun, deriv_mellinK_cut_phiF hX₀ hs, mellinK_cut_phiF_eq hX₀ hs]

/-! ### Landau's theorem applied to `A` -/

theorem conv_cut_Afun {X₀ : ℝ} (hX₀ : 2 ≤ X₀) (hA : ∀ x, X₀ ≤ x → 0 ≤ Afun x) :
    ∀ σ : ℝ, 3 / 2 < σ → Conv (cut X₀ Afun) σ := by
  obtain ⟨η, hη, hzf⟩ := exists_zeroFree_strip
  set V := hstrip (3 / 2) η with hVdef
  have hVsub : V ⊆ OmegaP ∩ {s | 3 / 2 < s.re} := by
    intro s hs
    refine ⟨⟨?_, hzf (s - 1) (by simp; linarith [hs.1]) (by simpa using hs.2)⟩, hs.1⟩
    intro h; rw [h] at hs; have := hs.1; simp at this; linarith
  have hHV : DifferentiableOn ℂ (Hfun X₀) V := (differentiableOn_Hfun hX₀).mono hVsub
  have hc3 : (3 / 2 : ℝ) < 3 := by norm_num
  -- the primitives
  set P₁ : ℂ → ℂ := fun w => wedgeIntegral ((3:ℝ) : ℂ) w (Hfun X₀) with hP₁def
  have hP₁ : ∀ z ∈ V, HasDerivAt P₁ (Hfun X₀ z) z := fun z hz =>
    hasDerivAt_wedge_hstrip hc3 hHV hz
  have hP₁d : DifferentiableOn ℂ P₁ V := fun z hz =>
    (hP₁ z hz).differentiableAt.differentiableWithinAt
  set P₂ : ℂ → ℂ := fun w => wedgeIntegral ((3:ℝ) : ℂ) w P₁ with hP₂def
  have hP₂ : ∀ z ∈ V, HasDerivAt P₂ (P₁ z) z := fun z hz =>
    hasDerivAt_wedge_hstrip hc3 hP₁d hz
  have hP₂d : DifferentiableOn ℂ P₂ V := fun z hz =>
    (hP₂ z hz).differentiableAt.differentiableWithinAt
  -- comparison on `V₂ = V ∩ {Re > 2}`
  set V₂ := V ∩ {s : ℂ | 2 < s.re} with hV₂def
  have hhalf : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hV₂open : IsOpen V₂ := (isOpen_hstrip _ _).inter hhalf
  have hV₂conn : IsPreconnected V₂ :=
    ((convex_hstrip _ _).inter (convex_halfSpace_re_gt 2)).isPreconnected
  have hconv_aF : ∀ σ, 2 < σ → ConvAbs (cut X₀ aF) σ := fun σ hσ => convAbs_cut_aF hX₀ hσ
  have hM1 : ∀ s : ℂ, 2 < s.re → HasDerivAt (mellinK (cut X₀ aF) 1) (mellinK (cut X₀ aF) 2 s) s :=
    fun s hs => hasDerivAt_mellinK (measurable_cut measurable_aF) hconv_aF 1 hs
  have hM0 : ∀ s : ℂ, 2 < s.re → HasDerivAt (mellinK (cut X₀ aF) 0) (mellinK (cut X₀ aF) 1 s) s :=
    fun s hs => hasDerivAt_mellinK (measurable_cut measurable_aF) hconv_aF 0 hs
  obtain ⟨α, hα⟩ := hV₂open.exists_eq_add_of_deriv_eq hV₂conn
    (f := mellinK (cut X₀ aF) 1) (g := P₁)
    (fun s hs => (hM1 s hs.2).differentiableAt.differentiableWithinAt)
    (hP₁d.mono inter_subset_left)
    (fun s hs => by
      rw [(hM1 s hs.2).deriv, (hP₁ s hs.1).deriv, mellinK_aF_two_eq hX₀ hs.2])
  have hlin : ∀ z, HasDerivAt (fun s : ℂ => P₂ s + α * s) (P₁ z + α) z → True := fun _ _ => trivial
  obtain ⟨β, hβ⟩ := hV₂open.exists_eq_add_of_deriv_eq hV₂conn
    (f := mellinK (cut X₀ aF) 0) (g := fun s => P₂ s + α * s)
    (fun s hs => (hM0 s hs.2).differentiableAt.differentiableWithinAt)
    (fun s hs => (((hP₂ s hs.1).add ((hasDerivAt_id s).const_mul α)).differentiableAt
      ).differentiableWithinAt)
    (fun s hs => by
      have h1 : HasDerivAt (fun s : ℂ => P₂ s + α * s) (P₁ s + α * 1) s :=
        (hP₂ s hs.1).add ((hasDerivAt_id s).const_mul α)
      rw [(hM0 s hs.2).deriv, h1.deriv, hα hs, mul_one])
  -- the continuation `G`
  set Gt : ℂ → ℂ := fun s => P₂ s + α * s + β with hGt
  set Fm : ℂ → ℂ := fun s => ((Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) + Gt s) / s with hFm
  set G : ℂ → ℂ := fun s => if 2 < s.re then mellinK (cut X₀ Afun) 0 s else Fm s with hG
  have hX₀c : (X₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < X₀).ne'
  have hGV : ∀ s ∈ V, G s = Fm s := by
    intro s hs
    by_cases h2 : 2 < s.re
    · simp only [hG, if_pos h2]
      have hs0 : s ≠ 0 := by intro h; rw [h] at h2; simp at h2; linarith
      have hibp := mellin_ibp hX₀ h2
      have hb : mellinK (cut X₀ (fun x => x * aFun x)) 0 s = Gt s := hβ ⟨hs, h2⟩
      rw [hFm]
      simp only
      rw [eq_div_iff hs0, mul_comm, hibp, hb]
    · simp only [hG, if_neg h2]
  have hFmd : ∀ s ∈ V, DifferentiableAt ℂ Fm s := by
    intro s hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; have := hs.1; simp at this; linarith
    have hGtd : DifferentiableAt ℂ Gt s :=
      (((hP₂ s hs).differentiableAt).add ((differentiableAt_id).const_mul α)).add_const β
    exact (((differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow
      (Or.inl hX₀c))).add hGtd).div differentiableAt_id hs0
  set U : Set ℂ := {s : ℂ | 2 < s.re} ∪ V with hUdef
  have hUopen : IsOpen U := hhalf.union (isOpen_hstrip _ _)
  have hconvA : ∀ σ, 2 < σ → ConvAbs (cut X₀ Afun) σ := fun σ hσ => convAbs_cut_Afun hX₀ hσ
  have hGdiff : DifferentiableOn ℂ G U := by
    rintro s (h2 | hV)
    · have hev : mellinK (cut X₀ Afun) 0 =ᶠ[𝓝 s] G := by
        filter_upwards [hhalf.mem_nhds h2] with z hz
        simp only [hG, if_pos (show 2 < z.re from hz)]
      have hd : DifferentiableAt ℂ (mellinK (cut X₀ Afun) 0) s :=
        (hasDerivAt_mellinK (measurable_cut_of_continuousOn hX₀ continuousOn_Afun_Ioi) hconvA 0
          h2).differentiableAt
      exact (hev.differentiableAt_iff.mp hd).differentiableWithinAt
    · have hev : Fm =ᶠ[𝓝 s] G := by
        filter_upwards [(isOpen_hstrip _ _).mem_nhds hV] with z hz
        exact (hGV z hz).symm
      exact (hev.differentiableAt_iff.mp (hFmd s hV)).differentiableWithinAt
  have hA0 : ∀ x, 1 < x → 0 ≤ cut X₀ Afun x := by
    intro x _
    unfold cut
    split_ifs with h
    · exact hA x h.le
    · exact le_rfl
  have hc : ∀ σ, 2 < σ → Conv (cut X₀ Afun) σ := by
    intro σ hσ
    refine (hconvA σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_nonneg (hA0 x hx)]
  have hUc : ∀ s : ℂ, 2 < s.re → s ∈ U := fun s hs => Or.inl hs
  have hUr : ∀ σ : ℝ, 3 / 2 < σ → (σ : ℂ) ∈ U := fun σ hσ =>
    Or.inr ⟨by simpa using hσ, by simpa using hη⟩
  have hFG : ∀ s : ℂ, 2 < s.re → mellinK (cut X₀ Afun) 0 s = G s := by
    intro s hs; simp only [hG, if_pos hs]
  exact landau (measurable_cut_of_continuousOn hX₀ continuousOn_Afun_Ioi) hA0 hc hUopen hGdiff
    hUc hUr hFG

end LandauRH

end

-- ===== LF8d.lean =====
section

set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory Metric
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction LandauMellin PsiOscillation ZetaAux

lemma zetaMulSubOne_not_eventually_zero (ρ : ℂ) : ¬ ∀ᶠ z in 𝓝 ρ, zetaMulSubOne z = 0 := by
  intro hev
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (differentiable_zetaMulSubOne.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ
    (mem_univ ρ) hev
  exact zetaMulSubOne_ne_zero_of_one_le_re (s := 2) (by norm_num) (this (mem_univ 2))

/-- **The ¬RH ⇒ ¬(Landau inequality) direction**, in contrapositive form. -/
theorem RH_of_landau_ineq
    (H : ∀ᶠ n : ℕ in atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ₀, hζ, hρ1, hρ2⟩ := exists_zero_of_not_RH hRH
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (Afun_nonneg_of_landau H)
  set X₀ := max X₁ 2 with hX₀def
  have hX₀ : 2 ≤ X₀ := le_max_right _ _
  have hA : ∀ x, X₀ ≤ x → 0 ≤ Afun x := fun x hx => hX₁ x ((le_max_left _ _).trans hx)
  have hconv := conv_cut_Afun hX₀ hA
  have hA0 : ∀ x, 1 < x → 0 ≤ cut X₀ Afun x := by
    intro x _
    unfold cut
    split_ifs with h
    · exact hA x h.le
    · exact le_rfl
  have hmeasA := measurable_cut_of_continuousOn hX₀ continuousOn_Afun_Ioi
  have hconvAbs : ∀ σ, 3 / 2 < σ → ConvAbs (cut X₀ Afun) σ := fun σ hσ =>
    convAbs_of_conv hA0 (hconv σ hσ)
  -- holomorphy on `W = {Re s > 3/2}`
  set W : Set ℂ := {s : ℂ | 3 / 2 < s.re} with hWdef
  have hWopen : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  set F := mellinK (cut X₀ Afun) 0 with hFdef
  have hFd : DifferentiableOn ℂ F W := differentiableOn_mellinK hmeasA hconvAbs 0
  have hX₀c : (X₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < X₀).ne'
  set G₁ : ℂ → ℂ := fun s => s * F s - (Afun X₀ : ℂ) * (X₀ : ℂ) ^ (-s) with hG₁def
  have hG₁d : DifferentiableOn ℂ G₁ W := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_id.mul (hFd.differentiableAt (hWopen.mem_nhds hs))).sub
      ((differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (Or.inl hX₀c)))
  have hG₁'d : DifferentiableOn ℂ (deriv G₁) W := hG₁d.deriv hWopen
  have hG₁''d : DifferentiableOn ℂ (deriv (deriv G₁)) W := hG₁'d.deriv hWopen
  have hE2d : DifferentiableOn ℂ (mellinK (cut X₀ e2F) 2) W :=
    differentiableOn_mellinK (measurable_cut measurable_e2F) (fun σ hσ => convAbs_cut_e2F hX₀ hσ) 2
  set R : ℂ → ℂ := fun s => deriv (deriv G₁) s - 3 * mellinK (cut X₀ e2F) 2 s with hRdef
  have hRd : DifferentiableOn ℂ R W := hG₁''d.sub (hE2d.const_mul 3)
  -- on `Re s > 2`, `R = Φ̃' + Φ̃`
  have hhalf : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv_aF : ∀ σ, 2 < σ → ConvAbs (cut X₀ aF) σ := fun σ hσ => convAbs_cut_aF hX₀ hσ
  have hG₁eq : ∀ s : ℂ, 2 < s.re → G₁ s = mellinK (cut X₀ aF) 0 s := by
    intro s hs
    have h := mellin_ibp hX₀ hs
    have h' : mellinK (cut X₀ aF) 0 s = mellinK (cut X₀ (fun x => x * aFun x)) 0 s := rfl
    rw [h']
    simp only [hG₁def, hFdef]
    rw [h]
    ring
  have hdG₁ : ∀ s : ℂ, 2 < s.re → deriv G₁ s = mellinK (cut X₀ aF) 1 s := by
    intro s hs
    have hev : G₁ =ᶠ[𝓝 s] mellinK (cut X₀ aF) 0 := by
      filter_upwards [hhalf.mem_nhds hs] with z hz using hG₁eq z hz
    rw [hev.deriv_eq, (hasDerivAt_mellinK (measurable_cut measurable_aF) hconv_aF 0 hs).deriv]
  have hRphi : ∀ s : ℂ, 2 < s.re → R s = deriv (Phit X₀) s + Phit X₀ s := by
    intro s hs
    have hev : deriv G₁ =ᶠ[𝓝 s] mellinK (cut X₀ aF) 1 := by
      filter_upwards [hhalf.mem_nhds hs] with z hz using hdG₁ z hz
    simp only [hRdef]
    rw [hev.deriv_eq, (hasDerivAt_mellinK (measurable_cut measurable_aF) hconv_aF 1 hs).deriv,
      mellinK_aF_two_eq hX₀ hs, Hfun]
    ring
  -- the ball `B` around `z₁ = ρ₀ + 3/2`
  set s₀ := ρ₀ + 1 with hs₀
  set z₁ := s₀ + 1 / 2 with hz₁
  set r := s₀.re - 1 with hr
  have hs₀re : s₀.re = ρ₀.re + 1 := by simp [hs₀]
  have hz₁re : z₁.re = ρ₀.re + 3 / 2 := by simp [hz₁, hs₀]; ring
  have hz₁im : z₁.im = ρ₀.im := by simp [hz₁, hs₀]
  set B := ball z₁ r with hBdef
  have hBW : B ⊆ W := by
    intro z hz
    have h1 : |z.re - z₁.re| ≤ ‖z - z₁‖ := by simpa using Complex.abs_re_le_norm (z - z₁)
    have h2 : ‖z - z₁‖ < r := by rw [← dist_eq_norm]; exact hz
    have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
    show 3 / 2 < z.re
    rw [hr, hs₀re] at this
    linarith
  have hs₀B : s₀ ∈ B := by
    show dist s₀ z₁ < r
    rw [dist_eq_norm, hz₁, show s₀ - (s₀ + 1 / 2) = -(1 / 2 : ℂ) by ring, norm_neg, hr, hs₀re]
    norm_num
    linarith
  have hz₁B : z₁ ∈ B := mem_ball_self (by rw [hr, hs₀re]; linarith)
  have hz₁half : 2 < z₁.re := by rw [hz₁re]; linarith
  -- primitive of `e^s R(s)` on `B`
  have hexpR : DifferentiableOn ℂ (fun s => Complex.exp s * R s) B :=
    (Complex.differentiable_exp.differentiableOn).mul (hRd.mono hBW)
  obtain ⟨Q, hQ⟩ := hexpR.isExactOn_ball
  have hQd : DifferentiableOn ℂ Q B := fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt
  -- on `B₂ = B ∩ {Re > 2}`, `e^s Φ̃(s) = Q(s) + κ`
  set B₂ := B ∩ {s : ℂ | 2 < s.re} with hB₂def
  have hB₂open : IsOpen B₂ := isOpen_ball.inter hhalf
  have hB₂conn : IsPreconnected B₂ :=
    ((convex_ball z₁ r).inter (convex_halfSpace_re_gt 2)).isPreconnected
  have hz₁B₂ : z₁ ∈ B₂ := ⟨hz₁B, hz₁half⟩
  have hOmega : ∀ s : ℂ, 2 < s.re → s ∈ OmegaP := by
    intro s hs
    refine ⟨?_, zetaMulSubOne_ne_zero_of_one_le_re (by simp; linarith)⟩
    intro h; rw [h] at hs; norm_num at hs
  have hPd := differentiableOn_Phit (X₀ := X₀) (by linarith)
  have hPhitAt : ∀ s : ℂ, 2 < s.re → DifferentiableAt ℂ (Phit X₀) s := fun s hs =>
    hPd.differentiableAt (isOpen_OmegaP.mem_nhds (hOmega s hs))
  obtain ⟨κ, hκ⟩ := hB₂open.exists_eq_add_of_deriv_eq hB₂conn
    (f := fun s => Complex.exp s * Phit X₀ s) (g := Q)
    (fun s hs => (Complex.differentiable_exp.differentiableAt.mul
      (hPhitAt s hs.2)).differentiableWithinAt)
    (hQd.mono inter_subset_left)
    (fun s hs => by
      have h1 : HasDerivAt (fun s => Complex.exp s * Phit X₀ s)
          (Complex.exp s * Phit X₀ s + Complex.exp s * deriv (Phit X₀) s) s :=
        (Complex.hasDerivAt_exp s).mul (hPhitAt s hs.2).hasDerivAt
      rw [h1.deriv, (hQ s hs.1).deriv]
      show _ = Complex.exp s * R s
      rw [hRphi s hs.2]
      ring)
  set Φs : ℂ → ℂ := fun s => Complex.exp (-s) * (Q s + κ) with hΦs
  have hΦsd : DifferentiableOn ℂ Φs B := fun z hz =>
    ((Complex.differentiable_exp.comp differentiable_neg).differentiableAt.mul
      ((hQ z hz).differentiableAt.add_const κ)).differentiableWithinAt
  have hΦsP : ∀ s ∈ B₂, Φs s = Phit X₀ s := by
    intro s hs
    have this : Complex.exp s * Phit X₀ s = Q s + κ := hκ hs
    simp only [hΦs]
    rw [← this, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  -- the identity `-h'(s-1) = h(s-1) ((s-1)Φ(s) + 1 + (s-1)E(s))` on `B`
  set h := zetaMulSubOne with hhdef
  set E := mellinK (cutc X₀ phiF) 0 with hEdef
  have hEd : Differentiable ℂ E := differentiable_mellinK_cutc_phiF (by linarith)
  have hsub : ∀ s : ℂ, DifferentiableAt ℂ (fun z : ℂ => z - 1) s := fun s =>
    differentiableAt_id.sub_const 1
  have hL : DifferentiableOn ℂ (fun s => -deriv h (s - 1)) B := fun s _ => by
    have := (differentiable_deriv_zetaMulSubOne (s - 1)).comp s (hsub s)
    exact this.neg.differentiableWithinAt
  have hRgt : DifferentiableOn ℂ (fun s => h (s - 1) * ((s - 1) * Φs s + 1 + (s - 1) * E s)) B :=
    fun s hs => by
      have h1 : DifferentiableAt ℂ (fun z => h (z - 1)) s := by
        have := (differentiable_zetaMulSubOne (s - 1)).comp s (hsub s)
        exact this
      have h2 : DifferentiableAt ℂ Φs s := hΦsd.differentiableAt (isOpen_ball.mem_nhds hs)
      exact (h1.mul ((((hsub s).mul h2).add_const 1).add ((hsub s).mul (hEd s))))
        |>.differentiableWithinAt
  have hidB : EqOn (fun s => -deriv h (s - 1))
      (fun s => h (s - 1) * ((s - 1) * Φs s + 1 + (s - 1) * E s)) B := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hL.analyticOnNhd isOpen_ball)
      (hRgt.analyticOnNhd isOpen_ball) (convex_ball z₁ r).isPreconnected hz₁B ?_
    filter_upwards [hB₂open.mem_nhds hz₁B₂] with s hs
    have hs2 : 2 < s.re := hs.2
    have hs1 : s - 1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hhs : h (s - 1) ≠ 0 := zetaMulSubOne_ne_zero_of_one_le_re (by simp; linarith)
    rw [hΦsP s hs, Phit]
    rw [← hhdef, ← hEdef]
    field_simp
    ring
  -- conclusion via `ne_zero_of_deriv_eq_mul`
  set V' : Set ℂ := (fun w : ℂ => w + 1) ⁻¹' B with hV'def
  have hV'open : IsOpen V' := isOpen_ball.preimage (continuous_id.add continuous_const)
  have hρV' : ρ₀ ∈ V' := by show ρ₀ + 1 ∈ B; exact hs₀B
  set P : ℂ → ℂ := fun w => -(w * Φs (w + 1) + 1 + w * E (w + 1)) with hPdef
  have hPc : ContinuousAt P ρ₀ := by
    have h1 : ContinuousAt (fun w : ℂ => Φs (w + 1)) ρ₀ := by
      have hc : ContinuousAt Φs (ρ₀ + 1) :=
        (hΦsd.differentiableAt (isOpen_ball.mem_nhds hs₀B)).continuousAt
      exact hc.comp (f := fun w : ℂ => w + 1) (continuous_add_right 1).continuousAt
    have h2 : ContinuousAt (fun w : ℂ => E (w + 1)) ρ₀ :=
      (hEd.continuous.comp (continuous_id.add continuous_const)).continuousAt
    exact (((continuousAt_id.mul h1).add continuousAt_const).add (continuousAt_id.mul h2)).neg
  have hfP : ∀ w ∈ V', deriv h w = P w * h w := by
    intro w hw
    have := hidB hw
    simp only [add_sub_cancel_right] at this
    simp only [hPdef]
    linear_combination -this
  have hhρ : h ρ₀ = 0 := by
    have hρ1' : ρ₀ ≠ 1 := by intro h1; rw [h1] at hρ2; simp at hρ2
    rw [hhdef, zetaMulSubOne_of_ne hρ1', hζ, mul_zero]
  exact ne_zero_of_deriv_eq_mul hV'open hρV' (differentiable_zetaMulSubOne.analyticAt ρ₀) hPc hfP
    (zetaMulSubOne_not_eventually_zero ρ₀) hhρ

end LandauRH

end


end

/-- The Landau inequality for all sufficiently large `n` implies RH. -/
theorem solution
    (h : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n)) :
    RiemannHypothesis :=
  LandauRH.RH_of_landau_ineq h
