-- Prove2me | solution 1 for GuthMaynard.davenport_truncated_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:16:48.357843+00:00
-- url     : https://prove2.me/submissions/43831772-13b4-4fb4-af9c-ff67be107303

import Mathlib
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_WeilEF_zeta_logDeriv_partial_fraction

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-!
# Davenport's truncated explicit formula (Davenport, *Multiplicative Number Theory*, Ch. 17): blueprint

Target: `davenport_dev`, with exactly the type of
`GuthMaynard.davenport_truncated_explicit_formula`.

Route (c = 1 + 1/log x, `F x s = -ζ'/ζ(s) x^s / s`, `J x T = (1/2π) ∫_{-T}^{T} F(c+it) dt`):

* (P) truncated Perron:  ‖ψ₀(x) − J(x,T)‖ ≪ x log²x/T + log x · min(1, x/(T⟨x⟩)).
  Kernel lemmas `perron_kernel_*` (pure analysis), interchange `perron_sum_eq`,
  arithmetic `psi0_hasSum`, `vonMangoldt_dirichlet_le`, `kb_sum_far`, `kb_sum_near`.
* (G) a good height T' ∈ [T, T+1] (`good_height`), and ζ'/ζ ≪ log²T on Im s = ±T'
  (`logDeriv_bound_mid` from the partial fraction, `logDeriv_zeta_FE`, `digamma_bound`,
  `cot_bound`, `logDeriv_bound_right`; glued in `logDeriv_bound_horizontal`, `logDeriv_bound_left`).
* (R) the rectangle [−(2M+1), c] × [−T', T']: residue identity `rect_residue`
  (from `rect_residue_theorem`, `rectInt_inv_sub`, the local expansions `F_local_*`,
  `order_trivial`, `zeta_zero_cases`), horizontal edges `horizontal_bound`,
  left edge `left_edge_tendsto`, trivial-zero series `trivSum_tendsto`; glued in `rect_bound`.
* (Z) back from T' to T: `zsum_diff` (local zero count) and `J_diff`.
-/
/-! ## Definitions -/
/-- ψ₀(x): Chebyshev's ψ with the half-weight at a prime-power jump. -/
def psi0 (x : ℝ) : ℝ :=
  Chebyshev.psi x -
    (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0)

/-- Nontrivial zeros with |γ| < T. -/
def ZS (T : ℝ) : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T}

/-- Σ_{|γ|<T} m_ρ x^ρ / ρ. -/
def zsum (x T : ℝ) : ℂ := ∑ᶠ ρ ∈ ZS T, (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- ⟨x⟩: distance from x to the nearest prime power other than x. -/
def ppDist (x : ℝ) : ℝ := sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) ≠ x ∧ d = |x - n|}

/-- The abscissa c = 1 + 1/log x. -/
def cx (x : ℝ) : ℝ := 1 + 1 / Real.log x

/-- The integrand −ζ'/ζ(s) x^s / s. -/
def F (x : ℝ) (s : ℂ) : ℂ := -logDeriv riemannZeta s * (x : ℂ) ^ s / s

/-- (1/2πi) ∫_{c−iT}^{c+iT} F(s) ds = (1/2π) ∫_{−T}^{T} F(c+it) dt. -/
def Jc (x c T : ℝ) : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, F x ((c : ℂ) + (t : ℂ) * I)

/-- J(x,T) on the line c = 1 + 1/log x. -/
def J (x T : ℝ) : ℂ := Jc x (cx x) T

/-- The truncated Perron integral (1/2πi) ∫_{c−iT}^{c+iT} y^s/s ds. -/
def perronInt (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)

/-- δ(y) = 1, 1/2, 0 for y > 1, y = 1, y < 1. -/
def delta (y : ℝ) : ℝ := if 1 < y then 1 else if y = 1 then 1 / 2 else 0

/-- The Perron-kernel error majorant. -/
def kb (y c T : ℝ) : ℝ := if y = 1 then 1 / T else y ^ c * min 1 (1 / (T * |Real.log y|))

/-- Counter-clockwise boundary integral of the rectangle [a, b] × [−T, T]
(the shape of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`). -/
def rectInt (f : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  (∫ σ in a..b, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) - (∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * I)) +
    I * (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * I)) - I * (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * I))

/-- T' is δ-good: every nontrivial zero has ordinate at distance ≥ δ from ±T'. -/
def IsGood (δ T' : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → δ ≤ |ρ.im - T'| ∧ δ ≤ |ρ.im + T'|

/-- Σ_{m=1}^{M} x^{−2m}/(2m): the residues at the trivial zeros −2, …, −2M. -/
def trivSum (x : ℝ) (M : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 M, x ^ (-(2 * (m : ℝ))) / (2 * m)

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-!
# Davenport blueprint, part A

Perron kernel (via the absolutely convergent second-order kernel and Fourier inversion, adapted
from the `riemann-pnt-lean4` project), the functional equation for ζ'/ζ, digamma / cot bounds,
ζ'/ζ on horizontal lines and left edges, and the edge estimates of the contour shift.
-/
/-! ## from Perron -/
/-- The Laplace transform of the first moment on the positive half-line. -/
theorem integral_mul_cexp_Ioi (a : ℂ) (ha : a.re < 0) :
    (∫ u : ℝ in Set.Ioi 0, (u : ℂ) * Complex.exp (a * u)) = 1 / a ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (a * u)) (Ioi 0) := by
    apply Integrable.mono'
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
        (b := -a.re) (by norm_num) (by norm_num) (by linarith))
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one, Real.rpow_one, mul_comm]
  let F : ℝ → ℂ := fun u => Complex.exp (a * u) * (a * u - 1) / a ^ 2
  have hF : ∀ u : ℝ, HasDerivAt F ((u : ℂ) * Complex.exp (a * u)) u := by
    intro u
    let H : ℂ → ℂ := fun z => Complex.exp (a * z) * (a * z - 1) / a ^ 2
    have hH : HasDerivAt H ((u : ℂ) * Complex.exp (a * u)) (u : ℂ) := by
      dsimp [H]
      convert ((((Complex.hasDerivAt_exp (a * u)).comp (u : ℂ)
        ((hasDerivAt_id (u : ℂ)).const_mul a)).mul
          ((((hasDerivAt_id (u : ℂ)).const_mul a).sub_const 1))).div_const (a ^ 2)) using 1 <;>
        (try rfl) <;> simp only [Function.comp_apply, id_eq] <;> field_simp <;> ring
    simpa [F, H] using hH.comp_ofReal
  have hlim : Filter.Tendsto F Filter.atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => Complex.exp (a * u)) atTop (𝓝 0) := by
      simpa [Complex.tendsto_exp_nhds_zero_iff] using
        tendsto_const_nhds.neg_mul_atTop ha tendsto_id
    have hmul : Tendsto (fun u : ℝ => (u : ℂ) * Complex.exp (a * u)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-a.re) (by linarith)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one]
    have hdiff :
        Tendsto (fun u : ℝ => (u : ℂ) * Complex.exp (a * u) / a -
          Complex.exp (a * u) / a ^ 2) atTop (𝓝 0) := by
      simpa using ((hmul.div_const a).sub (hexp.div_const (a ^ 2)))
    refine hdiff.congr' ?_
    filter_upwards with u
    dsimp [F]
    field_simp
  have hzero : F 0 = -(1 / a ^ 2) := by
    simp [F]
    field_simp
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (f' := fun u : ℝ => (u : ℂ) * Complex.exp (a * u))
    (a := 0) (m := 0) (by simpa [F] using (hF 0).continuousAt.continuousWithinAt)
    (fun u _ => hF u) hint hlim]
  rw [hzero]
  ring

/-- Continuous one-sided exponential ramp used in the second-order Perron formula. -/
noncomputable def smoothPerronStep (c : ℝ) : ℝ → ℂ :=
  fun u : ℝ => ((max u 0 : ℝ) : ℂ) * Complex.exp (-c * max u 0)

theorem fourier_smoothPerronStep (c : ℝ) (hc : 0 < c) (w : ℝ) :
    𝓕 (smoothPerronStep c) w =
      1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [show (fun u : ℝ =>
      Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I) • smoothPerronStep c u) =
      Set.indicator (Set.Ioi 0) (fun u : ℝ =>
        (u : ℂ) * Complex.exp ((-(c : ℂ) - 2 * Real.pi * w * Complex.I) * u)) by
    funext u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
      have hu' : 0 < u := Set.mem_Ioi.mp hu
      simp only [smoothPerronStep, smul_eq_mul, max_eq_left hu'.le]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [smoothPerronStep, hu, max_eq_right hu0]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [integral_mul_cexp_Ioi (-(c : ℂ) - 2 * Real.pi * w * Complex.I) (by simp [hc])]
  congr 1
  ring_nf

theorem integrable_smoothPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (smoothPerronStep c) := by
  have hbase : IntegrableOn
      (fun u : ℝ => (u : ℂ) * Complex.exp (-c * u)) (Set.Ioi 0) := by
    apply Integrable.mono'
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
        (b := c) (by norm_num) (by norm_num) hc)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one, mul_comm]
  apply (hbase.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with u
  by_cases hu : 0 < u
  · simp [smoothPerronStep, hu, max_eq_left hu.le]
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    simp [smoothPerronStep, hu, max_eq_right hu0]

theorem integrable_fourier_smoothPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (𝓕 (smoothPerronStep c)) := by
  rw [integrable_congr (Filter.Eventually.of_forall (fourier_smoothPerronStep c hc))]
  have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ => 1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
    exact (continuous_const.div₀ (by fun_prop) (fun w => pow_ne_zero 2 (hne w))).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  have hk : 2 * Real.pi / c ≠ 0 := by positivity
  have h := (integrable_inv_one_add_sq.comp_mul_left' hk).const_mul (c ^ (-2 : ℤ))
  convert h using 1 <;> (try rfl)
  funext w
  rw [show (c : ℂ) + 2 * Real.pi * w * Complex.I =
      (c : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_div, norm_one, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I]
  field_simp

theorem fourierInv_secondOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    𝓕⁻ (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) u =
      smoothPerronStep c u := by
  have hcont : Continuous (smoothPerronStep c) := by
    unfold smoothPerronStep
    fun_prop
  have hinv : 𝓕⁻ (𝓕 (smoothPerronStep c)) u = smoothPerronStep c u :=
    (integrable_smoothPerronStep c hc).fourierInv_fourier_eq
      (integrable_fourier_smoothPerronStep c hc) (v := u) hcont.continuousAt
  rw [show 𝓕 (smoothPerronStep c) =
      (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) by
        funext w
        exact fourier_smoothPerronStep c hc w] at hinv
  exact hinv

/-- Exact second-order Perron inversion in the Fourier-normalized vertical variable. -/
theorem integral_secondOrderPerronKernel_eq (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = smoothPerronStep c u := by
  rw [← fourierInv_secondOrderPerronKernel c hc u, Real.fourierInv_eq']
  congr 1
  funext w
  simp only [smul_eq_mul, one_div]
  rw [div_eq_mul_inv]
  rw [show inner ℝ w u = w * u by change u * w = w * u; ring]
  push_cast
  ring

/-- Exact second-order Perron formula. The Fourier variable is normalized so that
`s = c + 2πiw`; equivalently this is `(2πi)⁻¹ ∫ y^s / s² ds`. -/
theorem secondOrderPerron_eq_max (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = ((max u 0 : ℝ) : ℂ) := by
  rw [show (fun w : ℝ =>
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) =
      (fun w : ℝ => (Complex.exp (c * u) *
        (Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) : ℂ)) by
    funext w
    rw [show (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) =
        (c * u : ℝ) + 2 * Real.pi * (w * u) * Complex.I by push_cast; ring,
      Complex.exp_add]
    rw [show c * u = u * c by ring]
    push_cast
    ring]
  calc
    _ = Complex.exp (c * u) *
        (∫ w : ℝ, Complex.exp (2 * Real.pi * (w * u) * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) :=
      integral_const_mul _ _
    _ = Complex.exp (c * u) * smoothPerronStep c u := by
      rw [integral_secondOrderPerronKernel_eq c hc u]
    _ = ((max u 0 : ℝ) : ℂ) := by
      by_cases hu : 0 < u
      · simp only [smoothPerronStep, max_eq_left hu.le]
        rw [mul_left_comm, ← Complex.exp_add]
        simp
      · have hu0 : u ≤ 0 := le_of_not_gt hu
        simp [smoothPerronStep, max_eq_right hu0]

theorem integrable_secondOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  have hbase : Integrable (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2 : ℂ)) := by
    exact (integrable_fourier_smoothPerronStep c hc).congr
      (Filter.Eventually.of_forall fun w => fourier_smoothPerronStep c hc w)
  have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  apply Integrable.mono' (hbase.norm.const_mul ‖Complex.exp (c * u)‖)
  · exact ((by fun_prop : Continuous fun w : ℝ =>
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
          (by fun_prop) (fun w => pow_ne_zero 2 (hne w))).aestronglyMeasurable
  · filter_upwards with w
    simp only [norm_div, norm_one, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp
    ring

theorem norm_secondOrderPerronKernel_le
    {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * w ^ 2) := by
  have hw0 : w ≠ 0 := by
    intro hwzero
    subst w
    simp at hw
    linarith
  have hden_pos : 0 < 4 * Real.pi ^ 2 * w ^ 2 := by positivity
  rw [norm_div, norm_pow, Complex.norm_exp]
  have hre : (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u).re = c * u := by
    simp
  rw [hre]
  rw [show (c : ℂ) + 2 * Real.pi * w * Complex.I =
      (c : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hden_pos
  nlinarith [sq_nonneg c]

theorem norm_integral_secondOrderPerronKernel_Ioi_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Set.Ioi W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
  let A : ℝ := Real.exp (c * u) / (4 * Real.pi ^ 2)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-2 : ℝ)) (Set.Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-2 : ℝ)) (Set.Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Set.Ioi W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
        ∫ w : ℝ in Set.Ioi W, A * w ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
            Real.exp (c * u) / (4 * Real.pi ^ 2 * w ^ 2) :=
          norm_secondOrderPerronKernel_le hW (by simpa [abs_of_pos hw_pos] using hw.le)
        _ = A * w ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Set.Ioi W, w ^ (-2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A / W := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hW]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      field_simp
    _ = Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      dsimp [A]
      field_simp

theorem norm_integral_secondOrderPerronKernel_Iic_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Set.Iic (-W),
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  rw [← integral_comp_neg_Ioi W K]
  let A : ℝ := Real.exp (c * u) / (4 * Real.pi ^ 2)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-2 : ℝ)) (Set.Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-2 : ℝ)) (Set.Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Set.Ioi W, K (-w)‖ ≤
        ∫ w : ℝ in Set.Ioi W, A * w ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖K (-w)‖ ≤ Real.exp (c * u) / (4 * Real.pi ^ 2 * (-w) ^ 2) := by
          apply norm_secondOrderPerronKernel_le hW
          simpa [abs_of_pos hw_pos] using hw.le
        _ = A * w ^ (-2 : ℝ) := by
          rw [neg_sq, Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Set.Ioi W, w ^ (-2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A / W := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hW]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      field_simp
    _ = Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      dsimp [A]
      field_simp

/-- Quantitative finite-height second-order Perron inversion. -/
theorem norm_truncated_secondOrderPerron_sub_max_le
    {c u W : ℝ} (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        ((max u 0 : ℝ) : ℂ)‖ ≤
      Real.exp (c * u) / (2 * Real.pi ^ 2 * W) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  have hK : Integrable K := by
    simpa [K] using integrable_secondOrderPerronKernel c hc u
  have hWorder : -W ≤ W := by linarith
  have hinterval :
      (∫ w : ℝ in Set.Iic W, K w) - (∫ w : ℝ in Set.Iic (-W), K w) =
        ∫ w : ℝ in (-W)..W, K w :=
    intervalIntegral.integral_Iic_sub_Iic hK.integrableOn hK.integrableOn
  have hwhole :
      (∫ w : ℝ in Set.Iic W, K w) + (∫ w : ℝ in Set.Ioi W, K w) =
        ∫ w : ℝ, K w :=
    intervalIntegral.integral_Iic_add_Ioi hK.integrableOn hK.integrableOn
  have hdecomp :
      (∫ w : ℝ in (-W)..W, K w) - (∫ w : ℝ, K w) =
        -((∫ w : ℝ in Set.Iic (-W), K w) + (∫ w : ℝ in Set.Ioi W, K w)) := by
    rw [← hinterval, ← hwhole]
    abel
  rw [show ((max u 0 : ℝ) : ℂ) = ∫ w : ℝ, K w by
    simpa [K] using (secondOrderPerron_eq_max c hc u).symm]
  rw [show (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = K by rfl]
  rw [hdecomp, norm_neg]
  calc
    ‖(∫ w : ℝ in Set.Iic (-W), K w) + (∫ w : ℝ in Set.Ioi W, K w)‖ ≤
        ‖∫ w : ℝ in Set.Iic (-W), K w‖ + ‖∫ w : ℝ in Set.Ioi W, K w‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (c * u) / (4 * Real.pi ^ 2 * W) +
        Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      apply add_le_add
      · simpa [K] using norm_integral_secondOrderPerronKernel_Iic_le (c := c) (u := u) hW
      · simpa [K] using norm_integral_secondOrderPerronKernel_Ioi_le (c := c) (u := u) hW
    _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * W) := by
      field_simp
      norm_num

/-- The Heaviside step with the symmetric Perron half weight at the jump. -/
noncomputable def perronHalfStep (u : ℝ) : ℂ :=
  if 0 < u then 1 else if u = 0 then (1 / 2 : ℂ) else 0

private noncomputable def firstOrderBoundaryPrimitive (c u : ℝ) (w : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
    ((c : ℂ) + 2 * Real.pi * w * Complex.I)

private lemma hasDerivAt_firstOrderBoundaryPrimitive
    {c u w : ℝ} (hc : 0 < c) :
    HasDerivAt (firstOrderBoundaryPrimitive c u)
      ((2 * Real.pi * Complex.I) *
        (u * firstOrderBoundaryPrimitive c u w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) w := by
  let H : ℂ → ℂ := fun z =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * z * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * z * Complex.I)
  have hden : (c : ℂ) + 2 * Real.pi * (w : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hH : HasDerivAt H
      ((2 * Real.pi * Complex.I) *
        (u * H w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) (w : ℂ) := by
    dsimp [H]
    convert (((Complex.hasDerivAt_exp
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).comp (w : ℂ)
        (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
          |>.const_add (c : ℂ)).mul_const u)).div
            (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
              |>.const_add (c : ℂ))) hden) using 1 <;>
      all_goals (first
        | rfl
        | funext z <;> rfl
        | (field_simp [hden] <;> simp only [id_eq, Function.comp_apply] <;> ring)
        | (ring_nf <;> ring))
  have hHofReal : HasDerivAt (fun w : ℝ => H w)
      ((2 * Real.pi * Complex.I) *
        (u * H (w : ℂ) -
          Complex.exp (((c : ℂ) + 2 * Real.pi * (w : ℂ) * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * (w : ℂ) * Complex.I) ^ 2)) w := by
    simpa only [ofRealCLM_apply, ofReal_one, mul_one] using!
      hH.comp w ofRealCLM.hasDerivAt
  dsimp [firstOrderBoundaryPrimitive, H]
  exact hHofReal

/-- Integration by parts reduces a finite first-order Perron integral to its
two endpoint values and the finite second-order Perron integral. -/
lemma intervalIntegral_firstOrderPerron_eq_boundary_add_secondOrder
    {c u W : ℝ} (hc : 0 < c) (hu : u ≠ 0) :
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u) +
      (1 / u : ℂ) *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  let K₂ : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  let D : ℝ → ℂ := fun w =>
    (2 * Real.pi * Complex.I) *
      (u * firstOrderBoundaryPrimitive c u w - K₂ w)
  have hden_all : ∀ w : ℝ,
      (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro w h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hFcont : Continuous (firstOrderBoundaryPrimitive c u) := by
    unfold firstOrderBoundaryPrimitive
    exact (by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
        (by fun_prop) hden_all
  have hK₂cont : Continuous K₂ := by
    dsimp [K₂]
    exact (by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
        (by fun_prop) (fun w => pow_ne_zero 2 (hden_all w))
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  have hD : (∫ w : ℝ in (-W)..W, D w) =
      firstOrderBoundaryPrimitive c u W -
        firstOrderBoundaryPrimitive c u (-W) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro w _hw
      simpa [D, K₂] using hasDerivAt_firstOrderBoundaryPrimitive
        (c := c) (u := u) (w := w) hc
    · exact hDcont.intervalIntegrable _ _
  calc
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∫ w : ℝ in (-W)..W,
          (1 / ((2 * Real.pi * Complex.I) * u)) * D w +
            (1 / u : ℂ) * K₂ w := by
      apply intervalIntegral.integral_congr
      intro w _hw
      have hden : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      dsimp [D, K₂, firstOrderBoundaryPrimitive]
      field_simp
      simp [hu]
    _ = (1 / ((2 * Real.pi * Complex.I) * u)) *
          (∫ w : ℝ in (-W)..W, D w) +
        (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
      let f : ℝ → ℂ := fun w =>
        (1 / ((2 * Real.pi * Complex.I) * u)) * D w
      let g : ℝ → ℂ := fun w => (1 / u : ℂ) * K₂ w
      have hf : IntervalIntegrable f volume (-W) W := by
        exact (continuous_const.mul hDcont).intervalIntegrable _ _
      have hg : IntervalIntegrable g volume (-W) W := by
        exact (continuous_const.mul hK₂cont).intervalIntegrable _ _
      have hfconst : (∫ w : ℝ in (-W)..W, f w) =
          (1 / ((2 * Real.pi * Complex.I) * u)) *
            (∫ w : ℝ in (-W)..W, D w) := by
        simpa only [f] using
          (intervalIntegral.integral_const_mul
            (a := -W) (b := W)
            (1 / ((2 * Real.pi * Complex.I) * u)) D)
      have hgconst : (∫ w : ℝ in (-W)..W, g w) =
          (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
        simpa only [g] using
          (intervalIntegral.integral_const_mul
            (a := -W) (b := W) (1 / u : ℂ) K₂)
      calc
        (∫ w : ℝ in (-W)..W,
            (1 / ((2 * Real.pi * Complex.I) * u)) * D w +
              (1 / u : ℂ) * K₂ w) =
            (∫ w : ℝ in (-W)..W, f w) +
              (∫ w : ℝ in (-W)..W, g w) := by
                simpa [f, g] using intervalIntegral.integral_add hf hg
        _ = (1 / ((2 * Real.pi * Complex.I) * u)) *
              (∫ w : ℝ in (-W)..W, D w) +
            (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
              rw [hfconst, hgconst]
    _ = (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u) +
      (1 / u : ℂ) *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
      rw [hD]
      simp only [K₂, div_eq_mul_inv]
      ring

private lemma norm_firstOrderBoundaryPrimitive_le
    {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖firstOrderBoundaryPrimitive c u w‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) := by
  have hw_pos : 0 < |w| := hW.trans_le hw
  have hsmall_pos : 0 < 2 * Real.pi * W := by positivity
  rw [firstOrderBoundaryPrimitive, norm_div, Complex.norm_exp]
  have hre :
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u).re = c * u := by
    simp
  rw [hre]
  have him_le : 2 * Real.pi * |w| ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
    have hbase := abs_im_le_norm
      ((c : ℂ) + 2 * Real.pi * w * Complex.I)
    simpa [abs_mul, abs_of_pos Real.pi_pos] using hbase
  have hW_le : 2 * Real.pi * W ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
    exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans him_le
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hsmall_pos hW_le

private lemma perronHalfStep_eq_inv_mul_max {u : ℝ} (hu : u ≠ 0) :
    perronHalfStep u = (1 / u : ℂ) * ((max u 0 : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne hu with hu_neg | hu_pos
  · rw [perronHalfStep]
    simp [not_lt_of_ge hu_neg.le, hu, max_eq_right hu_neg.le]
  · rw [perronHalfStep, if_pos hu_pos, max_eq_left hu_pos.le]
    simpa [one_div] using (inv_mul_cancel₀ (ofReal_ne_zero.mpr hu)).symm

/-- Quantitative ordinary Perron inversion away from the jump.  Integration
by parts and the second-order truncation estimate give an explicit
`O(exp(c*u) / (|u| W))` error. -/
theorem norm_truncated_firstOrderPerron_sub_halfStep_le_of_ne_zero
    {c u W : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) -
        perronHalfStep u‖ ≤
      Real.exp (c * u) / (Real.pi ^ 2 * |u| * W) := by
  rw [intervalIntegral_firstOrderPerron_eq_boundary_add_secondOrder hc hu,
    perronHalfStep_eq_inv_mul_max hu]
  let B : ℂ :=
    (firstOrderBoundaryPrimitive c u W -
      firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u)
  let E : ℂ :=
    (1 / u : ℂ) *
      ((∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        ((max u 0 : ℝ) : ℂ))
  have hrewrite :
      (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
          ((2 * Real.pi * Complex.I) * u) +
        (1 / u : ℂ) *
          (∫ w : ℝ in (-W)..W,
            Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        (1 / u : ℂ) * ((max u 0 : ℝ) : ℂ) = B + E := by
    dsimp [B, E]
    ring
  rw [hrewrite]
  have hBW : ‖firstOrderBoundaryPrimitive c u W‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) :=
    norm_firstOrderBoundaryPrimitive_le hW (by simp [abs_of_pos hW])
  have hBnegW : ‖firstOrderBoundaryPrimitive c u (-W)‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) :=
    norm_firstOrderBoundaryPrimitive_le hW (by simp [abs_of_pos hW])
  have hB : ‖B‖ ≤ Real.exp (c * u) /
      (2 * Real.pi ^ 2 * |u| * W) := by
    dsimp [B]
    rw [norm_div]
    have hdennorm :
        ‖(2 * Real.pi * Complex.I) * (u : ℂ)‖ =
          2 * Real.pi * |u| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_real,
        norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [hdennorm]
    have hnum := (norm_sub_le _ _).trans (add_le_add hBW hBnegW)
    have hnum' : ‖firstOrderBoundaryPrimitive c u W -
        firstOrderBoundaryPrimitive c u (-W)‖ ≤
        Real.exp (c * u) / (Real.pi * W) := by
      calc
        ‖firstOrderBoundaryPrimitive c u W -
            firstOrderBoundaryPrimitive c u (-W)‖ ≤
            Real.exp (c * u) / (2 * Real.pi * W) +
              Real.exp (c * u) / (2 * Real.pi * W) := hnum
        _ = Real.exp (c * u) / (Real.pi * W) := by
          field_simp
          ring
    have hden_pos : 0 < 2 * Real.pi * |u| := by positivity
    calc
      ‖firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)‖ / (2 * Real.pi * |u|) ≤
          (Real.exp (c * u) / (Real.pi * W)) /
            (2 * Real.pi * |u|) := by
              exact div_le_div_of_nonneg_right hnum' hden_pos.le
      _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) := by
            field_simp
  have hE : ‖E‖ ≤ Real.exp (c * u) /
      (2 * Real.pi ^ 2 * |u| * W) := by
    dsimp [E]
    rw [norm_mul, norm_div, norm_one, norm_real, Real.norm_eq_abs]
    have hsecond := norm_truncated_secondOrderPerron_sub_max_le
      (c := c) (u := u) hc hW
    calc
      (1 / |u|) *
          ‖(∫ w : ℝ in (-W)..W,
            Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
            ((max u 0 : ℝ) : ℂ)‖ ≤
          (1 / |u|) * (Real.exp (c * u) /
            (2 * Real.pi ^ 2 * W)) :=
              mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) := by
            field_simp [abs_ne_zero.mpr hu]
  calc
    ‖B + E‖ ≤ ‖B‖ + ‖E‖ := norm_add_le _ _
    _ ≤ Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) +
        Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) :=
      add_le_add hB hE
    _ = Real.exp (c * u) / (Real.pi ^ 2 * |u| * W) := by
      field_simp
      ring

private lemma intervalIntegral_real_firstOrderPerron_zero
    {c W : ℝ} (hc : 0 < c) :
    (∫ w : ℝ in (-W)..W,
      c / (c ^ 2 + (2 * Real.pi * w) ^ 2)) =
        Real.arctan (2 * Real.pi * W / c) / Real.pi := by
  let f : ℝ → ℝ := fun x => (c ^ 2 + x ^ 2)⁻¹
  have hscale :
      (∫ w : ℝ in (-W)..W, f (2 * Real.pi * w)) =
        (2 * Real.pi)⁻¹ *
          (∫ x : ℝ in (2 * Real.pi * (-W))..(2 * Real.pi * W), f x) := by
    exact intervalIntegral.integral_comp_mul_left
      (a := -W) (b := W) f (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  calc
    (∫ w : ℝ in (-W)..W,
        c / (c ^ 2 + (2 * Real.pi * w) ^ 2)) =
        (∫ w : ℝ in (-W)..W, c * f (2 * Real.pi * w)) := by
      apply intervalIntegral.integral_congr
      intro w _hw
      simp [f, div_eq_mul_inv]
    _ = c * (∫ w : ℝ in (-W)..W, f (2 * Real.pi * w)) := by
      exact intervalIntegral.integral_const_mul
        (a := -W) (b := W) c (fun w => f (2 * Real.pi * w))
    _ = c * ((2 * Real.pi)⁻¹ *
        (∫ x : ℝ in (2 * Real.pi * (-W))..(2 * Real.pi * W), f x)) := by
      rw [hscale]
    _ = Real.arctan (2 * Real.pi * W / c) / Real.pi := by
      simp only [f, integral_inv_sq_add_sq hc.ne']
      rw [show 2 * Real.pi * (-W) / c = -(2 * Real.pi * W / c) by ring,
        Real.arctan_neg]
      field_simp [Real.pi_ne_zero, hc.ne']
      ring

private lemma intervalIntegral_im_firstOrderPerron_zero
    {c W : ℝ} :
    (∫ w : ℝ in (-W)..W,
      (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)) = 0 := by
  let g : ℝ → ℝ := fun w =>
    (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  have hodd : (fun w : ℝ => g (-w)) = fun w => -g w := by
    funext w
    dsimp [g]
    ring
  have hsym := intervalIntegral.integral_comp_neg
    (a := -W) (b := W) g
  have hneg : -(∫ w : ℝ in (-W)..W, g w) =
      (∫ w : ℝ in (-W)..W, g w) := by
    rw [hodd, intervalIntegral.integral_neg] at hsym
    simpa using hsym
  have hzero : (∫ w : ℝ in (-W)..W, g w) = 0 := by
    linarith
  simpa [g] using hzero

/-- At the discontinuity, the symmetric finite Perron integral is an arctangent
approximant.  Its limit is therefore exactly the standard half weight. -/
theorem intervalIntegral_firstOrderPerron_zero_eq
    {c W : ℝ} (hc : 0 < c) :
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * 0) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
  let r : ℝ → ℝ := fun w =>
    c / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  let g : ℝ → ℝ := fun w =>
    (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  have hden_real : ∀ w : ℝ,
      c ^ 2 + (2 * Real.pi * w) ^ 2 ≠ 0 := by
    intro w
    positivity
  have hrcont : Continuous r := by
    dsimp [r]
    exact (by fun_prop : Continuous fun _w : ℝ => c).div₀
      (by fun_prop) hden_real
  have hgcont : Continuous g := by
    dsimp [g]
    exact (by fun_prop : Continuous fun w : ℝ => 2 * Real.pi * w).div₀
      (by fun_prop) hden_real
  have hrint : IntervalIntegrable (fun w => (r w : ℂ)) volume (-W) W :=
    (Complex.continuous_ofReal.comp hrcont).intervalIntegrable _ _
  have hgint : IntervalIntegrable
      (fun w => Complex.I * (g w : ℂ)) volume (-W) W :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hgcont)).intervalIntegrable _ _
  calc
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * 0) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∫ w : ℝ in (-W)..W, (r w : ℂ) - Complex.I * (g w : ℂ) := by
      apply intervalIntegral.integral_congr
      intro w _hw
      have hden : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      simp only [mul_zero, Complex.exp_zero]
      dsimp [r, g]
      rw [one_div, Complex.inv_def]
      simp [Complex.normSq_apply]
      rw [starRingEnd_apply, star_ofNat]
      ring
    _ = (∫ w : ℝ in (-W)..W, (r w : ℂ)) -
        (∫ w : ℝ in (-W)..W, Complex.I * (g w : ℂ)) :=
      intervalIntegral.integral_sub hrint hgint
    _ = (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
      have hI :
          (∫ w : ℝ in (-W)..W, Complex.I * (g w : ℂ)) =
            Complex.I * (∫ w : ℝ in (-W)..W, (g w : ℂ)) := by
        exact intervalIntegral.integral_const_mul
          (a := -W) (b := W) Complex.I (fun w => (g w : ℂ))
      rw [hI]
      simp only [intervalIntegral.integral_ofReal]
      rw [intervalIntegral_real_firstOrderPerron_zero hc]
      rw [show (∫ w : ℝ in (-W)..W, g w) = 0 by
        simpa [g] using intervalIntegral_im_firstOrderPerron_zero (c := c) (W := W)]
      simp

lemma perronInt_eq_w (y c T : ℝ) (hy : 0 < y) :
    perronInt y c T = ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * (Real.log y : ℝ)) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) := by
  set f : ℝ → ℂ := fun t => Complex.exp (((c : ℂ) + (t : ℂ) * I) * (Real.log y : ℝ)) /
    ((c : ℂ) + (t : ℂ) * I) with hf
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h1 := intervalIntegral.integral_comp_mul_left (a := -(T / (2 * Real.pi)))
    (b := T / (2 * Real.pi)) f hπ
  have e1 : 2 * Real.pi * -(T / (2 * Real.pi)) = -T := by field_simp
  have e2 : 2 * Real.pi * (T / (2 * Real.pi)) = T := by field_simp
  rw [e1, e2] at h1
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hf' : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) = f := by
    funext t
    simp only [hf]
    rw [Complex.cpow_def_of_ne_zero hy', ← Complex.ofReal_log hy.le, mul_comm]
  unfold perronInt
  rw [hf']
  have : (∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * (Real.log y : ℝ)) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)), f (2 * Real.pi * w) := by
    congr 1; funext w; simp only [hf]; push_cast; ring_nf
  rw [this, h1, Complex.real_smul]
  push_cast
  ring

lemma delta_eq_halfStep (y : ℝ) (hy : 0 < y) : ((delta y : ℝ) : ℂ) = perronHalfStep (Real.log y) := by
  unfold delta perronHalfStep
  by_cases h1 : 1 < y
  · simp [h1, Real.log_pos h1]
  · by_cases h2 : y = 1
    · subst h2; simp
    · have h3 : y < 1 := lt_of_le_of_ne (not_lt.mp h1) h2
      have := Real.log_neg hy h3
      simp [h1, h2, this.ne, not_lt.mpr this.le]

theorem perron_kernel_log (y c T : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronInt y c T - delta y‖ ≤ y ^ c / (T * |Real.log y|) := by
  have hL : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hW : 0 < T / (2 * Real.pi) := by positivity
  have h := norm_truncated_firstOrderPerron_sub_halfStep_le_of_ne_zero (c := c) hc hL hW
  rw [perronInt_eq_w y c T hy, delta_eq_halfStep y hy]
  refine h.trans ?_
  have e : Real.exp (c * Real.log y) / (Real.pi ^ 2 * |Real.log y| * (T / (2 * Real.pi))) =
      y ^ c * 2 / (Real.pi * T * |Real.log y|) := by
    rw [Real.rpow_def_of_pos hy, mul_comm (Real.log y) c]
    field_simp
  rw [e]
  · have hLa : 0 < |Real.log y| := abs_pos.mpr hL
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := Real.pi_gt_three
    have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy c
    have : 0 < y ^ c * T * |Real.log y| := by positivity
    nlinarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## (P) Perron: pure analysis (the kernel) -/
alias perron_kernel_log := GuthMaynard.CitedZeros.Dav.PartA.perron_kernel_log

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
lemma integral_inv_line (c W : ℝ) (hc : 0 < c) :
    (∫ w : ℝ in (-W)..W, 1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
  rw [← intervalIntegral_firstOrderPerron_zero_eq (W := W) hc]
  simp

lemma perronInt_one_eq (c T : ℝ) (hc : 0 < c) :
    perronInt 1 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  rw [perronInt_eq_w 1 c T one_pos, Real.log_one]
  have h := integral_inv_line c (T / (2 * Real.pi)) hc
  have e : 2 * Real.pi * (T / (2 * Real.pi)) / c = T / c := by field_simp
  rw [e] at h
  rw [← h]
  congr 1
  funext w
  simp

lemma arctan_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h1 := Real.arctan_nonneg.mpr hx
  have h2 := Real.arctan_lt_pi_div_two x
  have := Real.le_tan h1 h2
  rwa [Real.tan_arctan] at this

theorem perron_kernel_one (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖perronInt 1 c T - delta 1‖ ≤ c / T := by
  rw [perronInt_one_eq c T hc]
  have hd : delta 1 = 1 / 2 := by simp [delta]
  rw [hd]
  have e : Real.arctan (T / c) = Real.pi / 2 - Real.arctan (c / T) := by
    rw [← Real.arctan_inv_of_pos (by positivity), inv_div]
  have : ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) =
      ((-(Real.arctan (c / T) / Real.pi) : ℝ) : ℂ) := by
    rw [e]; push_cast; field_simp; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have h0 : 0 ≤ Real.arctan (c / T) := Real.arctan_nonneg.mpr (by positivity)
  rw [abs_of_nonneg (by positivity)]
  have h1 := arctan_le_self' (le_of_lt (by positivity : 0 < c / T))
  rw [div_le_iff₀ Real.pi_pos]
  have : 0 < c / T := by positivity
  nlinarith [Real.pi_gt_three]

lemma perronInt_norm_le (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronInt y c T‖ ≤ y ^ c * (1 / 2 + T * |Real.log y| / Real.pi) := by
  rw [perronInt_eq_w y c T hy]
  set L := Real.log y
  set W := T / (2 * Real.pi) with hWdef
  have hW : 0 < W := by positivity
  have hden : ∀ w : ℝ, (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro w h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  set h : ℝ → ℂ := fun w => (Complex.exp (Complex.I * ((2 * Real.pi * w * L : ℝ) : ℂ)) - 1) /
    ((c : ℂ) + 2 * Real.pi * w * Complex.I) with hh
  have hsplit : ∀ w : ℝ, Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * (L : ℝ)) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) =
      Complex.exp ((c * L : ℝ) : ℂ) * (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) + h w) := by
    intro w
    have e : ((c : ℂ) + 2 * Real.pi * w * Complex.I) * (L : ℝ) =
        ((c * L : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * w * L : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.exp_add]
    simp only [hh]
    field_simp [hden w]
    ring
  have hc1 : Continuous fun w : ℝ => 1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) :=
    continuous_const.div (by fun_prop) hden
  have hc2 : Continuous h := by
    rw [hh]
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  simp_rw [hsplit]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _), integral_inv_line c W hc]
  rw [norm_mul, Complex.norm_exp, Complex.ofReal_re, mul_comm c L, ← Real.rpow_def_of_pos hy]
  have hyc : 0 ≤ y ^ c := (Real.rpow_pos_of_pos hy c).le
  refine mul_le_mul_of_nonneg_left ?_ hyc
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · rw [div_le_iff₀ Real.pi_pos]
      linarith [Real.arctan_lt_pi_div_two (2 * Real.pi * W / c)]
    · exact div_nonneg (Real.arctan_nonneg.mpr (by positivity)) Real.pi_pos.le
  · have hb : ∀ w ∈ Set.uIoc (-W) W, ‖h w‖ ≤ |L| := by
      intro w _
      rw [hh]
      dsimp only
      rw [norm_div]
      have hpos : 0 < ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := norm_pos_iff.mpr (hden w)
      rw [div_le_iff₀ hpos]
      have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * w * L)
      have h2 : |2 * Real.pi * w| ≤ ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
        have := Complex.abs_im_le_norm ((c : ℂ) + 2 * Real.pi * w * Complex.I)
        simpa using this
      rw [Real.norm_eq_abs, abs_mul] at h1
      nlinarith [abs_nonneg L]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    refine this.trans (le_of_eq ?_)
    rw [show W - -W = 2 * W by ring, abs_of_pos (show (0:ℝ) < 2 * W by linarith), hWdef]
    field_simp

theorem perron_kernel_unif : ∃ K : ℝ, 0 ≤ K ∧ ∀ y c T : ℝ, 0 < y → y ≠ 1 → 0 < c → 0 < T →
    ‖perronInt y c T - delta y‖ ≤ K * y ^ c := by
  refine ⟨2, by norm_num, fun y c T hy hy1 hc hT => ?_⟩
  have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hL : 0 < |Real.log y| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
  rcases le_or_gt 1 (T * |Real.log y|) with h1 | h1
  · refine (perron_kernel_log y c T hy hy1 hc hT).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have hn := perronInt_norm_le y c T hy hc hT
    have hd : ‖((delta y : ℝ) : ℂ)‖ ≤ y ^ c := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold delta
      by_cases h : 1 < y
      · simp only [h, if_true, abs_one]; exact Real.one_le_rpow h.le hc.le
      · simp only [h, hy1, if_false, abs_zero]; exact hyc.le
    have hp := Real.pi_gt_three
    have : T * |Real.log y| / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith
    calc ‖perronInt y c T - delta y‖ ≤ ‖perronInt y c T‖ + ‖((delta y : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ y ^ c * (1 / 2 + 1 / 2) + y ^ c := by
          have := mul_le_mul_of_nonneg_left
            (by linarith : 1 / 2 + T * |Real.log y| / Real.pi ≤ 1 / 2 + 1 / 2) hyc.le
          linarith
      _ = 2 * y ^ c := by ring

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias perron_kernel_unif := GuthMaynard.CitedZeros.Dav.PartA.perron_kernel_unif

alias perron_kernel_one := GuthMaynard.CitedZeros.Dav.PartA.perron_kernel_one

lemma half_le_log {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ Real.log x := by
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hx
  norm_num at *; linarith

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-!
# Davenport's truncated explicit formula, Part B

Zeros of ζ, local principal parts of `F`, the rectangle residue theorem and the residue identity;
Perron interchange and arithmetic; good heights; the passage from `T'` back to `T`.
-/
/-! ## Zeros of ζ -/
theorem zeta_zero_cases (s : ℂ) (hs : riemannZeta s = 0) :
    (0 < s.re ∧ s.re < 1) ∨ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  by_cases h1 : 1 ≤ s.re
  · exact absurd hs (riemannZeta_ne_zero_of_one_le_re h1)
  by_cases h0 : 0 < s.re
  · exact Or.inl ⟨h0, by linarith⟩
  right
  push Not at h0 h1
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by simp [hw]; linarith
  have hn : ∀ n : ℕ, w ≠ -n := by
    intro n hn; have := congrArg Complex.re hn; simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hw1 : w ≠ 1 := by intro h; apply hs0; rw [hw] at h; linear_combination -h
  have hfe := riemannZeta_one_sub hn hw1
  rw [hw, sub_sub_cancel, ← hw, hs] at hfe
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hn
  have hp : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    intro h0; exfalso
    exact (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) h0
  have hc : Complex.cos (↑Real.pi * w / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp) hG) hc) hz) hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw' : w = 2 * (k : ℂ) + 1 := by
    apply mul_left_cancel₀ hpi; linear_combination 2 * hk
  have hsk : s = -2 * (k : ℂ) := by rw [hw] at hw'; linear_combination -hw'
  have hk1 : 1 ≤ k := by
    by_contra hk1; push Not at hk1
    have hk0 : k ≤ 0 := by omega
    rcases lt_or_eq_of_le hk0 with hk0 | hk0
    · have := congrArg Complex.re hsk; simp at this
      have : (k : ℝ) < 0 := by exact_mod_cast hk0
      linarith
    · apply hs0; rw [hsk, hk0]; simp
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have h' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) this; push_cast at this; exact this
  rw [h', hsk]; ring

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias zeta_zero_cases := GuthMaynard.CitedZeros.Dav.PartB.zeta_zero_cases

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-! ## from Digamma -/
/-- The remainder after subtracting `1` from an elementary factor in the
canonical product for `1 / Gamma`. -/
noncomputable def gammaCanonicalRemainder (n : ℕ) (z : ℂ) : ℂ :=
  (1 + z / (n + 1)) * Complex.exp (-z / (n + 1)) - 1

/-- The elementary factor in the canonical product for `1 / Gamma`. -/
noncomputable def gammaCanonicalFactor (n : ℕ) (z : ℂ) : ℂ :=
  1 + gammaCanonicalRemainder n z

private theorem norm_gammaCanonicalFactor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(1 + u) * Complex.exp (-u) - 1‖ ≤ 3 * ‖u‖ ^ 2 := by
  have hneg : ‖-u‖ ≤ 1 := by simpa using hu
  have hrem : ‖Complex.exp (-u) - 1 - (-u)‖ ≤ ‖u‖ ^ 2 := by
    simpa using Complex.norm_exp_sub_one_sub_id_le hneg
  have hlin : ‖Complex.exp (-u) - 1‖ ≤ 2 * ‖u‖ := by
    simpa using Complex.norm_exp_sub_one_le hneg
  rw [show (1 + u) * Complex.exp (-u) - 1 =
      (Complex.exp (-u) - 1 - (-u)) -
        (-u) * (Complex.exp (-u) - 1) by ring]
  calc
    _ ≤ ‖Complex.exp (-u) - 1 - (-u)‖ +
        ‖(-u) * (Complex.exp (-u) - 1)‖ := norm_sub_le _ _
    _ ≤ ‖u‖ ^ 2 + ‖u‖ * (2 * ‖u‖) := by
      rw [norm_mul, norm_neg]
      exact add_le_add hrem (mul_le_mul_of_nonneg_left hlin (norm_nonneg _))
    _ = 3 * ‖u‖ ^ 2 := by ring

private theorem gammaCanonicalFactor_bound_aux {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖gammaCanonicalRemainder n z‖ ≤ u n := by
  have hf : ContinuousOn (fun z : ℂ => ‖z‖) K := by fun_prop
  obtain ⟨M, hM⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hK hf)
  let A : ℝ := 3 * |M| ^ 2
  refine ⟨fun n : ℕ => ‖(A : ℂ) / ((n : ℂ) + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (A : ℂ) 2 1 one_lt_two
  · filter_upwards [eventually_ge_atTop ⌈|M|⌉₊] with n hn z hz
    have hzM : ‖z‖ ≤ |M| := (hM ‖z‖ ⟨z, hz, rfl⟩).trans (le_abs_self M)
    have hMn : |M| ≤ (n + 1 : ℝ) := by
      have hceil : |M| ≤ (⌈|M|⌉₊ : ℝ) := Nat.le_ceil |M|
      exact hceil.trans (by exact_mod_cast hn.trans (Nat.le_succ n))
    have hden : 0 < (n + 1 : ℝ) := by positivity
    have hu : ‖z / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (div_le_one hden).mpr (hzM.trans hMn)
    have hmain := norm_gammaCanonicalFactor_sub_one_le hu
    rw [gammaCanonicalRemainder]
    have hmain' :
        ‖(1 + z / ((n : ℂ) + 1)) * Complex.exp (-z / ((n : ℂ) + 1)) - 1‖ ≤
          3 * ‖z / ((n : ℂ) + 1)‖ ^ 2 := by
      simpa [Nat.cast_add, Nat.cast_one, neg_div] using hmain
    refine hmain'.trans ?_
    have hA : 0 ≤ A := by dsimp [A]; positivity
    simp only [norm_div, norm_pow]
    rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
        rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      show ‖(A : ℂ)‖ = A by simpa using abs_of_nonneg hA]
    dsimp [A]
    have hsq : ‖z‖ ^ 2 ≤ |M| ^ 2 := by nlinarith [norm_nonneg z, abs_nonneg M]
    have hden0 : 0 ≤ (n + 1 : ℝ) ^ 2 := sq_nonneg _
    calc
      3 * (‖z‖ / (n + 1 : ℝ)) ^ 2 =
          3 * ‖z‖ ^ 2 / (n + 1 : ℝ) ^ 2 := by
        field_simp [hden.ne']
      _ ≤ 3 * |M| ^ 2 / (n + 1 : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) hden0
      _ = 3 * |M| ^ 2 / ((n : ℝ) + 1) ^ 2 := rfl

theorem multipliableLocallyUniformlyOn_gammaCanonicalFactor :
    MultipliableLocallyUniformlyOn gammaCanonicalFactor Set.univ := by
  refine ⟨fun z => ∏' n, gammaCanonicalFactor n z, ?_⟩
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  obtain ⟨u, hu, hbound⟩ := gammaCanonicalFactor_bound_aux hcompact
  exact Summable.hasProdUniformlyOn_nat_one_add hcompact hu hbound fun n => by
    change ContinuousOn (fun z : ℂ =>
      (1 + z / (n + 1)) * Complex.exp (-z / (n + 1)) - 1) K
    fun_prop

private theorem prod_gammaCanonicalFactor_eq (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, gammaCanonicalFactor j z) =
      (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
        Complex.exp (-((harmonic n : ℚ) : ℂ) * z) := by
  induction n with
  | zero => simp [harmonic_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, harmonic_succ]
      simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
      rw [show -((((harmonic n + (↑(n + 1))⁻¹ : ℚ) : ℂ))) * z =
          -((harmonic n : ℚ) : ℂ) * z + -z / ((n + 1 : ℕ) : ℂ) by
        have hk : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        push_cast
        field_simp [hk]
        ring]
      rw [Complex.exp_add]
      push_cast
      ring

private theorem prod_one_add_div_eq (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) =
      (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ((Nat.factorial n : ℕ) : ℂ) := by
  calc
    (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) =
        ∏ j ∈ Finset.range n,
          (z + ((j + 1 : ℕ) : ℂ)) / ((j + 1 : ℕ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _hj
      have hj : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero j
      field_simp [hj]
      ring
    _ = (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ∏ j ∈ Finset.range n, (((j + 1 : ℕ) : ℂ)) :=
      Finset.prod_div_distrib _ _
    _ = (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ((Nat.factorial n : ℕ) : ℂ) := by
      congr 1
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

private theorem prod_range_gamma_shift (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) =
      z * ∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ)) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  ring

private theorem inv_GammaSeq_mul_cpow_eq
    {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    (Complex.GammaSeq z n)⁻¹ * (n : ℂ) ^ z =
      z * ∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hpow : (n : ℂ) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hfac : (((Nat.factorial n : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hshift :
      (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjpos : 0 < (j + 1 : ℝ) := by positivity
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  rw [Complex.GammaSeq, prod_range_gamma_shift, prod_one_add_div_eq]
  field_simp [hz0, hpow, hfac, hshift]

private theorem canonicalPartialProduct_eq
    {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏ j ∈ Finset.range n, gammaCanonicalFactor j z) =
      (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + Real.log n) * z) := by
  rw [prod_gammaCanonicalFactor_eq]
  have hseq := inv_GammaSeq_mul_cpow_eq hz hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcpow : (n : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [hncast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  calc
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        ((∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) =
      (z * ∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
        (Complex.exp (Real.eulerMascheroniConstant * z) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) := by ring
    _ = ((Complex.GammaSeq z n)⁻¹ * (n : ℂ) ^ z) *
        (Complex.exp (Real.eulerMascheroniConstant * z) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) := by rw [hseq]
    _ = (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + Real.log n) * z) := by
      rw [hcpow, ← Complex.exp_add]
      rw [show (Complex.GammaSeq z n)⁻¹ *
          Complex.exp ((Real.log n : ℂ) * z) *
            Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z +
              -((harmonic n : ℚ) : ℂ) * z) =
          (Complex.GammaSeq z n)⁻¹ *
            (Complex.exp ((Real.log n : ℂ) * z) *
              Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z +
                -((harmonic n : ℚ) : ℂ) * z)) by ring]
      rw [← Complex.exp_add]
      congr 2
      ring

/-- Weierstrass' canonical product for the reciprocal Gamma function, on the
right half-plane where Euler's `GammaSeq` limit can be used directly. -/
theorem gammaCanonicalProduct_eq_one_div_Gamma {z : ℂ} (hz : 0 < z.re) :
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏' n : ℕ, gammaCanonicalFactor n z) = (Complex.Gamma z)⁻¹ := by
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hm :=
    multipliableLocallyUniformlyOn_gammaCanonicalFactor.multipliable
      (Set.mem_univ z)
  have hprod : Tendsto
      (fun n : ℕ => ∏ j ∈ Finset.range n, gammaCanonicalFactor j z)
      atTop (𝓝 (∏' j : ℕ, gammaCanonicalFactor j z)) :=
    (hm.hasProd_iff_tendsto_nat).mp ((hm.hasProd_iff).mpr rfl)
  have hleft : Tendsto
      (fun n : ℕ => z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏ j ∈ Finset.range n, gammaCanonicalFactor j z))
      atTop (𝓝 (z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏' j : ℕ, gammaCanonicalFactor j z))) :=
    (tendsto_const_nhds.mul tendsto_const_nhds).mul hprod
  have hcReal : Tendsto
      (fun n : ℕ => Real.eulerMascheroniConstant -
        (harmonic n : ℝ) + Real.log n) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => Real.eulerMascheroniConstant)
        atTop (𝓝 Real.eulerMascheroniConstant) := tendsto_const_nhds
    have h := hconst.sub Real.tendsto_harmonic_sub_log
    convert h using 1
    all_goals ring
  have hc : Tendsto
      (fun n : ℕ => (Real.eulerMascheroniConstant : ℂ) -
        ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h : Tendsto
        (fun n : ℕ => (((Real.eulerMascheroniConstant -
          (harmonic n : ℝ) + Real.log n) : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hcReal
    convert h using 1
    funext n
    push_cast
    rfl
  have hexp : Tendsto
      (fun n : ℕ => Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
        ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z))
      atTop (𝓝 1) := by
    have hmul : Tendsto
        (fun n : ℕ => ((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z)
        atTop (𝓝 0) := by
      simpa only [zero_mul] using hc.mul_const z
    have h := (Complex.continuous_exp.tendsto 0).comp hmul
    convert h using 1
    all_goals simp [Complex.exp_zero, Function.comp_def]
  have hright : Tendsto
      (fun n : ℕ => (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z))
      atTop (𝓝 ((Complex.Gamma z)⁻¹)) := by
    simpa using (Complex.GammaSeq_tendsto_Gamma z).inv₀ hGamma |>.mul hexp
  have hright' := hright.congr' (by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (canonicalPartialProduct_eq hz hn).symm)
  exact tendsto_nhds_unique hleft hright'

/-- The summand in Gauss' series for the digamma function. -/
noncomputable def digammaGaussTerm (z : ℂ) (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹

private theorem digammaGaussTerm_eq {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    digammaGaussTerm z n =
      z / (((n + 1 : ℕ) : ℂ) * (z + ((n + 1 : ℕ) : ℂ))) := by
  have hk : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hzk : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  simp only [digammaGaussTerm]
  field_simp [hk, hzk]
  ring

theorem norm_digammaGaussTerm_le_one_div
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖digammaGaussTerm z n‖ ≤ 1 / (n + 1 : ℝ) := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hnorm : ‖z‖ ≤ ‖z + k‖ := by
    apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + k))).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, k]
    nlinarith
  rw [digammaGaussTerm_eq hz, norm_div, norm_mul]
  rw [show ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) by
    rw [Complex.norm_natCast]
    norm_num]
  have hzkpos : 0 < ‖z + k‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [k] at hre
    linarith
  calc
    ‖z‖ / ((n + 1 : ℝ) * ‖z + k‖) ≤
        ‖z + k‖ / ((n + 1 : ℝ) * ‖z + k‖) :=
      div_le_div_of_nonneg_right hnorm (by positivity)
    _ = 1 / (n + 1 : ℝ) := by field_simp [hkpos.ne', hzkpos.ne']

theorem norm_digammaGaussTerm_le_norm_div_sq
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖digammaGaussTerm z n‖ ≤ ‖z‖ / (n + 1 : ℝ) ^ 2 := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hkNorm : (n + 1 : ℝ) ≤ ‖z + k‖ := by
    have hre : (n + 1 : ℝ) ≤ (z + k).re := by
      dsimp [k]
      simp
      exact hz.le
    exact hre.trans (le_abs_self _ |>.trans (Complex.abs_re_le_norm _))
  rw [digammaGaussTerm_eq hz, norm_div, norm_mul]
  rw [show ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) by
    rw [Complex.norm_natCast]
    norm_num]
  dsimp [k] at hkNorm
  push_cast at hkNorm
  exact div_le_div_of_nonneg_left (norm_nonneg z) (sq_pos_of_pos hkpos)
    (by simpa [pow_two] using mul_le_mul_of_nonneg_left hkNorm hkpos.le)

private theorem gammaCanonicalFactor_ne_zero
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) : gammaCanonicalFactor n z ≠ 0 := by
  have hlin : 1 + z / (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : 1 + z.re / (n + 1 : ℝ) = 0 := by
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      rw [show ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num,
        Complex.div_ofReal_re] at hre
      simpa only [Nat.cast_add, Nat.cast_one] using hre
    have : 0 < 1 + z.re / (n + 1 : ℝ) := by positivity
    exact this.ne' hre'
  rw [show gammaCanonicalFactor n z =
      (1 + z / (((n + 1 : ℕ) : ℂ))) *
        Complex.exp (-z / (((n + 1 : ℕ) : ℂ))) by
    simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
    push_cast
    ring]
  exact mul_ne_zero hlin (Complex.exp_ne_zero _)

private theorem logDeriv_gammaCanonicalFactor
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    logDeriv (gammaCanonicalFactor n) z = -digammaGaussTerm z n := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast Nat.succ_ne_zero n
  have hlin : 1 + z / k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : 1 + z.re / (n + 1 : ℝ) = 0 := by
      dsimp [k] at hre
      rw [show ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num,
        Complex.div_ofReal_re] at hre
      simpa only [Nat.cast_add, Nat.cast_one] using hre
    have hkpos : 0 < (n + 1 : ℝ) := by positivity
    have : 0 < 1 + z.re / (n + 1 : ℝ) := by positivity
    exact this.ne' hre'
  have hfactor : gammaCanonicalFactor n =
      fun w : ℂ => (1 + w / k) * Complex.exp (-w / k) := by
    funext w
    simp [gammaCanonicalFactor, gammaCanonicalRemainder, k]
  rw [hfactor, logDeriv_mul
    (f := fun w : ℂ => 1 + w / k)
    (g := fun w : ℂ => Complex.exp (-w / k))
    z hlin (Complex.exp_ne_zero _) (by fun_prop) (by fun_prop)]
  simp only [logDeriv_apply]
  rw [show deriv (fun w : ℂ => 1 + w / k) z = 1 / k by
      convert ((hasDerivAt_const z 1).add ((hasDerivAt_id z).div_const k)).deriv using 1
      all_goals simp]
  rw [show deriv (fun w : ℂ => Complex.exp (-w / k)) z =
      (-1 / k) * Complex.exp (-z / k) by
      convert (((hasDerivAt_neg z).div_const k).cexp).deriv using 1
      all_goals ring]
  simp only [digammaGaussTerm]
  field_simp [hk, hlin]
  ring

theorem summable_digammaGaussTerm {z : ℂ} (hz : 0 < z.re) :
    Summable (digammaGaussTerm z) := by
  have hmajor := summable_pow_div_add z 2 1 one_lt_two
  apply Summable.of_norm_bounded hmajor
  intro n
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast Nat.succ_ne_zero n
  have hzk : z + k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [k] at hre
    simp at hre
    linarith
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hkNorm : (n + 1 : ℝ) ≤ ‖z + k‖ := by
    have hre : (n + 1 : ℝ) ≤ (z + k).re := by
      dsimp [k]
      simp
      exact hz.le
    exact hre.trans (le_abs_self _ |>.trans (Complex.abs_re_le_norm _))
  rw [show digammaGaussTerm z n = z / (k * (z + k)) by
    change k⁻¹ - (z + k)⁻¹ = z / (k * (z + k))
    field_simp [hk, hzk]
    ring]
  rw [norm_div, norm_mul]
  have hden : 0 < (n + 1 : ℝ) ^ 2 := sq_pos_of_pos hkpos
  have hbound :
      ‖z‖ / (‖k‖ * ‖z + k‖) ≤ ‖z‖ / (n + 1 : ℝ) ^ 2 := by
    rw [show ‖k‖ = (n + 1 : ℝ) by
      dsimp [k]
      rw [Complex.norm_natCast]
      norm_num]
    exact div_le_div_of_nonneg_left (norm_nonneg z) hden
      (by simpa [pow_two] using mul_le_mul_of_nonneg_left hkNorm hkpos.le)
  refine hbound.trans_eq ?_
  rw [norm_div, norm_pow]
  congr 2
  have hnorm : ‖(n : ℂ) + (1 : ℂ)‖ = (n : ℝ) + 1 := by
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  convert hnorm.symm using 1
  all_goals norm_num

/-- The reciprocal-square tail used when splitting Gauss' digamma series at
a positive natural cutoff. -/
theorem tsum_one_div_nat_add_sq_le {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / (N + n : ℝ)
  let g : ℕ → ℝ := fun n => f n - f (n + 1)
  have hdenTop : Tendsto (fun n : ℕ => (N + n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono'
      (l := atTop) (f₁ := fun n : ℕ => (n : ℝ))
    · exact Eventually.of_forall fun n => by
        norm_num
    · exact tendsto_natCast_atTop_atTop
  have hf0 : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    exact tendsto_const_nhds.div_atTop hdenTop
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g, f]
    have hpos : 0 < (N + n : ℝ) := by positivity
    have hle : (N + n : ℝ) ≤ N + (n + 1 : ℕ) := by
      norm_num
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpos hle)
  have hgHas : HasSum g (1 / (N : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg_nonneg]
    have htel : (fun m : ℕ => ∑ n ∈ Finset.range m, g n) =
        fun m => f 0 - f m := by
      funext m
      exact Finset.sum_range_sub' f m
    rw [htel]
    simpa [f] using hf0.const_sub (1 / (N : ℝ))
  have hp : Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 2) := by
    have h := summable_pow_div_add (1 : ℝ) 2 (N + 1) one_lt_two
    apply h.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    congr 2
    push_cast
    ring
  have hpoint : ∀ n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2 ≤ g n := by
    intro n
    dsimp [g, f]
    have hA : 0 < (N + n : ℝ) := by positivity
    have hB : 0 < (N + n + 1 : ℝ) := by positivity
    have hgEq :
        1 / (N + n : ℝ) - 1 / (N + (n + 1 : ℕ) : ℝ) =
          1 / ((N + n : ℝ) * (N + n + 1 : ℝ)) := by
      push_cast
      field_simp [hA.ne', hB.ne']
      ring
    rw [hgEq]
    apply one_div_le_one_div_of_le (mul_pos hA hB)
    nlinarith
  calc
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) ≤ ∑' n : ℕ, g n :=
      Summable.tsum_le_tsum hpoint hp hgHas.summable
    _ = 1 / (N : ℝ) := hgHas.tsum_eq

theorem summable_norm_digammaGaussTerm {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => ‖digammaGaussTerm z n‖) := by
  have hmajorC := summable_pow_div_add z 2 1 one_lt_two
  have hmajor : Summable (fun n : ℕ => ‖z‖ / (n + 1 : ℝ) ^ 2) := by
    apply hmajorC.congr
    intro n
    rw [norm_div, norm_pow]
    have hnorm : ‖(n : ℂ) + (1 : ℂ)‖ = (n : ℝ) + 1 := by
      rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    norm_num only [Nat.cast_one]
    rw [hnorm]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_digammaGaussTerm_le_norm_div_sq hz n) hmajor

theorem norm_tsum_digammaGaussTerm_le {z : ℂ} (hz : 0 < z.re)
    {N : ℕ} (hN : 0 < N) :
    ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
      (harmonic N : ℝ) + ‖z‖ / (N : ℝ) := by
  have hsNorm := summable_norm_digammaGaussTerm hz
  have hnormTsum := norm_tsum_le_tsum_norm hsNorm
  have hsplit := hsNorm.sum_add_tsum_nat_add N
  have hfinite :
      (∑ n ∈ Finset.range N, ‖digammaGaussTerm z n‖) ≤ (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) := by
        exact Finset.sum_le_sum fun n _hn => norm_digammaGaussTerm_le_one_div hz n
      _ = (harmonic N : ℝ) := by
        rw [harmonic]
        push_cast
        simp [one_div]
  have hsTail : Summable
      (fun n : ℕ => ‖digammaGaussTerm z (n + N)‖) :=
    (summable_nat_add_iff N).mpr hsNorm
  have hpTail : Summable
      (fun n : ℕ => ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2)) := by
    have hp := summable_pow_div_add (1 : ℝ) 2 (N + 1) one_lt_two
    have hp' : Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 2) := by
      apply hp.congr
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      congr 2
      push_cast
      ring
    exact hp'.mul_left ‖z‖
  have htail :
      (∑' n : ℕ, ‖digammaGaussTerm z (n + N)‖) ≤
        ‖z‖ / (N : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2) := by
        apply Summable.tsum_le_tsum _ hsTail hpTail
        intro n
        have h := norm_digammaGaussTerm_le_norm_div_sq hz (n + N)
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc, div_eq_mul_inv] using h
      _ = ‖z‖ * (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) := tsum_mul_left
      _ ≤ ‖z‖ * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (tsum_one_div_nat_add_sq_le hN) (norm_nonneg z)
      _ = ‖z‖ / (N : ℝ) := by ring
  calc
    ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
        ∑' n : ℕ, ‖digammaGaussTerm z n‖ := hnormTsum
    _ = (∑ n ∈ Finset.range N, ‖digammaGaussTerm z n‖) +
        ∑' n : ℕ, ‖digammaGaussTerm z (n + N)‖ := hsplit.symm
    _ ≤ (harmonic N : ℝ) + ‖z‖ / (N : ℝ) := add_le_add hfinite htail

/-- Gauss' convergent series for the complex digamma function on the right
half-plane.  This supplies the representation missing from Mathlib's current
`Digamma` module. -/
theorem digamma_eq_gauss_series {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      -Real.eulerMascheroniConstant - z⁻¹ + ∑' n : ℕ, digammaGaussTerm z n := by
  let P : ℂ → ℂ := fun w => ∏' n : ℕ, gammaCanonicalFactor n w
  let F : ℂ → ℂ := fun w =>
    w * Complex.exp (Real.eulerMascheroniConstant * w) * P w
  let G : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hPne : P z ≠ 0 := by
    intro hzero
    have hproduct := gammaCanonicalProduct_eq_one_div_Gamma hz
    apply inv_ne_zero hGamma
    rw [← hproduct]
    simp [P, hzero]
  have hPdiff : DifferentiableAt ℂ P z := by
    have hloc :=
      multipliableLocallyUniformlyOn_gammaCanonicalFactor.hasProdLocallyUniformlyOn
        |>.tendstoLocallyUniformlyOn_finsetRange
    have hdiff : DifferentiableOn ℂ P Set.univ := by
      apply hloc.differentiableOn _ isOpen_univ
      filter_upwards with n
      apply Differentiable.differentiableOn
      apply Differentiable.fun_finset_prod
      intro i _hi
      rw [show gammaCanonicalFactor i = fun w : ℂ =>
          (1 + w / ((i + 1 : ℕ) : ℂ)) *
            Complex.exp (-w / ((i + 1 : ℕ) : ℂ)) by
        funext w
        simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
        push_cast
        ring]
      fun_prop
    exact hdiff.differentiableAt Filter.univ_mem
  have hsumLD : Summable
      (fun n : ℕ => logDeriv (gammaCanonicalFactor n) z) := by
    apply (summable_digammaGaussTerm hz).neg.congr
    intro n
    exact (logDeriv_gammaCanonicalFactor hz n).symm
  have hlogP : logDeriv P z =
      ∑' n : ℕ, logDeriv (gammaCanonicalFactor n) z := by
    dsimp [P]
    apply logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    · exact gammaCanonicalFactor_ne_zero hz
    · intro n
      apply Differentiable.differentiableOn
      rw [show gammaCanonicalFactor n = fun w : ℂ =>
          (1 + w / ((n + 1 : ℕ) : ℂ)) *
            Complex.exp (-w / ((n + 1 : ℕ) : ℂ)) by
        funext w
        simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
        push_cast
        ring]
      fun_prop
    · exact hsumLD
    · exact multipliableLocallyUniformlyOn_gammaCanonicalFactor
    · exact hPne
  have htsum :
      (∑' n : ℕ, logDeriv (gammaCanonicalFactor n) z) =
        -(∑' n : ℕ, digammaGaussTerm z n) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    exact logDeriv_gammaCanonicalFactor hz n
  have hnhds : {w : ℂ | 0 < w.re} ∈ 𝓝 z := by
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have heq : F =ᶠ[𝓝 z] G := by
    filter_upwards [hnhds] with w hw
    exact gammaCanonicalProduct_eq_one_div_Gamma hw
  have hlogEq : logDeriv F z = logDeriv G z := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  have hexpLog :
      logDeriv (fun w : ℂ =>
        Complex.exp (Real.eulerMascheroniConstant * w)) z =
        Real.eulerMascheroniConstant := by
    change logDeriv (Complex.exp ∘
      fun w : ℂ => Real.eulerMascheroniConstant * w) z = _
    rw [logDeriv_comp Complex.differentiableAt_exp (by fun_prop),
      Complex.logDeriv_exp]
    rw [show deriv (fun w : ℂ => Real.eulerMascheroniConstant * w) z =
        (Real.eulerMascheroniConstant : ℂ) by
      convert ((hasDerivAt_id z).const_mul
        (Real.eulerMascheroniConstant : ℂ)).deriv using 1
      all_goals simp]
    simp
  have hlogF : logDeriv F z =
      z⁻¹ + Real.eulerMascheroniConstant + logDeriv P z := by
    dsimp [F]
    rw [logDeriv_mul
      (f := fun w : ℂ => w *
        Complex.exp (Real.eulerMascheroniConstant * w))
      (g := P) z
      (mul_ne_zero hz0 (Complex.exp_ne_zero _)) hPne
      ((differentiableAt_id.mul (by fun_prop))) hPdiff]
    rw [logDeriv_mul
      (f := fun w : ℂ => w)
      (g := fun w : ℂ => Complex.exp (Real.eulerMascheroniConstant * w))
      z hz0 (Complex.exp_ne_zero _)
      differentiableAt_id (by fun_prop), logDeriv_id', hexpLog]
    simp only [one_div]
  have hGdiff : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      linarith)
  have hlogG : logDeriv G z = -Complex.digamma z := by
    dsimp [G]
    change logDeriv ((fun w : ℂ => w⁻¹) ∘ Complex.Gamma) z = _
    rw [logDeriv_comp (differentiableAt_inv hGamma) hGdiff,
      logDeriv_inv, Complex.digamma_def]
    rw [logDeriv_apply]
    ring
  rw [hlogF, hlogP, htsum, hlogG] at hlogEq
  linear_combination hlogEq

/-- A quantitative logarithmic-growth bound for digamma on `Re z >= 1`.
The constants are deliberately coarse; the logarithmic dependence is the
feature needed for contour decay. -/
theorem norm_digamma_le_log {z : ℂ} (hz : 1 ≤ z.re) :
    ‖Complex.digamma z‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 + Real.log (‖z‖ + 1) := by
  have hzpos : 0 < z.re := zero_lt_one.trans_le hz
  have hnormz : 1 ≤ ‖z‖ := by
    exact hz.trans (le_abs_self z.re |>.trans (Complex.abs_re_le_norm z))
  let N : ℕ := ⌈‖z‖⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (zero_lt_one.trans_le hnormz)
  have hzN : ‖z‖ ≤ (N : ℝ) := by
    exact Nat.le_ceil ‖z‖
  have hratio : ‖z‖ / (N : ℝ) ≤ 1 := by
    exact (div_le_one (Nat.cast_pos.mpr hN)).mpr hzN
  have hNlt : (N : ℝ) < ‖z‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg z)
  have hlogN : Real.log (N : ℝ) ≤ Real.log (‖z‖ + 1) := by
    exact (Real.strictMonoOn_log.le_iff_le
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hN))
      (Set.mem_Ioi.mpr (by positivity))).mpr hNlt.le
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log (‖z‖ + 1) := by
    exact (harmonic_le_one_add_log N).trans (by linarith)
  have hseries : ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
      2 + Real.log (‖z‖ + 1) := by
    exact (norm_tsum_digammaGaussTerm_le hzpos hN).trans (by linarith)
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hnormz
  rw [digamma_eq_gauss_series hzpos]
  calc
    ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
        ∑' n : ℕ, digammaGaussTerm z n‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ +
        ‖∑' n : ℕ, digammaGaussTerm z n‖ := by
      calc
        _ ≤ ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹‖ +
            ‖∑' n : ℕ, digammaGaussTerm z n‖ := norm_add_le _ _
        _ ≤ (‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖) +
            ‖∑' n : ℕ, digammaGaussTerm z n‖ := by
          apply add_le_add _ le_rfl
          calc
            ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹‖ ≤
                ‖-(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ :=
              norm_sub_le _ _
            _ = ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ := by
              rw [norm_neg]
    _ ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (‖z‖ + 1) := by
      calc
        _ ≤ (‖(Real.eulerMascheroniConstant : ℂ)‖ + 1) +
            (2 + Real.log (‖z‖ + 1)) :=
          add_le_add (add_le_add le_rfl hinv) hseries
        _ = _ := by ring

lemma log_two_le_log_norm_add_two (w : ℂ) : Real.log 2 ≤ Real.log (‖w‖ + 2) :=
  Real.log_le_log (by norm_num) (by linarith [norm_nonneg w])

theorem digamma_bound : ∃ C : ℝ, ∀ w : ℂ, 1 / 2 ≤ w.re →
    ‖logDeriv Complex.Gamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  set A : ℝ := ‖(Real.eulerMascheroniConstant : ℂ)‖ + 5 with hA
  have hA0 : 0 ≤ A := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / Real.log 2 + 1, fun w hw => ?_⟩
  rw [← Complex.digamma_def]
  have hL := log_two_le_log_norm_add_two w
  have hLpos : 0 < Real.log (‖w‖ + 2) := by linarith
  have key : ‖Complex.digamma w‖ ≤ A + Real.log (‖w‖ + 2) := by
    rcases le_or_gt 1 w.re with h1 | h1
    · refine (norm_digamma_le_log h1).trans ?_
      have : Real.log (‖w‖ + 1) ≤ Real.log (‖w‖ + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    · have hw0 : ∀ m : ℕ, w ≠ -(m : ℂ) := by
        intro m h
        have := congrArg Complex.re h
        simp at this
        have : (0 : ℝ) ≤ m := m.cast_nonneg
        linarith
      have hadd := Complex.digamma_apply_add_one w hw0
      have hre : 1 ≤ (w + 1).re := by simp; linarith
      have hb := norm_digamma_le_log hre
      have hn1 : ‖w + 1‖ + 1 ≤ ‖w‖ + 2 := by
        have := norm_add_le w 1; simp at this; linarith
      have hlog : Real.log (‖w + 1‖ + 1) ≤ Real.log (‖w‖ + 2) :=
        Real.log_le_log (by positivity) hn1
      have hwn : 1 / 2 ≤ ‖w‖ := hw.trans ((le_abs_self _).trans (Complex.abs_re_le_norm w))
      have hinv : ‖w⁻¹‖ ≤ 2 := by
        rw [norm_inv]
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have e : Complex.digamma w = Complex.digamma (w + 1) - w⁻¹ := by rw [hadd]; ring
      rw [e]
      calc ‖Complex.digamma (w + 1) - w⁻¹‖ ≤ ‖Complex.digamma (w + 1)‖ + ‖w⁻¹‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
  calc ‖Complex.digamma w‖ ≤ A + Real.log (‖w‖ + 2) := key
    _ ≤ A / Real.log 2 * Real.log (‖w‖ + 2) + Real.log (‖w‖ + 2) := by
        gcongr
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hL hA0
    _ = _ := by ring

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-! ## from Misc -/
/-! ### ζ'/ζ on Re ≥ 2 -/
theorem logDeriv_bound_right : ∃ C : ℝ, ∀ w : ℂ, 2 ≤ w.re → ‖logDeriv riemannZeta w‖ ≤ C := by
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt h2)
  have hsn : Summable fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ :=
    hs.norm
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖,
    fun w hw => ?_⟩
  have hw1 : 1 < w.re := by linarith
  have e : logDeriv riemannZeta w = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw1, logDeriv_apply]
    ring
  rw [e, norm_neg, LSeries]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact hsn.of_nonneg_of_le (fun _ => norm_nonneg _)
      (LSeries.norm_term_le_of_re_le_re _ (by simpa using hw))
  · exact Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hw) n)
      (hsn.of_nonneg_of_le (fun _ => norm_nonneg _)
        (LSeries.norm_term_le_of_re_le_re _ (by simpa using hw))) hsn

/-! ### cot -/
lemma norm_cos_le_two_sin (z : ℂ)
    (h : ‖Complex.exp (2 * z * I) + 1‖ ≤ 2 * ‖Complex.exp (2 * z * I) - 1‖) :
    ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  set E := Complex.exp (z * I) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hEn : 0 < ‖E‖ := norm_pos_iff.mpr hE0
  have hq : Complex.exp (2 * z * I) = E * E := by
    rw [hE, ← Complex.exp_add]; ring_nf
  have hinv : Complex.exp (-z * I) = E⁻¹ := by
    rw [hE, ← Complex.exp_neg]; ring_nf
  have hc : Complex.cos z * E = (E * E + 1) / 2 := by
    rw [Complex.cos, hinv]; field_simp; ring
  have hs : Complex.sin z * E = (1 - E * E) * I / 2 := by
    rw [Complex.sin, hinv]; field_simp; ring
  rw [hq] at h
  have h1 : ‖Complex.cos z‖ * ‖E‖ = ‖E * E + 1‖ / 2 := by
    rw [← norm_mul, hc, norm_div]; simp
  have h2 : ‖Complex.sin z‖ * ‖E‖ = ‖E * E - 1‖ / 2 := by
    rw [← norm_mul, hs, norm_div, norm_mul, Complex.norm_I, mul_one, ← norm_neg]
    simp
  have : ‖Complex.cos z‖ * ‖E‖ ≤ 2 * ‖Complex.sin z‖ * ‖E‖ := by
    rw [h1, mul_assoc, h2]; linarith
  exact le_of_mul_le_mul_right this hEn

lemma norm_cot_le_of (z : ℂ) (h : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖) :
    ‖Complex.cot z‖ ≤ 2 := by
  rw [Complex.cot_eq_cos_div_sin, norm_div]
  by_cases hs : ‖Complex.sin z‖ = 0
  · rw [hs, div_zero]; norm_num
  · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs))]; linarith

lemma exp_pi_ge_three : 3 ≤ Real.exp Real.pi := by
  have := Real.add_one_le_exp Real.pi
  linarith [Real.pi_gt_three]

theorem cot_bound (s : ℂ) (hs : 1 ≤ |s.im| ∨ ∃ k : ℤ, s.re = 2 * k + 1) :
    ‖Complex.cot (Real.pi * s / 2)‖ ≤ 2 := by
  apply norm_cot_le_of
  apply norm_cos_le_two_sin
  have e2 : 2 * (Real.pi * s / 2) * I = Real.pi * s * I := by ring
  rw [e2]
  set q := Complex.exp (Real.pi * s * I) with hq
  have hqn : ‖q‖ = Real.exp (-(Real.pi * s.im)) := by
    rw [hq, Complex.norm_exp]; congr 1; simp
  rcases hs with hs | ⟨k, hk⟩
  · have h1 : ‖q + 1‖ ≤ ‖q‖ + 1 := by simpa using norm_add_le q 1
    have h2 : ‖q‖ - 1 ≤ ‖q - 1‖ := by simpa using norm_sub_norm_le q 1
    have h3 : 1 - ‖q‖ ≤ ‖q - 1‖ := by
      have := norm_sub_norm_le 1 q; rw [norm_sub_rev] at this; simpa using this
    have he := exp_pi_ge_three
    rcases le_abs'.mp hs with hneg | hpos
    · -- Im s ≤ -1: ‖q‖ ≥ e^π ≥ 3
      have : Real.exp Real.pi ≤ ‖q‖ := by
        rw [hqn]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      linarith
    · -- Im s ≥ 1: ‖q‖ ≤ e^{-π} ≤ 1/3
      have hle : ‖q‖ ≤ Real.exp (-Real.pi) := by
        rw [hqn]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have : Real.exp (-Real.pi) ≤ 1 / 3 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; simpa using he
      linarith
  · have hsq : s = ((2 * k + 1 : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [hk]
    have hqv : q = -((Real.exp (-(Real.pi * s.im)) : ℝ) : ℂ) := by
      rw [hq]
      conv_lhs => rw [hsq]
      have : (Real.pi : ℂ) * (((2 * k + 1 : ℝ) : ℂ) + (s.im : ℂ) * I) * I =
          ((-(Real.pi * s.im) : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * I) + Real.pi * I := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I, Complex.ofReal_exp]
      ring
    rw [hqv]
    set r := Real.exp (-(Real.pi * s.im))
    have hr : 0 < r := Real.exp_pos _
    have e1 : -(r : ℂ) + 1 = ((1 - r : ℝ) : ℂ) := by push_cast; ring
    have e2 : -(r : ℂ) - 1 = ((-(1 + r) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_neg, abs_of_pos (by linarith : (0:ℝ) < 1 + r)]
    rcases le_total r 1 with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
lemma zeta_analyticAt {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun z hz => ?_) (isOpen_compl_singleton.mem_nhds hs)
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma cpow_analyticAt {x : ℝ} (hx : 0 < x) (z : ℂ) : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
  AnalyticAt.cpow analyticAt_const analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx)

lemma gamma_analyticAt {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gamma s := by
  refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re}) (fun z hz => ?_)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).differentiableWithinAt
  have := congrArg Complex.re hm; simp at this
  have h' : (0:ℝ) < z.re := hz
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem order_trivial (n : ℕ) : analyticOrderNatAt riemannZeta (-2 * ((n : ℂ) + 1)) = 1 := by
  set p : ℂ := -2 * ((n : ℂ) + 1) with hp
  have hpre : p.re = -2 * ((n : ℝ) + 1) := by simp [hp]
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  let A : ℂ → ℂ := fun z => 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - z)) * Complex.Gamma (1 - z) *
    riemannZeta (1 - z)
  let C : ℂ → ℂ := fun z => Complex.cos (↑Real.pi * (1 - z) / 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2pi : (2 * (Real.pi : ℂ)) ∈ slitPlane := by
    have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  -- the functional equation near p
  have hev : ∀ᶠ z in 𝓝 p, riemannZeta z = (A * C) z := by
    have hU : {z : ℂ | z.re < -1} ∈ 𝓝 p :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp only [mem_ofPred_eq]; rw [hpre]; linarith)
    filter_upwards [hU] with z hz
    have hn : ∀ m : ℕ, (1 - z) ≠ -m := by
      intro m hm; have := congrArg Complex.re hm; simp at this
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
    have h1 : (1 - z) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have := riemannZeta_one_sub hn h1
    rw [sub_sub_cancel] at this
    rw [this]; simp only [Pi.mul_apply, A, C]; ring
  have hA : AnalyticAt ℂ A p := by
    have h1p : 0 < (1 - p).re := by simp [hpre]; linarith
    have hne1 : 1 - p ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp [hpre] at this; linarith
    refine ((analyticAt_const.mul ?_).mul ?_).mul ?_
    · exact AnalyticAt.cpow analyticAt_const (analyticAt_const.sub analyticAt_id).neg h2pi
    · exact (gamma_analyticAt h1p).comp (analyticAt_const.sub analyticAt_id)
    · exact (zeta_analyticAt hne1).comp (analyticAt_const.sub analyticAt_id)
  have hAp : A p ≠ 0 := by
    have h1p : 0 < (1 - p).re := by simp [hpre]; linarith
    have h1p' : 1 ≤ (1 - p).re := by simp [hpre]; linarith
    have hp' : (2 * (Real.pi : ℂ)) ^ (-(1 - p)) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0; exfalso
      exact (mul_ne_zero two_ne_zero hpi) h0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp') (Complex.Gamma_ne_zero_of_re_pos h1p))
      (riemannZeta_ne_zero_of_one_le_re h1p')
  have hC : AnalyticAt ℂ C p := by
    have : AnalyticAt ℂ (fun z : ℂ => ↑Real.pi * (1 - z) / 2) p :=
      (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).div_const
    exact Complex.analyticAt_cos.comp this
  have hCarg : ↑Real.pi * (1 - p) / 2 = (2 * ((n + 1 : ℕ) : ℤ) + 1) * ↑Real.pi / 2 := by
    rw [hp]; push_cast; ring
  have hCp : C p = 0 := by
    simp only [C]; rw [hCarg]; exact Complex.cos_eq_zero_iff.mpr ⟨_, rfl⟩
  have hdC : HasDerivAt C (Complex.sin (↑Real.pi * (1 - p) / 2) * (↑Real.pi / 2)) p := by
    have h1 : HasDerivAt (fun z : ℂ => ↑Real.pi * (1 - z) / 2) (-(↑Real.pi / 2)) p := by
      have := (((hasDerivAt_id' p).const_sub (1:ℂ)).const_mul (↑Real.pi : ℂ)).div_const 2
      exact this.congr_deriv (by ring)
    exact ((Complex.hasDerivAt_cos _).comp p h1).congr_deriv (by ring)
  have hdC0 : deriv C p ≠ 0 := by
    rw [hdC.deriv]
    refine mul_ne_zero ?_ (div_ne_zero hpi two_ne_zero)
    rw [hCarg]
    intro hsin
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
    have h2 : (2 * (((n + 1 : ℕ) : ℤ) : ℂ) + 1) = 2 * (k : ℂ) := by
      apply mul_left_cancel₀ hpi; linear_combination 2 * hk
    have h3 : (2 * ((n + 1 : ℕ) : ℤ) + 1 : ℤ) = 2 * k := by exact_mod_cast h2
    omega
  have hord : analyticOrderAt riemannZeta p = 1 := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hA hC,
      analyticOrderAt_eq_zero.mpr (Or.inr hAp),
      hC.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hCp hdC0, zero_add]
  simp [analyticOrderNatAt, hord]

/-! ## Local principal parts of `F` -/
lemma F_eq (x : ℝ) (s : ℂ) : F x s = -logDeriv riemannZeta s * (x : ℂ) ^ s / s := rfl

theorem F_differentiableAt (x : ℝ) (hx : 0 < x) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζ : riemannZeta z ≠ 0) : DifferentiableAt ℂ (F x) z := by
  have hL : DifferentiableAt ℂ (logDeriv riemannZeta) z := by
    have ha := zeta_analyticAt hz1
    exact (ha.deriv.div ha hζ).differentiableAt
  exact ((hL.neg.mul (cpow_analyticAt hx z).differentiableAt).div differentiableAt_id hz0)

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-- A function `Ψ(z)/(z - p)` with `Ψ` analytic at `p` has a simple pole with residue `Ψ p`. -/
lemma principal_of_div {f Ψ : ℂ → ℂ} {p r : ℂ} (hΨ : AnalyticAt ℂ Ψ p) (hr : Ψ p = r)
    (hf : ∀ᶠ z in 𝓝[≠] p, f z = Ψ z / (z - p)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h p ∧ ∀ᶠ z in 𝓝[≠] p, f z = r / (z - p) + h z := by
  refine ⟨dslope Ψ p, ?_, ?_⟩
  · obtain ⟨U, hU, hUo⟩ := hΨ.eventually_analyticAt.exists_mem
    obtain ⟨V, hVU, hVo, hpV⟩ := mem_nhds_iff.mp hU
    have hd : DifferentiableOn ℂ Ψ V := fun z hz => (hUo z (hVU hz)).differentiableAt.differentiableWithinAt
    exact ((differentiableOn_dslope (hVo.mem_nhds hpV)).mpr hd).analyticAt (hVo.mem_nhds hpV)
  · filter_upwards [hf, self_mem_nhdsWithin] with z hz hzp
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    rw [hz, dslope_of_ne _ hzp, slope_def_field, ← hr]
    field_simp
    ring

/-- `(z - p) · f'/f` near a point where `f = (z-p)^k g` with `g(p) ≠ 0`. -/
lemma logDeriv_local {f g : ℂ → ℂ} {p : ℂ} (k : ℤ) (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0)
    (hf : ∀ᶠ z in 𝓝[≠] p, f z = (z - p) ^ k * g z) :
    ∀ᶠ z in 𝓝[≠] p, (z - p) * logDeriv f z = k + (z - p) * logDeriv g z := by
  have hg' : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hgp)
  have hf' : ∀ᶠ z in 𝓝[≠] p, ∀ᶠ w in 𝓝 z, f w = (w - p) ^ k * g w := by
    rw [eventually_nhdsWithin_iff] at hf ⊢
    obtain ⟨U, hU, hUo, hpU⟩ := mem_nhds_iff.mp hf
    filter_upwards [hUo.mem_nhds hpU] with z hz hzp
    have : U ∩ {p}ᶜ ∈ 𝓝 z := (hUo.inter isOpen_compl_singleton).mem_nhds ⟨hz, hzp⟩
    filter_upwards [this] with w hw
    exact hU hw.1 hw.2
  filter_upwards [hf', nhdsWithin_le_nhds hg', self_mem_nhdsWithin] with z hz hgz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hL : logDeriv f z = logDeriv (fun w => (w - p) ^ k * g w) z := by
    have hz' : f =ᶠ[𝓝 z] fun w => (w - p) ^ k * g w := hz
    rw [logDeriv_apply, logDeriv_apply, hz'.deriv_eq, hz'.self_of_nhds]
  have hpw := logDeriv_fun_zpow (f := fun w : ℂ => w - p) (x := z) (by fun_prop) k
  rw [hL, logDeriv_mul (f := fun w => (w - p) ^ k) z (zpow_ne_zero _ hzp') hgz.2
    ((differentiableAt_id.sub_const p).zpow (Or.inl hzp')) hgz.1.differentiableAt, hpw]
  have : logDeriv (fun w : ℂ => w - p) z = 1 / (z - p) := by
    rw [logDeriv_apply]; simp
  rw [this]; field_simp

lemma logDeriv_analyticAt {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0) :
    AnalyticAt ℂ (logDeriv g) p := by
  have : logDeriv g = fun z => deriv g z / g z := funext (logDeriv_apply g)
  rw [this]; exact hg.deriv.div hg hgp

theorem F_local_zero (x : ℝ) (hx : 0 < x) (ρ : ℂ) (hρ : riemannZeta ρ = 0) (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ z in 𝓝[≠] ρ,
      F x z = (-(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) / (z - ρ) + h z := by
  set m := analyticOrderNatAt riemannZeta ρ
  have ha := zeta_analyticAt hρ1
  have hm : analyticOrderAt riemannZeta ρ = (m : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1)).symm
  obtain ⟨g, hg, hgρ, hfg⟩ := (ha.analyticOrderAt_eq_natCast).mp hm
  have hloc := logDeriv_local (f := riemannZeta) (g := g) (p := ρ) (m : ℤ) hg hgρ
    (by filter_upwards [nhdsWithin_le_nhds hfg] with z hz; rw [hz, smul_eq_mul, zpow_natCast])
  let Ψ : ℂ → ℂ := fun z => -((m : ℂ) + (z - ρ) * logDeriv g z) * (x : ℂ) ^ z / z
  have hΨ : AnalyticAt ℂ Ψ ρ := by
    refine ((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul
      (logDeriv_analyticAt hg hgρ))).neg.mul (cpow_analyticAt hx ρ)).div analyticAt_id hρ0
  refine principal_of_div hΨ (by simp [Ψ]) ?_
  filter_upwards [hloc, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - ρ ≠ 0 := sub_ne_zero.mpr hzp
  simp only [Ψ, F_eq]
  push_cast at hz
  rw [← hz]
  field_simp

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
theorem F_local_one (x : ℝ) (hx : 0 < x) : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 1 ∧ ∀ᶠ z in 𝓝[≠] (1 : ℂ),
    F x z = (x : ℂ) / (z - 1) + h z := by
  classical
  let G : ℂ → ℂ := Function.update (fun z => (z - 1) * riemannZeta z) 1 1
  have hGc : ContinuousAt G 1 := continuousAt_update_same.mpr riemannZeta_residue_one
  have hGd : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ G z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 1 := hz
    have hev : G =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz'] with w hw
      exact Function.update_of_ne hw _ _
    exact (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz'))).congr_of_eventuallyEq hev
  have hG : AnalyticAt ℂ G 1 := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hGd hGc
  have hG1 : G 1 = 1 := Function.update_self _ _ _
  have hloc := logDeriv_local (f := riemannZeta) (g := G) (p := 1) (-1) hG (by rw [hG1]; exact one_ne_zero)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      simp only [G, Function.update_of_ne (show z ≠ 1 from hz)]
      rw [zpow_neg_one]; field_simp)
  let Ψ : ℂ → ℂ := fun z => (1 - (z - 1) * logDeriv G z) * (x : ℂ) ^ z / z
  have hΨ : AnalyticAt ℂ Ψ 1 := by
    refine ((analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul
      (logDeriv_analyticAt hG (by rw [hG1]; exact one_ne_zero)))).mul (cpow_analyticAt hx 1)).div
      analyticAt_id one_ne_zero
  refine principal_of_div hΨ (by simp [Ψ]) ?_
  filter_upwards [hloc, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (show (1:ℂ) ∈ ({0}ᶜ : Set ℂ) by simp))] with z hz hzp hz0
  have hzp' : z - 1 ≠ 0 := sub_ne_zero.mpr hzp
  have hz0' : z ≠ 0 := hz0
  have hL : logDeriv riemannZeta z = (-1 + (z - 1) * logDeriv G z) / (z - 1) := by
    rw [eq_div_iff hzp']; push_cast at hz; linear_combination hz
  simp only [Ψ, F_eq, hL]
  field_simp
  ring

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
theorem F_local_zero_pt (x : ℝ) (hx : 0 < x) : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F x z = (-(Real.log (2 * Real.pi) : ℂ)) / (z - 0) + h z := by
  have ha := zeta_analyticAt (show (0 : ℂ) ≠ 1 from zero_ne_one)
  have h0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  let Ψ : ℂ → ℂ := fun z => -logDeriv riemannZeta z * (x : ℂ) ^ z
  have hΨ : AnalyticAt ℂ Ψ 0 := (logDeriv_analyticAt ha h0).neg.mul (cpow_analyticAt hx 0)
  refine principal_of_div hΨ ?_ ?_
  · simp only [Ψ, logDeriv_apply, deriv_riemannZeta_zero, riemannZeta_zero, Complex.cpow_zero]
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    ring
  · filter_upwards with z
    simp [Ψ, F_eq]

/-! ## Rectangle integrals -/
lemma ftc_log {u : ℝ → ℂ} {u' : ℂ} (a b : ℝ) (hu : ∀ t, HasDerivAt u u' t)
    (hs : ∀ t, u t ∈ slitPlane) : ∫ t in a..b, u' / u t = Complex.log (u b) - Complex.log (u a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hu t).clog_real (hs t)) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  refine continuous_const.div (continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt) ?_
  exact fun t => slitPlane_ne_zero (hs t)

lemma log_sub_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log w - Complex.log (-w) = Real.pi * I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, norm_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]

lemma log_sub_log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log w - Complex.log (-w) = -(Real.pi * I) := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, norm_neg,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]

theorem rectInt_inv_sub (a b T : ℝ) (p : ℂ) (hpa : a < p.re) (hpb : p.re < b) (hpT : |p.im| < T) :
    rectInt (fun z => 1 / (z - p)) a b T = 2 * Real.pi * I := by
  obtain ⟨hT1, hT2⟩ := abs_lt.mp hpT
  have h0 : ∀ σ : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 σ := fun σ => by
    simpa using (hasDerivAt_id σ).ofReal_comp
  have hhor : ∀ y : ℝ, y ≠ p.im → ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => (σ : ℂ) + (y : ℂ) * I - p) 1 σ :=
    fun y _ σ => ((h0 σ).add_const _).sub_const p
  have hver : ∀ x : ℝ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I - p) I t :=
    fun x t => ((((h0 t).mul_const I).const_add (x : ℂ)).sub_const p).congr_deriv (one_mul I)
  have hver' : ∀ x : ℝ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => -((x : ℂ) + (t : ℂ) * I - p)) (-I) t :=
    fun x t => (hver x t).neg
  -- bottom
  have hB : ∫ σ in a..b, (fun z => 1 / (z - p)) ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) =
      Complex.log ((b : ℂ) + ((-T : ℝ) : ℂ) * I - p) - Complex.log ((a : ℂ) + ((-T : ℝ) : ℂ) * I - p) :=
    ftc_log (u := fun σ : ℝ => (σ : ℂ) + ((-T : ℝ) : ℂ) * I - p) a b (hhor _ (by linarith))
      (fun σ => Or.inr (by simp; linarith))
  have hT : ∫ σ in a..b, (fun z => 1 / (z - p)) ((σ : ℂ) + (T : ℂ) * I) =
      Complex.log ((b : ℂ) + (T : ℂ) * I - p) - Complex.log ((a : ℂ) + (T : ℂ) * I - p) :=
    ftc_log (u := fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I - p) a b (hhor _ (by linarith))
      (fun σ => Or.inr (by simp; linarith))
  have hR : ∫ t in (-T)..T, (fun z => 1 / (z - p)) ((b : ℂ) + (t : ℂ) * I) =
      -I * (Complex.log ((b : ℂ) + (T : ℂ) * I - p) - Complex.log ((b : ℂ) + ((-T : ℝ) : ℂ) * I - p)) := by
    have := ftc_log (u := fun t : ℝ => (b : ℂ) + (t : ℂ) * I - p) (-T) T (hver b)
      (fun t => Or.inl (by simp; linarith))
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have : (b : ℂ) + (t : ℂ) * I - p ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only
    field_simp
    rw [Complex.I_sq]; ring
  have hL : ∫ t in (-T)..T, (fun z => 1 / (z - p)) ((a : ℂ) + (t : ℂ) * I) =
      -I * (Complex.log (-((a : ℂ) + (T : ℂ) * I - p)) -
        Complex.log (-((a : ℂ) + ((-T : ℝ) : ℂ) * I - p))) := by
    have := ftc_log (u := fun t : ℝ => -((a : ℂ) + (t : ℂ) * I - p)) (-T) T (hver' a)
      (fun t => Or.inl (by simp; linarith))
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have : (a : ℂ) + (t : ℂ) * I - p ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only
    field_simp
    rw [Complex.I_sq]; ring
  have e1 := log_sub_log_neg_of_im_pos (w := (a : ℂ) + (T : ℂ) * I - p) (by simp; linarith)
  have e2 := log_sub_log_neg_of_im_neg (w := (a : ℂ) + ((-T : ℝ) : ℂ) * I - p) (by simp; linarith)
  unfold rectInt
  rw [hB, hT, hR, hL]
  linear_combination (1 : ℂ) * e1 - e2 - (Complex.log ((b : ℂ) + (T : ℂ) * I - p) -
    Complex.log ((b : ℂ) + ((-T : ℝ) : ℂ) * I - p) - Complex.log (-((a : ℂ) + (T : ℂ) * I - p)) +
    Complex.log (-((a : ℂ) + ((-T : ℝ) : ℂ) * I - p))) * Complex.I_sq

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## (R) the rectangle: residues -/

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-- Interval integrability of the four edges. -/
def RI (f : ℂ → ℂ) (a b T : ℝ) : Prop :=
  IntervalIntegrable (fun σ : ℝ => f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) volume a b ∧
  IntervalIntegrable (fun σ : ℝ => f ((σ : ℂ) + (T : ℂ) * I)) volume a b ∧
  IntervalIntegrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I)) volume (-T) T ∧
  IntervalIntegrable (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * I)) volume (-T) T

lemma RI_of {f : ℂ → ℂ} {a b T : ℝ}
    (h : ∀ z : ℂ, z.re ∈ uIcc a b → z.im ∈ uIcc (-T) T →
      (z.im = -T ∨ z.im = T ∨ z.re = a ∨ z.re = b) → ContinuousAt f z) : RI f a b T := by
  have hp1 : Continuous (fun σ : ℝ => (σ : ℂ) + ((-T : ℝ) : ℂ) * I) := by fun_prop
  have hp2 : Continuous (fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I) := by fun_prop
  have hp3 : Continuous (fun t : ℝ => (b : ℂ) + (t : ℂ) * I) := by fun_prop
  have hp4 : Continuous (fun t : ℝ => (a : ℂ) + (t : ℂ) * I) := by fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable fun u hu => ?_
  · exact (h _ (by simpa using hu) (by simp) (Or.inl (by simp))).comp_continuousWithinAt
      hp1.continuousWithinAt
  · exact (h _ (by simpa using hu) (by simp) (Or.inr (Or.inl (by simp)))).comp_continuousWithinAt
      hp2.continuousWithinAt
  · exact (h _ (by simp) (by simpa using hu) (Or.inr (Or.inr (Or.inr (by simp))))).comp_continuousWithinAt
      hp3.continuousWithinAt
  · exact (h _ (by simp) (by simpa using hu) (Or.inr (Or.inr (Or.inl (by simp))))).comp_continuousWithinAt
      hp4.continuousWithinAt

lemma rectInt_add {f g : ℂ → ℂ} {a b T : ℝ} (hf : RI f a b T) (hg : RI g a b T) :
    rectInt (fun z => f z + g z) a b T = rectInt f a b T + rectInt g a b T := by
  unfold rectInt
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma rectInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {a b T : ℝ}
    (h : ∀ i ∈ s, RI (f i) a b T) :
    rectInt (fun z => ∑ i ∈ s, f i z) a b T = ∑ i ∈ s, rectInt (f i) a b T := by
  unfold rectInt
  rw [intervalIntegral.integral_finsetSum (fun i hi => (h i hi).1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.2.2)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (a b T : ℝ) :
    rectInt (fun z => c * f z) a b T = c * rectInt f a b T := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma rectInt_congr {f g : ℂ → ℂ} {a b T : ℝ}
    (h : ∀ z : ℂ, (z.im = -T ∨ z.im = T ∨ z.re = a ∨ z.re = b) → f z = g z) :
    rectInt f a b T = rectInt g a b T := by
  unfold rectInt
  congr 2
  · congr 1
    · congr 1; funext σ; exact h _ (Or.inl (by simp))
    · congr 1; funext σ; exact h _ (Or.inr (Or.inl (by simp)))
  · congr 1; congr 1; funext t; exact h _ (Or.inr (Or.inr (Or.inr (by simp))))
  · congr 1; congr 1; funext t; exact h _ (Or.inr (Or.inr (Or.inl (by simp))))

theorem rect_residue_theorem (f : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ) (a b T : ℝ)
    (hab : a < b) (hT : 0 < T)
    (hP : ∀ p ∈ P, a < p.re ∧ p.re < b ∧ |p.im| < T)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ T → z ∉ P → DifferentiableAt ℂ f z)
    (hloc : ∀ p ∈ P, ∃ h : ℂ → ℂ, AnalyticAt ℂ h p ∧
      ∀ᶠ z in 𝓝[≠] p, f z = r p / (z - p) + h z) :
    rectInt f a b T = 2 * Real.pi * I * ∑ p ∈ P, r p := by
  classical
  choose! H hH hEq using hloc
  let S : ℂ → ℂ := fun z => ∑ q ∈ P, r q / (z - q)
  let G : ℂ → ℂ := fun z => if z ∈ P then H z z - ∑ q ∈ P.erase z, r q / (z - q) else f z - S z
  have hfinP : ∀ (Q : Finset ℂ) (z : ℂ), z ∉ Q → ∀ᶠ w in 𝓝 z, w ∉ Q := fun Q z hz =>
    Q.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
  have hSd : ∀ (Q : Finset ℂ) (z : ℂ), z ∉ Q →
      DifferentiableAt ℂ (fun w => ∑ q ∈ Q, r q / (w - q)) z := by
    intro Q z hz
    have : (fun w => ∑ q ∈ Q, r q / (w - q)) = ∑ q ∈ Q, (fun w => r q / (w - q)) := by
      funext w; simp
    rw [this]
    refine DifferentiableAt.sum fun q hq => (differentiableAt_const (r q)).div (differentiableAt_id.sub_const q) ?_
    exact sub_ne_zero.mpr (fun h => hz (h ▸ hq))
  have hGd : ∀ z : ℂ, DifferentiableAt ℂ f z ∨ z ∈ P → DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hzP : z ∈ P
    · have hev : G =ᶠ[𝓝 z] fun w => H z w - ∑ q ∈ P.erase z, r q / (w - q) := by
        have h1 := eventually_nhdsWithin_iff.mp (hEq z hzP)
        filter_upwards [h1, hfinP (P.erase z) z (Finset.notMem_erase z P)] with w hw1 hw2
        by_cases hw : w = z
        · subst hw; simp [G, hzP]
        · have hwP : w ∉ P := fun h => hw2 (Finset.mem_erase.mpr ⟨hw, h⟩)
          simp only [G, hwP, if_false, S, hw1 hw]
          rw [← Finset.add_sum_erase P _ hzP]
          ring
      exact ((hH z hzP).differentiableAt.sub (hSd _ z (Finset.notMem_erase z P))).congr_of_eventuallyEq hev
    · have hev : G =ᶠ[𝓝 z] fun w => f w - S w := by
        filter_upwards [hfinP P z hzP] with w hw
        simp [G, hw]
      exact ((hz.resolve_right hzP).sub (hSd P z hzP)).congr_of_eventuallyEq hev
  have hrect : ∀ z : ℂ, z.re ∈ uIcc a b → z.im ∈ uIcc (-T) T → DifferentiableAt ℂ G z := by
    intro z hre him
    rw [uIcc_of_le hab.le] at hre
    rw [uIcc_of_le (by linarith)] at him
    refine hGd z ?_
    by_cases hzP : z ∈ P
    · exact Or.inr hzP
    · exact Or.inl (hdiff z hre.1 hre.2 (abs_le.mpr him) hzP)
  have hG0 : rectInt G a b T = 0 := by
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨a, -T⟩ ⟨b, T⟩
      (fun z hz => (hrect z hz.1 hz.2).differentiableWithinAt)
    unfold rectInt
    simpa [smul_eq_mul] using this
  have hbd : ∀ z : ℂ, (z.im = -T ∨ z.im = T ∨ z.re = a ∨ z.re = b) → z ∉ P := by
    intro z hz hzP
    obtain ⟨h1, h2, h3⟩ := hP z hzP
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    rcases hz with h | h | h | h <;> linarith
  have hsplit : rectInt f a b T =
      rectInt (fun z => G z + ∑ p ∈ P, r p * (1 / (z - p))) a b T := by
    refine rectInt_congr fun z hz => ?_
    have hzP := hbd z hz
    simp only [G, hzP, if_false, S]
    simp only [mul_one_div]
    ring
  have hRIG : RI G a b T := RI_of fun z h1 h2 _ => (hrect z h1 h2).continuousAt
  have hRIp : ∀ p ∈ P, RI (fun z => r p * (1 / (z - p))) a b T := by
    intro p hp
    refine RI_of fun z _ _ hz => ?_
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr (fun h => hbd z hz (h ▸ hp))
    exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hzp))
  have hRIs : RI (fun z => ∑ p ∈ P, r p * (1 / (z - p))) a b T := by
    refine RI_of fun z _ _ hz => ?_
    refine tendsto_finsetSum P fun p hp => ?_
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr (fun h => hbd z hz (h ▸ hp))
    exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hzp))
  rw [hsplit, rectInt_add hRIG hRIs, hG0, zero_add,
    rectInt_sum P (fun p z => r p * (1 / (z - p))) hRIp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := hP p hp
  rw [rectInt_const_mul, rectInt_inv_sub a b T p h1 h2 h3]
  ring

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
lemma ZS_finite (T : ℝ) : (ZS T).Finite :=
  (Zeta23.zetaSeam.finite_window (-T) T).subset fun _ ⟨h1, h2, h3, h4⟩ =>
    ⟨⟨h1, h2, h3⟩, (abs_lt.1 h4).1, (abs_lt.1 h4).2.le⟩

theorem rect_residue (x c T' : ℝ) (M : ℕ) (hx : 1 < x) (hc : 1 < c) (hT' : 0 < T')
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T') :
    rectInt (F x) (-(2 * (M : ℝ) + 1)) c T' =
      2 * Real.pi * I * ((x : ℂ) - zsum x T' - (Real.log (2 * Real.pi) : ℂ) + (trivSum x M : ℂ)) := by
  classical
  have hx0 : 0 < x := by linarith
  set Z : Finset ℂ := (ZS_finite T').toFinset with hZ
  set Tr : Finset ℂ := (Finset.range M).image (fun n : ℕ => -2 * ((n : ℂ) + 1)) with hTr
  set P : Finset ℂ := insert 1 (insert 0 (Z ∪ Tr)) with hPdef
  let r : ℂ → ℂ := fun p => if p = 1 then (x : ℂ) else if p = 0 then -(Real.log (2 * Real.pi) : ℂ)
    else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have memZ : ∀ ρ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' := by
    intro ρ; simp [hZ, ZS]
  have memTr : ∀ z, z ∈ Tr ↔ ∃ n < M, -2 * ((n : ℂ) + 1) = z := by
    intro z; simp [hTr]
  have hTre : ∀ z ∈ Tr, z.re < 0 ∧ -(2 * (M : ℝ)) ≤ z.re ∧ z.im = 0 ∧ riemannZeta z = 0 ∧
      analyticOrderNatAt riemannZeta z = 1 := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := (memTr z).mp hz
    have hn' : (n : ℝ) + 1 ≤ M := by exact_mod_cast hn
    refine ⟨?_, ?_, by simp, riemannZeta_neg_two_mul_nat_add_one n, order_trivial n⟩
    · simp; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    · simp; linarith
  have h1Z : (1 : ℂ) ∉ Z := by rw [memZ]; simp
  have h0Z : (0 : ℂ) ∉ Z := by rw [memZ]; simp
  have h1Tr : (1 : ℂ) ∉ Tr := fun h => by have := (hTre 1 h).1; norm_num at this
  have h0Tr : (0 : ℂ) ∉ Tr := fun h => by have := (hTre 0 h).1; simp at this
  have hdisj : Disjoint Z Tr := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have := ((memZ z).mp hz).2.1
    have := (hTre z hz').1
    linarith
  have hsum : ∑ p ∈ P, r p =
      (x : ℂ) - zsum x T' - (Real.log (2 * Real.pi) : ℂ) + (trivSum x M : ℂ) := by
    rw [hPdef, Finset.sum_insert (by simp [h1Z, h1Tr]), Finset.sum_insert (by simp [h0Z, h0Tr]),
      Finset.sum_union hdisj]
    have e1 : r 1 = x := by simp [r]
    have e0 : r 0 = -(Real.log (2 * Real.pi) : ℂ) := by simp [r]
    have eZ : ∑ p ∈ Z, r p = -zsum x T' := by
      rw [zsum, finsum_mem_eq_finite_toFinset_sum _ (ZS_finite T'), ← hZ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp1 : p ≠ 1 := fun h => h1Z (h ▸ hp)
      have hp0 : p ≠ 0 := fun h => h0Z (h ▸ hp)
      simp only [r, hp1, hp0, if_false]
      ring
    have eTr : ∑ p ∈ Tr, r p = (trivSum x M : ℂ) := by
      rw [hTr, Finset.sum_image (fun a _ b _ h => by
        have : ((a : ℂ) + 1) = (b : ℂ) + 1 := by linear_combination h / (-2)
        exact_mod_cast (add_right_cancel this))]
      rw [trivSum, Complex.ofReal_sum]
      have hIcc : Finset.Icc 1 M = (Finset.range M).map ⟨fun n => n + 1, add_left_injective 1⟩ := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨m - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      rw [hIcc, Finset.sum_map]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hz : -2 * ((n : ℂ) + 1) ∈ Tr := (memTr _).mpr ⟨n, Finset.mem_range.mp hn, rfl⟩
      have hp1 : -2 * ((n : ℂ) + 1) ≠ 1 := fun h => h1Tr (h ▸ hz)
      have hp0 : -2 * ((n : ℂ) + 1) ≠ 0 := fun h => h0Tr (h ▸ hz)
      simp only [r, hp1, hp0, if_false, (hTre _ hz).2.2.2.2]
      simp only [Function.Embedding.coeFn_mk]
      rw [Complex.ofReal_div, Complex.ofReal_cpow hx0.le]
      push_cast
      have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
    rw [e1, e0, eZ, eTr]; ring
  rw [← hsum]
  refine rect_residue_theorem (F x) P r _ _ _ (by linarith) hT' ?_ ?_ ?_
  · intro p hp
    rw [hPdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · simp; refine ⟨by linarith, hc, hT'⟩
    · simp; refine ⟨by linarith, by linarith, hT'⟩
    · obtain ⟨_, h2, h3, h4⟩ := (memZ p).mp hp
      exact ⟨by linarith, by linarith, h4⟩
    · obtain ⟨h1, h2, h3, -⟩ := hTre p hp
      refine ⟨by linarith, by linarith, by rw [h3]; simpa using hT'⟩
  · intro z hz1 hz2 hz3 hzP
    rw [hPdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hzP
    push Not at hzP
    obtain ⟨hz1', hz0', hzZ, hzTr⟩ := hzP
    refine F_differentiableAt x hx0 z hz0' hz1' fun hζ => ?_
    rcases zeta_zero_cases z hζ with ⟨h0, h1⟩ | ⟨n, rfl⟩
    · exact hzZ ((memZ z).mpr ⟨hζ, h0, h1, lt_of_le_of_ne hz3 (hgood z hζ h0 h1)⟩)
    · refine hzTr ((memTr _).mpr ⟨n, ?_, rfl⟩)
      have : -(2 * (M : ℝ) + 1) ≤ -2 * ((n : ℝ) + 1) := by simpa using hz1
      have : (n : ℝ) < M := by linarith
      exact_mod_cast this
  · intro p hp
    rw [hPdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · simpa [r] using F_local_one x hx0
    · simpa [r] using F_local_zero_pt x hx0
    · have hp1 : p ≠ 1 := fun h => h1Z (h ▸ hp)
      have hp0 : p ≠ 0 := fun h => h0Z (h ▸ hp)
      simp only [r, hp1, hp0, if_false]
      exact F_local_zero x hx0 p ((memZ p).mp hp).1 hp0 hp1
    · have hp1 : p ≠ 1 := fun h => h1Tr (h ▸ hp)
      have hp0 : p ≠ 0 := fun h => h0Tr (h ▸ hp)
      simp only [r, hp1, hp0, if_false]
      exact F_local_zero x hx0 p (hTre p hp).2.2.2.1 hp0 hp1

/-! ## ψ₀ as a Perron sum -/
theorem psi0_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n * delta (x / n)) (psi0 x) := by
  classical
  set N := ⌊x⌋₊ with hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hzero : ∀ n ∉ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n * delta (x / n) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have : x / n < 1 := (div_lt_one hnpos).mpr (by linarith)
    simp [delta, not_lt.mpr this.le, this.ne]
  have hs : HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n * delta (x / n)) _ :=
    hasSum_sum_of_ne_finset_zero hzero
  suffices h : ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n * delta (x / n) = psi0 x by
    rwa [h] at hs
  have hterm : ∀ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n * delta (x / n) =
      ArithmeticFunction.vonMangoldt n -
        (if (n : ℝ) = x then ArithmeticFunction.vonMangoldt n / 2 else 0) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnN) hNx
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    by_cases he : (n : ℝ) = x
    · have : x / n = 1 := by rw [← he]; exact div_self hnpos.ne'
      rw [this, if_pos he]; simp [delta]; ring
    · have hlt : (n : ℝ) < x := lt_of_le_of_ne hnx he
      have : 1 < x / n := (one_lt_div hnpos).mpr hlt
      simp [he, this, delta]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h1 : ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc]
    congr 1
    ext n; simp [Finset.mem_Icc, Finset.mem_range]; omega
  have h2 : ∑ n ∈ Finset.range (N + 1),
      (if (n : ℝ) = x then ArithmeticFunction.vonMangoldt n / 2 else 0) =
      (if ((N : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt N / 2 else 0) := by
    rw [Finset.sum_eq_single N]
    · intro n hn hnN
      have hnN' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [if_neg]
      intro he
      have : (N : ℝ) ≤ n := he ▸ hNx
      have : N ≤ n := by exact_mod_cast this
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) h
  rw [h1, h2, psi0]

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias psi0_hasSum := GuthMaynard.CitedZeros.Dav.PartB.psi0_hasSum

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-! ## Σ Λ(n) n^{-σ} -/
lemma vm_term_re {σ : ℝ} (n : ℕ) :
    (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn]
  have : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
  rw [this, ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

lemma vm_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ))
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have h1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H := Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt h1).hasSum
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1]
  unfold LSeries
  simpa only [vm_term_re] using H

lemma vm_term_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma exists_bound_logDeriv_zeta1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
    ‖deriv riemannZeta₁ (x : ℂ) / riemannZeta₁ (x : ℂ)‖ ≤ C := by
  have hne : ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 → riemannZeta₁ (x : ℂ) ≠ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; simp
    · have hx1 : (x : ℂ) ≠ 1 := by
        intro h'; have := congrArg Complex.re h'; simp at this; linarith
      have := riemannZeta_eq_inv_sub_mul hx1
      intro h0
      rw [h0, mul_zero] at this
      exact riemannZeta_ne_zero_of_one_lt_re (by simpa using h) this
  have hc : ContinuousOn (fun x : ℝ => ‖deriv riemannZeta₁ (x : ℂ) / riemannZeta₁ (x : ℂ)‖)
      (Set.Icc 1 2) := by
    apply ContinuousOn.norm
    apply ContinuousOn.div
    · exact (differentiable_riemannZeta₁.deriv.continuous.comp continuous_ofReal).continuousOn
    · exact (differentiable_riemannZeta₁.continuous.comp continuous_ofReal).continuousOn
    · exact hne
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

lemma neg_logDeriv_zeta_real {σ : ℝ} (hσ : 1 < σ) :
    -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = ((σ : ℂ) - 1)⁻¹ - deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ) := by
  have hx1 : (σ : ℂ) ≠ 1 := by
    intro h'; have := congrArg Complex.re h'; simp at this; linarith
  have hsub : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hz := riemannZeta_eq_inv_sub_mul hx1
  have hd := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hx1
  have hz1 : riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hz
    exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ) hz
  rw [hz, hd]
  field_simp
  ring

lemma vm_sum_le_two : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) ≤ 1 / (σ - 1) + C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_logDeriv_zeta1
  refine ⟨C, hC0, fun σ hσ hσ2 => ?_⟩
  rw [(vm_hasSum hσ).tsum_eq, neg_logDeriv_zeta_real hσ, Complex.sub_re]
  have h1 : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div]
  have h2 := hC σ ⟨hσ.le, hσ2⟩
  have h3 := Complex.abs_re_le_norm (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))
  have h4 := neg_abs_le (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re
  linarith

theorem vonMangoldt_dirichlet_le : ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 3 →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) ∧
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) ≤ C / (σ - 1) := by
  obtain ⟨C, hC0, hC⟩ := vm_sum_le_two
  refine ⟨2 * (1 + C), fun σ hσ hσ3 => ⟨(vm_hasSum hσ).summable, ?_⟩⟩
  have hσ1 : 0 < σ - 1 := by linarith
  rcases le_or_gt σ 2 with h2 | h2
  · have := hC σ hσ h2
    have : C ≤ C / (σ - 1) := le_div_self hC0 hσ1 (by linarith)
    have e : 2 * (1 + C) / (σ - 1) = 2 * (1 / (σ - 1)) + 2 * (C / (σ - 1)) := by ring
    have : 0 ≤ 1 / (σ - 1) := by positivity
    have : 0 ≤ C / (σ - 1) := by positivity
    linarith
  · have hmono : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) ≤
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2:ℝ)) := by
      refine (vm_hasSum hσ).summable.tsum_le_tsum (fun n => ?_) (vm_hasSum one_lt_two).summable
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    have h22 := hC 2 one_lt_two le_rfl
    rw [show (1:ℝ) / (2 - 1) = 1 by norm_num] at h22
    rw [le_div_iff₀ hσ1]
    have h0 : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
      tsum_nonneg (vm_term_nonneg σ)
    nlinarith

/-! ## Perron interchange -/
theorem perron_sum_eq (x c T : ℝ) (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    HasSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * perronInt (x / n) c T)
      (Jc x c T) := by
  set s : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I with hs
  have hsre : ∀ t, (s t).re = c := fun t => by simp [hs]
  have hs0 : ∀ t, s t ≠ 0 := fun t h => by have := hsre t; rw [h] at this; simp at this; linarith
  have hsc : ∀ t, c ≤ ‖s t‖ := fun t => by
    have := Complex.abs_re_le_norm (s t); rw [hsre, abs_of_pos (by linarith)] at this; exact this
  have hscont : Continuous s := by fun_prop
  let Fn : ℕ → ℝ → ℂ := fun n t =>
    (ArithmeticFunction.vonMangoldt n : ℂ) * ((((x / n : ℝ)) : ℂ) ^ s t / s t)
  let bound : ℕ → ℝ → ℝ := fun n _ => x ^ c / c * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c))
  have hFn_cont : ∀ n, Continuous (Fn n) := fun n =>
    continuous_const.mul ((hscont.const_cpow (Or.inr hs0)).div hscont hs0)
  have hbound : ∀ n t, ‖Fn n t‖ ≤ bound n t := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Fn, bound]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hy : 0 < x / n := div_pos hx hnpos
    simp only [Fn, bound, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, hsre, Real.div_rpow hx.le hnpos.le,
      Real.rpow_neg hnpos.le]
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
    have hnc : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
    have hc0 : 0 < c := by linarith
    have : x ^ c / (n : ℝ) ^ c / ‖s t‖ ≤ x ^ c / (n : ℝ) ^ c / c :=
      div_le_div_of_nonneg_left (by positivity) hc0 (hsc t)
    calc ArithmeticFunction.vonMangoldt n * (x ^ c / (n : ℝ) ^ c / ‖s t‖)
        ≤ ArithmeticFunction.vonMangoldt n * (x ^ c / (n : ℝ) ^ c / c) :=
          mul_le_mul_of_nonneg_left this hΛ
      _ = _ := by field_simp
  have hsum : Summable fun n => x ^ c / c * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) :=
    (vm_hasSum hc).summable.mul_left _
  have hpt : ∀ t, HasSum (fun n => Fn n t) (F x (s t)) := by
    intro t
    have h1 : 1 < (s t).re := by rw [hsre]; exact hc
    have H := (ArithmeticFunction.LSeriesSummable_vonMangoldt h1).hasSum.mul_right
      ((x : ℂ) ^ s t / s t)
    rw [← LSeries, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1] at H
    have e : F x (s t) = -deriv riemannZeta (s t) / riemannZeta (s t) * ((x : ℂ) ^ s t / s t) := by
      rw [F_eq, logDeriv_apply]; ring
    rw [e]
    refine H.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Fn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [Fn, LSeries.term_of_ne_zero hn]
    rw [Complex.ofReal_div, div_cpow_ofReal_nonneg hx.le hnpos.le]
    push_cast
    have : (n : ℂ) ^ s t ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hn)
    field_simp
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -T) (b := T)
    (f := fun t => F x (s t)) bound (fun n => (hFn_cont n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t _ => hbound n t)
    (Eventually.of_forall fun t _ => hsum) (by simp [bound])
    (Eventually.of_forall fun t _ => hpt t)
  have H2 := H.mul_left (1 / (2 * Real.pi) : ℂ)
  unfold Jc
  refine H2.congr_fun fun n => ?_
  simp only [Fn, perronInt]
  rw [intervalIntegral.integral_const_mul]
  ring

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## (P) Perron: interchange and arithmetic -/
alias perron_sum_eq := GuthMaynard.CitedZeros.Dav.PartB.perron_sum_eq

alias rect_residue := GuthMaynard.CitedZeros.Dav.PartB.rect_residue

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-! ### trivial-zero series -/
lemma trivSum_eq (x : ℝ) (hx : 0 < x) (M : ℕ) :
    trivSum x M = (1 / 2) * ∑ n ∈ Finset.range M, (x ^ (-2 : ℝ)) ^ (n + 1) / (n + 1) := by
  unfold trivSum
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    push_cast
    field_simp

theorem trivSum_tendsto (x : ℝ) (hx : 1 < x) :
    Tendsto (trivSum x) atTop (𝓝 (-(1 / 2) * Real.log (1 - x ^ (-2 : ℝ)))) := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hr1 : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x ^ (-2 : ℝ))
    (by rw [abs_of_pos hr0]; exact hr1)).tendsto_sum_nat
  have h2 := h.const_mul (1 / 2)
  have e : (1 / 2) * -Real.log (1 - x ^ (-2 : ℝ)) = -(1 / 2) * Real.log (1 - x ^ (-2 : ℝ)) := by ring
  rw [e] at h2
  refine h2.congr (fun M => ?_)
  rw [trivSum_eq x hx0 M]

/-! ## from FE -/
/-- The functional equation with `s ↦ 1 - s`. -/
noncomputable def zetaFE (z : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (z - 1) * Complex.sin (Real.pi * z / 2) * Complex.Gamma (1 - z) *
    riemannZeta (1 - z)

lemma zeta_eq_zetaFE (z : ℂ) (hz : z.re < 1) (hz0 : z ≠ 0) : riemannZeta z = zetaFE z := by
  have h1 : ∀ n : ℕ, (1 - z) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have h2 : (1 - z) ≠ 1 := by
    intro h; apply hz0; linear_combination -h
  have h := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at h
  rw [h, zetaFE]
  have e1 : -(1 - z) = z - 1 := by ring
  have e2 : (Real.pi : ℂ) * (1 - z) / 2 = Real.pi / 2 - Real.pi * z / 2 := by ring
  rw [e1, e2, Complex.cos_pi_div_two_sub]
  ring

theorem logDeriv_zeta_FE (s : ℂ) (hs : s.re < 1) (hs0 : s ≠ 0) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      (Real.log (2 * Real.pi) : ℂ) + (Real.pi / 2 : ℂ) * Complex.cot (Real.pi * s / 2) -
        logDeriv Complex.Gamma (1 - s) - logDeriv riemannZeta (1 - s) := by
  -- eventual equality near s
  have hU : IsOpen {z : ℂ | z.re < 1 ∧ z ≠ 0} :=
    (isOpen_lt continuous_re continuous_const).inter isOpen_ne
  have hev : riemannZeta =ᶠ[𝓝 s] zetaFE := by
    filter_upwards [hU.mem_nhds ⟨hs, hs0⟩] with z hz
    exact zeta_eq_zetaFE z hz.1 hz.2
  have hΓ : ∀ m : ℕ, (1 - s) ≠ -(m : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have h1s : (1 - s) ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hΓd : DifferentiableAt ℂ Complex.Gamma (1 - s) := Complex.differentiableAt_Gamma _ hΓ
  have hζd : DifferentiableAt ℂ riemannZeta (1 - s) := differentiableAt_riemannZeta h1s
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  -- derivative of zetaFE
  have hA : HasDerivAt (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (z - 1))
      ((2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.log (2 * Real.pi) * 1) s :=
    ((hasDerivAt_id s).sub_const 1).const_cpow (Or.inl h2π)
  have hB : HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z / 2))
      (Complex.cos (Real.pi * s / 2) * (Real.pi / 2)) s := by
    have := (((hasDerivAt_id' s).const_mul (Real.pi : ℂ)).div_const 2).csin
    convert this using 2
    ring
  have hC : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z)) (deriv Complex.Gamma (1 - s) * (-1)) s := by
    have := (hasDerivAt_id s).const_sub 1
    exact hΓd.hasDerivAt.comp s (by simpa using this)
  have hD : HasDerivAt (fun z : ℂ => riemannZeta (1 - z)) (deriv riemannZeta (1 - s) * (-1)) s := by
    have := (hasDerivAt_id s).const_sub 1
    exact hζd.hasDerivAt.comp s (by simpa using this)
  have hF := ((((hA.const_mul 2).mul hB).mul hC).mul hD)
  have hF' := hF.congr_of_eventuallyEq (f₁ := zetaFE)
    (Eventually.of_forall fun z => by simp only [zetaFE, Pi.mul_apply])
  have hval : riemannZeta s = zetaFE s := zeta_eq_zetaFE s hs hs0
  rw [logDeriv_apply, (hF'.congr_of_eventuallyEq hev).deriv, hval]
  rw [hval, zetaFE] at hζ
  have hsin : Complex.sin (Real.pi * s / 2) ≠ 0 := by
    intro h; apply hζ; rw [h]; ring
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hΓ
  have hZ : riemannZeta (1 - s) ≠ 0 := by
    intro h; apply hζ; rw [h]; ring
  have hP : (2 * (Real.pi : ℂ)) ^ (s - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hlog : Complex.log (2 * Real.pi) = (Real.log (2 * Real.pi) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [logDeriv_apply, logDeriv_apply, Complex.cot_eq_cos_div_sin, zetaFE, hlog]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-! ## from Mid -/
lemma good_dist {δ T' t : ℝ} (hg : IsGood δ T') (ht : t = T' ∨ t = -T') {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : δ ≤ |t - ρ.im| := by
  obtain ⟨ha, hb⟩ := hg ρ hρ h0 h1
  rcases ht with rfl | rfl
  · rwa [abs_sub_comm]
  · rw [show -T' - ρ.im = -(ρ.im + T') by ring, abs_neg]; exact hb

lemma abs_pm {t T' : ℝ} (ht : t = T' ∨ t = -T') (h : 0 ≤ T') : |t| = T' := by
  rcases ht with h' | h' <;> rw [h'] <;> simp [abs_of_nonneg h]

lemma zeta_ne_zero_line {δ T' σ t : ℝ} (hδ : 0 < δ) (hg : IsGood δ T') (ht : t = T' ∨ t = -T')
    (hσ : 0 < σ) : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro hz
  rcases le_or_gt 1 σ with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h1) hz
  · have := good_dist hg ht hz (by simpa using hσ) (by simpa using h1)
    simp at this
    linarith

lemma log_add_four_le {T : ℝ} (hT : 6 ≤ T) : Real.log (T + 4) ≤ 2 * Real.log T := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by linarith)
  rw [show T ^ (2 : ℝ) = T * T by rw [Real.rpow_two]; ring]
  nlinarith

theorem logDeriv_bound_mid_large (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ T T' : ℝ, 6 ≤ T → T ≤ T' →
    T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' → ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      (t = T' ∨ t = -T') → ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨C₁, hC₁, hP⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  refine ⟨2 * C₁ + 2 * C₁ / c₀, fun T T' hT hTT' hT'T hg σ t hσ1 hσ2 ht => ?_⟩
  have hlogT : 1 ≤ Real.log T := by
    have := Real.add_one_le_exp 1
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlT0 : 0 < Real.log T := by linarith
  set δ := c₀ / Real.log T with hδ
  have hδ0 : 0 < δ := div_pos hc₀ hlT0
  have hat : |t| = T' := abs_pm ht (by linarith)
  obtain ⟨Z, hZ, hsum, hbd⟩ := hP t (by rw [hat]; linarith)
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsball : s ∈ Metric.closedBall (2 + t * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + t * I) = ((σ - 2 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hsne : riemannZeta s ≠ 0 := zeta_ne_zero_line hδ0 hg ht (by linarith)
  have h1 := hbd s hsball hsne
  have hlog3 : Real.log (|t| + 3) ≤ 2 * Real.log T := by
    rw [hat]
    exact (Real.log_le_log (by linarith) (by linarith)).trans (log_add_four_le hT)
  -- each term
  have hterm : ∀ ρ ∈ Z, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      (analyticOrderNatAt riemannZeta ρ : ℝ) * (Real.log T / c₀) := by
    intro ρ hρ
    have hρ' : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at hρ'
    obtain ⟨hball, hz⟩ := hρ'
    rw [Metric.mem_closedBall, dist_eq_norm] at hball
    have hre0 : 0 < ρ.re := by
      have := Complex.abs_re_le_norm (ρ - (2 + t * I))
      simp at this
      rw [abs_le] at this
      norm_num at hball
      linarith [this.1]
    have hre1 : ρ.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    have hd := good_dist hg ht hz hre0 hre1
    have hn : δ ≤ ‖s - ρ‖ := by
      refine hd.trans ?_
      have := Complex.abs_im_le_norm (s - ρ)
      simpa [hs] using this
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (hδ0.trans_le hn)]
    have hm : (0 : ℝ) ≤ analyticOrderNatAt riemannZeta ρ := Nat.cast_nonneg _
    have : Real.log T / c₀ * δ = 1 := by rw [hδ]; field_simp
    calc (analyticOrderNatAt riemannZeta ρ : ℝ) = (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (Real.log T / c₀ * δ) := by rw [this, mul_one]
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hn (mul_nonneg hm (by positivity))
  have hS : ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (Real.log T / c₀) := by
    rw [Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hS2 : (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (Real.log T / c₀) ≤
      C₁ * (2 * Real.log T) * (Real.log T / c₀) :=
    mul_le_mul_of_nonneg_right (hsum.trans (mul_le_mul_of_nonneg_left hlog3 hC₁.le)) (by positivity)
  have htot : ‖logDeriv riemannZeta s‖ ≤ C₁ * Real.log (|t| + 3) +
      ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := by
    have := norm_add_le (logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
    rw [sub_add_cancel] at this
    linarith
  have e : C₁ * (2 * Real.log T) * (Real.log T / c₀) = 2 * C₁ / c₀ * Real.log T ^ 2 := by
    field_simp
  have hl2 : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  calc ‖logDeriv riemannZeta s‖ ≤ C₁ * (2 * Real.log T) + 2 * C₁ / c₀ * Real.log T ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlog3 hC₁.le
        linarith
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0:ℝ) ≤ 2 * C₁)
        nlinarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-! ### small heights: compactness -/
theorem logDeriv_bound_mid_small (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ T T' : ℝ, 2 ≤ T → T ≤ 6 →
    T ≤ T' → T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' → ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      (t = T' ∨ t = -T') → ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  set δ₀ := c₀ / Real.log 6 with hδ₀
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hδ₀p : 0 < δ₀ := div_pos hc₀ hl6
  let K : Set ℂ := (Icc (1 / 2 : ℝ) 2 ×ℂ Icc (-7 : ℝ) 7) ∩ {z | 2 ≤ |z.im|} ∩
    ⋂ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}, {z : ℂ | δ₀ ≤ |z.im - ρ.im|}
  have hKc : IsCompact K := by
    refine (isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset ?_
      (inter_subset_left.trans inter_subset_left)
    refine ((isClosed_Icc.reProdIm isClosed_Icc).inter
      (isClosed_le continuous_const (continuous_abs.comp continuous_im))).inter ?_
    refine isClosed_biInter fun ρ _ => isClosed_le continuous_const ?_
    exact continuous_abs.comp (continuous_im.sub continuous_const)
  have hne : ∀ z ∈ K, riemannZeta z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    obtain ⟨⟨⟨hre, him⟩, h2⟩, hρ⟩ := hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at h2; simp at h2; linarith
    refine ⟨fun h0 => ?_, hz1⟩
    rcases le_or_gt 1 z.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 h0
    · have := mem_iInter₂.mp hρ z ⟨h0, by linarith [hre.1], h1⟩
      simp at this
      linarith
  have hcont : ContinuousOn (logDeriv riemannZeta) K := by
    intro z hz
    obtain ⟨h0, h1⟩ := hne z hz
    have hU : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
      fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
    have han := (analyticOnNhd_iff_differentiableOn hU).mpr hd z h1
    have : ContinuousAt (logDeriv riemannZeta) z := by
      have e : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
        funext w; rfl
      rw [e]
      exact han.deriv.continuousAt.div han.continuousAt h0
    exact this.continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨B, fun T T' hT hT6 hTT' hT'T hg σ t hσ1 hσ2 ht => ?_⟩
  apply hB
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hδle : δ₀ ≤ c₀ / Real.log T :=
    div_le_div_of_nonneg_left hc₀.le hlT (Real.log_le_log (by linarith) hT6)
  have hat : |t| = T' := abs_pm ht (by linarith)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp
    constructor <;> linarith
  · simp; rw [← abs_le, hat]; linarith
  · simp; rw [hat]; linarith
  · refine mem_iInter₂.mpr fun ρ hρ => ?_
    have := good_dist hg ht hρ.1 hρ.2.1 hρ.2.2
    simp
    linarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-- The glue of `logDeriv_bound_mid_small` and `logDeriv_bound_mid_large` (the Blueprint's
`logDeriv_bound_mid`, re-proved from this part's lemmas). -/
theorem logDeriv_bound_mid_glue (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ T T' : ℝ, 2 ≤ T → T ≤ T' →
    T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' → ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      (t = T' ∨ t = -T') → ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨C1, h1⟩ := logDeriv_bound_mid_small c₀ hc₀
  obtain ⟨C2, h2⟩ := logDeriv_bound_mid_large c₀ hc₀
  refine ⟨|C1| * 4 + |C2|, fun T T' hT hTT' hT'T hg σ t hσ1 hσ2 ht => ?_⟩
  have hl := half_le_log hT
  have hsq : 1 / 4 ≤ Real.log T ^ 2 := by nlinarith
  have a1 := mul_nonneg (abs_nonneg C1) (by linarith : 0 ≤ 4 * Real.log T ^ 2 - 1)
  have a2 := mul_nonneg (abs_nonneg C2) (sq_nonneg (Real.log T))
  have a3 := mul_nonneg (abs_nonneg C1) (sq_nonneg (Real.log T))
  rcases le_or_gt T 6 with h6 | h6
  · have := h1 T T' hT h6 hTT' hT'T hg σ t hσ1 hσ2 ht
    nlinarith [le_abs_self C1]
  · have := h2 T T' h6.le hTT' hT'T hg σ t hσ1 hσ2 ht
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C2) (sq_nonneg (Real.log T))]

/-! ## ζ'/ζ on the horizontal lines and on the left edges -/
lemma log_two_pi_const : ‖(Real.log (2 * Real.pi) : ℂ)‖ + ‖(Real.pi / 2 : ℂ)‖ * 2 ≤
    |Real.log (2 * Real.pi)| + Real.pi := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 := by
    rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]; linarith

/-- The functional-equation estimate: ‖ζ'/ζ(s)‖ ≤ K₀ + ‖ψ(1-s)‖ + ‖ζ'/ζ(1-s)‖ when the cot term is
bounded. -/
lemma logDeriv_FE_norm (s : ℂ) (hs : s.re < 1) (hs0 : s ≠ 0) (hζ : riemannZeta s ≠ 0)
    (hcot : 1 ≤ |s.im| ∨ ∃ k : ℤ, s.re = 2 * k + 1) :
    ‖logDeriv riemannZeta s‖ ≤ (|Real.log (2 * Real.pi)| + Real.pi) +
      ‖logDeriv Complex.Gamma (1 - s)‖ + ‖logDeriv riemannZeta (1 - s)‖ := by
  rw [logDeriv_zeta_FE s hs hs0 hζ]
  have hc := cot_bound s hcot
  have h1 := norm_sub_le ((Real.log (2 * Real.pi) : ℂ) + (Real.pi / 2 : ℂ) *
    Complex.cot (Real.pi * s / 2) - logDeriv Complex.Gamma (1 - s)) (logDeriv riemannZeta (1 - s))
  have h2 := norm_sub_le ((Real.log (2 * Real.pi) : ℂ) + (Real.pi / 2 : ℂ) *
    Complex.cot (Real.pi * s / 2)) (logDeriv Complex.Gamma (1 - s))
  have h3 := norm_add_le (Real.log (2 * Real.pi) : ℂ) ((Real.pi / 2 : ℂ) *
    Complex.cot (Real.pi * s / 2))
  have h4 : ‖(Real.pi / 2 : ℂ) * Complex.cot (Real.pi * s / 2)‖ ≤ ‖(Real.pi / 2 : ℂ)‖ * 2 := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have h5 := log_two_pi_const
  linarith

theorem logDeriv_bound_horizontal (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ T T' : ℝ, 2 ≤ T → T ≤ T' →
    T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' → ∀ σ t : ℝ, σ ≤ 2 → (t = T' ∨ t = -T') →
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * (Real.log T ^ 2 + Real.log (|σ| + 2)) := by
  obtain ⟨Cm, hm⟩ := logDeriv_bound_mid_glue c₀ hc₀
  obtain ⟨CR, hR⟩ := logDeriv_bound_right
  obtain ⟨Cψ, hψ⟩ := digamma_bound
  set K₀ := |Real.log (2 * Real.pi)| + Real.pi with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨|Cm| + 4 * |Cψ| + 4 * (K₀ + |CR|) + |Cψ|,
    fun T T' hT hTT' hT'T hg σ t hσ ht => ?_⟩
  have hlT := half_le_log hT
  have hsq : 1 / 4 ≤ Real.log T ^ 2 := by nlinarith
  have hl2 : 0 ≤ Real.log (|σ| + 2) := Real.log_nonneg (by linarith [abs_nonneg σ])
  have hat : |t| = T' := abs_pm ht (by linarith)
  set Q := Real.log T ^ 2 + Real.log (|σ| + 2) with hQ
  have hQ0 : Real.log T ^ 2 ≤ Q := by linarith
  have hCm : Cm * Real.log T ^ 2 ≤ |Cm| * Real.log T ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hpos : 0 ≤ (4 * |Cψ| + 4 * (K₀ + |CR|) + |Cψ|) * Q := by positivity
  have hpos2 : 0 ≤ |Cm| * Q := by positivity
  rcases le_or_gt (1 / 2) σ with hσ1 | hσ1
  · have := hm T T' hT hTT' hT'T hg σ t hσ1 hσ ht
    have := mul_le_mul_of_nonneg_left hQ0 (abs_nonneg Cm)
    nlinarith
  · -- the functional equation
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have hT'0 : 2 ≤ T' := by linarith
    have hs0 : s ≠ 0 := by
      intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this
      rw [this] at hat; simp at hat; linarith
    have hδ : 0 < c₀ / Real.log T := div_pos hc₀ (by linarith)
    have hζ : riemannZeta s ≠ 0 := by
      intro h
      rcases zeta_zero_cases s h with ⟨h0, h1⟩ | ⟨n, hn⟩
      · have := good_dist hg ht h h0 h1
        rw [hsim] at this; simp at this; linarith
      · have := congrArg Complex.im hn
        rw [hsim] at this; simp at this
        rw [this] at hat; simp at hat; linarith
    have hFE := logDeriv_FE_norm s (by rw [hsre]; linarith) hs0 hζ
      (Or.inl (by rw [hsim, hat]; linarith))
    -- digamma term
    have h1s : (1 - s) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hψ1 := hψ (1 - s) (by rw [h1s]; simp; linarith)
    have hn1s : ‖1 - s‖ + 2 ≤ (|σ| + 2) * (T + 2) := by
      rw [h1s]
      have := norm_add_le ((1 - σ : ℝ) : ℂ) (((-t : ℝ) : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, hat] at this
      have : |1 - σ| ≤ 1 + |σ| := by
        have := abs_sub (1 : ℝ) σ; simpa using this
      nlinarith [abs_nonneg σ]
    have hlogψ : Real.log (‖1 - s‖ + 2) ≤ Real.log (|σ| + 2) + 2 * Real.log T := by
      have h := Real.log_le_log (by positivity) hn1s
      rw [Real.log_mul (by positivity) (by positivity)] at h
      have : Real.log (T + 2) ≤ 2 * Real.log T := by
        rw [← Real.log_rpow (by linarith)]
        apply Real.log_le_log (by linarith)
        rw [show T ^ (2 : ℝ) = T * T by rw [Real.rpow_two]; ring]
        nlinarith
      linarith
    have hψ2 : ‖logDeriv Complex.Gamma (1 - s)‖ ≤ |Cψ| * (Real.log (|σ| + 2) + 2 * Real.log T) := by
      refine hψ1.trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by
        linarith [norm_nonneg (1 - s)]))).trans ?_
      exact mul_le_mul_of_nonneg_left hlogψ (abs_nonneg _)
    -- ζ'/ζ(1 - s)
    have hz2 : ‖logDeriv riemannZeta (1 - s)‖ ≤ |Cm| * Real.log T ^ 2 + |CR| := by
      rcases le_or_gt (1 - σ) 2 with h2 | h2
      · rw [h1s]
        have := hm T T' hT hTT' hT'T hg (1 - σ) (-t) (by linarith) h2
          (by rcases ht with h | h <;> [right; left] <;> rw [h] <;> ring)
        linarith [abs_nonneg CR]
      · have := hR (1 - s) (by rw [h1s]; simp; linarith)
        have : 0 ≤ |Cm| * Real.log T ^ 2 := by positivity
        linarith [le_abs_self CR]
    have hlogT2 : Real.log T ≤ 2 * Real.log T ^ 2 := by nlinarith
    have hfin : ‖logDeriv riemannZeta s‖ ≤ K₀ + |Cψ| * (Real.log (|σ| + 2) + 4 * Real.log T ^ 2) +
        |Cm| * Real.log T ^ 2 + |CR| := by
      have := mul_le_mul_of_nonneg_left hlogT2 (abs_nonneg Cψ)
      nlinarith [abs_nonneg Cψ]
    refine hfin.trans ?_
    have e1 : K₀ + |CR| ≤ 4 * (K₀ + |CR|) * Q := by nlinarith [abs_nonneg CR]
    have e2 : |Cψ| * (Real.log (|σ| + 2) + 4 * Real.log T ^ 2) ≤ (4 * |Cψ| + |Cψ|) * Q := by
      nlinarith [abs_nonneg Cψ]
    have e3 : |Cm| * Real.log T ^ 2 ≤ |Cm| * Q := mul_le_mul_of_nonneg_left hQ0 (abs_nonneg _)
    nlinarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
theorem logDeriv_bound_left : ∃ C : ℝ, ∀ (M : ℕ) (t : ℝ),
    ‖logDeriv riemannZeta (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * Real.log (2 * M + |t| + 4) := by
  obtain ⟨CR, hR⟩ := logDeriv_bound_right
  obtain ⟨Cψ, hψ⟩ := digamma_bound
  set K₀ := |Real.log (2 * Real.pi)| + Real.pi with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨K₀ + |CR| + |Cψ|, fun M t => ?_⟩
  set s : ℂ := (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) with hs
  have hsre : s.re = -(2 * (M : ℝ) + 1) := by simp [hs]
  have hM : (0 : ℝ) ≤ M := M.cast_nonneg
  have hL : 1 ≤ Real.log (2 * M + |t| + 4) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg t]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    rcases zeta_zero_cases s h with ⟨h0, _⟩ | ⟨n, hn⟩
    · rw [hsre] at h0; linarith
    · have := congrArg Complex.re hn
      rw [hsre] at this
      simp at this
      have h' : ((2 * M + 1 : ℕ) : ℝ) = ((2 * (n + 1) : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_injective h'
      omega
  have hFE := logDeriv_FE_norm s (by rw [hsre]; linarith) hs0 hζ
    (Or.inr ⟨-(M : ℤ) - 1, by rw [hsre]; push_cast; ring⟩)
  have h1s : (1 - s) = ((2 * M + 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hre : (1 - s).re = 2 * M + 2 := by rw [h1s]; simp
  have hψ1 := hψ (1 - s) (by rw [hre]; linarith)
  have hn : ‖1 - s‖ + 2 ≤ 2 * M + |t| + 4 := by
    rw [h1s]
    have := norm_add_le ((2 * M + 2 : ℝ) : ℂ) (((-t : ℝ) : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * M + 2)] at this
    linarith
  have hlog : Real.log (‖1 - s‖ + 2) ≤ Real.log (2 * M + |t| + 4) :=
    Real.log_le_log (by positivity) hn
  have hψ2 : ‖logDeriv Complex.Gamma (1 - s)‖ ≤ |Cψ| * Real.log (2 * M + |t| + 4) :=
    hψ1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.log_nonneg (by linarith [norm_nonneg (1 - s)]))).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)))
  have hz := hR (1 - s) (by rw [hre]; linarith)
  have : K₀ + |CR| ≤ (K₀ + |CR|) * Real.log (2 * M + |t| + 4) := by
    nlinarith [abs_nonneg CR]
  nlinarith [le_abs_self CR]

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
/-! ## The edges of the rectangle -/
lemma norm_F (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖F x s‖ = ‖logDeriv riemannZeta s‖ * x ^ s.re / ‖s‖ := by
  unfold F
  rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]

lemma integral_exp_sub_le {b a c : ℝ} (hb : 0 < b) (hac : a ≤ c) :
    ∫ σ in a..c, Real.exp (b * (σ - c)) ≤ 1 / b := by
  have hd : ∀ σ ∈ uIcc a c, HasDerivAt (fun σ => Real.exp (b * (σ - c)) / b)
      (Real.exp (b * (σ - c))) σ := by
    intro σ _
    have := ((((hasDerivAt_id' σ).sub_const c).const_mul b).exp).div_const b
    exact this.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun σ => Real.exp (b * (σ - c))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have := Real.exp_pos (b * (a - c))
  rw [sub_le_iff_le_add]
  have : 0 ≤ Real.exp (b * (a - c)) / b := by positivity
  linarith

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias trivSum_tendsto := GuthMaynard.CitedZeros.Dav.PartA.trivSum_tendsto

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-! ## From `T'` back to `T` on the line `Re s = c` -/
lemma rpow_cx_le {x : ℝ} (hx : 2 ≤ x) : x ^ cx x ≤ 3 * x := by
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  have hx0 : 0 < x := by linarith
  unfold cx
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
    show Real.log x * (1 / Real.log x) = 1 by field_simp]
  have := Real.exp_one_lt_d9
  nlinarith

lemma norm_logDeriv_le_vm {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv riemannZeta s‖ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have e : ‖logDeriv riemannZeta s‖ = ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ := by
    rw [hL, logDeriv_apply, neg_div, norm_neg]
  rw [e]
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  refine tsum_congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## Assembly (no sorry below this line) -/
lemma ppDist_nonneg (x : ℝ) : 0 ≤ ppDist x :=
  Real.sInf_nonneg (by rintro d ⟨n, -, -, rfl⟩; exact abs_nonneg _)

lemma min_term_nonneg (x T : ℝ) (hx : 0 ≤ x) (hT : 0 ≤ T) : 0 ≤ min 1 (x / (T * ppDist x)) :=
  le_min zero_le_one (div_nonneg hx (mul_nonneg hT (ppDist_nonneg x)))

lemma cx_bounds {x : ℝ} (hx : 2 ≤ x) : 1 < cx x ∧ cx x ≤ 3 := by
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  unfold cx
  have h1 : 0 < 1 / Real.log x := by positivity
  refine ⟨by linarith, ?_⟩
  have : 1 / Real.log x ≤ 2 := by rw [div_le_iff₀ hl0]; linarith
  linarith

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
theorem horizontal_bound (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ x T T' : ℝ, 2 ≤ x → 2 ≤ T →
    T ≤ T' → T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' → ∀ U : ℝ, 1 ≤ U → ∀ t : ℝ,
      (t = T' ∨ t = -T') →
        ‖∫ σ in (-U)..(cx x), F x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (x * Real.log T ^ 2 / T) := by
  obtain ⟨Ch, hCh⟩ := logDeriv_bound_horizontal c₀ hc₀
  obtain ⟨CR, hCR⟩ := logDeriv_bound_right
  set A := |Ch|
  set B := |CR|
  set b := Real.log 2 / 2 with hbdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := by positivity
  set K := A + 4 * (4 * A + B + A / b) with hK
  have hA : 0 ≤ A := abs_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  refine ⟨Real.exp 1 * K / b, fun x T T' hx hT hTT' hT'T hg U hU t ht => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlxp : 0 < Real.log x := by linarith
  obtain ⟨hc1, hc3⟩ := cx_bounds hx
  set c := cx x with hcdef
  have hclog : c * Real.log x = Real.log x + 1 := by
    rw [hcdef, cx]; field_simp
  have hLT := half_le_log hT
  set L2 := Real.log T ^ 2 with hL2
  have hsq : 1 / 4 ≤ L2 := by nlinarith
  have hat : |t| = T' := abs_pm ht (by linarith)
  set M0 := Real.exp 1 * x * K * L2 / T with hM0
  have hK0 : 0 ≤ K := by positivity
  have hM00 : 0 ≤ M0 := by positivity
  have hpt : ∀ σ ∈ Ioc (-U) c, ‖F x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M0 * Real.exp (b * (σ - c)) := by
    intro σ hσ
    have hσc : σ ≤ c := hσ.2
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsT : T ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      simp [hs] at this
      rw [hat] at this; linarith
    -- ζ'/ζ bound
    have hz : ‖logDeriv riemannZeta s‖ ≤ A * (L2 + Real.log (|σ| + 2)) + B := by
      rcases le_or_gt σ 2 with h2 | h2
      · have := hCh T T' hT hTT' hT'T hg σ t h2 ht
        have hnn : 0 ≤ L2 + Real.log (|σ| + 2) :=
          add_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg σ]))
        have := mul_le_mul_of_nonneg_right (le_abs_self Ch) hnn
        linarith
      · have := hCR s (by rw [hsre]; linarith)
        have : 0 ≤ A * (L2 + Real.log (|σ| + 2)) :=
          mul_nonneg hA (add_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg σ])))
        linarith [le_abs_self CR]
    -- x^σ
    have hxσ : x ^ σ ≤ Real.exp 1 * x * Real.exp (2 * b * (σ - c)) := by
      rw [Real.rpow_def_of_pos hx0]
      have e : Real.exp 1 * x * Real.exp (2 * b * (σ - c)) =
          Real.exp (c * Real.log x + 2 * b * (σ - c)) := by
        rw [hclog, Real.exp_add, Real.exp_add, Real.exp_log hx0]; ring
      rw [e]
      apply Real.exp_le_exp.mpr
      have : 2 * b = Real.log 2 := by rw [hbdef]; ring
      rw [this]
      nlinarith
    -- log(|σ|+2)
    have hlogσ : Real.log (|σ| + 2) ≤ (c - σ) + 4 := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < |σ| + 2)
      rcases le_total 0 σ with h | h
      · rw [abs_of_nonneg h] at this ⊢; linarith
      · rw [abs_of_nonpos h] at this ⊢; linarith
    have hcs : c - σ ≤ Real.exp (b * (c - σ)) / b := by
      rw [le_div_iff₀ hb]
      have := Real.add_one_le_exp (b * (c - σ))
      linarith
    have he2 : Real.exp (2 * b * (σ - c)) ≤ Real.exp (b * (σ - c)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hmix : Real.exp (b * (c - σ)) * Real.exp (2 * b * (σ - c)) = Real.exp (b * (σ - c)) := by
      rw [← Real.exp_add]; ring_nf
    have hE := Real.exp_pos (2 * b * (σ - c))
    have hE1 := Real.exp_pos (b * (σ - c))
    -- combine
    have hbr : (A * (L2 + Real.log (|σ| + 2)) + B) * Real.exp (2 * b * (σ - c)) ≤
        K * L2 * Real.exp (b * (σ - c)) := by
      have s1 : (A * (L2 + Real.log (|σ| + 2)) + B) * Real.exp (2 * b * (σ - c)) ≤
          (A * L2 + 4 * A + B) * Real.exp (2 * b * (σ - c)) +
            A * (c - σ) * Real.exp (2 * b * (σ - c)) := by
        have := mul_le_mul_of_nonneg_left hlogσ hA
        nlinarith
      have s2 : A * (c - σ) * Real.exp (2 * b * (σ - c)) ≤ A / b * Real.exp (b * (σ - c)) := by
        have := mul_le_mul_of_nonneg_right hcs hE.le
        rw [div_mul_eq_mul_div, hmix] at this
        calc A * (c - σ) * Real.exp (2 * b * (σ - c)) = A * ((c - σ) * Real.exp (2 * b * (σ - c))) := by ring
          _ ≤ A * (Real.exp (b * (σ - c)) / b) := mul_le_mul_of_nonneg_left this hA
          _ = _ := by ring
      have s3 : (A * L2 + 4 * A + B) * Real.exp (2 * b * (σ - c)) ≤
          (A * L2 + 4 * A + B) * Real.exp (b * (σ - c)) :=
        mul_le_mul_of_nonneg_left he2 (by positivity)
      have s4 : (A * L2 + 4 * A + B + A / b) ≤ K * L2 := by
        rw [hK]
        have : 0 ≤ 4 * A + B + A / b := by positivity
        nlinarith
      nlinarith
    rw [norm_F x hx0, hsre]
    have hsn : 0 < ‖s‖ := by linarith
    rw [div_le_iff₀ hsn]
    calc ‖logDeriv riemannZeta s‖ * x ^ σ
        ≤ (A * (L2 + Real.log (|σ| + 2)) + B) * (Real.exp 1 * x * Real.exp (2 * b * (σ - c))) :=
          mul_le_mul hz hxσ (Real.rpow_nonneg hx0.le _) (by
            have : 0 ≤ A * (L2 + Real.log (|σ| + 2)) :=
              mul_nonneg hA (add_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg σ])))
            linarith)
      _ = Real.exp 1 * x * ((A * (L2 + Real.log (|σ| + 2)) + B) * Real.exp (2 * b * (σ - c))) := by
          ring
      _ ≤ Real.exp 1 * x * (K * L2 * Real.exp (b * (σ - c))) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ = M0 * Real.exp (b * (σ - c)) * T := by rw [hM0]; field_simp
      _ ≤ M0 * Real.exp (b * (σ - c)) * ‖s‖ :=
          mul_le_mul_of_nonneg_left hsT (by positivity)
  have hUc : -U ≤ c := by linarith
  have hint := intervalIntegral.norm_integral_le_of_norm_le hUc
    (Eventually.of_forall fun σ hσ => hpt σ hσ)
    ((by fun_prop : Continuous fun σ => M0 * Real.exp (b * (σ - c))).intervalIntegrable
      (μ := volume) _ _)
  refine hint.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have := mul_le_mul_of_nonneg_left (integral_exp_sub_le hb hUc) hM00
  refine this.trans (le_of_eq ?_)
  rw [hM0]
  field_simp

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## (R) the rectangle: edges -/
alias horizontal_bound := GuthMaynard.CitedZeros.Dav.PartA.horizontal_bound

end
end GuthMaynard.CitedZeros.Dav
end

section
set_option maxHeartbeats 800000
open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform
namespace GuthMaynard.CitedZeros.Dav.PartA
open GuthMaynard.CitedZeros.Dav
theorem left_edge_tendsto (x T' : ℝ) (hx : 1 < x) (hT' : 0 < T') :
    Tendsto (fun M : ℕ => ∫ t in (-T')..T', F x (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨CL, hCL⟩ := logDeriv_bound_left
  have hx0 : 0 < x := by linarith
  set r := x⁻¹ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    have : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have : 0 < x⁻¹ := by positivity
    nlinarith
  set D := 2 * T' * |CL| * x⁻¹ with hD
  have hbound : ∀ M : ℕ, ‖∫ t in (-T')..T', F x (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      D * (2 * ((M : ℝ) * r ^ M) + (T' + 4) * r ^ M) := by
    intro M
    have hM : (0 : ℝ) ≤ M := M.cast_nonneg
    have hxpow : x ^ (-(2 * (M : ℝ) + 1)) = x⁻¹ * r ^ M := by
      rw [Real.rpow_neg hx0.le, show (2 * (M : ℝ) + 1) = ((2 * M + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, ← inv_pow, hr, ← pow_mul, pow_succ]
      ring
    have hpt : ∀ t ∈ Set.uIoc (-T') T',
        ‖F x (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          |CL| * (2 * M + T' + 4) * (x⁻¹ * r ^ M) := by
      intro t ht
      have ht' : |t| ≤ T' := by
        rw [Set.uIoc_of_le (by linarith)] at ht
        exact abs_le.mpr ⟨ht.1.le, ht.2⟩
      set s : ℂ := (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) with hs
      have hsre : s.re = -(2 * (M : ℝ) + 1) := by simp [hs]
      have hsn : 1 ≤ ‖s‖ := by
        have := Complex.abs_re_le_norm s
        rw [hsre, abs_neg, abs_of_pos (by linarith)] at this
        linarith
      rw [norm_F x hx0, hsre, hxpow]
      have hl := hCL M t
      have hlog : Real.log (2 * M + |t| + 4) ≤ 2 * M + T' + 4 := by
        have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * (M : ℝ) + |t| + 4)
        linarith
      have hl0 : 0 ≤ Real.log (2 * M + |t| + 4) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      have hz : ‖logDeriv riemannZeta s‖ ≤ |CL| * (2 * M + T' + 4) :=
        hl.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hl0).trans
          (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)))
      have hq : 0 ≤ x⁻¹ * r ^ M := by positivity
      rw [div_le_iff₀ (by linarith)]
      calc ‖logDeriv riemannZeta s‖ * (x⁻¹ * r ^ M) ≤ |CL| * (2 * M + T' + 4) * (x⁻¹ * r ^ M) :=
            mul_le_mul_of_nonneg_right hz hq
        _ ≤ |CL| * (2 * M + T' + 4) * (x⁻¹ * r ^ M) * ‖s‖ := by
            have : 0 ≤ |CL| * (2 * M + T' + 4) * (x⁻¹ * r ^ M) := by positivity
            nlinarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans (le_of_eq ?_)
    rw [show T' - -T' = 2 * T' by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * T'), hD]
    ring
  apply squeeze_zero_norm hbound
  have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have := ((h1.const_mul 2).add (h2.const_mul (T' + 4))).const_mul D
  simpa using this

end GuthMaynard.CitedZeros.Dav.PartA
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias left_edge_tendsto := GuthMaynard.CitedZeros.Dav.PartA.left_edge_tendsto

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
theorem J_diff : ∃ C : ℝ, ∀ x T T' : ℝ, 2 ≤ x → 2 ≤ T → T ≤ T' → T' ≤ T + 1 →
    ‖J x T' - J x T‖ ≤ C * (x * Real.log x / T) := by
  obtain ⟨Cv, hCv⟩ := vonMangoldt_dirichlet_le
  refine ⟨6 * |Cv|, fun x T T' hx hT hTT' hT'T => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  obtain ⟨hc1, hc3⟩ := cx_bounds hx
  set c := cx x with hcdef
  have hc1' : c - 1 = 1 / Real.log x := by rw [hcdef, cx]; ring
  set s : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I with hs
  have hsre : ∀ t, (s t).re = c := fun t => by simp [hs]
  have hcont : Continuous fun t => F x (s t) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have h1 : 1 < (s t).re := by rw [hsre]; exact hc1
    have hz0 : s t ≠ 0 := fun h => by have := hsre t; rw [h] at this; simp at this; linarith
    have hz1 : s t ≠ 1 := fun h => by have := hsre t; rw [h] at this; simp at this; linarith
    exact (F_differentiableAt x hx0 (s t) hz0 hz1
      (riemannZeta_ne_zero_of_one_lt_re h1)).continuousAt.comp (by fun_prop)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => F x (s t)) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  -- pointwise bound for |t| ≥ T
  obtain ⟨_, hsumle⟩ := hCv c hc1 hc3
  set K : ℝ := Cv / (c - 1) * (3 * x) / T with hK
  have hpt : ∀ t : ℝ, T ≤ |t| → ‖F x (s t)‖ ≤ K := by
    intro t ht
    have h1 : 1 < (s t).re := by rw [hsre]; exact hc1
    have hsT : T ≤ ‖s t‖ := by
      have := Complex.abs_im_le_norm (s t); simp [hs] at this ⊢; linarith
    have hL : ‖logDeriv riemannZeta (s t)‖ ≤ Cv / (c - 1) :=
      (norm_logDeriv_le_vm h1).trans (by rw [hsre]; exact hsumle)
    have hxs : ‖(x : ℂ) ^ s t‖ ≤ 3 * x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre]; exact rpow_cx_le hx
    rw [F_eq, norm_div, norm_mul, norm_neg]
    have hCv0 : 0 ≤ Cv / (c - 1) := (norm_nonneg _).trans hL
    calc ‖logDeriv riemannZeta (s t)‖ * ‖(x : ℂ) ^ s t‖ / ‖s t‖
        ≤ Cv / (c - 1) * (3 * x) / ‖s t‖ :=
          div_le_div_of_nonneg_right (mul_le_mul hL hxs (norm_nonneg _) hCv0) (norm_nonneg _)
      _ ≤ K := div_le_div_of_nonneg_left (by positivity) hT0 hsT
  have hsplit : J x T' - J x T = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t in (-T')..(-T), F x (s t)) + ∫ t in T..T', F x (s t)) := by
    simp only [J, Jc]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-T') (-T)) (hint (-T) T'),
      ← intervalIntegral.integral_add_adjacent_intervals (hint (-T) T) (hint T T')]
    ring
  have b1 : ‖∫ t in (-T')..(-T), F x (s t)‖ ≤ K * |(-T) - (-T')| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
      rw [uIoc_of_le (by linarith)] at ht
      exact hpt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
  have b2 : ‖∫ t in T..T', F x (s t)‖ ≤ K * |T' - T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
      rw [uIoc_of_le hTT'] at ht
      exact hpt t (by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1])
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hpt T (by rw [abs_of_pos hT0]))
  have hKval : K = Cv * Real.log x * (3 * x) / T := by rw [hK, hc1']; field_simp
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]; exact hpi
  rw [hsplit, norm_mul]
  have e1 : |(-T) - (-T')| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have e2 : |T' - T| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hsum2 : ‖(∫ t in (-T')..(-T), F x (s t)) + ∫ t in T..T', F x (s t)‖ ≤ 2 * K := by
    refine (norm_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left e1 hK0, mul_le_mul_of_nonneg_left e2 hK0]
  calc ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖(∫ t in (-T')..(-T), F x (s t)) + ∫ t in T..T', F x (s t)‖
      ≤ 1 * (2 * K) := mul_le_mul hn hsum2 (norm_nonneg _) zero_le_one
    _ = 2 * K := one_mul _
    _ ≤ 6 * |Cv| * (x * Real.log x / T) := by
      rw [hKval]
      have : Cv ≤ |Cv| := le_abs_self Cv
      have hq : 0 ≤ Real.log x * (3 * x) / T := by positivity
      have : Cv * Real.log x * (3 * x) / T ≤ |Cv| * (Real.log x * (3 * x) / T) := by
        rw [mul_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self Cv) hq
      have e : 2 * (|Cv| * (Real.log x * (3 * x) / T)) = 6 * |Cv| * (x * Real.log x / T) := by ring
      linarith

/-! ## Davenport (5): the far terms -/
lemma kb_nonneg {y c T : ℝ} (hy : 0 ≤ y) (hT : 0 ≤ T) : 0 ≤ kb y c T := by
  unfold kb
  split_ifs
  · positivity
  · exact mul_nonneg (Real.rpow_nonneg hy c) (le_min zero_le_one (by positivity))

lemma kb_le_of_ne {y c T : ℝ} (hy : 0 ≤ y) (hy1 : y ≠ 1) :
    kb y c T ≤ y ^ c * (1 / (T * |Real.log y|)) := by
  unfold kb
  rw [if_neg hy1]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hy c)

lemma log_far {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 0 < n) (hfar : x / 4 ≤ |x - n|) :
    Real.log (5 / 4) ≤ |Real.log (x / n)| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt (n : ℝ) x with h | h
  · rw [abs_of_nonneg (by linarith)] at hfar
    have : (5 / 4 : ℝ) ≤ x / n := by rw [le_div_iff₀ hnpos]; linarith
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    exact Real.log_le_log (by norm_num) this
  · rw [abs_of_neg (by linarith)] at hfar
    have hlt : x / n < 1 := (div_lt_one hnpos).mpr h
    rw [abs_of_neg (Real.log_neg (by positivity) hlt), ← Real.log_inv, inv_div]
    have : (5 / 4 : ℝ) ≤ n / x := by rw [le_div_iff₀ hx]; linarith
    exact Real.log_le_log (by norm_num) this

theorem kb_sum_far : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    Summable (fun n : ℕ => if x / 4 ≤ |x - n| then
        ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T else 0) ∧
      ∑' n : ℕ, (if x / 4 ≤ |x - n| then
        ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T else 0) ≤ C * (x * Real.log x / T) := by
  obtain ⟨Cv, hCv⟩ := vonMangoldt_dirichlet_le
  have hL0 : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  refine ⟨3 * |Cv| / Real.log (5 / 4), fun x T hx hT => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  obtain ⟨hc1, hc3⟩ := cx_bounds hx
  set c := cx x with hcdef
  have hc1' : c - 1 = 1 / Real.log x := by rw [hcdef, cx]; ring
  obtain ⟨hs, hsle⟩ := hCv c hc1 hc3
  set K : ℝ := x ^ c / (T * Real.log (5 / 4)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hb : ∀ n : ℕ, (if x / 4 ≤ |x - n| then
      ArithmeticFunction.vonMangoldt n * kb (x / n) c T else 0) ≤
      K * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
    intro n
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    split_ifs with hfar
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hy1 : x / n ≠ 1 := by
        intro h
        have : x = n := by field_simp at h; linarith
        rw [this, sub_self, abs_zero] at hfar; linarith
      have hlog := log_far hx0 hn hfar
      have h1 := kb_le_of_ne (c := c) (T := T) (div_pos hx0 hnpos).le hy1
      have h2 : (x / n) ^ c * (1 / (T * |Real.log (x / n)|)) ≤
          x ^ c * (n : ℝ) ^ (-c) * (1 / (T * Real.log (5 / 4))) := by
        rw [Real.div_rpow hx0.le hnpos.le, Real.rpow_neg hnpos.le, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hlog hT0.le)
      calc ArithmeticFunction.vonMangoldt n * kb (x / n) c T
          ≤ ArithmeticFunction.vonMangoldt n * (x ^ c * (n : ℝ) ^ (-c) * (1 / (T * Real.log (5 / 4)))) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hΛ
        _ = _ := by rw [hK]; ring
    · exact mul_nonneg hK0 (mul_nonneg hΛ (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hnn : ∀ n : ℕ, 0 ≤ (if x / 4 ≤ |x - n| then
      ArithmeticFunction.vonMangoldt n * kb (x / n) c T else 0) := by
    intro n
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (kb_nonneg (div_nonneg hx0.le (Nat.cast_nonneg n)) hT0.le)
    · exact le_rfl
  have hsK := hs.mul_left K
  have hsum := Summable.of_nonneg_of_le hnn hb hsK
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' n : ℕ, K * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) :=
        hsum.tsum_le_tsum hb hsK
    _ = K * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c) := tsum_mul_left
    _ ≤ K * (Cv / (c - 1)) := mul_le_mul_of_nonneg_left hsle hK0
    _ ≤ 3 * x / (T * Real.log (5 / 4)) * (|Cv| * Real.log x) := by
        rw [hc1', div_div_eq_mul_div, div_one]
        have hxc := rpow_cx_le hx
        rw [← hcdef] at hxc
        refine mul_le_mul (div_le_div_of_nonneg_right hxc (by positivity))
          (mul_le_mul_of_nonneg_right (le_abs_self Cv) hl0.le) ?_ (by positivity)
        have h0 : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c) :=
          tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        have := h0.trans hsle
        rw [hc1', div_div_eq_mul_div, div_one] at this
        exact this
    _ = 3 * |Cv| / Real.log (5 / 4) * (x * Real.log x / T) := by field_simp

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias kb_sum_far := GuthMaynard.CitedZeros.Dav.PartB.kb_sum_far

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-! ## Davenport (5): the near terms -/
lemma ppDist_le {x : ℝ} {n : ℕ} (hpp : IsPrimePow n) (hne : (n : ℝ) ≠ x) : ppDist x ≤ |x - n| :=
  csInf_le ⟨0, by rintro d ⟨m, -, -, rfl⟩; exact abs_nonneg _⟩ ⟨n, hpp, hne, rfl⟩

lemma ppDist_pos {x : ℝ} (hx : 0 < x) : 0 < ppDist x := by
  classical
  set N := ⌊x⌋₊ with hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  set a : ℝ := if (N : ℝ) = x then 1 else x - N with ha
  set b : ℝ := N + 1 - x with hb
  have ha0 : 0 < a := by
    rw [ha]; split_ifs with h
    · exact one_pos
    · exact sub_pos.mpr (lt_of_le_of_ne hNx h)
  have hb0 : 0 < b := by rw [hb]; linarith
  have hδ : 0 < min 1 (min a b) := lt_min one_pos (lt_min ha0 hb0)
  refine lt_of_lt_of_le hδ (le_csInf ?_ ?_)
  · by_cases h2 : (2 : ℝ) = x
    · refine ⟨_, 3, (Nat.prime_three).isPrimePow, ?_, rfl⟩
      push_cast; intro h; rw [← h2] at h; norm_num at h
    · exact ⟨_, 2, Nat.prime_two.isPrimePow, by exact_mod_cast h2, rfl⟩
  · rintro d ⟨n, -, hne, rfl⟩
    rcases lt_trichotomy n N with h | h | h
    · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · subst h
      have hax : a = x - N := by rw [ha, if_neg hne]
      rw [abs_of_nonneg (by linarith), ← hax]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'
        rw [abs_of_neg (by push_cast; linarith)]
        refine (min_le_right _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
        rw [hb]; push_cast; ring
      · have : (N : ℝ) + 2 ≤ n := by exact_mod_cast h'
        rw [abs_of_neg (by linarith)]
        exact (min_le_left _ _).trans (by linarith)

lemma log_near {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 0 < n) (hn2 : (n : ℝ) ≤ 2 * x) :
    |x - n| / (2 * x) ≤ |Real.log (x / n)| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt (n : ℝ) x with h | h
  · have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx hnpos)
    rw [inv_div] at hl
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (Real.log_nonneg ((one_le_div hnpos).mpr h))]
    have : (x - n) / (2 * x) ≤ 1 - n / x := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 - n / x = (x - n) / x := by field_simp
      rw [this]
      rw [div_mul_eq_mul_div, le_div_iff₀ hx]; nlinarith
    linarith
  · have hl := Real.one_sub_inv_le_log_of_pos (div_pos hnpos hx)
    rw [inv_div] at hl
    have hlt : x / n < 1 := (div_lt_one hnpos).mpr h
    rw [abs_of_neg (by linarith), abs_of_neg (Real.log_neg (by positivity) hlt), ← Real.log_inv,
      inv_div]
    have : -(x - n) / (2 * x) ≤ 1 - x / n := by
      have : 1 - x / n = (n - x) / n := by field_simp
      rw [this, div_le_div_iff₀ (by positivity) hnpos]; nlinarith
    linarith

lemma rpow_near {y c : ℝ} (hy : 0 < y) (hy43 : y ≤ 4 / 3) (hc : 0 ≤ c) (hc3 : c ≤ 3) : y ^ c ≤ 3 := by
  rcases le_or_gt y 1 with h | h
  · exact (Real.rpow_le_one hy.le h hc).trans (by norm_num)
  · calc y ^ c ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hc3
      _ = y ^ (3 : ℕ) := by norm_cast
      _ ≤ (4 / 3) ^ (3 : ℕ) := pow_le_pow_left₀ hy.le hy43 3
      _ ≤ 3 := by norm_num

lemma kb_near {x c T : ℝ} {n : ℕ} (hx : 0 < x) (hT : 0 < T) (hc : 0 ≤ c) (hc3 : c ≤ 3)
    (hne : (n : ℝ) ≠ x) (hnear : |x - n| < x / 4) :
    kb (x / n) c T ≤ 3 * min 1 (2 * x / (T * |x - n|)) := by
  have hn34 : 3 * x / 4 < n := by
    have := (abs_lt.mp hnear); linarith [this.2]
  have hnpos : (0 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast hnpos
  have hn2 : (n : ℝ) ≤ 2 * x := by have := (abs_lt.mp hnear); linarith [this.1]
  have hy : 0 < x / n := div_pos hx hnpos
  have hy43 : x / n ≤ 4 / 3 := by rw [div_le_iff₀ hnpos]; linarith
  have hy1 : x / n ≠ 1 := by
    intro h; apply hne; field_simp at h; linarith
  have hd : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  unfold kb
  rw [if_neg hy1]
  refine mul_le_mul (rpow_near hy hy43 hc hc3) (min_le_min_left _ ?_) (le_min zero_le_one
    (by positivity)) (by norm_num)
  have hl := log_near hx hn hn2
  have hlpos : 0 < |x - n| / (2 * x) := by positivity
  calc 1 / (T * |Real.log (x / n)|) ≤ 1 / (T * (|x - n| / (2 * x))) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hl hT.le)
    _ = 2 * x / (T * |x - n|) := by field_simp

lemma sum_inv_le (n : ℕ) : ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
    simp [harmonic]
  rw [← e]; exact h

lemma near_harm {x : ℝ} (hx : 1 ≤ x) (N : ℕ) (hN : (N : ℝ) ≤ 3 * x) :
    ∑ n ∈ Finset.range N, (if 1 ≤ |x - n| then 1 / |x - n| else 0) ≤ 4 + 4 * Real.log (3 * x) := by
  classical
  set m := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  let A : ℕ → ℝ := fun n => if n ≤ m then 1 / (((m - n : ℕ) : ℝ) + 1) else 0
  let B : ℕ → ℝ := fun n => if m + 1 ≤ n then 1 / (((n - (m + 1) : ℕ) : ℝ) + 1) else 0
  have hpt : ∀ n : ℕ, (if 1 ≤ |x - n| then 1 / |x - n| else 0) ≤ 2 * A n + 2 * B n := by
    intro n
    have hA0 : 0 ≤ A n := by simp only [A]; split_ifs <;> positivity
    have hB0 : 0 ≤ B n := by simp only [B]; split_ifs <;> positivity
    split_ifs with h1
    · rcases le_or_gt n m with hnm | hnm
      · have hB : B n = 0 := by simp only [B]; rw [if_neg (by omega)]
        have hA : A n = 1 / (((m - n : ℕ) : ℝ) + 1) := by simp only [A]; rw [if_pos hnm]
        rw [hB, hA]
        have hk : ((m - n : ℕ) : ℝ) = m - n := by push_cast [Nat.cast_sub hnm]; ring
        have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnm) hmx
        rw [abs_of_nonneg (by linarith)] at h1 ⊢
        rw [hk]
        have h2 : ((m : ℝ) - n + 1) / 2 ≤ x - n := by linarith
        have hpos : 0 < (m : ℝ) - n + 1 := by
          have : (n : ℝ) ≤ m := by exact_mod_cast hnm
          linarith
        have h3 := one_div_le_one_div_of_le (by positivity) h2
        have e : 1 / (((m : ℝ) - n + 1) / 2) = 2 * (1 / ((m : ℝ) - n + 1)) := by field_simp
        linarith
      · have hA : A n = 0 := by simp only [A]; rw [if_neg (by omega)]
        have hB : B n = 1 / (((n - (m + 1) : ℕ) : ℝ) + 1) := by simp only [B]; rw [if_pos (by omega)]
        rw [hA, hB]
        have hk : ((n - (m + 1) : ℕ) : ℝ) = n - (m + 1) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hnx : x < n := by
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hnm
          linarith
        rw [abs_of_neg (by linarith)] at h1 ⊢
        rw [hk]
        have hpos : 0 < (n : ℝ) - (m + 1) + 1 := by
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hnm
          linarith
        have h2 : ((n : ℝ) - (m + 1) + 1) / 2 ≤ -(x - n) := by linarith
        have h3 := one_div_le_one_div_of_le (by positivity) h2
        have e : 1 / (((n : ℝ) - (m + 1) + 1) / 2) = 2 * (1 / ((n : ℝ) - (m + 1) + 1)) := by field_simp
        linarith
    · linarith
  have hsA : ∑ n ∈ Finset.range N, A n ≤ 1 + Real.log (m + 1) := by
    have e1 : ∑ n ∈ Finset.range N, A n =
        ∑ n ∈ (Finset.range N).filter (· ≤ m), 1 / (((m - n : ℕ) : ℝ) + 1) := by
      rw [Finset.sum_filter]
    rw [e1]
    have hsub : (Finset.range N).filter (· ≤ m) ⊆ Finset.range (m + 1) := by
      intro n hn; simp only [Finset.mem_filter] at hn; exact Finset.mem_range.mpr (by omega)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    have e2 : ∑ n ∈ Finset.range (m + 1), 1 / (((m - n : ℕ) : ℝ) + 1) =
        ∑ n ∈ Finset.range (m + 1), 1 / ((n : ℝ) + 1) := by
      have := Finset.sum_range_reflect (fun k : ℕ => 1 / ((k : ℝ) + 1)) (m + 1)
      simpa using this
    rw [e2]
    have := sum_inv_le (m + 1)
    push_cast at this
    exact this
  have hsB : ∑ n ∈ Finset.range N, B n ≤ 1 + Real.log N := by
    have e1 : ∑ n ∈ Finset.range N, B n =
        ∑ n ∈ (Finset.range N).filter (m + 1 ≤ ·), 1 / (((n - (m + 1) : ℕ) : ℝ) + 1) := by
      rw [Finset.sum_filter]
    rw [e1]
    have hinj : Set.InjOn (fun n : ℕ => n - (m + 1)) ↑((Finset.range N).filter (m + 1 ≤ ·)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      simp only at hab; omega
    rw [← Finset.sum_image (f := fun k : ℕ => 1 / ((k : ℝ) + 1)) hinj]
    have hsub : ((Finset.range N).filter (m + 1 ≤ ·)).image (fun n : ℕ => n - (m + 1)) ⊆
        Finset.range N := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨n, ⟨hn, _⟩, rfl⟩ := hk
      exact Finset.mem_range.mpr (by omega)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (sum_inv_le N)
  have hlog1 : Real.log (m + 1) ≤ Real.log (3 * x) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log N ≤ Real.log (3 * x) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h) hN
  calc _ ≤ ∑ n ∈ Finset.range N, (2 * A n + 2 * B n) := Finset.sum_le_sum fun n _ => hpt n
    _ = 2 * ∑ n ∈ Finset.range N, A n + 2 * ∑ n ∈ Finset.range N, B n := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by linarith

lemma sum_ite_le_card {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p] {K : ℝ} (hK : 0 ≤ K) {k : ℕ}
    (hcard : (s.filter p).card ≤ k) :
    ∑ n ∈ s, (if p n then K else 0) ≤ k * K := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK

theorem kb_sum_near : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1), (if |x - n| < x / 4 then
        ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T else 0) ≤
      C * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) := by
  classical
  refine ⟨300, fun x T hx hT => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  obtain ⟨hc1, hc3⟩ := cx_bounds hx
  set c := cx x with hcdef
  set L := Real.log x with hL
  set μ := min 1 (x / (T * ppDist x)) with hμ
  have hpp := ppDist_pos hx0
  have hμ0 : 0 ≤ μ := le_min zero_le_one (by positivity)
  set N := ⌊2 * x⌋₊ + 1 with hN
  have hNle : (N : ℝ) ≤ 3 * x := by
    have : ((⌊2 * x⌋₊ : ℕ) : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
    rw [hN]; push_cast; linarith
  -- pointwise bound
  have hpt : ∀ n : ℕ, (if |x - n| < x / 4 then ArithmeticFunction.vonMangoldt n * kb (x / n) c T else 0) ≤
      (if (n : ℝ) = x then 2 * L / T else 0) +
        12 * x * L / T * (if 1 ≤ |x - n| then 1 / |x - n| else 0) +
        (if 0 < |x - n| ∧ |x - n| < 1 then 12 * L * μ else 0) := by
    intro n
    have hA0 : 0 ≤ (if (n : ℝ) = x then 2 * L / T else 0) := by split_ifs <;> positivity
    have hB0 : 0 ≤ 12 * x * L / T * (if 1 ≤ |x - n| then 1 / |x - n| else 0) := by
      split_ifs <;> positivity
    have hC0 : 0 ≤ (if 0 < |x - n| ∧ |x - n| < 1 then 12 * L * μ else 0) := by
      split_ifs <;> positivity
    by_cases hnear : |x - n| < x / 4
    swap
    · rw [if_neg hnear]; linarith
    rw [if_pos hnear]
    have hn34 : 3 * x / 4 < n := by have := (abs_lt.mp hnear); linarith [this.2]
    have hnpos : (0 : ℝ) < n := by linarith
    have hn : 0 < n := by exact_mod_cast hnpos
    have hn2 : (n : ℝ) ≤ 2 * x := by have := (abs_lt.mp hnear); linarith [this.1]
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ 2 * L := by
      refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
      have h1 : Real.log n ≤ Real.log (2 * x) := Real.log_le_log hnpos hn2
      have h2 : Real.log (2 * x) = Real.log 2 + L := Real.log_mul (by norm_num) hx0.ne'
      have h3 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
      linarith
    by_cases he : (n : ℝ) = x
    · rw [if_pos he]
      have hk : kb (x / n) c T = 1 / T := by rw [he, div_self hx0.ne']; simp [kb]
      rw [hk]
      have : ArithmeticFunction.vonMangoldt n * (1 / T) ≤ 2 * L / T := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hΛ hT0.le
      linarith
    · rw [if_neg he]
      have hkb := kb_near hx0 hT0 (by linarith) hc3 he hnear
      have hd : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm he))
      have hkb0 : 0 ≤ kb (x / n) c T := kb_nonneg (by positivity) hT0.le
      by_cases h1 : 1 ≤ |x - n|
      · rw [if_pos h1]
        have : ArithmeticFunction.vonMangoldt n * kb (x / n) c T ≤ 2 * L * (3 * (2 * x / (T * |x - n|))) :=
          mul_le_mul hΛ (hkb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)))
            hkb0 (by positivity)
        have e : 2 * L * (3 * (2 * x / (T * |x - n|))) = 12 * x * L / T * (1 / |x - n|) := by
          field_simp; ring
        linarith
      · rw [if_neg h1, if_pos ⟨hd, not_le.mp h1⟩]
        by_cases hΛz : ArithmeticFunction.vonMangoldt n = 0
        · rw [hΛz, zero_mul]; positivity
        have hppn : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛz
        have hdist := ppDist_le hppn he
        have hm : min 1 (2 * x / (T * |x - n|)) ≤ 2 * μ := by
          have h1' : 2 * x / (T * |x - n|) ≤ 2 * (x / (T * ppDist x)) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left hx0.le (by positivity) (mul_le_mul_of_nonneg_left hdist hT0.le))
              (by norm_num)
          rw [hμ, mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), mul_one]
          exact le_min ((min_le_left _ _).trans (by norm_num)) ((min_le_right _ _).trans h1')
        have : ArithmeticFunction.vonMangoldt n * kb (x / n) c T ≤ 2 * L * (3 * (2 * μ)) :=
          mul_le_mul hΛ (hkb.trans (mul_le_mul_of_nonneg_left hm (by norm_num))) hkb0 (by positivity)
        linarith
  -- sum the three pieces
  have s1 : ∑ n ∈ Finset.range N, (if (n : ℝ) = x then 2 * L / T else 0) ≤ 1 * (2 * L / T) := by
    have := sum_ite_le_card (s := Finset.range N) (p := fun n : ℕ => (n : ℝ) = x) (K := 2 * L / T)
      (k := 1) (by positivity) ?_
    · simpa using this
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    exact_mod_cast ha.2.trans hb.2.symm
  have s3 : ∑ n ∈ Finset.range N, (if 0 < |x - n| ∧ |x - n| < 1 then 12 * L * μ else 0) ≤
      2 * (12 * L * μ) := by
    have := sum_ite_le_card (s := Finset.range N) (p := fun n : ℕ => 0 < |x - n| ∧ |x - n| < 1)
      (K := 12 * L * μ) (k := 2) (by positivity) ?_
    · simpa using this
    have hsub : (Finset.range N).filter (fun n : ℕ => 0 < |x - n| ∧ |x - n| < 1) ⊆
        {⌊x⌋₊, ⌊x⌋₊ + 1} := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨-, -, h⟩ := hn
      obtain ⟨h1, h2⟩ := abs_lt.mp h
      have hf1 : ⌊x⌋₊ ≤ n := by
        have : x < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        have := Nat.floor_lt (by linarith : 0 ≤ x) |>.mpr this
        omega
      have hf2 : n ≤ ⌊x⌋₊ + 1 := by
        have : (n : ℝ) - 1 ≤ x := by linarith
        have h' : ((n - 1 : ℕ) : ℝ) ≤ x := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · simp [h0]; linarith
          · rw [Nat.cast_sub h0]; push_cast; linarith
        have := Nat.le_floor h'
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have s2 := near_harm (by linarith : (1:ℝ) ≤ x) N hNle
  have hlog3 : Real.log (3 * x) ≤ 3 * L := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have h4 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
    linarith
  have hxL : 0 ≤ 12 * x * L / T := by positivity
  calc _ ≤ ∑ n ∈ Finset.range N, ((if (n : ℝ) = x then 2 * L / T else 0) +
        12 * x * L / T * (if 1 ≤ |x - n| then 1 / |x - n| else 0) +
        (if 0 < |x - n| ∧ |x - n| < 1 then 12 * L * μ else 0)) := Finset.sum_le_sum fun n _ => hpt n
    _ = ∑ n ∈ Finset.range N, (if (n : ℝ) = x then 2 * L / T else 0) +
        12 * x * L / T * ∑ n ∈ Finset.range N, (if 1 ≤ |x - n| then 1 / |x - n| else 0) +
        ∑ n ∈ Finset.range N, (if 0 < |x - n| ∧ |x - n| < 1 then 12 * L * μ else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 1 * (2 * L / T) + 12 * x * L / T * (4 + 4 * Real.log (3 * x)) + 2 * (12 * L * μ) := by
        gcongr
    _ ≤ 300 * (x * L ^ 2 / T + L * μ) := by
        have e1 : 2 * L / T ≤ 2 * (x * L ^ 2 / T) := by
          rw [show 2 * (x * L ^ 2 / T) = 2 * L * (x * L) / T by ring]
          refine div_le_div_of_nonneg_right ?_ hT0.le
          have : 1 ≤ x * L := by nlinarith
          nlinarith
        have e2 : 12 * x * L / T * (4 + 4 * Real.log (3 * x)) ≤ 12 * x * L / T * (20 * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hxL
          nlinarith
        have e3 : 12 * x * L / T * (20 * L) = 240 * (x * L ^ 2 / T) := by ring
        have : 0 ≤ x * L ^ 2 / T := by positivity
        have : 0 ≤ L * μ := by positivity
        nlinarith

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
alias kb_sum_near := GuthMaynard.CitedZeros.Dav.PartB.kb_sum_near

end
end GuthMaynard.CitedZeros.Dav
end

section
open Complex MeasureTheory Filter Topology Set
open GuthMaynard.CitedZeros.Dav
namespace GuthMaynard.CitedZeros.Dav.PartB
noncomputable section
/-! ## Local zero counts -/
lemma window_finite (a b : ℝ) : (Zeta23.zerosIn a b).Finite := Zeta23.zetaSeam.finite_window a b

lemma window_sum_le (D : Finset ℂ) (t : ℝ)
    (hD : ∀ ρ ∈ D, Zeta23.IsNontrivialZero ρ ∧ t < ρ.im ∧ ρ.im ≤ t + 1) :
    ∑ ρ ∈ D, analyticOrderNatAt riemannZeta ρ ≤ Zeta23.Ncount t (t + 1) := by
  rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ (window_finite t (t + 1))]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) (fun _ _ _ => Nat.zero_le _)
  rw [Set.Finite.mem_toFinset]
  exact hD ρ hρ

lemma log_add_four_le {T : ℝ} (hT : 2 ≤ T) : Real.log (T + 4) ≤ 3 * Real.log T := by
  rw [show 3 * Real.log T = Real.log (T ^ 3) by rw [Real.log_pow]; norm_num]
  refine Real.log_le_log (by linarith) ?_
  nlinarith [mul_nonneg (sub_nonneg.2 hT) (mul_self_nonneg T)]

/-- Zeros with ordinate in `(T - 1, T + 2]` (or `T ≤ |γ| < T + 1`), counted with multiplicity,
are `≪ log T`. -/
lemma three_windows : ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 2 ≤ T → ∀ (a : ℝ), |a| ≤ T + 1 →
    (Zeta23.Ncount a (a + 1) : ℝ) ≤ B / 3 * Real.log T := by
  obtain ⟨A₀, hA₀, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨9 * A₀, by linarith, fun T hT a ha => ?_⟩
  refine (hA a).trans ?_
  have h1 : Real.log (|a| + 3) ≤ Real.log (T + 4) := Real.log_le_log (by positivity) (by linarith)
  have h2 := log_add_four_le hT
  have : A₀ * Real.log (|a| + 3) ≤ A₀ * (3 * Real.log T) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)
  linarith

theorem zsum_diff : ∃ C : ℝ, ∀ x T T' : ℝ, 2 ≤ x → 2 ≤ T → T ≤ T' → T' ≤ T + 1 →
    ‖zsum x T' - zsum x T‖ ≤ C * (x * Real.log T / T) := by
  classical
  obtain ⟨B, hB0, hB⟩ := three_windows
  refine ⟨B, fun x T T' hx hT hTT' hT'T => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  set S' := (ZS_finite T').toFinset
  set S := (ZS_finite T).toFinset
  have hsub : S ⊆ S' := by
    intro ρ hρ
    simp only [S, S', Set.Finite.mem_toFinset, ZS, Set.mem_ofPred_eq] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, lt_of_lt_of_le hρ.2.2.2 hTT'⟩
  set f : ℂ → ℂ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  have hdiff : zsum x T' - zsum x T = ∑ ρ ∈ S' \ S, f ρ := by
    rw [zsum, zsum, finsum_mem_eq_finite_toFinset_sum _ (ZS_finite T'),
      finsum_mem_eq_finite_toFinset_sum _ (ZS_finite T), ← Finset.sum_sdiff hsub]
    ring
  set D := S' \ S
  have hDmem : ∀ ρ ∈ D, Zeta23.IsNontrivialZero ρ ∧ T ≤ |ρ.im| ∧ |ρ.im| < T' := by
    intro ρ hρ
    simp only [D, S, S', Finset.mem_sdiff, Set.Finite.mem_toFinset, ZS, Set.mem_ofPred_eq] at hρ
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hρ
    exact ⟨⟨h1, h2, h3⟩, not_lt.mp fun h => h5 ⟨h1, h2, h3, h⟩, h4⟩
  have hterm : ∀ ρ ∈ D, ‖f ρ‖ ≤ x / T * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨⟨_, _, h3⟩, h4, _⟩ := hDmem ρ hρ
    have hρn : T ≤ ‖ρ‖ := h4.trans (Complex.abs_im_le_norm ρ)
    simp only [f, norm_div, norm_mul, Complex.norm_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hxr : x ^ ρ.re ≤ x := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ x) h3.le
    have hm : (0 : ℝ) ≤ analyticOrderNatAt riemannZeta ρ := Nat.cast_nonneg _
    calc (analyticOrderNatAt riemannZeta ρ : ℝ) * x ^ ρ.re / ‖ρ‖
        ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * x / T :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hxr hm) hT0 hρn
      _ = _ := by ring
  -- multiplicity count over D
  have hcount : (∑ ρ ∈ D, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B * Real.log T := by
    have e1 := Finset.sum_filter_add_sum_filter_not D (fun ρ : ℂ => 0 ≤ ρ.im)
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
    have e2 := Finset.sum_filter_add_sum_filter_not (D.filter (fun ρ : ℂ => 0 ≤ ρ.im))
      (fun ρ : ℂ => ρ.im ≤ T) (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
    have w1 : (∑ ρ ∈ (D.filter (fun ρ : ℂ => 0 ≤ ρ.im)).filter (fun ρ : ℂ => ρ.im ≤ T),
        (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B / 3 * Real.log T := by
      have := window_sum_le ((D.filter (fun ρ : ℂ => 0 ≤ ρ.im)).filter (fun ρ : ℂ => ρ.im ≤ T))
        (T - 1) (fun ρ hρ => by
          simp only [Finset.mem_filter] at hρ
          obtain ⟨⟨hD, h0⟩, h1⟩ := hρ
          obtain ⟨hz, h4, _⟩ := hDmem ρ hD
          rw [abs_of_nonneg h0] at h4
          exact ⟨hz, by linarith, by linarith⟩)
      have h' := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at h'
      refine h'.trans ?_
      have := hB T hT (T - 1) (by rw [abs_of_nonneg (by linarith)]; linarith)
      rwa [show T - 1 + 1 = T by ring] at this ⊢
    have w2 : (∑ ρ ∈ (D.filter (fun ρ : ℂ => 0 ≤ ρ.im)).filter (fun ρ : ℂ => ¬ ρ.im ≤ T),
        (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B / 3 * Real.log T := by
      have := window_sum_le ((D.filter (fun ρ : ℂ => 0 ≤ ρ.im)).filter (fun ρ : ℂ => ¬ ρ.im ≤ T))
        T (fun ρ hρ => by
          simp only [Finset.mem_filter] at hρ
          obtain ⟨⟨hD, h0⟩, h1⟩ := hρ
          obtain ⟨hz, _, h5⟩ := hDmem ρ hD
          rw [abs_of_nonneg h0] at h5
          exact ⟨hz, by linarith, by linarith⟩)
      have h' := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at h'
      refine h'.trans ?_
      exact hB T hT T (by rw [abs_of_nonneg (by linarith)]; linarith)
    have w3 : (∑ ρ ∈ D.filter (fun ρ : ℂ => ¬ 0 ≤ ρ.im),
        (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B / 3 * Real.log T := by
      have := window_sum_le (D.filter (fun ρ : ℂ => ¬ 0 ≤ ρ.im)) (-T - 1) (fun ρ hρ => by
          simp only [Finset.mem_filter] at hρ
          obtain ⟨hD, h0⟩ := hρ
          obtain ⟨hz, h4, h5⟩ := hDmem ρ hD
          rw [abs_of_neg (not_le.mp h0)] at h4 h5
          exact ⟨hz, by linarith, by linarith⟩)
      have h' := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at h'
      refine h'.trans ?_
      exact hB T hT (-T - 1) (by rw [abs_of_neg (by linarith)]; linarith)
    linarith
  rw [hdiff]
  calc ‖∑ ρ ∈ D, f ρ‖ ≤ ∑ ρ ∈ D, ‖f ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ D, x / T * (analyticOrderNatAt riemannZeta ρ : ℝ) := Finset.sum_le_sum hterm
    _ = x / T * ∑ ρ ∈ D, (analyticOrderNatAt riemannZeta ρ : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x / T * (B * Real.log T) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = B * (x * Real.log T / T) := by ring

/-! ## Good heights -/
theorem good_height : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ T : ℝ, 2 ≤ T →
    ∃ T' ∈ Icc T (T + 1), IsGood (c₀ / Real.log T) T' := by
  classical
  obtain ⟨B, hB0, hB⟩ := three_windows
  refine ⟨1 / (4 * (B + 2)), by positivity, fun T hT => ?_⟩
  have hl := half_le_log hT
  have hL0 : 0 < Real.log T := by linarith
  set L := Real.log T with hL
  set c₀ : ℝ := 1 / (4 * (B + 2)) with hc₀
  set δ : ℝ := c₀ / L with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ14 : δ ≤ 1 / 4 := by
    rw [hδ, hc₀, div_le_iff₀ hL0]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  set W := (window_finite (T - 1) (T + 2)).toFinset with hW
  have hWmem : ∀ ρ, ρ ∈ W ↔ Zeta23.IsNontrivialZero ρ ∧ T - 1 < ρ.im ∧ ρ.im ≤ T + 2 := by
    intro ρ; rw [hW, Set.Finite.mem_toFinset]; rfl
  set Γ := W.image Complex.im with hΓ
  set K := Γ.card with hK
  -- K ≪ log T
  have hWsum : (∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B * L := by
    have e1 := Finset.sum_filter_add_sum_filter_not W (fun ρ : ℂ => ρ.im ≤ T)
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
    have e2 := Finset.sum_filter_add_sum_filter_not (W.filter (fun ρ : ℂ => ¬ ρ.im ≤ T))
      (fun ρ : ℂ => ρ.im ≤ T + 1) (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
    have cast_le : ∀ (D : Finset ℂ) (t : ℝ),
        (∀ ρ ∈ D, Zeta23.IsNontrivialZero ρ ∧ t < ρ.im ∧ ρ.im ≤ t + 1) → |t| ≤ T + 1 →
        (∑ ρ ∈ D, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ B / 3 * L := by
      intro D t hD ht
      have h' := (Nat.cast_le (α := ℝ)).mpr (window_sum_le D t hD)
      push_cast at h'
      exact h'.trans (hB T hT t ht)
    have w1 := cast_le (W.filter (fun ρ : ℂ => ρ.im ≤ T)) (T - 1) (fun ρ hρ => by
        simp only [Finset.mem_filter, hWmem] at hρ
        exact ⟨hρ.1.1, hρ.1.2.1, by linarith [hρ.2]⟩)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    have w2 := cast_le ((W.filter (fun ρ : ℂ => ¬ ρ.im ≤ T)).filter (fun ρ : ℂ => ρ.im ≤ T + 1)) T
      (fun ρ hρ => by
        simp only [Finset.mem_filter, hWmem] at hρ
        exact ⟨hρ.1.1.1, not_le.mp hρ.1.2, hρ.2⟩)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    have w3 := cast_le ((W.filter (fun ρ : ℂ => ¬ ρ.im ≤ T)).filter (fun ρ : ℂ => ¬ ρ.im ≤ T + 1))
      (T + 1) (fun ρ hρ => by
        simp only [Finset.mem_filter, hWmem] at hρ
        exact ⟨hρ.1.1.1, not_le.mp hρ.2, by linarith [hρ.1.1.2.2]⟩)
      (by rw [abs_of_nonneg (by linarith)])
    linarith
  have hKle : (K : ℝ) ≤ B * L := by
    have h1 : K ≤ W.card := Finset.card_image_le
    have h2 : (W.card : ℝ) ≤ ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have := Zeta23.ZetaSeam.one_le_mult_holds ρ ((hWmem ρ).mp hρ).1
      push_cast
      exact_mod_cast this
    have h1' : (K : ℝ) ≤ W.card := by exact_mod_cast h1
    linarith
  have hsep : 2 * δ * (K + 1) ≤ 1 / 2 := by
    have : δ * (K + 1) ≤ c₀ * (B + 2) := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hL0]
      have : (K : ℝ) + 1 ≤ (B + 2) * L := by nlinarith
      calc c₀ * (K + 1) ≤ c₀ * ((B + 2) * L) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have e : c₀ * (B + 2) = 1 / 4 := by rw [hc₀]; field_simp
    linarith
  -- pigeonhole
  set t : ℕ → ℝ := fun j => T + j / (K + 1) with ht
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  set Bd := (Finset.range (K + 1)).filter (fun j => ∃ γ ∈ Γ, |γ - t j| < δ) with hBd
  have hBd_sub : Bd ⊆ Γ.biUnion (fun γ => (Finset.range (K + 1)).filter (fun j => |γ - t j| < δ)) := by
    intro j hj
    simp only [hBd, Finset.mem_filter] at hj
    obtain ⟨hj, γ, hγ, hlt⟩ := hj
    exact Finset.mem_biUnion.mpr ⟨γ, hγ, Finset.mem_filter.mpr ⟨hj, hlt⟩⟩
  have hone : ∀ γ ∈ Γ, ((Finset.range (K + 1)).filter (fun j => |γ - t j| < δ)).card ≤ 1 := by
    intro γ _
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    have h1 : |t a - t b| < 2 * δ := by
      calc |t a - t b| = |(γ - t b) - (γ - t a)| := by ring_nf
        _ ≤ |γ - t b| + |γ - t a| := abs_sub _ _
        _ < δ + δ := add_lt_add hb.2 ha.2
        _ = 2 * δ := by ring
    have h2 : t a - t b = ((a : ℝ) - b) / (K + 1) := by simp only [ht]; ring
    rw [h2, abs_div, abs_of_pos hK1, div_lt_iff₀ hK1] at h1
    have h3 : |(a : ℝ) - b| < 1 := by nlinarith
    have h4 : |(a : ℤ) - b| < 1 := by
      have : ((|(a : ℤ) - b| : ℤ) : ℝ) < 1 := by push_cast; exact h3
      exact_mod_cast this
    have := abs_lt.mp h4
    omega
  have hcardBd : Bd.card < (Finset.range (K + 1)).card := by
    rw [Finset.card_range]
    have := (Finset.card_le_card hBd_sub).trans Finset.card_biUnion_le
    have h2 : ∑ γ ∈ Γ, ((Finset.range (K + 1)).filter (fun j => |γ - t j| < δ)).card ≤ ∑ γ ∈ Γ, 1 :=
      Finset.sum_le_sum hone
    rw [Finset.sum_const, smul_eq_mul, mul_one] at h2
    omega
  obtain ⟨j, hjr, hjB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardBd
  have hjK : (j : ℝ) ≤ K := by
    have := Finset.mem_range.mp hjr; exact_mod_cast Nat.lt_succ_iff.mp this
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  refine ⟨t j, ⟨?_, ?_⟩, ?_⟩
  · simp only [ht]; have : 0 ≤ (j : ℝ) / (K + 1) := by positivity
    linarith
  · simp only [ht]
    have : (j : ℝ) / (K + 1) ≤ 1 := by rw [div_le_one hK1]; linarith
    linarith
  have hT'lo : T ≤ t j := by simp only [ht]; have : 0 ≤ (j : ℝ) / (K + 1) := by positivity
                             linarith
  have hT'hi : t j ≤ T + 1 := by
    simp only [ht]; have : (j : ℝ) / (K + 1) ≤ 1 := by rw [div_le_one hK1]; linarith
    linarith
  have key : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → δ ≤ |ρ.im - t j| := by
    intro ρ h0 h1 h2
    by_contra hlt
    push Not at hlt
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hlt
    have hρW : ρ ∈ W := (hWmem ρ).mpr ⟨⟨h0, h1, h2⟩, by linarith, by linarith⟩
    apply hjB
    simp only [hBd, Finset.mem_filter]
    exact ⟨hjr, ρ.im, Finset.mem_image_of_mem _ hρW, hlt⟩
  intro ρ h0 h1 h2
  refine ⟨key ρ h0 h1 h2, ?_⟩
  have hc0 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, h0, map_zero]
  have := key ((starRingEnd ℂ) ρ) hc0 (by simpa using h1) (by simpa using h2)
  rw [Complex.conj_im, show -ρ.im - t j = -(ρ.im + t j) by ring, abs_neg] at this
  exact this

end
end GuthMaynard.CitedZeros.Dav.PartB
end

section
open Complex MeasureTheory Filter Topology Set
namespace GuthMaynard.CitedZeros.Dav
noncomputable section
/-! ## (G) good heights and ζ'/ζ on the horizontal lines -/
alias good_height := GuthMaynard.CitedZeros.Dav.PartB.good_height

/-! ## (Z) from T' back to T -/
alias zsum_diff := GuthMaynard.CitedZeros.Dav.PartB.zsum_diff

alias J_diff := GuthMaynard.CitedZeros.Dav.PartB.J_diff

/-- (P1) the Perron kernel error against the majorant `kb`. -/
theorem perron_kernel : ∃ K : ℝ, 0 ≤ K ∧ ∀ y c T : ℝ, 0 < y → 0 < c → c ≤ 3 → 0 < T →
    ‖perronInt y c T - delta y‖ ≤ K * kb y c T := by
  obtain ⟨K₀, hK₀, hK⟩ := perron_kernel_unif
  refine ⟨K₀ + 3, by linarith, fun y c T hy hc hc3 hT => ?_⟩
  by_cases hy1 : y = 1
  · subst hy1
    have h := perron_kernel_one c T hc hT
    simp only [kb, if_true]
    calc ‖perronInt 1 c T - delta 1‖ ≤ c / T := h
      _ ≤ 3 / T := div_le_div_of_nonneg_right hc3 hT.le
      _ ≤ (K₀ + 3) / T := div_le_div_of_nonneg_right (by linarith) hT.le
      _ = (K₀ + 3) * (1 / T) := by ring
  · simp only [kb, hy1, if_false]
    have h1 := hK y c T hy hy1 hc hT
    have h2 := perron_kernel_log y c T hy hy1 hc hT
    have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
    have ha : 0 ≤ 1 / (T * |Real.log y|) := by positivity
    rw [← mul_assoc, mul_min_of_nonneg _ _ (mul_nonneg (by linarith) hyc), mul_one]
    refine le_min (by nlinarith) ?_
    calc _ ≤ y ^ c / (T * |Real.log y|) := h2
      _ = 1 * (y ^ c * (1 / (T * |Real.log y|))) := by ring
      _ ≤ (K₀ + 3) * (y ^ c * (1 / (T * |Real.log y|))) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hyc ha)
      _ = _ := by ring

/-- (P4) Davenport's (5): Σ Λ(n) kb(x/n) ≪ x log²x/T + log x · min(1, x/(T⟨x⟩)). -/
theorem kb_sum : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T) ∧
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T ≤
        C * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) := by
  obtain ⟨Cf, hf⟩ := kb_sum_far
  obtain ⟨Cn, hn⟩ := kb_sum_near
  refine ⟨2 * |Cf| + |Cn|, fun x T hx hT => ?_⟩
  obtain ⟨sf, bf⟩ := hf x T hx hT
  have bn := hn x T hx hT
  set f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T with hfdef
  set gf : ℕ → ℝ := fun n => if x / 4 ≤ |x - n| then f n else 0 with hgf
  set gn : ℕ → ℝ := fun n => if |x - n| < x / 4 then f n else 0 with hgn
  have hsplit : f = fun n => gf n + gn n := by
    funext n
    by_cases h : x / 4 ≤ |x - n|
    · simp [gf, gn, h, not_lt.mpr h]
    · simp [gf, gn, h, not_le.mp h]
  have hgn0 : ∀ n ∉ Finset.range (⌊2 * x⌋₊ + 1), gn n = 0 := by
    intro n hn'
    simp only [Finset.mem_range, not_lt] at hn'
    have h2x : 2 * x < n := by
      have := Nat.lt_floor_add_one (2 * x)
      have h' : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
      push_cast at h'
      linarith
    have : ¬ |x - n| < x / 4 := by
      rw [not_lt, abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    simp [gn, this]
  have sn : Summable gn := summable_of_ne_finset_zero hgn0
  have hQ : 0 ≤ Real.log x * min 1 (x / (T * ppDist x)) :=
    mul_nonneg (by linarith [half_le_log hx]) (min_term_nonneg x T (by linarith) (by linarith))
  have hl := half_le_log hx
  have hA : 0 ≤ x * Real.log x / T := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hA2 : x * Real.log x / T ≤ 2 * (x * Real.log x ^ 2 / T) := by
    calc x * Real.log x / T = (x * Real.log x / T) * 1 := by ring
      _ ≤ (x * Real.log x / T) * (2 * Real.log x) := mul_le_mul_of_nonneg_left (by linarith) hA
      _ = 2 * (x * Real.log x ^ 2 / T) := by ring
  have hB : 0 ≤ x * Real.log x ^ 2 / T := by positivity
  refine ⟨hsplit ▸ sf.add sn, ?_⟩
  rw [hsplit, sf.tsum_add sn, tsum_eq_sum hgn0]
  have e1 : Cf * (x * Real.log x / T) ≤ |Cf| * (2 * (x * Real.log x ^ 2 / T)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left hA2 (abs_nonneg _))
  have e2 : Cn * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) ≤
      |Cn| * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have e3 : |Cf| * (2 * (x * Real.log x ^ 2 / T)) ≤
      2 * |Cf| * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) := by
    have := abs_nonneg Cf
    nlinarith
  calc _ ≤ Cf * (x * Real.log x / T) + Cn * (x * Real.log x ^ 2 / T +
        Real.log x * min 1 (x / (T * ppDist x))) := add_le_add bf bn
    _ ≤ _ := by nlinarith

/-- (P) ‖ψ₀(x) − J(x,T)‖ ≪ x log²x/T + log x · min(1, x/(T⟨x⟩)). -/
theorem perron_error : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖((psi0 x : ℝ) : ℂ) - J x T‖ ≤
      C * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x))) := by
  obtain ⟨K, hK0, hK⟩ := perron_kernel
  obtain ⟨C, hC⟩ := kb_sum
  refine ⟨K * C, fun x T hx hT => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hc1, hc3⟩ := cx_bounds hx
  obtain ⟨hs, hb⟩ := hC x T hx hT
  have h1 : HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n * delta (x / n) : ℝ) : ℂ))
      ((psi0 x : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr (psi0_hasSum x hx0)
  have h2 := perron_sum_eq x (cx x) T hx0 hc1 hT0
  have h := h1.sub h2
  have hg := hs.hasSum.mul_left K
  have hbound : ∀ n : ℕ, ‖((ArithmeticFunction.vonMangoldt n * delta (x / n) : ℝ) : ℂ) -
      (ArithmeticFunction.vonMangoldt n : ℂ) * perronInt (x / n) (cx x) T‖ ≤
        K * (ArithmeticFunction.vonMangoldt n * kb (x / n) (cx x) T) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hy : 0 < x / n := div_pos hx0 (by exact_mod_cast hn)
      have hk := hK (x / n) (cx x) T hy (by linarith) hc3 hT0
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      calc _ = ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (perronInt (x / n) (cx x) T - delta (x / n))‖ := by
              rw [← norm_neg]; congr 1; push_cast; ring
        _ = ArithmeticFunction.vonMangoldt n * ‖perronInt (x / n) (cx x) T - delta (x / n)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ]
        _ ≤ ArithmeticFunction.vonMangoldt n * (K * kb (x / n) (cx x) T) :=
              mul_le_mul_of_nonneg_left hk hΛ
        _ = _ := by ring
  have hfin := tsum_of_norm_bounded hg hbound
  rw [h.tsum_eq] at hfin
  calc _ ≤ _ := hfin
    _ ≤ K * (C * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x)))) :=
        mul_le_mul_of_nonneg_left hb hK0
    _ = _ := by ring

/-- (R) the contour shift at a good height T' ∈ [T, T+1]. -/
theorem rect_bound (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ x T T' : ℝ, 2 ≤ x → 2 ≤ T → T ≤ T' →
    T' ≤ T + 1 → IsGood (c₀ / Real.log T) T' →
      ‖J x T' - x + zsum x T' +
          ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤
        C * (x * Real.log T ^ 2 / T) := by
  obtain ⟨C, hC⟩ := horizontal_bound c₀ hc₀
  refine ⟨|C|, fun x T T' hx hT hTT' hT'T hgood => ?_⟩
  have hx1 : 1 < x := by linarith
  have hT'0 : 0 < T' := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨hc1, -⟩ := cx_bounds hx
  have hgood' : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T' := by
    intro ρ hρ h0 h1 heq
    have hδ : 0 < c₀ / Real.log T := div_pos hc₀ hlogT
    obtain ⟨ha, hb⟩ := hgood ρ hρ h0 h1
    rcases (abs_eq hT'0.le).mp heq with h | h
    · rw [h, sub_self, abs_zero] at ha; linarith
    · rw [h, neg_add_cancel, abs_zero] at hb; linarith
  set Q : ℝ := x * Real.log T ^ 2 / T with hQdef
  have hQ : 0 ≤ Q := by positivity
  set R : ℂ := ∫ t in (-T')..T', F x ((cx x : ℂ) + (t : ℂ) * I) with hR
  have hJR : (2 * Real.pi : ℂ) * J x T' = R := by
    simp only [J, Jc, R]
    have : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [← mul_assoc, mul_one_div_cancel this, one_mul]
  let B : ℕ → ℂ := fun M =>
    ∫ σ in (-(2 * (M : ℝ) + 1))..(cx x), F x ((σ : ℂ) + ((-T' : ℝ) : ℂ) * I)
  let Tp : ℕ → ℂ := fun M => ∫ σ in (-(2 * (M : ℝ) + 1))..(cx x), F x ((σ : ℂ) + (T' : ℂ) * I)
  let L : ℕ → ℂ := fun M => ∫ t in (-T')..T', F x (((-(2 * (M : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)
  let DM : ℕ → ℂ := fun M =>
    J x T' - x + zsum x T' + (Real.log (2 * Real.pi) : ℂ) - (trivSum x M : ℂ)
  have h2πI : (2 * Real.pi * I : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ I_ne_zero
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hDM : ∀ M, DM M = (-B M + Tp M + I * L M) / (2 * Real.pi * I) := by
    intro M
    have h := rect_residue x (cx x) T' M hx1 hc1 hT'0 hgood'
    unfold rectInt at h
    rw [eq_div_iff h2πI]
    simp only [DM, B, Tp, L]
    linear_combination h + I * hJR
  have hBd : ∀ M : ℕ, ‖DM M‖ ≤ (2 * (|C| * Q) + ‖L M‖) / (2 * Real.pi) := by
    intro M
    have hU : (1 : ℝ) ≤ 2 * (M : ℝ) + 1 := by have := M.cast_nonneg (α := ℝ); linarith
    have hb := hC x T T' hx hT hTT' hT'T hgood (2 * (M : ℝ) + 1) hU (-T') (Or.inr rfl)
    have ht := hC x T T' hx hT hTT' hT'T hgood (2 * (M : ℝ) + 1) hU T' (Or.inl rfl)
    have hb' : ‖B M‖ ≤ |C| * Q := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hQ)
    have ht' : ‖Tp M‖ ≤ |C| * Q := ht.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hQ)
    rw [hDM M, norm_div]
    have hn : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one]
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [hn]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ‖-B M + Tp M + I * L M‖ ≤ ‖-B M‖ + ‖Tp M‖ + ‖I * L M‖ := norm_add₃_le
      _ = ‖B M‖ + ‖Tp M‖ + ‖L M‖ := by rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      _ ≤ _ := by linarith
  have hLt : Tendsto L atTop (𝓝 0) := left_edge_tendsto x T' hx1 hT'0
  have hgt : Tendsto (fun M => (2 * (|C| * Q) + ‖L M‖) / (2 * Real.pi)) atTop
      (𝓝 ((2 * (|C| * Q) + 0) / (2 * Real.pi))) := by
    have := hLt.norm
    rw [norm_zero] at this
    exact (tendsto_const_nhds.add this).div_const _
  have hDt : Tendsto DM atTop (𝓝 (J x T' - x + zsum x T' +
      ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
    have ht := (Complex.continuous_ofReal.tendsto _).comp (trivSum_tendsto x hx1)
    have := (tendsto_const_nhds (x := J x T' - x + zsum x T' + (Real.log (2 * Real.pi) : ℂ))).sub ht
    have hlim : J x T' - x + zsum x T' +
        ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ) =
        J x T' - x + zsum x T' + (Real.log (2 * Real.pi) : ℂ) -
          ((-(1 / 2) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hlim]
    exact this
  have hfin := le_of_tendsto_of_tendsto' hDt.norm hgt hBd
  calc _ ≤ (2 * (|C| * Q) + 0) / (2 * Real.pi) := hfin
    _ = |C| * Q / Real.pi := by field_simp; ring
    _ ≤ |C| * Q := div_le_self (by positivity) (by linarith [Real.pi_gt_three])

/-- **Davenport's truncated explicit formula** (the type of
`GuthMaynard.davenport_truncated_explicit_formula`). -/
theorem davenport_dev :
    ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ‖(((Chebyshev.psi x -
            (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0) - x : ℝ)) : ℂ) +
          (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
            (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) +
          ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤
        C * (x * Real.log (x * T) ^ 2 / T +
          Real.log x * min 1 (x / (T * sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) ≠ x ∧
            d = |x - n|}))) := by
  obtain ⟨Cp, hP⟩ := perron_error
  obtain ⟨c₀, hc₀, hG⟩ := good_height
  obtain ⟨Cr, hR⟩ := rect_bound c₀ hc₀
  obtain ⟨C1, hZ1⟩ := zsum_diff
  obtain ⟨C2, hZ2⟩ := J_diff
  refine ⟨|Cp| + |Cr| + |C1| + |C2|, fun x T hx hT => ?_⟩
  obtain ⟨T', ⟨hTT', hT'T⟩, hgood⟩ := hG T hT
  set Lc : ℂ := ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)
  change ‖((psi0 x - x : ℝ) : ℂ) + zsum x T + Lc‖ ≤
    _ * (x * Real.log (x * T) ^ 2 / T + Real.log x * min 1 (x / (T * ppDist x)))
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlx := half_le_log hx
  have hlT := half_le_log hT
  set Lg := Real.log (x * T) with hLg
  have hLg : Lg = Real.log x + Real.log T := Real.log_mul hx0.ne' hT0.ne'
  have hLg1 : 1 ≤ Lg := by linarith
  set m := min 1 (x / (T * ppDist x))
  have hm : 0 ≤ m := min_term_nonneg x T hx0.le hT0.le
  set Q := x * Lg ^ 2 / T + Real.log x * m with hQdef
  have hxT : 0 ≤ x / T := by positivity
  have hmono : ∀ a : ℝ, 0 ≤ a → a ≤ Lg ^ 2 → x * a / T ≤ Q := by
    intro a _ ha
    have : x * a / T ≤ x * Lg ^ 2 / T :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hx0.le) hT0.le
    have : 0 ≤ Real.log x * m := mul_nonneg (by linarith) hm
    linarith
  have hLgsq : Lg ≤ Lg ^ 2 := by nlinarith
  have hQ0 : 0 ≤ Q := by
    have := hmono 0 le_rfl (by positivity); simpa using (show (0:ℝ) ≤ x * 0 / T by simp).trans this
  have hsplit : ((psi0 x - x : ℝ) : ℂ) + zsum x T + Lc =
      (((psi0 x : ℝ) : ℂ) - J x T) + (J x T - J x T') + (J x T' - x + zsum x T' + Lc) +
        (zsum x T - zsum x T') := by
    push_cast; ring
  -- the four bounds
  have bA : ‖((psi0 x : ℝ) : ℂ) - J x T‖ ≤ |Cp| * Q := by
    refine (hP x T hx hT).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ Real.log x) hm; positivity)).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have : x * Real.log x ^ 2 / T ≤ x * Lg ^ 2 / T := by
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hx0.le) hT0.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  have bB : ‖J x T - J x T'‖ ≤ |C2| * Q := by
    rw [norm_sub_rev]
    refine (hZ2 x T T' hx hT hTT' hT'T).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (by have : 0 ≤ Real.log x := by linarith
          positivity)).trans ?_)
    exact mul_le_mul_of_nonneg_left (hmono _ (by linarith) (by linarith)) (abs_nonneg _)
  have bD : ‖J x T' - x + zsum x T' + Lc‖ ≤ |Cr| * Q := by
    refine (hR x T T' hx hT hTT' hT'T hgood).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (by positivity)).trans ?_)
    refine mul_le_mul_of_nonneg_left (hmono _ (by positivity) ?_) (abs_nonneg _)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have bE : ‖zsum x T - zsum x T'‖ ≤ |C1| * Q := by
    rw [norm_sub_rev]
    refine (hZ1 x T T' hx hT hTT' hT'T).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (by have : 0 ≤ Real.log T := by linarith
          positivity)).trans ?_)
    exact mul_le_mul_of_nonneg_left (hmono _ (by linarith) (by linarith)) (abs_nonneg _)
  rw [hsplit]
  calc _ ≤ ‖((psi0 x : ℝ) : ℂ) - J x T‖ + ‖J x T - J x T'‖ + ‖J x T' - x + zsum x T' + Lc‖ +
        ‖zsum x T - zsum x T'‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add₃_le
    _ ≤ |Cp| * Q + |C2| * Q + |Cr| * Q + |C1| * Q := by linarith
    _ = _ := by ring

end
end GuthMaynard.CitedZeros.Dav
end

theorem solution :
    ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ‖(((Chebyshev.psi x -
            (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0) - x : ℝ)) : ℂ) +
          (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
            (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) +
          ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤
        C * (x * Real.log (x * T) ^ 2 / T +
          Real.log x * min 1 (x / (T * sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) ≠ x ∧
            d = |x - n|}))) :=
  GuthMaynard.CitedZeros.Dav.davenport_dev
