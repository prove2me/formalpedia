-- Prove2me | solution 1 for Martingale.clt_of_bounded_mds_array
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:45:25.930338+00:00
-- url     : https://prove2.me/submissions/37b215f8-5333-492e-8739-0861c07c6458

import Theorems.Thm_Martingale_norm_charFun_sub_const_le
import Theorems.Thm_Martingale_tendstoInDistribution_gaussian_of_tendsto_charFun

set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (hadapt : ∀ n k, Measurable[ℱ k] (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hmds : ∀ n k, P[D n (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∀ n, ∫ ω, D n 0 ω ∂P = 0)
    (C : ℕ → ℝ) (hCbdd : ∀ n k ω, |D n k ω| ≤ C n)
    (hC0 : Tendsto C atTop (𝓝 0))
    (M : ℝ) (hM : ∀ n ω, ∑ k ∈ Finset.range n, D n k ω ^ 2 ≤ M)
    (σ : ℝ)
    (hvar : Tendsto (fun n : ℕ => ∫ ω, |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| ∂P)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (σ ^ 2).toNNReal) := by
  classical
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  have hCnn : ∀ n, 0 ≤ C n := fun n =>
    le_trans (abs_nonneg _) (hCbdd n 0 (Classical.arbitrary Ω))
  -- `|e^x - e^y| ≤ |x - y|` for `x, y ≤ 0`
  have hexpdiff : ∀ x y : ℝ, x ≤ 0 → y ≤ 0 → |Real.exp x - Real.exp y| ≤ |x - y| := by
    have key : ∀ x y : ℝ, x ≤ y → y ≤ 0 → Real.exp y - Real.exp x ≤ y - x := by
      intro x y hxy hy0
      have heypos := Real.exp_pos y
      have hey : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy0
      have h1 := Real.add_one_le_exp (x - y)
      rw [Real.exp_sub, le_div_iff₀ heypos] at h1
      nlinarith [h1, mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hey)]
    intro x y hx hy
    rcases le_total x y with h | h
    · have h1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith [key x y h hy]
    · have h1 : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith [key y x h hx]
  -- `0 ≤ M`
  have hM0 : 0 ≤ M := by
    have := hM 0 (Classical.arbitrary Ω)
    simpa using this
  refine Martingale.tendstoInDistribution_gaussian_of_tendsto_charFun P _
    (fun n => Finset.measurable_sum _ (fun k _ => hmeas n k)) (σ ^ 2) (by positivity) ?_
  intro t
  set c : ℂ := ((Real.exp (-(σ ^ 2 * t ^ 2) / 2) : ℝ) : ℂ) with hc
  have hclim : Complex.exp (-((σ ^ 2 : ℝ) * t ^ 2) / 2) = c := by
    rw [hc, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hclim]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- the majorant
  set R : ℕ → ℝ := fun n => Real.exp (t ^ 2 * M / 2) *
    (|t| ^ 3 * (C n * M) + t ^ 2 / 2 * ∫ ω, |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| ∂P)
    with hR
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => |t| ^ 3 * (C n * M)) atTop (𝓝 0) := by
      have := (hC0.mul_const M).const_mul (|t| ^ 3)
      simpa using this
    have h2 : Tendsto (fun n : ℕ => t ^ 2 / 2 *
        ∫ ω, |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| ∂P) atTop (𝓝 0) := by
      have := hvar.const_mul (t ^ 2 / 2)
      simpa using this
    have := (h1.add h2).const_mul (Real.exp (t ^ 2 * M / 2))
    simpa [hR] using this
  refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ hRlim
  -- for large `n` the increments are small enough for the master inequality
  have hev : ∀ᶠ n : ℕ in atTop, C n ≤ (|t| + 1)⁻¹ := by
    have hpos : (0:ℝ) < (|t| + 1)⁻¹ := by positivity
    exact hC0.eventually (eventually_le_nhds hpos)
  filter_upwards [hev] with n hn
  -- (1) the master inequality applies
  have hsmall : ∀ k ∈ Finset.range n, ∀ ω, |t * D n k ω| ≤ 1 := by
    intro k _ ω
    rw [abs_mul]
    have h1 : |D n k ω| ≤ C n := hCbdd n k ω
    have h2 : C n ≤ (|t| + 1)⁻¹ := hn
    have h3 : (0:ℝ) < |t| + 1 := by positivity
    have h4 : |t| * C n ≤ |t| * (|t| + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg t)
    have h5 : |t| * (|t| + 1)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ h3]; linarith
    calc |t| * |D n k ω| ≤ |t| * C n := mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
      _ ≤ 1 := le_trans h4 h5
  have hmaster := Martingale.norm_charFun_sub_const_le P ℱ (D n) (hmeas n) (hadapt n)
    (hint n) (hmds n) (hcent n) (C n) (hCbdd n) t M n (fun ω => hM n ω) hsmall c
  refine le_trans hmaster ?_
  -- (2) bound the integral by the two explicit terms
  set g : Ω → ℝ := fun ω => (∑ k ∈ Finset.range n, |t * D n k ω| ^ 3)
    + ‖((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ) - c‖ with hg
  set h2 : Ω → ℝ := fun ω => |t| ^ 3 * (C n * M)
    + t ^ 2 / 2 * |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| with hh2
  -- pathwise cube bound, used twice below
  have hcubeAll : ∀ ω, (∑ k ∈ Finset.range n, |t * D n k ω| ^ 3) ≤ |t| ^ 3 * (C n * M) := by
      intro ω
      have hterm : ∀ k ∈ Finset.range n,
          |t * D n k ω| ^ 3 ≤ |t| ^ 3 * C n * D n k ω ^ 2 := by
        intro k _
        have h1 : |D n k ω| ≤ C n := hCbdd n k ω
        have h0 : (0:ℝ) ≤ |D n k ω| := abs_nonneg _
        have hsq : |D n k ω| ^ 2 = D n k ω ^ 2 := sq_abs _
        calc |t * D n k ω| ^ 3 = |t| ^ 3 * |D n k ω| ^ 3 := by
              rw [abs_mul, mul_pow]
          _ = |t| ^ 3 * (|D n k ω| * |D n k ω| ^ 2) := by ring
          _ ≤ |t| ^ 3 * (C n * D n k ω ^ 2) := by
              rw [← hsq]
              have : |D n k ω| * |D n k ω| ^ 2 ≤ C n * |D n k ω| ^ 2 :=
                mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = |t| ^ 3 * C n * D n k ω ^ 2 := by ring
      calc ∑ k ∈ Finset.range n, |t * D n k ω| ^ 3
          ≤ ∑ k ∈ Finset.range n, |t| ^ 3 * C n * D n k ω ^ 2 :=
            Finset.sum_le_sum hterm
        _ = |t| ^ 3 * C n * ∑ k ∈ Finset.range n, D n k ω ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ |t| ^ 3 * C n * M := by
            refine mul_le_mul_of_nonneg_left (hM n ω) ?_
            exact mul_nonneg (by positivity) (hCnn n)
        _ = |t| ^ 3 * (C n * M) := by ring
  -- pathwise: `g ≤ h2`
  have hpt : ∀ ω, g ω ≤ h2 ω := by
    intro ω
    have hcube := hcubeAll ω
    have hgauss : ‖((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ) - c‖
        ≤ t ^ 2 / 2 * |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| := by
      have hsum0 : (0:ℝ) ≤ ∑ k ∈ Finset.range n, D n k ω ^ 2 :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have hx : -(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2 ≤ 0 := by
        have : (0:ℝ) ≤ t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2 :=
          mul_nonneg (sq_nonneg t) hsum0
        linarith
      have hy : -(σ ^ 2 * t ^ 2) / 2 ≤ 0 := by
        have : (0:ℝ) ≤ σ ^ 2 * t ^ 2 := by positivity
        linarith
      have hcoe : ((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ) - c
          = ((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2)
              - Real.exp (-(σ ^ 2 * t ^ 2) / 2) : ℝ) : ℂ) := by
        rw [hc]; push_cast; ring
      rw [hcoe, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans (hexpdiff _ _ hx hy) ?_
      have hid : -(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2 - -(σ ^ 2 * t ^ 2) / 2
          = (t ^ 2 / 2) * (σ ^ 2 - ∑ k ∈ Finset.range n, D n k ω ^ 2) := by ring
      rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2 / 2), abs_sub_comm]
    rw [hg, hh2]
    linarith
  -- (3) integrate
  have hIbdd : ∀ (f : Ω → ℝ) (B : ℝ), Measurable f → (∀ ω, |f ω| ≤ B) → Integrable f P := by
    intro f B hf hb
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const B).mono ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_trans (hb ω) (le_abs_self B)
  have hmg : Measurable g := by
    rw [hg]
    refine Measurable.add (Finset.measurable_sum _ (fun k _ => by
      have := hmeas n k; fun_prop)) ?_
    have := Finset.measurable_sum (Finset.range n) (fun k (_ : k ∈ Finset.range n) =>
      (hmeas n k).pow_const 2)
    fun_prop
  have hmh2 : Measurable h2 := by
    rw [hh2]
    have := Finset.measurable_sum (Finset.range n) (fun k (_ : k ∈ Finset.range n) =>
      (hmeas n k).pow_const 2)
    fun_prop
  have hIg : Integrable g P := by
    refine hIbdd g (|t| ^ 3 * (C n * M) + (1 + ‖c‖)) hmg (fun ω => ?_)
    have hnn : 0 ≤ g ω := by
      rw [hg]
      have : (0:ℝ) ≤ ∑ k ∈ Finset.range n, |t * D n k ω| ^ 3 :=
        Finset.sum_nonneg (fun k _ => by positivity)
      linarith [norm_nonneg (((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ) - c)]
    rw [abs_of_nonneg hnn, hg]
    have hcube := hcubeAll ω
    have hgle : ‖((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ) - c‖
        ≤ 1 + ‖c‖ := by
      refine le_trans (norm_sub_le _ _) ?_
      have : ‖((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2) / 2) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_one_iff.mpr ?_
        have hsum0 : (0:ℝ) ≤ ∑ k ∈ Finset.range n, D n k ω ^ 2 :=
          Finset.sum_nonneg (fun k _ => sq_nonneg _)
        have : (0:ℝ) ≤ t ^ 2 * ∑ k ∈ Finset.range n, D n k ω ^ 2 :=
          mul_nonneg (sq_nonneg t) hsum0
        linarith
      linarith
    linarith
  have hIvar : Integrable
      (fun ω => |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2|) P := by
    refine hIbdd _ (M + σ ^ 2) (by
      have := Finset.measurable_sum (Finset.range n) (fun k (_ : k ∈ Finset.range n) =>
        (hmeas n k).pow_const 2)
      fun_prop) (fun ω => ?_)
    have hsum0 : (0:ℝ) ≤ ∑ k ∈ Finset.range n, D n k ω ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [abs_abs, abs_le]
    constructor <;> [linarith [hM n ω, sq_nonneg σ]; linarith [hM n ω, sq_nonneg σ]]
  have hIh2 : Integrable h2 P := by
    rw [hh2]
    exact (integrable_const _).add (hIvar.const_mul _)
  have hmono : ∫ ω, g ω ∂P ≤ ∫ ω, h2 ω ∂P := integral_mono hIg hIh2 hpt
  have hint2 : ∫ ω, h2 ω ∂P
      = |t| ^ 3 * (C n * M)
        + t ^ 2 / 2 * ∫ ω, |(∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2| ∂P := by
    rw [hh2, integral_add (integrable_const _) (hIvar.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hRval : R n = Real.exp (t ^ 2 * M / 2) * ∫ ω, h2 ω ∂P := by
    rw [hR, hint2]
  rw [hRval]
  exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
