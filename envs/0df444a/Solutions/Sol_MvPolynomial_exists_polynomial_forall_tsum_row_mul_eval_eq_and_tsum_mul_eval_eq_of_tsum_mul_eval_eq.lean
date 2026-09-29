-- Prove2me | solution 1 for MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/743ca311-8f67-566d-89b7-fda6d7d2af8c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq

set_option autoImplicit false

namespace RC

open Finset FormalMultilinearSeries

theorem inv_poly_series (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0) :
    ∃ (c : ℕ → ℂ) (R : ℝ), 0 < R ∧ (∀ Y : ℂ, ‖Y‖ < R → D.eval Y ≠ 0) ∧
      ∀ Y : ℂ, ‖Y‖ < R → Summable (fun n => ‖c n * Y ^ n‖) ∧ ∑' n, c n * Y ^ n = (D.eval Y)⁻¹ := by
  have hcont : ContinuousAt (fun Y : ℂ => D.eval Y) 0 := D.continuous.continuousAt
  have hev : ∀ᶠ Y in nhds (0 : ℂ), D.eval Y ≠ 0 := hcont.eventually_ne hD
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hne : ∀ Y : ℂ, ‖Y‖ ≤ ε / 2 → D.eval Y ≠ 0 := fun Y hY =>
    hball Y (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  set R : NNReal := ⟨ε / 2, by positivity⟩ with hRdef
  have hRpos : (0 : NNReal) < R := by
    rw [← NNReal.coe_lt_coe]; show (0 : ℝ) < ε / 2; positivity
  set f : ℂ → ℂ := fun Y => (D.eval Y)⁻¹ with hfdef
  have hdiff : DifferentiableOn ℂ f (closure (Metric.ball (0 : ℂ) R)) := by
    refine (D.differentiable.differentiableOn.inv ?_)
    intro Y hY
    have hY' : Y ∈ Metric.closedBall (0 : ℂ) R := Metric.closure_ball_subset_closedBall hY
    rw [Metric.mem_closedBall, dist_zero_right] at hY'
    exact hne Y hY'
  have hps := hdiff.diffContOnCl.hasFPowerSeriesOnBall hRpos
  refine ⟨fun n => (cauchyPowerSeries f 0 R).coeff n, ε / 2, by positivity, fun Y hY => hne Y hY.le,
    fun Y hY => ?_⟩
  have hYR : ‖Y‖₊ < R := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hY
  have hYball : Y ∈ Metric.eball (0 : ℂ) (R : ENNReal) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]; exact hYR
  have hsum := hps.hasSum hYball
  have hterm : ∀ n, (cauchyPowerSeries f 0 R n fun _ => Y) = (cauchyPowerSeries f 0 R).coeff n * Y ^ n :=
    fun n => by rw [apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  constructor
  · have hs := (cauchyPowerSeries f 0 R).summable_norm_apply (Metric.eball_subset_eball hps.r_le hYball)
    exact hs.congr fun n => by rw [hterm]
  · rw [show (∑' n, (cauchyPowerSeries f 0 R).coeff n * Y ^ n) = ∑' n, cauchyPowerSeries f 0 R n fun _ => Y
        from tsum_congr fun n => (hterm n).symm, hsum.tsum_eq, zero_add]

theorem poly_decomp (P : MvPolynomial (Fin 2) ℂ) :
    ∃ (d : ℕ) (pc : ℕ → Polynomial ℂ), (∀ i, d < i → pc i = 0) ∧
      ∀ X Y : ℂ, MvPolynomial.eval ![X, Y] P = ∑ i ∈ range (d + 1), (pc i).eval X * Y ^ i := by
  classical
  refine ⟨P.support.sup (fun s => s 1),
    fun i => ∑ s ∈ P.support with s 1 = i, Polynomial.monomial (s 0) (P.coeff s), ?_, ?_⟩
  · intro i hi
    refine Finset.sum_eq_zero fun s hs => ?_
    exfalso
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    have := Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s 1) hs1
    omega
  · intro X Y
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_mul]
    symm
    calc ∑ i ∈ range (P.support.sup (fun s => s 1) + 1),
          ∑ s ∈ P.support with s 1 = i, P.coeff s * X ^ (s 0) * Y ^ i
        = ∑ i ∈ range (P.support.sup (fun s => s 1) + 1),
          ∑ s ∈ P.support with s 1 = i, P.coeff s * X ^ (s 0) * Y ^ (s 1) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s hs => ?_
          rw [(Finset.mem_filter.mp hs).2]
      _ = ∑ s ∈ P.support, P.coeff s * X ^ (s 0) * Y ^ (s 1) := by
          refine Finset.sum_fiberwise_of_maps_to (fun s hs => ?_) _
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s 1) hs))
      _ = ∑ s ∈ P.support, P.coeff s * (X ^ (s 0) * Y ^ (s 1)) := by
          refine Finset.sum_congr rfl fun s _ => ?_; ring

theorem rows (A : ℕ × ℕ → ℂ) (X z : ℂ)
    (hS : Summable fun m : ℕ × ℕ => ‖A m * X ^ m.1 * z ^ m.2‖) :
    (∀ j, Summable fun m₁ => ‖A (m₁, j) * X ^ m₁ * z ^ j‖) ∧
    Summable (fun j => ‖(∑' m₁, A (m₁, j) * X ^ m₁) * z ^ j‖) ∧
    ∑' j, (∑' m₁, A (m₁, j) * X ^ m₁) * z ^ j = ∑' m, A m * X ^ m.1 * z ^ m.2 := by
  set g : ℕ × ℕ → ℂ := fun p => A (p.2, p.1) * X ^ p.2 * z ^ p.1 with hg
  have hgn : Summable fun p => ‖g p‖ :=
    ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hS).congr fun p => rfl
  have hg' : Summable g := hgn.of_norm
  have hrow : ∀ j, HasSum (fun m₁ => g (j, m₁)) (∑' m₁, g (j, m₁)) := fun j => (hg'.prod_factor j).hasSum
  have hfib : HasSum (fun j => ∑' m₁, g (j, m₁)) (∑' p, g p) := hg'.hasSum.prod_fiberwise hrow
  have hswap : ∑' p, g p = ∑' m, A m * X ^ m.1 * z ^ m.2 :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (fun m : ℕ × ℕ => A m * X ^ m.1 * z ^ m.2)
  have hinner : ∀ j, ∑' m₁, g (j, m₁) = (∑' m₁, A (m₁, j) * X ^ m₁) * z ^ j := fun j => by
    simp only [hg]; exact tsum_mul_right
  refine ⟨fun j => hgn.prod_factor j, ?_, ?_⟩
  · have hN : Summable fun j => ∑' m₁, ‖g (j, m₁)‖ := hgn.prod
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hN
    rw [← hinner]
    exact norm_tsum_le_tsum_norm (hgn.prod_factor j)
  · simp_rw [← hinner]
    rw [hfib.tsum_eq, hswap]

theorem coeff_unique (a b : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖a n * z ^ n‖)
    (hb : ∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖b n * z ^ n‖)
    (hab : ∀ z : ℂ, ‖z‖ < ρ → ∑' n, a n * z ^ n = ∑' n, b n * z ^ n) : a = b := by
  have hrad : ∀ e : ℕ → ℂ, (∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖e n * z ^ n‖) →
      0 < (ofScalars ℂ e).radius := by
    intro e he
    set ρ' : NNReal := ⟨ρ / 2, by positivity⟩ with hρ'
    have hρ'pos : 0 < ρ' := by
      rw [← NNReal.coe_pos]; show (0 : ℝ) < ρ / 2; positivity
    have hz : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have hs := he _ hz
    have hle : (ρ' : ENNReal) ≤ (ofScalars ℂ e).radius := by
      refine le_radius_of_summable (p := ofScalars ℂ e) (r := ρ') (hs.congr fun n => ?_)
      rw [ofScalars_norm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < ρ / 2)]
      rfl
    exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hρ'pos) hle
  have hpa := ((ofScalars ℂ a).hasFPowerSeriesOnBall (hrad a ha)).hasFPowerSeriesAt
  have hpb := ((ofScalars ℂ b).hasFPowerSeriesOnBall (hrad b hb)).hasFPowerSeriesAt
  have heq : ∀ᶠ z in nhds (0 : ℂ), (ofScalars ℂ a).sum z = (ofScalars ℂ b).sum z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) hρ) fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right] at hz
    show ofScalarsSum a z = ofScalarsSum b z
    rw [ofScalars_sum_eq, ofScalars_sum_eq]
    simp only [smul_eq_mul]
    exact hab z hz
  have := hpa.eq_formalMultilinearSeries_of_eventually hpb heq
  exact ofScalars_series_injective ℂ ℂ this

end RC
open Finset in
theorem solution
    (A : ℕ × ℕ → ℂ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hD₂ : D₂.eval 0 ≠ 0) (hr : 0 < r)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A m * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A m * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) = MvPolynomial.eval ![X, Y] P) :
    ∃ (q : ℕ → Polynomial ℂ) (r₂ : ℝ), 0 < r₂ ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
        Summable (fun m₁ : ℕ => ‖A (m₁, j) * X ^ m₁‖) ∧
        (∑' m₁ : ℕ, A (m₁, j) * X ^ m₁) * D₁.eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < r₂ →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D₂.eval Y = MvPolynomial.eval ![X, Y] P) := by
  classical
  obtain ⟨c, R, hR, hD₂ne, hc⟩ := RC.inv_poly_series D₂ hD₂
  obtain ⟨d, pc, hpc0, hP⟩ := RC.poly_decomp P
  have hII : ∀ X Y : ℂ, ‖Y‖ < R →
      Summable (fun j : ℕ => ‖(∑ i ∈ range (j + 1), pc i * Polynomial.C (c (j - i))).eval X * Y ^ j‖) ∧
      (∑' j : ℕ, (∑ i ∈ range (j + 1), pc i * Polynomial.C (c (j - i))).eval X * Y ^ j) * D₂.eval Y =
        MvPolynomial.eval ![X, Y] P := by
    intro X Y hY
    obtain ⟨hcs, hct⟩ := hc Y hY
    have hu0 : ∀ i ∉ range (d + 1), (pc i).eval X * Y ^ i = 0 := by
      intro i hi
      rw [hpc0 i (by simpa using hi), Polynomial.eval_zero, zero_mul]
    have hus : Summable (fun i => ‖(pc i).eval X * Y ^ i‖) :=
      (hasSum_sum_of_ne_finset_zero (s := range (d + 1)) (f := fun i => ‖(pc i).eval X * Y ^ i‖)
        (fun i hi => by simp only [hu0 i hi, norm_zero])).summable
    have hut : ∑' i, (pc i).eval X * Y ^ i = MvPolynomial.eval ![X, Y] P := by
      rw [(hasSum_sum_of_ne_finset_zero (s := range (d + 1)) hu0).tsum_eq, hP]
    have hqj : ∀ j, (∑ i ∈ range (j + 1), pc i * Polynomial.C (c (j - i))).eval X * Y ^ j =
        ∑ i ∈ range (j + 1), ((pc i).eval X * Y ^ i) * (c (j - i) * Y ^ (j - i)) := by
      intro j
      rw [Polynomial.eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Polynomial.eval_mul, Polynomial.eval_C, ← pow_mul_pow_sub Y hij]
      ring
    have hnorm := summable_norm_sum_mul_range_of_summable_norm
      (f := fun i => (pc i).eval X * Y ^ i) (g := fun l => c l * Y ^ l) hus hcs
    have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (f := fun i => (pc i).eval X * Y ^ i) (g := fun l => c l * Y ^ l) hus hcs
    refine ⟨hnorm.congr fun j => ?_, ?_⟩
    · rw [hqj]
    · calc (∑' j : ℕ, (∑ i ∈ range (j + 1), pc i * Polynomial.C (c (j - i))).eval X * Y ^ j) * D₂.eval Y
          = (∑' n : ℕ, ∑ i ∈ range (n + 1), ((pc i).eval X * Y ^ i) * (c (n - i) * Y ^ (n - i))) *
              D₂.eval Y := by rw [tsum_congr hqj]
        _ = ((∑' i : ℕ, (pc i).eval X * Y ^ i) * ∑' l : ℕ, c l * Y ^ l) * D₂.eval Y := by rw [hprod]
        _ = MvPolynomial.eval ![X, Y] P := by
            rw [hut, hct, mul_assoc, inv_mul_cancel₀ (hD₂ne Y hY), mul_one]
  refine ⟨fun j => ∑ i ∈ range (j + 1), pc i * Polynomial.C (c (j - i)), R, hR, ?_, hII⟩
  intro j X hX
  have hY₀ : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  have hY₀ne : ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (r / 2 : ℝ) ≠ 0 from by positivity)
  obtain ⟨hrows0, -, -⟩ := RC.rows A X _ (h X _ hX hY₀).1
  have hrow : Summable (fun m₁ : ℕ => ‖A (m₁, j) * X ^ m₁‖) := by
    refine ((hrows0 j).mul_right (‖((r / 2 : ℝ) : ℂ) ^ j‖⁻¹)).congr fun m₁ => ?_
    rw [norm_mul, mul_assoc, mul_inv_cancel₀ (by rw [norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hY₀ne)), mul_one]
  refine ⟨hrow, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, ∀ j', a j' = (∑' m₁, A (m₁, j') * X ^ m₁) * D₁.eval X := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, ∀ j',
      b j' = (∑ i ∈ range (j' + 1), pc i * Polynomial.C (c (j' - i))).eval X := ⟨_, fun _ => rfl⟩
  suffices hab : a = b by
    have := congrFun hab j
    rwa [ha, hb] at this
  have hρ : 0 < min r R := lt_min hr hR
  have hEA : ∀ z : ℂ, ‖z‖ < min r R →
      Summable (fun n => ‖a n * z ^ n‖) ∧ (∑' n, a n * z ^ n) * D₂.eval z = MvPolynomial.eval ![X, z] P := by
    intro z hz
    have hzr : ‖z‖ < r := lt_of_lt_of_le hz (min_le_left _ _)
    obtain ⟨hS, hE⟩ := h X z hX hzr
    obtain ⟨-, hN, hT⟩ := RC.rows A X z hS
    constructor
    · refine ((hN.mul_right ‖D₁.eval X‖)).congr fun n => ?_
      rw [ha]
      simp only [norm_mul]; ring
    · have : (∑' n, a n * z ^ n) = (∑' n, (∑' m₁, A (m₁, n) * X ^ m₁) * z ^ n) * D₁.eval X := by
        rw [← tsum_mul_right]
        refine tsum_congr fun n => ?_
        rw [ha]; ring
      rw [this, hT, mul_assoc, hE]
  have hEB : ∀ z : ℂ, ‖z‖ < min r R →
      Summable (fun n => ‖b n * z ^ n‖) ∧ (∑' n, b n * z ^ n) * D₂.eval z = MvPolynomial.eval ![X, z] P := by
    intro z hz
    simp only [hb]
    exact hII X z (lt_of_lt_of_le hz (min_le_right _ _))
  refine RC.coeff_unique a b (min r R) hρ (fun z hz => (hEA z hz).1) (fun z hz => (hEB z hz).1)
    (fun z hz => ?_)
  have hz' : D₂.eval z ≠ 0 := hD₂ne z (lt_of_lt_of_le hz (min_le_right _ _))
  exact mul_right_cancel₀ hz' ((hEA z hz).2.trans (hEB z hz).2.symm)

end S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq
end P2MW
export P2MW.S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq (solution)
