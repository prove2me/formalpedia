-- Prove2me | solution 1 for GuthMaynard.primes_in_almost_all_short_intervals
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T01:11:27.77082+00:00
-- url     : https://prove2.me/submissions/482f2210-0253-4b18-b3c0-af9435e9553b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Definitions.Def_Zeta23_Statement_Seam
import Theorems.Thm_GuthMaynard_zeroDensityCount_le_uniform
import Theorems.Thm_GuthMaynard_zeroDensityCount_eq_zero_vinogradov_korobov
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_GuthMaynard_norm_sum_vonMangoldt_sub_explicit_formula_le

section
open Filter MeasureTheory Set
open scoped ComplexConjugate
namespace GuthMaynardS1213.C14.PartL
open Finset Complex
/-!
Part L of the §14 Blueprint: `L2_bound`.

Route: `((x+y)^ρ - x^ρ)/ρ = ∫_x^{x+y} t^{ρ-1} dt`, Cauchy–Schwarz and Fubini give
`∫_X^{3X} |E|² ≤ y² ∫_X^{4X} |F|²` with `F(t) = Σ m_ρ t^{ρ-1}`; expanding `|F|²` and integrating
`t^{ρ₁ + ρ̄₂ - 2}` gives the pair bound `8 X^{β₁+β₂-1} / (1 + |γ₁ - γ₂|)`; the pair sum over
`ρ₂` is `≪ (log T)²` by the local zero count in unit windows.
-/
/-- `F(t) = Σ_ρ m_ρ t^{ρ-1}`. -/
noncomputable def Fz (S : Finset ℂ) (m : ℂ → ℝ) (t : ℝ) : ℂ :=
  ∑ ρ ∈ S, (m ρ : ℂ) * (t : ℂ) ^ (ρ - 1)

/-- `|F(max t 1)|²`, a globally continuous version of `|F|²`. -/
noncomputable def G (S : Finset ℂ) (m : ℂ → ℝ) (t : ℝ) : ℝ := ‖Fz S m (max t 1)‖ ^ 2

lemma continuousAt_Fz (S : Finset ℂ) (m : ℂ → ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (Fz S m) t := by
  unfold Fz
  refine tendsto_finsetSum _ fun ρ _ => ?_
  exact continuousAt_const.mul (continuousAt_ofReal_cpow_const t _ (Or.inr ht.ne'))

lemma continuous_Fz_max (S : Finset ℂ) (m : ℂ → ℝ) (a : ℝ) :
    Continuous (fun u : ℝ => Fz S m (max (a + u) 1)) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have h : ContinuousAt (Fz S m) (max (a + u) 1) :=
    continuousAt_Fz S m (lt_of_lt_of_le one_pos (le_max_right _ _))
  exact h.comp (f := fun u : ℝ => max (a + u) 1) (by fun_prop)

lemma continuous_G (S : Finset ℂ) (m : ℂ → ℝ) : Continuous (G S m) := by
  have := continuous_Fz_max S m 0
  simp only [zero_add] at this
  exact (this.norm).pow 2

lemma G_nonneg (S : Finset ℂ) (m : ℂ → ℝ) (t : ℝ) : 0 ≤ G S m t := by
  unfold G; positivity

/-- FTC: the explicit-formula sum is the integral of `F`. -/
lemma E_eq (S : Finset ℂ) (m : ℂ → ℝ) (hS : ∀ ρ ∈ S, 0 < ρ.re) {x y : ℝ} :
    ∑ ρ ∈ S, (m ρ : ℂ) * ((((x : ℂ) + y) ^ ρ - (x : ℂ) ^ ρ) / ρ) =
      ∫ t in x..x + y, Fz S m t := by
  unfold Fz
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    have h1 : -1 < (ρ - 1).re := by simp; linarith [hS ρ hρ]
    rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inl h1)]
    push_cast
    simp
  · intro ρ hρ
    have h1 : -1 < (ρ - 1).re := by simp; linarith [hS ρ hρ]
    exact (intervalIntegral.intervalIntegrable_cpow' h1).const_mul _

/-- Cauchy–Schwarz on `[0, y]`. -/
lemma sq_integral_le {g : ℝ → ℝ} (hg : Continuous g) {y : ℝ} (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y, g u) ^ 2 ≤ y * ∫ u in (0 : ℝ)..y, g u ^ 2 := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  set I := ∫ u in (0 : ℝ)..y, g u with hI
  set c := I / y with hc
  have h : ∫ u in (0 : ℝ)..y, (2 * c * g u - c ^ 2) ≤ ∫ u in (0 : ℝ)..y, g u ^ 2 := by
    apply intervalIntegral.integral_mono_on hy.le
    · exact (by fun_prop : Continuous fun u => 2 * c * g u - c ^ 2).intervalIntegrable _ _
    · exact (hg.pow 2).intervalIntegrable _ _
    · intro u _; nlinarith [sq_nonneg (g u - c)]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hI] at h
  · have key : I ^ 2 = y * (2 * c * I - (y - 0) • c ^ 2) := by
      rw [hc, smul_eq_mul]; field_simp; ring
    rw [key]
    exact mul_le_mul_of_nonneg_left h hy.le
  · exact (by fun_prop : Continuous fun u => 2 * c * g u).intervalIntegrable _ _
  · exact intervalIntegrable_const

/-- Pointwise: `|E(x)|² ≤ y ∫_0^y |F(x+u)|² du`. -/
lemma E_sq_le (S : Finset ℂ) (m : ℂ → ℝ) (hS : ∀ ρ ∈ S, 0 < ρ.re) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) :
    ‖∑ ρ ∈ S, (m ρ : ℂ) * ((((x : ℂ) + y) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2 ≤
      y * ∫ u in (0 : ℝ)..y, G S m (x + u) := by
  rw [E_eq S m hS]
  have h1 : ∫ t in x..x + y, Fz S m t = ∫ u in (0 : ℝ)..y, Fz S m (max (x + u) 1) := by
    have h0 := intervalIntegral.integral_comp_add_left (fun t => Fz S m t) (a := 0) (b := y) x
    simp only [add_zero] at h0
    rw [← h0]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hy] at hu
    rw [max_eq_left (by linarith [hu.1])]
  rw [h1]
  have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u => Fz S m (max (x + u) 1)) hy
  calc _ ≤ (∫ u in (0 : ℝ)..y, ‖Fz S m (max (x + u) 1)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ y * ∫ u in (0 : ℝ)..y, ‖Fz S m (max (x + u) 1)‖ ^ 2 :=
        sq_integral_le (continuous_Fz_max S m x).norm hy
    _ = _ := rfl

/-- Fubini: averaging `∫_0^y G(x+u) du` over `x ∈ [X, 3X]`. -/
lemma fubini_bound (S : Finset ℂ) (m : ℂ → ℝ) {X y : ℝ} (hX : 1 ≤ X) (hy : 0 ≤ y) (hyX : y ≤ X)
    (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x ∈ Ioc X (3 * X), f x ≤ y * ∫ u in (0 : ℝ)..y, G S m (x + u)) :
    ∫ x in X..3 * X, f x ≤ y * (y * ∫ t in X..4 * X, G S m t) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  set μ := volume.restrict (Ioc X (3 * X)) with hμ
  set ν := volume.restrict (Ioc (0 : ℝ) y) with hν
  have hcont : Continuous (fun p : ℝ × ℝ => G S m (p.1 + p.2)) :=
    (continuous_G S m).comp (by fun_prop)
  have hInt : Integrable (Function.uncurry fun x u => G S m (x + u)) (μ.prod ν) := by
    rw [hμ, hν, Measure.prod_restrict]
    have := (hcont.continuousOn (s := Icc X (3 * X) ×ˢ Icc (0 : ℝ) y)).integrableOn_compact
      (μ := volume.prod volume) (isCompact_Icc.prod isCompact_Icc)
    exact this.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hGi : IntervalIntegrable (G S m) volume X (4 * X) :=
    (continuous_G S m).intervalIntegrable _ _
  calc ∫ x, f x ∂μ ≤ ∫ x, y * ∫ u, G S m (x + u) ∂ν ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ hf0) (hInt.integral_prod_left.const_mul y) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
        have := hf x hx
        rwa [intervalIntegral.integral_of_le hy] at this
    _ = y * ∫ u, ∫ x, G S m (x + u) ∂μ ∂ν := by
        rw [integral_const_mul, integral_integral_swap hInt]
    _ ≤ y * ∫ _u, (∫ t in X..4 * X, G S m t) ∂ν := by
        refine mul_le_mul_of_nonneg_left ?_ hy
        refine integral_mono_of_nonneg (ae_of_all _ fun u => integral_nonneg fun x => G_nonneg S m _)
          (integrable_const _) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu => ?_)
        dsimp only
        rw [← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_comp_add_right (fun t => G S m t) u]
        refine intervalIntegral.integral_mono_interval (by linarith [hu.1]) (by linarith)
          (by linarith [hu.2]) (ae_of_all _ fun t => G_nonneg S m t) hGi
    _ = y * (y * ∫ t in X..4 * X, G S m t) := by
        rw [integral_const, smul_eq_mul, hν]
        simp [Measure.real, hy]

/-- `|F(t)|²` expanded as a double sum, for `t > 0`. -/
lemma normsq_Fz (S : Finset ℂ) (m : ℂ → ℝ) {t : ℝ} (ht : 0 < t) :
    (((‖Fz S m t‖ ^ 2 : ℝ)) : ℂ) =
      ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S, ((m ρ₁ * m ρ₂ : ℝ) : ℂ) * (t : ℂ) ^ (ρ₁ + conj ρ₂ - 2) := by
  have hconj : ∀ z : ℂ, conj ((t : ℂ) ^ z) = (t : ℂ) ^ (conj z) := by
    intro z
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne
    have := conj_cpow (t : ℂ) z harg
    rw [conj_ofReal] at this
    rw [this, conj_conj]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  rw [← mul_conj', Fz, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ₁ _ => Finset.sum_congr rfl fun ρ₂ _ => ?_
  rw [map_mul, conj_ofReal, hconj, show ρ₁ + conj ρ₂ - 2 = (ρ₁ - 1) + (conj ρ₂ - 1) by ring,
    cpow_add _ _ ht0, map_sub, map_one]
  ring

/-- The basic integral bound. -/
lemma int_bound {X : ℝ} (hX : 1 ≤ X) {w : ℂ} (h2 : w.re ≤ 0) :
    (1 + |w.im|) * ‖∫ t in X..4 * X, (t : ℂ) ^ w‖ ≤ 8 * X ^ (w.re + 1) := by
  have hX0 : 0 < X := by linarith
  have hXr : 0 < X ^ (w.re + 1) := Real.rpow_pos_of_pos hX0 _
  have i1 : ‖∫ t in X..4 * X, (t : ℂ) ^ w‖ ≤ 3 * X ^ (w.re + 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := X) (b := 4 * X)
      (f := fun t : ℝ => (t : ℂ) ^ w) (C := X ^ w.re) (fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        rw [norm_cpow_eq_rpow_re_of_pos (by linarith [ht.1])]
        exact Real.rpow_le_rpow_of_nonpos hX0 ht.1.le h2)
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_add_one hX0.ne', abs_of_nonneg (by linarith)]
    ring
  have i2 : |w.im| * ‖∫ t in X..4 * X, (t : ℂ) ^ w‖ ≤ 5 * X ^ (w.re + 1) := by
    by_cases hw : w = -1
    · subst hw; simp
    have h0 : (0 : ℝ) ∉ Set.uIcc X (4 * X) := by
      rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
    rw [integral_cpow (Or.inr ⟨hw, h0⟩), norm_div]
    have hw1 : w + 1 ≠ 0 := fun h => hw (by linear_combination h)
    have hn : 0 < ‖w + 1‖ := norm_pos_iff.2 hw1
    have him : |w.im| ≤ ‖w + 1‖ := by
      have := abs_im_le_norm (w + 1); simpa using this
    have hnum : ‖((4 * X : ℝ) : ℂ) ^ (w + 1) - (X : ℂ) ^ (w + 1)‖ ≤ 5 * X ^ (w.re + 1) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith), norm_cpow_eq_rpow_re_of_pos hX0]
      simp only [add_re, one_re]
      rw [Real.mul_rpow (by norm_num) hX0.le]
      have h4 : (4 : ℝ) ^ (w.re + 1) ≤ 4 := by
        have := Real.rpow_le_rpow_of_exponent_le (x := 4) (by norm_num)
          (show w.re + 1 ≤ 1 by linarith)
        simpa using this
      nlinarith
    calc |w.im| * (‖((4 * X : ℝ) : ℂ) ^ (w + 1) - (X : ℂ) ^ (w + 1)‖ / ‖w + 1‖)
        ≤ ‖w + 1‖ * (‖((4 * X : ℝ) : ℂ) ^ (w + 1) - (X : ℂ) ^ (w + 1)‖ / ‖w + 1‖) :=
          mul_le_mul_of_nonneg_right him (by positivity)
      _ = ‖((4 * X : ℝ) : ℂ) ^ (w + 1) - (X : ℂ) ^ (w + 1)‖ := by field_simp
      _ ≤ _ := hnum
  nlinarith

/-- AM–GM: `X^{β₁+β₂-1} ≤ X⁻¹ (X^{2β₁} + X^{2β₂}) / 2`. -/
lemma amgm {X : ℝ} (hX : 0 < X) (a b : ℝ) :
    X ^ (a + b - 1) ≤ X⁻¹ * ((X ^ (2 * a) + X ^ (2 * b)) / 2) := by
  have e1 : X ^ (a + b - 1) = X ^ a * X ^ b * X⁻¹ := by
    rw [Real.rpow_sub hX, Real.rpow_add hX, Real.rpow_one, div_eq_mul_inv]
  have e2 : ∀ c : ℝ, X ^ (2 * c) = (X ^ c) ^ 2 := fun c => by
    rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]
  rw [e1, e2, e2]
  have : 0 < X⁻¹ := inv_pos.2 hX
  nlinarith [sq_nonneg (X ^ a - X ^ b)]

/-- The mean square of `F` over `[X, 4X]`. -/
lemma G_bound (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ ρ, 0 ≤ m ρ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1) (K : ℝ)
    (hK : ∀ ρ₁ ∈ S, ∑ ρ₂ ∈ S, m ρ₂ / (1 + |ρ₁.im - ρ₂.im|) ≤ K) {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in X..4 * X, G S m t ≤ 8 * K * X⁻¹ * ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re) := by
  have hX0 : 0 < X := by linarith
  have hcongr : ∫ t in X..4 * X, G S m t = ∫ t in X..4 * X, ‖Fz S m t‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [G]
    rw [max_eq_left (by linarith [ht.1])]
  have hint : ∀ w : ℂ, IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ w) volume X (4 * X) := by
    intro w
    refine intervalIntegral.intervalIntegrable_cpow (Or.inr ?_)
    rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have hC : (((∫ t in X..4 * X, ‖Fz S m t‖ ^ 2 : ℝ)) : ℂ) =
      ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S, ((m ρ₁ * m ρ₂ : ℝ) : ℂ) *
        ∫ t in X..4 * X, (t : ℂ) ^ (ρ₁ + conj ρ₂ - 2) := by
    rw [← intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S,
      ((m ρ₁ * m ρ₂ : ℝ) : ℂ) * (t : ℂ) ^ (ρ₁ + conj ρ₂ - 2)) (fun t ht => by
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact normsq_Fz S m (by linarith [ht.1]))]
    rw [intervalIntegral.integral_finsetSum fun ρ₁ _ => ?_]
    swap
    · have := IntervalIntegrable.sum S fun ρ₂ (_ : ρ₂ ∈ S) =>
        (hint (ρ₁ + conj ρ₂ - 2)).const_mul ((m ρ₁ * m ρ₂ : ℝ) : ℂ)
      rwa [Finset.sum_fn] at this
    refine Finset.sum_congr rfl fun ρ₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum fun ρ₂ _ => (hint _).const_mul _]
    refine Finset.sum_congr rfl fun ρ₂ _ => ?_
    rw [intervalIntegral.integral_const_mul]
  set A : ℂ → ℝ := fun ρ => X ^ (2 * ρ.re) with hA
  set D : ℂ → ℂ → ℝ := fun ρ₁ ρ₂ => 1 + |ρ₁.im - ρ₂.im| with hD
  have hDpos : ∀ ρ₁ ρ₂, 0 < D ρ₁ ρ₂ := fun _ _ => by simp only [hD]; positivity
  have hDsymm : ∀ ρ₁ ρ₂, D ρ₁ ρ₂ = D ρ₂ ρ₁ := fun _ _ => by simp only [hD]; rw [abs_sub_comm]
  have hterm : ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S,
      ‖∫ t in X..4 * X, (t : ℂ) ^ (ρ₁ + conj ρ₂ - 2)‖ ≤ 4 * X⁻¹ * (A ρ₁ + A ρ₂) / D ρ₁ ρ₂ := by
    intro ρ₁ h₁ ρ₂ h₂
    have hb := int_bound hX (w := ρ₁ + conj ρ₂ - 2) (by simp; linarith [(hS ρ₁ h₁).2, (hS ρ₂ h₂).2])
    simp only [sub_re, add_re, conj_re, sub_im, add_im, conj_im, re_ofNat, im_ofNat] at hb
    rw [le_div_iff₀ (hDpos _ _)]
    have hg := amgm hX0 ρ₁.re ρ₂.re
    have e : ρ₁.re + ρ₂.re - 2 + 1 = ρ₁.re + ρ₂.re - 1 := by ring
    rw [e] at hb
    simp only [hD, hA]
    have e2 : ρ₁.im + -ρ₂.im - 0 = ρ₁.im - ρ₂.im := by ring
    rw [e2] at hb
    nlinarith
  have hsplit : ∀ ρ₁ ρ₂, m ρ₁ * m ρ₂ * (4 * X⁻¹ * (A ρ₁ + A ρ₂) / D ρ₁ ρ₂) =
      4 * X⁻¹ * (m ρ₁ * A ρ₁ * (m ρ₂ / D ρ₁ ρ₂)) +
        4 * X⁻¹ * (m ρ₂ * A ρ₂ * (m ρ₁ / D ρ₂ ρ₁)) := by
    intro ρ₁ ρ₂
    rw [hDsymm ρ₂ ρ₁]
    have := (hDpos ρ₁ ρ₂).ne'
    field_simp
  calc ∫ t in X..4 * X, G S m t = ∫ t in X..4 * X, ‖Fz S m t‖ ^ 2 := hcongr
    _ ≤ ‖∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S, ((m ρ₁ * m ρ₂ : ℝ) : ℂ) *
          ∫ t in X..4 * X, (t : ℂ) ^ (ρ₁ + conj ρ₂ - 2)‖ := by
        rw [← hC, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S, m ρ₁ * m ρ₂ * (4 * X⁻¹ * (A ρ₁ + A ρ₂) / D ρ₁ ρ₂) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ₁ h₁ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ₂ h₂ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hm _) (hm _))]
        exact mul_le_mul_of_nonneg_left (hterm ρ₁ h₁ ρ₂ h₂) (mul_nonneg (hm _) (hm _))
    _ = 2 * (4 * X⁻¹ * ∑ ρ₁ ∈ S, m ρ₁ * A ρ₁ * ∑ ρ₂ ∈ S, m ρ₂ / D ρ₁ ρ₂) := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun ρ₁ ρ₂ => 4 * X⁻¹ * (m ρ₂ * A ρ₂ * (m ρ₁ / D ρ₂ ρ₁)))]
        simp_rw [← Finset.mul_sum]
        ring
    _ ≤ 2 * (4 * X⁻¹ * ∑ ρ₁ ∈ S, m ρ₁ * A ρ₁ * K) := by
        gcongr with ρ₁ h₁
        · have : 0 ≤ A ρ₁ := by simp only [hA]; positivity
          exact mul_nonneg (hm _) this
        · exact hK ρ₁ h₁
    _ = 8 * K * X⁻¹ * ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re) := by
        rw [Finset.sum_congr rfl fun ρ _ => show m ρ * A ρ * K = K * (m ρ * X ^ (2 * ρ.re)) by
          simp only [hA]; ring, ← Finset.mul_sum]
        ring

/-- The abstract `L²` bound for a finite weighted set of points in the strip. -/
theorem abstract_bound (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ ρ, 0 ≤ m ρ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1) (K : ℝ)
    (hK : ∀ ρ₁ ∈ S, ∑ ρ₂ ∈ S, m ρ₂ / (1 + |ρ₁.im - ρ₂.im|) ≤ K) {X y : ℝ} (hX : 1 ≤ X)
    (hy : 0 ≤ y) (hyX : y ≤ X) :
    ∫ x in X..3 * X, ‖∑ ρ ∈ S, (m ρ : ℂ) * ((((x : ℂ) + y) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2 ≤
      8 * K * y ^ 2 * X⁻¹ * ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re) := by
  have h1 := fubini_bound S m hX hy hyX
    (fun x => ‖∑ ρ ∈ S, (m ρ : ℂ) * ((((x : ℂ) + y) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2)
    (fun x => by positivity)
    (fun x hx => E_sq_le S m (fun ρ h => (hS ρ h).1) (by linarith [hx.1]) hy)
  have h2 := G_bound S m hm hS K hK hX
  calc _ ≤ y * (y * ∫ t in X..4 * X, G S m t) := h1
    _ ≤ y * (y * (8 * K * X⁻¹ * ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re))) := by gcongr
    _ = _ := by ring

/-! ## The pair sum over zeros -/
lemma finite_box (a b : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ a ≤ ρ.im ∧ ρ.im ≤ b}.Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (1 + |a| + |b|)).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0, h1, h2, h3, h4⟩
  refine ⟨?_, h0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
  have e1 : |ρ.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
  have e2 : |ρ.im| ≤ |a| + |b| :=
    abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  linarith

lemma re_lt_one_of_zero {ρ : ℂ} (h : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h'
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h') h

/-- Unit windows `(k-1, k]` carry multiplicity `≤ A₀ log (T + 4)`. -/
lemma window_zeta {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {T : ℝ} (hT : 0 ≤ T) (Cl : Finset ℂ)
    (hCl : ∀ ρ ∈ Cl, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T) (k : ℤ) :
    ∑ ρ ∈ Cl.filter (fun ρ : ℂ => ⌈ρ.im⌉ = k), (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      A₀ * Real.log (T + 4) := by
  rcases (Cl.filter (fun ρ : ℂ => ⌈ρ.im⌉ = k)).eq_empty_or_nonempty with he | ⟨ρ₀, hρ₀⟩
  · rw [he, sum_empty]
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    positivity
  rw [mem_filter] at hρ₀
  obtain ⟨_, _, hI⟩ := hCl ρ₀ hρ₀.1
  have c1 := Int.le_ceil ρ₀.im
  have c2 := Int.ceil_lt_add_one ρ₀.im
  rw [hρ₀.2] at c1 c2
  have hI' := abs_le.mp hI
  set t : ℝ := (k : ℝ) - 1 with ht
  have htT : |t| ≤ T + 1 := abs_le.mpr ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have hfin : (Zeta23.zerosIn t (t + 1)).Finite := by
    refine (finite_box t (t + 1)).subset ?_
    rintro ρ ⟨⟨h0, h1, h2⟩, h3, h4⟩
    exact ⟨h0, h1.le, h2.le, h3.le, h4⟩
  have hsub : Cl.filter (fun ρ : ℂ => ⌈ρ.im⌉ = k) ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [mem_filter] at hρ
    obtain ⟨h0, h1, _⟩ := hCl ρ hρ.1
    have d1 := Int.le_ceil ρ.im
    have d2 := Int.ceil_lt_add_one ρ.im
    rw [hρ.2] at d1 d2
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨h0, h1, re_lt_one_of_zero h0⟩, by rw [ht]; linarith, by rw [ht]; linarith⟩
  calc ∑ ρ ∈ Cl.filter (fun ρ : ℂ => ⌈ρ.im⌉ = k), (analyticOrderNatAt riemannZeta ρ : ℝ)
      = ((∑ ρ ∈ Cl.filter (fun ρ : ℂ => ⌈ρ.im⌉ = k), Zeta23.zeroMult ρ : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((∑ ρ ∈ hfin.toFinset, Zeta23.zeroMult ρ : ℕ) : ℝ) := by
        exact_mod_cast sum_le_sum_of_subset hsub
    _ = (Zeta23.Ncount t (t + 1) : ℝ) := by
        rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ hfin]
    _ ≤ A₀ * Real.log (|t| + 3) := hA t
    _ ≤ A₀ * Real.log (T + 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.log_le_log (by positivity) (by linarith)

lemma harmonic_real (M : ℕ) :
    ∑ j ∈ range M, (1 : ℝ) / (1 + j) ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  refine le_trans (le_of_eq ?_) h
  simp only [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm, one_div]

lemma log_T4 {T : ℝ} (hT : 2 ≤ T) : Real.log (T + 4) ≤ 3 * Real.log T := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by linarith)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h4 : 4 ≤ T ^ 2 := by nlinarith
  have h5 : 4 * T ≤ T ^ 3 := by
    have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ T by linarith)
    nlinarith
  nlinarith

lemma log_M {T : ℝ} (hT : 2 ≤ T) {M : ℝ} (hM0 : 0 < M) (hM : M ≤ 2 * T + 2) :
    1 + Real.log M ≤ 5 * Real.log T := by
  have h1 : Real.log M ≤ 3 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log hM0
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : 4 ≤ T ^ 2 := by nlinarith
    have h5 : 4 * T ≤ T ^ 3 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ T by linarith)
      nlinarith
    nlinarith
  have h2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have h3 := Real.log_two_gt_d9
  linarith

/-- The pair sum: `Σ_{ρ₂} m₂ / (1 + |γ₁ - γ₂|) ≤ 60 A₀ (log T)²`. -/
lemma pair_sum {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {T : ℝ} (hT : 2 ≤ T) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T) {ρ₁ : ℂ} (hρ₁ : |ρ₁.im| ≤ T) :
    ∑ ρ₂ ∈ S, (analyticOrderNatAt riemannZeta ρ₂ : ℝ) / (1 + |ρ₁.im - ρ₂.im|) ≤
      60 * A₀ * Real.log T ^ 2 := by
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) with hm
  have hm0 : ∀ ρ, 0 ≤ m ρ := fun ρ => by simp only [hm]; positivity
  set k₁ : ℤ := ⌈ρ₁.im⌉ with hk₁
  set n : ℂ → ℕ := fun ρ => (⌈ρ.im⌉ - k₁).natAbs with hn
  set M : ℕ := ⌈2 * T⌉₊ + 1 with hM
  set L : ℝ := A₀ * Real.log (T + 4) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    simp only [hL]; positivity
  have hncast : ∀ ρ, (n ρ : ℝ) = |(⌈ρ.im⌉ : ℝ) - k₁| := fun ρ => by
    simp only [hn]
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  have a1 := Int.le_ceil ρ₁.im
  have a2 := Int.ceil_lt_add_one ρ₁.im
  -- step a
  have stepa : ∀ ρ ∈ S, m ρ / (1 + |ρ₁.im - ρ.im|) ≤ 2 * m ρ / (1 + n ρ) := by
    intro ρ _
    have b1 := Int.le_ceil ρ.im
    have b2 := Int.ceil_lt_add_one ρ.im
    have hnle : (n ρ : ℝ) ≤ 1 + |ρ₁.im - ρ.im| := by
      rw [hncast]
      rw [abs_sub_comm ρ₁.im]
      have : |ρ.im - ρ₁.im| ≥ 0 := abs_nonneg _
      rcases abs_cases ((⌈ρ.im⌉ : ℝ) - k₁) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (ρ.im - ρ₁.im) with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;> linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := hm0 ρ
    nlinarith [mul_le_mul_of_nonneg_left hnle this, mul_nonneg this (abs_nonneg (ρ₁.im - ρ.im))]
  have hnM : ∀ ρ ∈ S, n ρ ∈ range M := by
    intro ρ hρ
    have b1 := Int.le_ceil ρ.im
    have b2 := Int.ceil_lt_add_one ρ.im
    have hI := abs_le.mp (hS ρ hρ).2.2
    have hI1 := abs_le.mp hρ₁
    have hc := Nat.le_ceil (2 * T)
    rw [Finset.mem_range]
    have : (n ρ : ℝ) < M := by
      rw [hncast, hM]; push_cast
      rw [abs_lt]; constructor <;> linarith
    exact_mod_cast this
  have hfib : ∀ j : ℕ, ∑ ρ ∈ S.filter (fun ρ => n ρ = j), m ρ ≤ 2 * L := by
    intro j
    have w1 := window_zeta hA₀ hA (by linarith) S hS (k₁ + j)
    have w2 := window_zeta hA₀ hA (by linarith) S hS (k₁ - j)
    rw [sum_filter] at w1 w2 ⊢
    have : ∑ ρ ∈ S, (if n ρ = j then m ρ else 0) ≤
        ∑ ρ ∈ S, ((if ⌈ρ.im⌉ = k₁ + j then m ρ else 0) +
          (if ⌈ρ.im⌉ = k₁ - j then m ρ else 0)) := by
      refine sum_le_sum fun ρ _ => ?_
      have := hm0 ρ
      by_cases h : n ρ = j
      · have h' : ⌈ρ.im⌉ = k₁ + j ∨ ⌈ρ.im⌉ = k₁ - j := by
          simp only [hn] at h; omega
        rw [if_pos h]
        rcases h' with h' | h'
        · rw [if_pos h']; split_ifs <;> linarith
        · rw [if_pos h']; split_ifs <;> linarith
      · rw [if_neg h]; split_ifs <;> linarith
    rw [sum_add_distrib] at this
    simp only [hm, hL] at this w1 w2 ⊢
    linarith
  calc ∑ ρ₂ ∈ S, (analyticOrderNatAt riemannZeta ρ₂ : ℝ) / (1 + |ρ₁.im - ρ₂.im|)
      = ∑ ρ ∈ S, m ρ / (1 + |ρ₁.im - ρ.im|) := rfl
    _ ≤ ∑ ρ ∈ S, 2 * m ρ / (1 + n ρ) := sum_le_sum stepa
    _ = ∑ j ∈ range M, ∑ ρ ∈ S.filter (fun ρ => n ρ = j), 2 * m ρ / (1 + n ρ) :=
        (sum_fiberwise_of_maps_to hnM _).symm
    _ = ∑ j ∈ range M, (2 / (1 + j)) * ∑ ρ ∈ S.filter (fun ρ => n ρ = j), m ρ := by
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun ρ hρ => ?_
        rw [(mem_filter.mp hρ).2]
        ring
    _ ≤ ∑ j ∈ range M, (2 / (1 + j)) * (2 * L) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hfib j) (by positivity)
    _ = 4 * L * ∑ j ∈ range M, (1 : ℝ) / (1 + j) := by
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
    _ ≤ 4 * L * (1 + Real.log M) := mul_le_mul_of_nonneg_left (harmonic_real M) (by positivity)
    _ ≤ 4 * (A₀ * (3 * Real.log T)) * (5 * Real.log T) := by
        have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hM1 : (0 : ℝ) < M := by rw [hM]; positivity
        have hM2 : (M : ℝ) ≤ 2 * T + 2 := by
          rw [hM]; push_cast
          have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * T by linarith)
          linarith
        have e1 := log_M hT hM1 hM2
        have e2 : L ≤ A₀ * (3 * Real.log T) :=
          mul_le_mul_of_nonneg_left (log_T4 hT) (by linarith)
        have : 0 ≤ 1 + Real.log M := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ M by rw [hM]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * T⌉₊])
          linarith
        gcongr
    _ = 60 * A₀ * Real.log T ^ 2 := by ring

/-! ## The theorem -/
theorem L2_bound :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ X : ℝ, 1 ≤ X → ∀ y : ℝ, 0 ≤ y → y ≤ X →
      ∫ x in X..(3 * X), ‖∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2 ≤
        C * y ^ 2 * Real.log T ^ 2 * X⁻¹ *
          ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
            (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ (2 * ρ.re) := by
  obtain ⟨A₀, hA₀, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨8 * (60 * A₀), fun T hT X hX y hy hyX => ?_⟩
  set Z : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T} with hZ
  have hfin : Z.Finite := by
    apply ((isCompact_closedBall (0 : ℂ) T).inter_riemannZetaZeros_finite).subset
    rintro ρ ⟨h0, _, _, h3⟩
    refine ⟨?_, h0⟩
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hmem : ∀ ρ ∈ hfin.toFinset, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T :=
    fun ρ h => (Set.Finite.mem_toFinset hfin).mp h
  have hS' : ∀ ρ ∈ hfin.toFinset, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T := fun ρ h =>
    ⟨(hmem ρ h).1, (hmem ρ h).2.1, (abs_im_le_norm ρ).trans (hmem ρ h).2.2.2⟩
  have h := abstract_bound hfin.toFinset (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
    (fun ρ => by positivity) (fun ρ h => ⟨(hmem ρ h).2.1, (hmem ρ h).2.2.1⟩)
    (60 * A₀ * Real.log T ^ 2)
    (fun ρ₁ h₁ => pair_sum hA₀ hA hT _ hS' (hS' ρ₁ h₁).2.2) hX hy hyX
  simp only [Complex.ofReal_natCast] at h
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine h.trans (le_of_eq ?_)
  ring

end GuthMaynardS1213.C14.PartL
end

section
namespace GuthMaynardS1213.C14
/-!
Blueprint for Corollary 1.4 (`GuthMaynard.primes_in_almost_all_short_intervals`), §13.2.

* `L2_bound` (Part L): the mean square over `x ∈ [X, 3X]` of the zero sum of the explicit formula
  for `[x, x + y]` is `≪ y² (log T)² X⁻¹ ∑_ρ X^{2 Re ρ}` (pair sum over zeros, local zero count).
* `moment_bound` (Part D): `∑_{|ρ| ≤ T} X^{2 Re ρ} ≤ X² exp(-6 (log X)^{1/4})` for
  `X^{1/100} ≤ T ≤ X^{13/15 - ε}` ((13.3) uniform, Vinogradov–Korobov).
* `psi_exceptional` (Part F): few integers `x ∈ [X, 2X]` have a large error for `ψ(x + y) - ψ(x)`.
* `primes_in_almost_all_short_intervals_dev` (Part G): from `ψ` to `π`.
-/
alias L2_bound := GuthMaynardS1213.C14.PartL.L2_bound

end GuthMaynardS1213.C14
end

section
open Filter
open scoped ENNReal
namespace GuthMaynardS1213.C14.PartD
open Finset Complex
/-!
Part D of the §13.2 Blueprint: `moment_bound`.

Route: discretize `σ` in steps `1/(2K)`, `K = ⌈log X⌉₊`; a zero with `β ≥ 1/2` has
`X^{2β} ≤ e X^{2σ_i}` for the largest `σ_i ≤ β`; zeros with `β < 1/2` are reflected
(`ρ ↦ 1 - conj ρ`) to zeros with `β > 1/2`. Each `X^{2σ} N(σ, T)` is `0` above the
Vinogradov–Korobov line and otherwise `≤ |C| (log X)^{|A|} X² X^{-ε(1-σ)}` by (13.3).
-/
lemma finite_box (a b : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ a ≤ ρ.im ∧ ρ.im ≤ b}.Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (1 + |a| + |b|)).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0, h1, h2, h3, h4⟩
  refine ⟨?_, h0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
  have e1 : |ρ.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
  have e2 : |ρ.im| ≤ |a| + |b| :=
    abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  linarith

lemma re_lt_one_of_zero {ρ : ℂ} (h : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h'
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h') h

lemma zd_set_finite {σ T : ℝ} (hσ : 0 ≤ σ) :
    {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T}.Finite :=
  (finite_box (-T) T).subset fun _ ⟨h0, h1, h2⟩ =>
    ⟨h0, hσ.trans h1, (re_lt_one_of_zero h0).le, (abs_le.mp h2).1, (abs_le.mp h2).2⟩

lemma natOrder_coe {ρ : ℂ} (h : riemannZeta ρ = 0) :
    ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℕ∞) = analyticOrderAt riemannZeta ρ := by
  have h1 : ρ ≠ 1 := fun h1 => by
    have := re_lt_one_of_zero h
    rw [h1] at this
    simp at this
  exact ENat.natCast_toNat (Zeta23.analyticOrderAt_riemannZeta_ne_top h1)

/-- A finite family of zeros counted by `N(σ, T)` has total multiplicity at most the bound. -/
lemma sum_le_count {σ T B : ℝ} (hσ : 0 ≤ σ)
    (hB : (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal B)
    (F : Finset ℂ) (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ max B 0 := by
  have hZ : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T}.Finite := zd_set_finite hσ
  have hsub : F ⊆ hZ.toFinset := fun ρ hρ => by
    rw [Set.Finite.mem_toFinset]; exact hF ρ hρ
  have hcount : LindelofHypothesis.zeroDensityCount σ T =
      ((∑ ρ ∈ hZ.toFinset, analyticOrderNatAt riemannZeta ρ : ℕ) : ℕ∞) := by
    unfold LindelofHypothesis.zeroDensityCount
    have h1 := Finset.tsum_subtype' hZ.toFinset (fun ρ => analyticOrderAt riemannZeta ρ)
    rw [hZ.coe_toFinset] at h1
    rw [h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ρ hρ => (natOrder_coe ?_).symm
    exact (hZ.mem_toFinset.mp hρ).1
  rw [hcount] at hB
  have h2 : ((∑ ρ ∈ hZ.toFinset, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ max B 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
    rw [ENNReal.toReal_ofReal', ENat.toENNReal_coe, ENNReal.toReal_natCast] at this
    exact this
  calc ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ)
      ≤ ∑ ρ ∈ hZ.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ max B 0 := by exact_mod_cast h2

/-- Reflection `ρ ↦ 1 - conj ρ` moves the zeros with `β < 1/2` to zeros with `β > 1/2`. -/
lemma low_reflect {T : ℝ} (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ ‖ρ‖ ≤ T) :
    ∃ G : Finset ℂ, (∀ ρ ∈ G, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) =
        ∑ ρ ∈ G, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  classical
  refine ⟨F.image Zeta23.reflect, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hρ
    obtain ⟨h0, h1, h2, h3⟩ := hF r hr
    have hz := Zeta23.zetaSeam.reflect_zero r ⟨h0, h1, by linarith⟩
    refine ⟨hz.1, ?_, ?_⟩
    · simp only [Zeta23.reflect, sub_re, one_re, conj_re]; linarith
    · simp only [Zeta23.reflect, sub_im, one_im, conj_im, zero_sub, neg_neg]
      exact (Complex.abs_im_le_norm r).trans h3
  · rw [sum_image (fun a _ b _ h => by
      have h' : (starRingEnd ℂ) a = (starRingEnd ℂ) b := by simpa [Zeta23.reflect] using h
      simpa using congrArg (starRingEnd ℂ) h')]
    refine sum_congr rfl fun r hr => ?_
    obtain ⟨h0, h1, h2, h3⟩ := hF r hr
    have := Zeta23.zetaSeam.mult_reflect r ⟨h0, h1, by linarith⟩
    simp only [Zeta23.zeroMult] at this
    simp only [analyticOrderNatAt, this]

lemma delta_le {c T X : ℝ} (hc : 0 < c) (hT3 : 3 ≤ Real.log T) (hLT : Real.log T ≤ Real.log X) :
    c * Real.log X ^ (-(2 / 3) : ℝ) * Real.log (Real.log X) ^ (-(1 / 3) : ℝ) ≤
      c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) := by
  have hlT : 0 < Real.log T := by linarith
  have hll : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have hll' : Real.log (Real.log T) ≤ Real.log (Real.log X) := Real.log_le_log hlT hLT
  have e1 : Real.log X ^ (-(2 / 3) : ℝ) ≤ Real.log T ^ (-(2 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlT hLT (by norm_num)
  have e2 : Real.log (Real.log X) ^ (-(1 / 3) : ℝ) ≤ Real.log (Real.log T) ^ (-(1 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hll hll' (by norm_num)
  have p1 : 0 ≤ Real.log X ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ Real.log (Real.log X) ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
  have p3 : 0 ≤ Real.log T ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg hlT.le _
  calc c * Real.log X ^ (-(2 / 3) : ℝ) * Real.log (Real.log X) ^ (-(1 / 3) : ℝ)
      ≤ c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log X) ^ (-(1 / 3) : ℝ) := by gcongr
    _ ≤ _ := by gcongr

/-- The exponent bookkeeping: `X^{2σ} T^{a(1-σ)} ≤ X² exp(-ε δ' log X)`. -/
lemma exp_part {c ε a X T σ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hc : 0 < c) (hX : 1 < X)
    (hT0 : 0 < T) (hT3 : 3 ≤ Real.log T) (hTL : Real.log T ≤ (13 / 15 - ε) * Real.log X)
    (ha : |a - 30 / 13| ≤ ε / 2)
    (hδ : σ < 1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ)) :
    X ^ (2 * σ) * T ^ (a * (1 - σ)) ≤
      X ^ 2 * Real.exp (-(ε * c * Real.log X * Real.log X ^ (-(2 / 3) : ℝ) *
          Real.log (Real.log X) ^ (-(1 / 3) : ℝ))) := by
  set L := Real.log X with hLdef
  have hL0 : 0 < L := Real.log_pos hX
  have hLT : Real.log T ≤ L := by nlinarith
  have hd := delta_le hc hT3 hLT
  set δ := c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ)
  set δ' := c * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ)
  have hδ'0 : 0 ≤ δ' := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    positivity
  have ha1 := (abs_le.mp ha).1
  have ha2 := (abs_le.mp ha).2
  have hapos : 0 < a := by linarith
  have h2 : Real.log T * a ≤ (2 - ε) * L := by
    have q1 : Real.log T * a ≤ (13 / 15 - ε) * L * a := mul_le_mul_of_nonneg_right hTL hapos.le
    have q2 : (13 / 15 - ε) * a ≤ 2 - ε := by nlinarith
    nlinarith
  have hX0 : 0 < X := by linarith
  rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hT0,
    show X ^ 2 = Real.exp (L * 2) by
      rw [hLdef, ← Real.rpow_natCast, Real.rpow_def_of_pos hX0]; norm_num,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have e1 : ε * c * L * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ) = ε * L * δ' := by ring
  rw [e1]
  have hσδ : δ' ≤ 1 - σ := by linarith
  have k1 : Real.log T * (a * (1 - σ)) ≤ (2 - ε) * L * (1 - σ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 (by linarith)
  have k2 : ε * L * δ' ≤ ε * L * (1 - σ) := mul_le_mul_of_nonneg_left hσδ (by positivity)
  nlinarith

/-- The bound `R(X) = |C| (log X)^{|A|} exp(-ε c (log X)^{1/3} (log log X)^{-1/3})`. -/
noncomputable def Rb (C A c ε X : ℝ) : ℝ :=
  |C| * Real.log X ^ |A| * Real.exp (-(ε * c * Real.log X * Real.log X ^ (-(2 / 3) : ℝ) *
    Real.log (Real.log X) ^ (-(1 / 3) : ℝ)))

lemma Rb_nonneg (C A c ε X : ℝ) (hX : 1 ≤ X) : 0 ≤ Rb C A c ε X := by
  have : 0 ≤ Real.log X := Real.log_nonneg hX
  unfold Rb; positivity

/-- One value of `σ`: `X^{2σ} N(σ, T) ≤ X² R(X)`. -/
lemma key {C A c ε a X T σ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hc : 0 < c) (hX : 1 < X)
    (hT0 : 0 < T) (hT3 : 3 ≤ Real.log T) (hTL : Real.log T ≤ (13 / 15 - ε) * Real.log X)
    (ha : |a - 30 / 13| ≤ ε / 2) (hσ1 : 0 ≤ σ)
    (hN : (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (a * (1 - σ)) * Real.log T ^ A))
    (hV : 1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ →
        LindelofHypothesis.zeroDensityCount σ T = 0)
    (F : Finset ℂ) (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    X ^ (2 * σ) * ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ X ^ 2 * Rb C A c ε X := by
  have hX0 : 0 < X := by linarith
  have hR := Rb_nonneg C A c ε X hX.le
  have hS0 : 0 ≤ ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) := by positivity
  have hXs : 0 ≤ X ^ (2 * σ) := Real.rpow_nonneg hX0.le _
  by_cases hσV : 1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ
  · have h0 := hV hσV
    have hS := sum_le_count (B := 0) hσ1 (by rw [h0]; simp) F hF
    simp only [max_self] at hS
    have : ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) = 0 := le_antisymm hS hS0
    rw [this, mul_zero]
    positivity
  · push Not at hσV
    have hS := sum_le_count hσ1 hN F hF
    have hL0 : 0 < Real.log X := Real.log_pos hX
    have hLT : Real.log T ≤ Real.log X := by nlinarith
    have hP1 : 0 < T ^ (a * (1 - σ)) := Real.rpow_pos_of_pos hT0 _
    have hP2 : 0 < Real.log T ^ A := Real.rpow_pos_of_pos (by linarith) _
    have hS' : ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        |C| * (T ^ (a * (1 - σ)) * Real.log T ^ A) := by
      refine hS.trans (max_le ?_ (by positivity))
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hlog : Real.log T ^ A ≤ Real.log X ^ |A| :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self A)).trans
        (Real.rpow_le_rpow (by linarith) hLT (abs_nonneg A))
    have hE := exp_part hε0 hε hc hX hT0 hT3 hTL ha hσV
    calc X ^ (2 * σ) * ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ)
        ≤ X ^ (2 * σ) * (|C| * (T ^ (a * (1 - σ)) * Real.log T ^ A)) :=
          mul_le_mul_of_nonneg_left hS' hXs
      _ = |C| * (X ^ (2 * σ) * T ^ (a * (1 - σ))) * Real.log T ^ A := by ring
      _ ≤ |C| * (X ^ 2 * Real.exp (-(ε * c * Real.log X * Real.log X ^ (-(2 / 3) : ℝ) *
            Real.log (Real.log X) ^ (-(1 / 3) : ℝ)))) * Real.log X ^ |A| := by
          gcongr
      _ = X ^ 2 * Rb C A c ε X := by unfold Rb; ring

/-- The grid `σ_i = 1/2 + i/(2K)`. -/
noncomputable def sg (K i : ℕ) : ℝ := 1 / 2 + (i : ℝ) / (2 * K)

lemma sg_ge (K i : ℕ) : 1 / 2 ≤ sg K i := by
  unfold sg; have : (0 : ℝ) ≤ (i : ℝ) / (2 * K) := by positivity
  linarith

lemma sg_le {K i : ℕ} (hi : i < K) : sg K i ≤ 1 := by
  unfold sg
  have hK : (0 : ℝ) < K := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  have : (i : ℝ) / (2 * K) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (i : ℝ) ≤ K := by exact_mod_cast hi.le
    linarith
  linarith

lemma pointwise {X β : ℝ} {K : ℕ} (hX : 1 < X) (hK : Real.log X ≤ K) (hK1 : 0 < K)
    (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) :
    X ^ (2 * β) ≤ Real.exp 1 *
      ∑ i ∈ range K, (if sg K i ≤ β then X ^ (2 * sg K i) else 0) := by
  have hX0 : 0 < X := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  set i₀ := ⌊(β - 1 / 2) * (2 * K)⌋₊ with hi₀
  have hnn : 0 ≤ (β - 1 / 2) * (2 * K) := by
    have : 0 ≤ β - 1 / 2 := by linarith
    positivity
  have hi0 : (i₀ : ℝ) ≤ (β - 1 / 2) * (2 * K) := Nat.floor_le hnn
  have hi1 : (β - 1 / 2) * (2 * K) < i₀ + 1 := Nat.lt_floor_add_one _
  have hiK : i₀ < K := by
    have : (i₀ : ℝ) < K := by nlinarith
    exact_mod_cast this
  have hsg : sg K i₀ ≤ β := by
    unfold sg
    have : (i₀ : ℝ) / (2 * K) ≤ β - 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hsg2 : 2 * β ≤ 2 * sg K i₀ + 1 / K := by
    unfold sg
    have : β - 1 / 2 ≤ ((i₀ : ℝ) + 1) / (2 * K) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have e : ((i₀ : ℝ) + 1) / (2 * K) = (i₀ : ℝ) / (2 * K) + 1 / (2 * K) := by
      rw [add_div]
    have e2 : (1 : ℝ) / K = 2 * (1 / (2 * K)) := by field_simp
    linarith
  have hterm : X ^ (2 * β) ≤ Real.exp 1 * X ^ (2 * sg K i₀) := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_add, Real.exp_le_exp]
    have hL0 : 0 ≤ Real.log X := Real.log_nonneg hX.le
    have h1 : Real.log X * (1 / K) ≤ 1 := by
      rw [mul_one_div, div_le_one hKr]; exact hK
    have h2 : Real.log X * (2 * β) ≤ Real.log X * (2 * sg K i₀ + 1 / K) :=
      mul_le_mul_of_nonneg_left hsg2 hL0
    nlinarith
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le)
  have := Finset.single_le_sum (f := fun i => if sg K i ≤ β then X ^ (2 * sg K i) else 0)
    (fun i _ => by
      split_ifs
      · exact Real.rpow_nonneg hX0.le _
      · exact le_refl 0) (Finset.mem_range.mpr hiK)
  simpa [hsg] using this

lemma total {X T R : ℝ} (hX : 1 < X) {K : ℕ} (hK : Real.log X ≤ K) (hK1 : 0 < K) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T)
    (hkey : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset ℂ,
      (∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      X ^ (2 * σ) * ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ X ^ 2 * R) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ (2 * ρ.re) ≤
      (1 + Real.exp 1 * K) * (X ^ 2 * R) := by
  classical
  have hX0 : 0 < X := by linarith
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) with hm
  set g : ℂ → ℝ := fun ρ => (if ρ.re < 1 / 2 then X else 0) +
    Real.exp 1 * ∑ i ∈ range K, (if sg K i ≤ ρ.re then X ^ (2 * sg K i) else 0) with hg
  have hpt : ∀ ρ ∈ S, X ^ (2 * ρ.re) ≤ g ρ := by
    intro ρ hρ
    obtain ⟨_, h1, h2, _⟩ := hS ρ hρ
    have hsum0 : 0 ≤ ∑ i ∈ range K, (if sg K i ≤ ρ.re then X ^ (2 * sg K i) else 0) :=
      Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact Real.rpow_nonneg hX0.le _
        · exact le_refl 0
    by_cases hlow : ρ.re < 1 / 2
    · simp only [hg, if_pos hlow]
      have : X ^ (2 * ρ.re) ≤ X := by
        calc X ^ (2 * ρ.re) ≤ X ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
          _ = X := Real.rpow_one X
      have := mul_nonneg (Real.exp_pos 1).le hsum0
      linarith
    · simp only [hg, if_neg hlow, zero_add]
      exact pointwise hX hK hK1 (not_lt.mp hlow) h2
  have hmain : ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re) ≤ ∑ ρ ∈ S, m ρ * g ρ :=
    Finset.sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (hpt ρ hρ) (by positivity)
  have heq : ∑ ρ ∈ S, m ρ * g ρ = X * ∑ ρ ∈ S.filter (fun ρ => ρ.re < 1 / 2), m ρ +
      Real.exp 1 * ∑ i ∈ range K,
        X ^ (2 * sg K i) * ∑ ρ ∈ S.filter (fun ρ => sg K i ≤ ρ.re), m ρ := by
    simp only [hg, mul_add, Finset.sum_add_distrib, Finset.sum_filter, Finset.mul_sum, mul_ite,
      mul_zero]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun ρ _ => by split_ifs <;> ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> ring
  -- low part
  obtain ⟨G, hG, hGsum⟩ := low_reflect (T := T) (S.filter (fun ρ => ρ.re < 1 / 2)) (by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h0, h1, _, h3⟩ := hS ρ hρ.1
    exact ⟨h0, h1, hρ.2, h3⟩)
  have hlow : X * ∑ ρ ∈ S.filter (fun ρ => ρ.re < 1 / 2), m ρ ≤ X ^ 2 * R := by
    have := hkey (1 / 2) le_rfl (by norm_num) G hG
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, ← hGsum] at this
    exact this
  have hhigh : ∀ i ∈ range K,
      X ^ (2 * sg K i) * ∑ ρ ∈ S.filter (fun ρ => sg K i ≤ ρ.re), m ρ ≤ X ^ 2 * R := by
    intro i hi
    refine hkey (sg K i) (sg_ge K i) (sg_le (Finset.mem_range.mp hi)) _ ?_
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h0, _, _, h3⟩ := hS ρ hρ.1
    exact ⟨h0, hρ.2, (Complex.abs_im_le_norm ρ).trans h3⟩
  have hsumhigh := Finset.sum_le_sum hhigh
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumhigh
  calc ∑ ρ ∈ S, m ρ * X ^ (2 * ρ.re) ≤ ∑ ρ ∈ S, m ρ * g ρ := hmain
    _ = _ := heq
    _ ≤ X ^ 2 * R + Real.exp 1 * (K * (X ^ 2 * R)) := by
        gcongr
    _ = _ := by ring

lemma rpow_inv24 {L : ℝ} (hL : 0 ≤ L) (q : ℝ) (n : ℕ) (hq : q = (n : ℝ) / 24) :
    L ^ q = (L ^ ((1 : ℝ) / 24)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL, hq]
  congr 1
  ring

lemma asymp (D A κ : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hκ : 0 < κ) : ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    D * L ^ (A + 1) * Real.exp (-(κ * L * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ))) ≤
      Real.exp (-6 * L ^ (1 / 4 : ℝ)) := by
  set W := Real.log (D + 1) + 8 * (A + 1) + 6 with hW
  set U := max (2 * W / κ) 1 with hU
  refine ⟨max 2 (U ^ 24), fun L hL => ?_⟩
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hL
  have hLU : U ^ 24 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hlogD : 0 ≤ Real.log (D + 1) := Real.log_nonneg (by linarith)
  set u := L ^ ((1 : ℝ) / 24) with hu
  have hU1 : 1 ≤ U := le_max_right _ _
  have huU : U ≤ u := by
    have := Real.rpow_le_rpow (by positivity) hLU (by norm_num : (0 : ℝ) ≤ 1 / 24)
    rwa [rpow_inv24 (by positivity) (1 / 24) 1 (by norm_num), pow_one,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
    |> fun h => by norm_num at h; exact h
  have hu1 : 1 ≤ u := hU1.trans huU
  have hu0 : 0 < u := by linarith
  have e14 : L ^ (1 / 4 : ℝ) = u ^ 6 := rpow_inv24 hL0.le _ 6 (by norm_num)
  have e13 : L * L ^ (-(2 / 3) : ℝ) = u ^ 8 := by
    rw [← rpow_inv24 hL0.le (1 / 3) 8 (by norm_num)]
    conv_lhs => rw [show L * L ^ (-(2 / 3) : ℝ) = L ^ (1 : ℝ) * L ^ (-(2 / 3) : ℝ) by
      rw [Real.rpow_one]]
    rw [← Real.rpow_add hL0]; norm_num
  have hlogL : Real.log L ≤ 8 * u ^ 3 := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 8)
    rw [rpow_inv24 hL0.le (1 / 8) 3 (by norm_num)] at this
    linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hcube : Real.log L ^ (1 / 3 : ℝ) ≤ 2 * u := by
    have h1 := Real.rpow_le_rpow hlogL0.le hlogL (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h2 : (8 * u ^ 3) ^ (1 / 3 : ℝ) = 2 * u := by
      rw [show (8 : ℝ) * u ^ 3 = (2 * u) ^ (3 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have hneg : 1 / (2 * u) ≤ Real.log L ^ (-(1 / 3) : ℝ) := by
    rw [Real.rpow_neg hlogL0.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogL0 _) hcube
  have hexp1 : κ * u ^ 7 / 2 ≤ κ * L * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ) := by
    rw [mul_assoc κ L, e13]
    calc κ * u ^ 7 / 2 = κ * u ^ 8 * (1 / (2 * u)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hneg (by positivity)
  have hDL : D * L ^ (A + 1) ≤ Real.exp (Real.log (D + 1) + (A + 1) * (8 * u ^ 3)) := by
    rw [Real.exp_add]
    rw [Real.exp_log (by linarith)]
    have h1 : L ^ (A + 1) ≤ Real.exp ((A + 1) * (8 * u ^ 3)) := by
      rw [Real.rpow_def_of_pos hL0]
      refine Real.exp_le_exp.mpr ?_
      have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
      nlinarith
    calc D * L ^ (A + 1) ≤ (D + 1) * L ^ (A + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hL0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by linarith)
  calc D * L ^ (A + 1) * Real.exp (-(κ * L * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ)))
      ≤ Real.exp (Real.log (D + 1) + (A + 1) * (8 * u ^ 3)) * Real.exp (-(κ * u ^ 7 / 2)) := by
        gcongr
    _ ≤ Real.exp (-6 * L ^ (1 / 4 : ℝ)) := by
        rw [← Real.exp_add, Real.exp_le_exp, e14]
        have hWU : 2 * W / κ ≤ u := (le_max_left _ _).trans huU
        have hWu : W ≤ κ * u / 2 := by
          rw [div_le_iff₀ hκ] at hWU; linarith
        have u3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
        have u6 : u ^ 3 ≤ u ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
        have h7 : W * u ^ 6 ≤ κ * u / 2 * u ^ 6 := mul_le_mul_of_nonneg_right hWu (by positivity)
        have e7 : κ * u / 2 * u ^ 6 = κ * u ^ 7 / 2 := by ring
        rw [hW] at h7
        nlinarith

theorem moment_bound :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ T : ℝ, X ^ (1 / 100 : ℝ) ≤ T →
      T ≤ X ^ (13 / 15 - ε) →
      ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ (2 * ρ.re) ≤
        X ^ 2 * Real.exp (-6 * Real.log X ^ (1 / 4 : ℝ)) := by
  intro ε hε
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, A, e, he, hzd⟩ := GuthMaynard.zeroDensityCount_le_uniform
  obtain ⟨c, hc, T₀, hvk⟩ := GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp he (ε' / 2) (by positivity)
  obtain ⟨L₀, hL₀⟩ := asymp (7 * |C|) |A| (ε' * c) (by positivity) (abs_nonneg A) (by positivity)
  set M := |T₀| + |T₁| + 3 with hM
  refine ⟨Real.exp (max (max L₀ 1) (100 * M)), fun X hX T hT1 hT2 => ?_⟩
  set L := Real.log X with hLdef
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hLge : max (max L₀ 1) (100 * M) ≤ L := by
    rw [← Real.log_exp (max (max L₀ 1) (100 * M))]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLge
  have hLL₀ : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hLM : 100 * M ≤ L := le_trans (le_max_right _ _) hLge
  have hX1 : 1 < X := by
    by_contra h
    push Not at h
    have := Real.log_nonpos hXpos.le h
    linarith
  have hT0 : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hT1
  have hlogT1 : L / 100 ≤ Real.log T := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hT1
    rw [Real.log_rpow hXpos] at this
    linarith
  have hlogT2 : Real.log T ≤ (13 / 15 - ε') * L := by
    have := Real.log_le_log hT0 hT2
    rw [Real.log_rpow hXpos] at this
    nlinarith
  have hM3 : 3 ≤ M := by
    have := abs_nonneg T₀; have := abs_nonneg T₁; linarith
  have hlogT3 : 3 ≤ Real.log T := by linarith
  have hTM : M + 1 ≤ T := by
    have h1 : Real.exp M ≤ T := by
      rw [← Real.exp_log hT0]; exact Real.exp_le_exp.mpr (by linarith)
    linarith [Real.add_one_le_exp M]
  have hTT₀ : T₀ ≤ T := by linarith [le_abs_self T₀, abs_nonneg T₁]
  have hTT₁ : T₁ ≤ T := by linarith [le_abs_self T₁, abs_nonneg T₀]
  have hT2' : 2 ≤ T := by linarith [abs_nonneg T₁, abs_nonneg T₀]
  have ha : |(30 / 13 + e T) - 30 / 13| ≤ ε' / 2 := by
    have := hT₁ T hTT₁
    rw [Real.dist_eq, sub_zero] at this
    rw [add_sub_cancel_left]; exact this.le
  have hkey : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset ℂ,
      (∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      X ^ (2 * σ) * ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        X ^ 2 * Rb C A c ε' X :=
    fun σ h1 h2 F hF => key hε'0 hε'1 hc hX1 hT0 hlogT3 hlogT2 ha (by linarith)
      (hzd T hT2' σ ⟨h1, h2⟩) (hvk T hTT₀ σ) F hF
  have hSf : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T}.Finite := by
    refine (finite_box (-T) T).subset ?_
    rintro ρ ⟨h0, h1, h2, h3⟩
    have := (Complex.abs_im_le_norm ρ).trans h3
    exact ⟨h0, h1.le, h2.le, (abs_le.mp this).1, (abs_le.mp this).2⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf]
  have hL0 : 0 < L := by linarith
  have hK : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hK1 : 0 < ⌈L⌉₊ := Nat.ceil_pos.mpr hL0
  have htot := total hX1 hK hK1 hSf.toFinset (fun ρ hρ => hSf.mem_toFinset.mp hρ) hkey
  refine htot.trans ?_
  have hKle : (⌈L⌉₊ : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0.le).le
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hfac : 1 + Real.exp 1 * ⌈L⌉₊ ≤ 7 * L := by
    have := Real.exp_pos 1
    nlinarith
  have hR := Rb_nonneg C A c ε' X hX1.le
  have hfin : (1 + Real.exp 1 * ⌈L⌉₊) * Rb C A c ε' X ≤
      Real.exp (-6 * Real.log X ^ (1 / 4 : ℝ)) := by
    refine (mul_le_mul_of_nonneg_right hfac hR).trans ?_
    have h := hL₀ L hLL₀
    have e1 : 7 * L * Rb C A c ε' X = 7 * |C| * L ^ (|A| + 1) *
        Real.exp (-(ε' * c * L * L ^ (-(2 / 3) : ℝ) * Real.log L ^ (-(1 / 3) : ℝ))) := by
      rw [Real.rpow_add_one hL0.ne']
      unfold Rb
      ring
    rw [e1]
    exact h
  calc (1 + Real.exp 1 * ⌈L⌉₊) * (X ^ 2 * Rb C A c ε' X)
      = X ^ 2 * ((1 + Real.exp 1 * ⌈L⌉₊) * Rb C A c ε' X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)

end GuthMaynardS1213.C14.PartD
end

section
namespace GuthMaynardS1213.C14
alias moment_bound := GuthMaynardS1213.C14.PartD.moment_bound

end GuthMaynardS1213.C14
end

section
open Filter MeasureTheory Set
namespace GuthMaynardS1213.C14.PartF
open Finset Complex
/-!
Part F of the §14 Blueprint: `psi_exceptional`.

Route: with `T = (X/y) exp(2 (log X)^{1/4})` the explicit formula makes the error of
`ψ(x + y) - ψ(x) - y` within `λ/4` of the zero sum `E(x)` for every real `x ∈ [X, 3X]`
(`λ = y exp(-(log X)^{1/4})`); moving `x` within `[n, n + 1)` changes the prime sum by at most
two terms `≤ log(3X + 1) ≤ λ/8`. So every exceptional integer `n` gives `|E| ≥ λ/2` on `(n, n+1)`,
and `L2_bound` with `moment_bound` bounds the number of such `n`.
-/
/-! ## Elementary helpers -/
lemma sum_insert_le' {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (a : ℕ) (s : Finset ℕ) :
    ∑ n ∈ insert a s, f n ≤ f a + ∑ n ∈ s, f n := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]; linarith [hf a]
  · rw [Finset.sum_insert h]

/-- Moving both endpoints of an `Icc` up by at most one changes a nonnegative sum by at most the
two boundary terms. -/
lemma abs_sum_Icc_sub_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {a a' b b' : ℕ}
    (ha : a ≤ a') (ha' : a' ≤ a + 1) (hb : b ≤ b') (hb' : b' ≤ b + 1) :
    |∑ n ∈ Finset.Icc a' b', f n - ∑ n ∈ Finset.Icc a b, f n| ≤ f a + f (b + 1) := by
  have h1 : ∑ n ∈ Finset.Icc a' b', f n ≤ f (b + 1) + ∑ n ∈ Finset.Icc a b, f n := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc a' b')
      (t := insert (b + 1) (Finset.Icc a b)) ?_ fun n _ _ => hf n) (sum_insert_le' hf _ _)
    intro n hn
    rw [Finset.mem_insert, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hn
    omega
  have h2 : ∑ n ∈ Finset.Icc a b, f n ≤ f a + ∑ n ∈ Finset.Icc a' b', f n := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc a b)
      (t := insert a (Finset.Icc a' b')) ?_ fun n _ _ => hf n) (sum_insert_le' hf _ _)
    intro n hn
    rw [Finset.mem_insert, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hn
    omega
  rw [abs_le]
  constructor <;> linarith [hf a, hf (b + 1)]

lemma polyexp (K : ℝ) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : K * (n + 1).factorial ≤ u) :
    K * u ^ n ≤ Real.exp u := by
  have h := Real.pow_div_factorial_le_exp (x := u) hu0 (n + 1)
  have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hun : 0 ≤ u ^ n := pow_nonneg hu0 n
  have : K * u ^ n ≤ u ^ (n + 1) / (n + 1).factorial := by
    rw [le_div_iff₀ hf, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hu hun]
  linarith

/-! ## Counting via the integral -/
lemma count_le_integral (f : ℝ → ℝ) {X : ℝ} (hX : 0 ≤ X) (hf : ContinuousOn f (Icc X (3 * X)))
    (hf0 : ∀ t, 0 ≤ f t) (A : Finset ℕ) (hA : ∀ x ∈ A, X ≤ x ∧ (x : ℝ) + 1 ≤ 3 * X) (c : ℝ)
    (hc : ∀ x ∈ A, ∀ t ∈ Ioo (x : ℝ) (x + 1), c ≤ f t) :
    A.card * c ≤ ∫ t in X..3 * X, f t := by
  have hint : IntegrableOn f (Icc X (3 * X)) := hf.integrableOn_Icc
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hsub : (⋃ x ∈ A, Ioo (x : ℝ) (x + 1)) ⊆ Ioc X (3 * X) := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨by linarith [(hA x hx).1, ht.1], by linarith [(hA x hx).2, ht.2]⟩
  have hdisj : Set.Pairwise (↑A) (Function.onFun Disjoint fun x : ℕ => Ioo (x : ℝ) (x + 1)) := by
    intro x _ x' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro t h1 h2
    apply hne
    have e1 : (x : ℝ) < x' + 1 := by linarith [h1.1, h2.2]
    have e2 : (x' : ℝ) < x + 1 := by linarith [h2.1, h1.2]
    have e1' : x < x' + 1 := by exact_mod_cast e1
    have e2' : x' < x + 1 := by exact_mod_cast e2
    omega
  calc (A.card : ℝ) * c = ∑ x ∈ A, ∫ t in Ioo (x : ℝ) (x + 1), c := by
        simp
    _ ≤ ∑ x ∈ A, ∫ t in Ioo (x : ℝ) (x + 1), f t := by
        refine Finset.sum_le_sum fun x hx => ?_
        refine setIntegral_mono_on (integrableOn_const (by simp)) ?_ measurableSet_Ioo (hc x hx)
        refine hint.mono_set ?_
        intro t ht
        exact ⟨by linarith [(hA x hx).1, ht.1], by linarith [(hA x hx).2, ht.2]⟩
    _ = ∫ t in ⋃ x ∈ A, Ioo (x : ℝ) (x + 1), f t := by
        rw [integral_biUnion_finset A (fun _ _ => measurableSet_Ioo) hdisj]
        intro x hx
        refine hint.mono_set ?_
        intro t ht
        exact ⟨by linarith [(hA x hx).1, ht.1], by linarith [(hA x hx).2, ht.2]⟩
    _ ≤ ∫ t in Ioc X (3 * X), f t :=
        setIntegral_mono_set (hint.mono_set Ioc_subset_Icc_self)
          (ae_of_all _ fun t => hf0 t) (Eventually.of_forall hsub)

/-! ## The zero sum -/
/-- The zeros counted by the explicit formula. -/
def Zset (T : ℝ) : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T}

/-- The zero sum of the explicit formula for `[t, t + y]`. -/
noncomputable def E (T y t : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ Zset T, (analyticOrderNatAt riemannZeta ρ : ℂ) * (((t + y : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ)

lemma Zset_finite (T : ℝ) : (Zset T).Finite := by
  apply ((isCompact_closedBall (0 : ℂ) T).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨h0, _, _, h3⟩
  refine ⟨?_, h0⟩
  rwa [Metric.mem_closedBall, dist_zero_right]

lemma continuousOn_E (T : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    ContinuousOn (fun t => ‖E T y t‖ ^ 2) (Ioi 0) := by
  have hfin := Zset_finite T
  have heq : (fun t => ‖E T y t‖ ^ 2) = fun t : ℝ => ‖∑ ρ ∈ hfin.toFinset,
      (analyticOrderNatAt riemannZeta ρ : ℂ) * (((t + y : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ)‖ ^ 2 :=
    funext fun t => by rw [E, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [heq]
  refine ((continuousOn_finsetSum _ fun ρ _ => ?_).norm).pow 2
  refine continuousOn_of_forall_continuousAt fun t (ht : 0 < t) => ?_
  have h1 : ContinuousAt (fun t : ℝ => ((t : ℂ) + y) ^ ρ) t := by
    have := (continuousAt_ofReal_cpow_const (t + y) ρ (Or.inr (by positivity))).comp
      (f := fun t : ℝ => t + y) (continuous_add_const y).continuousAt
    simpa [Function.comp_def] using this
  have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ ρ) t :=
    continuousAt_ofReal_cpow_const t ρ (Or.inr ht.ne')
  exact continuousAt_const.mul ((h1.sub h2).div_const _)

lemma vonMangoldt_le_log_of_le {n : ℕ} {B : ℝ} (hB : 1 ≤ B) (h : (n : ℝ) ≤ B) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero]; exact Real.log_nonneg hB
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) h)

/-- An exceptional integer `x` forces `|E| ≥ λ/2` on `(x, x + 1)`. -/
lemma pointwise {X y lam : ℝ} (E' : ℝ → ℂ) (hX : 1 ≤ X) (hy : 0 ≤ y) (hyX : y ≤ X)
    (hEF : ∀ t, X ≤ t → t ≤ 3 * X →
      ‖(∑ n ∈ Finset.Icc ⌈t⌉₊ ⌊t + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y + E' t‖ ≤
        lam / 4)
    (hjump : 2 * Real.log (3 * X + 1) ≤ lam / 4)
    {x : ℕ} (hx1 : X ≤ x) (hx2 : (x : ℝ) ≤ 2 * X)
    (hexc : lam < |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y|)
    {t : ℝ} (ht : t ∈ Ioo (x : ℝ) (x + 1)) : lam / 2 ≤ ‖E' t‖ := by
  set S' := ∑ n ∈ Finset.Icc ⌈t⌉₊ ⌊t + y⌋₊, ArithmeticFunction.vonMangoldt n with hS'
  set S := ∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n with hS
  have h1 := hEF t (by linarith [ht.1]) (by linarith [ht.2])
  have hc : (∑ n ∈ Finset.Icc ⌈t⌉₊ ⌊t + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y =
      ((S' - y : ℝ) : ℂ) := by rw [hS']; push_cast; rfl
  rw [hc] at h1
  have h2 : |S' - y| ≤ ‖((S' - y : ℝ) : ℂ) + E' t‖ + ‖E' t‖ := by
    have := norm_sub_le (((S' - y : ℝ) : ℂ) + E' t) (E' t)
    rwa [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at this
  have hxy : 0 ≤ (x : ℝ) + y := by positivity
  have hj : |S' - S| ≤ ArithmeticFunction.vonMangoldt x +
      ArithmeticFunction.vonMangoldt (⌊(x : ℝ) + y⌋₊ + 1) := by
    refine abs_sum_Icc_sub_le (fun n => ArithmeticFunction.vonMangoldt_nonneg) ?_ ?_ ?_ ?_
    · have := Nat.le_ceil t
      have : (x : ℝ) < ⌈t⌉₊ := by linarith [ht.1]
      exact_mod_cast this.le
    · exact Nat.ceil_le.2 (by push_cast; linarith [ht.2])
    · exact Nat.floor_mono (by linarith [ht.1])
    · rw [← Nat.floor_add_one hxy]; exact Nat.floor_mono (by linarith [ht.2])
  have hB : (1 : ℝ) ≤ 3 * X + 1 := by linarith
  have l1 := vonMangoldt_le_log_of_le (n := x) hB (by linarith)
  have l2 := vonMangoldt_le_log_of_le (n := ⌊(x : ℝ) + y⌋₊ + 1) hB (by
    push_cast; linarith [Nat.floor_le hxy])
  have k1 : |S - y| ≤ |S' - y| + |S' - S| := by
    have := abs_sub (S' - y) (S' - S)
    rwa [show S' - y - (S' - S) = S - y by ring] at this
  linarith

/-! ## The theorem -/
set_option maxHeartbeats 1000000 in
theorem psi_exceptional :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ y : ℝ,
      y ∈ Set.Icc (X ^ (2 / 15 + ε)) (X ^ (0.99 : ℝ)) →
      ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          y * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) <
            |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y|).card ≤
        X * Real.exp (-2 * Real.log X ^ (1 / 4 : ℝ)) := by
  intro ε hε
  obtain ⟨CE, hCE⟩ := GuthMaynard.norm_sum_vonMangoldt_sub_explicit_formula_le
  obtain ⟨CL, hCL⟩ := L2_bound
  obtain ⟨X₁, hX₁⟩ := moment_bound (ε / 2) (by positivity)
  set K := |CE| with hK
  set CP := max CL 0 with hCP
  set U : ℝ := max (max 10 (96 * K * (Nat.factorial 13))) (max (4 * CP * (Nat.factorial 9)) (4 / ε))
    with hU
  refine ⟨max (max X₁ 4) (Real.exp (U ^ 4)), fun X hX y hy => ?_⟩
  have hX₁X : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX4 : 4 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXU : Real.exp (U ^ 4) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hU10 : 10 ≤ U := le_trans (le_max_left _ _) (le_max_left _ _)
  have hUK : 96 * K * (Nat.factorial 13) ≤ U := le_trans (le_max_right _ _) (le_max_left _ _)
  have hUC : 4 * CP * (Nat.factorial 9) ≤ U := le_trans (le_max_left _ _) (le_max_right _ _)
  have hUε : 4 / ε ≤ U := le_trans (le_max_right _ _) (le_max_right _ _)
  set ℓ := Real.log X with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  set u := ℓ ^ (1 / 4 : ℝ) with hu
  have hu4 : u ^ 4 = ℓ := by
    rw [hu, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hℓ0 (by norm_num)
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hUu : U ≤ u := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hu0 ?_
    rw [hu4, hℓ, Real.le_log_iff_exp_le hXpos]; exact hXU
  have hu10 : 10 ≤ u := by linarith
  have hu3 : 1000 ≤ u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hu10 3]
  -- `y`
  obtain ⟨hylo, hyhi⟩ := hy
  rw [Real.rpow_def_of_pos hXpos] at hylo hyhi
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hylo
  set ly := Real.log y with hly
  have hly1 : ℓ * (2 / 15 + ε) ≤ ly := (Real.le_log_iff_exp_le hy0).2 hylo
  have hly2 : ly ≤ ℓ * 0.99 := (Real.log_le_iff_le_exp hy0).2 hyhi
  have hyexp : y = Real.exp ly := (Real.exp_log hy0).symm
  have hXexp : X = Real.exp ℓ := (Real.exp_log hXpos).symm
  have hyX : y ≤ X := by
    rw [hyexp, hXexp, Real.exp_le_exp]; nlinarith
  set lam := y * Real.exp (-u) with hlam
  have hlamexp : lam = Real.exp (ly - u) := by
    rw [hlam, hyexp, ← Real.exp_add]; ring_nf
  -- `T`
  set T := Real.exp (ℓ - ly + 2 * u) with hT
  have hℓε : 0 ≤ ℓ * ε := mul_nonneg hℓ0 hε.le
  have hεu : 2 * u ≤ ε / 2 * ℓ := by
    rw [← hu4]
    have h1 : 4 / ε ≤ u := by linarith
    have h2 : 4 ≤ ε * u := by rwa [div_le_iff₀ hε, mul_comm] at h1
    have h3 : 4 * u ^ 3 ≤ ε * u * u ^ 3 := mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : u ≤ u ^ 3 := by
      have : 1 ≤ u ^ 2 := by nlinarith
      calc u = u * 1 := (mul_one u).symm
        _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left this hu0
        _ = u ^ 3 := by ring
    have e : ε * u * u ^ 3 = ε * u ^ 4 := by ring
    linarith
  have hT2 : 2 ≤ T := by
    have : 1 ≤ ℓ - ly + 2 * u := by linarith
    have h := Real.add_one_le_exp (ℓ - ly + 2 * u)
    rw [hT]; linarith
  have hTlo : X ^ (1 / 100 : ℝ) ≤ T := by
    rw [Real.rpow_def_of_pos hXpos, hT, Real.exp_le_exp]; linarith
  have hThi : T ≤ X ^ (13 / 15 - ε / 2) := by
    rw [Real.rpow_def_of_pos hXpos, hT, Real.exp_le_exp]; linarith
  have hTX : T ≤ X := by
    rw [hXexp, hT, Real.exp_le_exp]; linarith
  have hlogT : Real.log T = ℓ - ly + 2 * u := by rw [hT, Real.log_exp]
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTle : Real.log T ≤ u ^ 4 := by rw [hlogT, hu4]; linarith
  -- the explicit formula is within `λ/4`
  have hu12 : 96 * K * u ^ 12 ≤ Real.exp u :=
    polyexp (96 * K) 12 hu0 (by have := hUK.trans hUu; norm_num [Nat.factorial] at this ⊢; linarith)
  have hK0 : 0 ≤ K := abs_nonneg _
  have hXT : X / T = Real.exp (ly - 2 * u) := by
    rw [hT, hXexp, ← Real.exp_sub]; congr 1; ring
  have hlam2 : lam = Real.exp (ly - 2 * u) * Real.exp u := by
    rw [hlamexp, ← Real.exp_add]; congr 1; ring
  have hEF : ∀ t, X ≤ t → t ≤ 3 * X →
      ‖(∑ n ∈ Finset.Icc ⌈t⌉₊ ⌊t + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y + E T y t‖ ≤
        lam / 4 := by
    intro t ht1 ht3
    have h : ‖(∑ n ∈ Finset.Icc ⌈t⌉₊ ⌊t + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y +
        E T y t‖ ≤ CE * t * Real.log t ^ 3 / T :=
      hCE t T y hT2 (hTX.trans ht1) hy0.le (hyX.trans ht1)
    refine h.trans ?_
    have ht0 : 0 < t := by linarith
    have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hlt : Real.log t ≤ 2 * ℓ := by
      have e : 2 * ℓ = Real.log (X ^ 2) := by rw [hℓ, Real.log_pow]; norm_num
      rw [e]
      have : 4 * X ≤ X * X := mul_le_mul_of_nonneg_right hX4 hXpos.le
      exact Real.log_le_log ht0 (by rw [sq]; linarith)
    have hnum : CE * t * Real.log t ^ 3 ≤ K * (3 * X) * (2 * ℓ) ^ 3 := by
      calc CE * t * Real.log t ^ 3 ≤ K * t * Real.log t ^ 3 := by
            gcongr; exact le_abs_self CE
        _ ≤ K * (3 * X) * (2 * ℓ) ^ 3 := by gcongr
    have hTpos : 0 < T := by linarith
    calc CE * t * Real.log t ^ 3 / T ≤ K * (3 * X) * (2 * ℓ) ^ 3 / T :=
          div_le_div_of_nonneg_right hnum hTpos.le
      _ = 24 * K * u ^ 12 * (X / T) := by rw [← hu4]; ring
      _ = (96 * K * u ^ 12) * Real.exp (ly - 2 * u) / 4 := by rw [hXT]; ring
      _ ≤ Real.exp u * Real.exp (ly - 2 * u) / 4 := by gcongr
      _ = lam / 4 := by rw [hlam2]; ring
  -- moving inside a unit interval costs at most `λ/4`
  have hjump : 2 * Real.log (3 * X + 1) ≤ lam / 4 := by
    have h1 : Real.log (3 * X + 1) ≤ 2 * ℓ := by
      have e : 2 * ℓ = Real.log (X ^ 2) := by rw [hℓ, Real.log_pow]; norm_num
      rw [e]
      have : 4 * X ≤ X * X := mul_le_mul_of_nonneg_right hX4 hXpos.le
      exact Real.log_le_log (by linarith) (by rw [sq]; linarith)
    have e4 : u ^ 4 = u * u ^ 3 := by ring
    have hk : u * 1000 ≤ u * u ^ 3 := mul_le_mul_of_nonneg_left hu3 hu0
    have hu4big : 10000 ≤ u ^ 4 := by
      have := mul_le_mul hu10 hu3 (by norm_num) hu0
      linarith
    have h2 : u ^ 4 / 15 ≤ ly - u := by
      linarith
    have h3 : 240 * (u ^ 4 / 15) ^ 1 ≤ Real.exp (u ^ 4 / 15) :=
      polyexp 240 1 (by positivity) (by norm_num [Nat.factorial]; linarith)
    have h4 : Real.exp (u ^ 4 / 15) ≤ lam := by rw [hlamexp]; exact Real.exp_le_exp.2 h2
    rw [← hu4] at h1
    norm_num at h3
    linarith
  -- counting
  have hlam0 : 0 < lam := by rw [hlamexp]; exact Real.exp_pos _
  set A := (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
      lam < |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y| with hA
  have hAmem : ∀ x ∈ A, X ≤ x ∧ (x : ℝ) ≤ 2 * X ∧
      lam < |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y| := by
    intro x hx
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨Nat.ceil_le.1 hx.1.1, (Nat.le_floor_iff (by linarith)).1 hx.1.2, hx.2⟩
  have hcount := count_le_integral (fun t => ‖E T y t‖ ^ 2) hXpos.le
    ((continuousOn_E T hy0.le).mono fun t ht => lt_of_lt_of_le hXpos ht.1)
    (fun t => by positivity) A
    (fun x hx => ⟨(hAmem x hx).1, by linarith [(hAmem x hx).2.1]⟩) ((lam / 2) ^ 2)
    (fun x hx t ht => pow_le_pow_left₀ (by positivity)
      (pointwise (E T y) (by linarith) hy0.le hyX hEF hjump (hAmem x hx).1 (hAmem x hx).2.1
        (hAmem x hx).2.2 ht) 2)
  set M := ∑ᶠ ρ ∈ Zset T, (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ (2 * ρ.re) with hMdef
  have hL2 : ∫ t in X..3 * X, ‖E T y t‖ ^ 2 ≤ CL * y ^ 2 * Real.log T ^ 2 * X⁻¹ * M :=
    hCL T hT2 X (by linarith) y hy0.le hyX
  have hM : M ≤ X ^ 2 * Real.exp (-6 * u) := hX₁ X hX₁X T hTlo hThi
  have hM0 : 0 ≤ M := by
    rw [hMdef, finsum_mem_eq_finite_toFinset_sum _ (Zset_finite T)]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hP : 0 ≤ y ^ 2 * Real.log T ^ 2 * X⁻¹ * M := by positivity
  have hCP0 : 0 ≤ CP := le_max_right _ _
  have hlt2 : Real.log T ^ 2 ≤ (u ^ 4) ^ 2 := pow_le_pow_left₀ hlogT0 hlogTle 2
  set a := Real.exp (-u) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have e2 : Real.exp (-2 * u) = a ^ 2 := by rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e6 : Real.exp (-6 * u) = a ^ 6 := by rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hv : 4 * CP * u ^ 8 * a ^ 2 ≤ 1 := by
    have h1 : 4 * CP * u ^ 8 ≤ Real.exp u :=
      polyexp (4 * CP) 8 hu0 (by have := hUC.trans hUu; norm_num [Nat.factorial] at this ⊢; linarith)
    have h2 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (2 * u) * a ^ 2 = 1 := by
      rw [ha, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have := mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg a)
    linarith
  have hfin : (A.card : ℝ) * (lam / 2) ^ 2 ≤ (X * a ^ 2) * (lam / 2) ^ 2 := by
    have s1 : (A.card : ℝ) * (lam / 2) ^ 2 ≤ CP * (y ^ 2 * Real.log T ^ 2 * X⁻¹ * M) := by
      calc (A.card : ℝ) * (lam / 2) ^ 2 ≤ CL * (y ^ 2 * Real.log T ^ 2 * X⁻¹ * M) := by
            refine hcount.trans (hL2.trans (le_of_eq ?_)); ring
        _ ≤ CP * (y ^ 2 * Real.log T ^ 2 * X⁻¹ * M) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hP
    have s2 : y ^ 2 * Real.log T ^ 2 * X⁻¹ * M ≤
        (y ^ 2 * X⁻¹) * ((u ^ 4) ^ 2 * (X ^ 2 * a ^ 6)) := by
      rw [← e6]
      calc y ^ 2 * Real.log T ^ 2 * X⁻¹ * M = (y ^ 2 * X⁻¹) * (Real.log T ^ 2 * M) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hlt2 hM hM0 (by positivity))
            (by positivity)
    have s3 : CP * ((y ^ 2 * X⁻¹) * ((u ^ 4) ^ 2 * (X ^ 2 * a ^ 6))) =
        (y ^ 2 * X * a ^ 4) * (CP * u ^ 8 * a ^ 2) := by
      field_simp
    have s4 : (y ^ 2 * X * a ^ 4) * (CP * u ^ 8 * a ^ 2) ≤ (y ^ 2 * X * a ^ 4) * (1 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have s5 : (X * a ^ 2) * (lam / 2) ^ 2 = (y ^ 2 * X * a ^ 4) * (1 / 4) := by
      rw [hlam]; ring
    calc (A.card : ℝ) * (lam / 2) ^ 2 ≤ CP * (y ^ 2 * Real.log T ^ 2 * X⁻¹ * M) := s1
      _ ≤ CP * ((y ^ 2 * X⁻¹) * ((u ^ 4) ^ 2 * (X ^ 2 * a ^ 6))) :=
          mul_le_mul_of_nonneg_left s2 hCP0
      _ = _ := s3
      _ ≤ _ := s4
      _ = _ := s5.symm
  rw [e2]
  exact le_of_mul_le_mul_right hfin (by positivity)

end GuthMaynardS1213.C14.PartF
end

section
namespace GuthMaynardS1213.C14
alias psi_exceptional := GuthMaynardS1213.C14.PartF.psi_exceptional

end GuthMaynardS1213.C14
end

section
open Filter Topology
namespace GuthMaynardS1213.C14.PartG
lemma pi_sub (a b : ℕ) (h : a ≤ b) :
    ((Nat.primeCounting b : ℝ) - Nat.primeCounting a) =
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) := by
  have key : (Finset.range (b + 1)).filter Nat.Prime =
      (Finset.range (a + 1)).filter Nat.Prime ∪ (Finset.Ioc a b).filter Nat.Prime := by
    ext n; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hn : n < a + 1
      · exact Or.inl ⟨hn, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h3⟩
  have hd : Disjoint ((Finset.range (a + 1)).filter Nat.Prime) ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at h1 h2
    omega
  have : Nat.primeCounting b = Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card := by
    simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [key, Finset.card_union_of_disjoint hd]
  rw [this]; push_cast; ring

/-- A finite set of naturals with pairwise gaps controlled has bounded size. -/
lemma card_le_of_spread (S : Finset ℕ) (D L : ℝ) (hD : 0 < D) (hL : 0 ≤ L)
    (h : ∀ a ∈ S, ∀ c ∈ S, a < c → ((c : ℝ) - a) * D ≤ L) :
    (S.card : ℝ) ≤ L / D + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp; positivity
  set a := S.min' hS
  set c := S.max' hS
  have hac : a ≤ c := S.min'_le_max' hS
  have hsub : S ⊆ Finset.Icc a c := fun n hn =>
    Finset.mem_Icc.2 ⟨S.min'_le n hn, S.le_max' n hn⟩
  have hcard : (S.card : ℝ) ≤ (c : ℝ) - a + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((c + 1 - a : ℕ) : ℝ) = (c : ℝ) + 1 - a := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : (S.card : ℝ) ≤ ((c + 1 - a : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  rcases hac.lt_or_eq with hlt | heq
  · have := h a (S.min'_mem hS) c (S.max'_mem hS) hlt
    have : (c : ℝ) - a ≤ L / D := by rw [le_div_iff₀ hD]; exact this
    linarith
  · rw [heq] at hcard
    have : 0 ≤ L / D := div_nonneg hL hD.le
    linarith

/-- k-th powers (k ≥ 2) in `(x, x + y]` are spread by at least `√x`. -/
lemma kpow_spread (x : ℕ) (y : ℝ) (k : ℕ) (hk : 2 ≤ k) (m1 m2 : ℕ) (h12 : m1 < m2)
    (h1 : x < m1 ^ k) (h2 : ((m2 ^ k : ℕ) : ℝ) ≤ x + y) :
    ((m2 : ℝ) - m1) * Real.sqrt x ≤ y := by
  have hm1 : 1 ≤ m1 := by
    rcases Nat.eq_zero_or_pos m1 with h | h
    · subst h; rw [zero_pow (by omega)] at h1; omega
    · exact h
  have hpow : m1 ^ k ≤ (m1 ^ (k - 1)) ^ 2 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hm1 (by omega)
  have hsq : Real.sqrt x ≤ (m1 : ℝ) ^ (k - 1) := by
    have : (x : ℝ) ≤ ((m1 : ℝ) ^ (k - 1)) ^ 2 := by
      have : x ≤ (m1 ^ (k - 1)) ^ 2 := by omega
      exact_mod_cast this
    calc Real.sqrt x ≤ Real.sqrt (((m1 : ℝ) ^ (k - 1)) ^ 2) := Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq (by positivity)
  have hk' : k = (k - 1) + 1 := by omega
  have hA : (m2 : ℝ) * (m1 : ℝ) ^ (k - 1) ≤ (m2 : ℝ) ^ k := by
    conv_rhs => rw [hk', pow_succ]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h12.le) _
  have hB : (m1 : ℝ) ^ k = (m1 : ℝ) * (m1 : ℝ) ^ (k - 1) := by
    conv_lhs => rw [hk', pow_succ]
    ring
  have h1' : (x : ℝ) < (m1 : ℝ) ^ k := by exact_mod_cast h1
  have h2' : (m2 : ℝ) ^ k ≤ x + y := by exact_mod_cast h2
  have hd : 0 ≤ (m2 : ℝ) - m1 := by
    have : (m1 : ℝ) < m2 := by exact_mod_cast h12
    linarith
  calc ((m2 : ℝ) - m1) * Real.sqrt x ≤ ((m2 : ℝ) - m1) * (m1 : ℝ) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hsq hd
    _ = (m2 : ℝ) * (m1 : ℝ) ^ (k - 1) - (m1 : ℝ) ^ k := by rw [hB]; ring
    _ ≤ y := by linarith

/-- Count of proper prime powers in `(x, b]` with `b ≤ x + y`. -/
lemma pp_count (x b : ℕ) (y : ℝ) (hx : 1 ≤ x) (hy : 0 ≤ y) (hb : (b : ℝ) ≤ x + y) :
    (((Finset.Ioc x b).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card : ℝ) ≤
      (Nat.log 2 b : ℝ) * (y / Real.sqrt x + 1) := by
  set K := Nat.log 2 b
  set T : ℕ → Finset ℕ := fun k =>
    (Finset.range (b + 1)).filter fun m => x < m ^ k ∧ m ^ k ≤ b
  have hsub : ((Finset.Ioc x b).filter fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
      (Finset.Icc 2 K).biUnion fun k => (T k).image fun m => m ^ k := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hxn, hnb⟩, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra hc
      have : k = 1 := by omega
      subst this; simp at hnp; exact hnp hp
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le (by norm_num)
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hnb
    have hpb : p ≤ b := le_trans (Nat.le_self_pow (by omega) p) hnb
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    refine ⟨k, ⟨hk2, hkK⟩, p, ?_, rfl⟩
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hxn, hnb⟩
  have hxpos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
  have hT : ∀ k ∈ Finset.Icc 2 K, (((T k).image fun m => m ^ k).card : ℝ) ≤ y / Real.sqrt x + 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine le_trans (b := ((T k).card : ℝ)) (by exact_mod_cast Finset.card_image_le) ?_
    apply card_le_of_spread _ _ _ hxpos hy
    intro a ha c hc hac
    simp only [T, Finset.mem_filter, Finset.mem_range] at ha hc
    apply kpow_spread x y k hk.1 a c hac ha.2.1
    exact le_trans (by exact_mod_cast hc.2.2) hb
  calc (((Finset.Ioc x b).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card : ℝ)
      ≤ (((Finset.Icc 2 K).biUnion fun k => (T k).image fun m => m ^ k).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 2 K, (((T k).image fun m => m ^ k).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 2 K, (y / Real.sqrt x + 1) := Finset.sum_le_sum hT
    _ = ((Finset.Icc 2 K).card : ℝ) * (y / Real.sqrt x + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * (y / Real.sqrt x + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Icc]; exact_mod_cast (by omega)

lemma decomp (x b : ℕ) (hxb : x ≤ b) :
    ∑ n ∈ Finset.Icc x b, ArithmeticFunction.vonMangoldt n =
      ArithmeticFunction.vonMangoldt x +
        ∑ n ∈ (Finset.Ioc x b).filter Nat.Prime, Real.log n +
        ∑ n ∈ (Finset.Ioc x b).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n := by
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hxb, add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc x b) Nat.Prime]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    exact ArithmeticFunction.vonMangoldt_apply_prime hn.2
  · symm
    apply Finset.sum_subset
    · intro n hn; simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.2⟩
    · intro n hn hn'
      simp only [Finset.mem_filter, not_and] at hn hn'
      have : ¬ IsPrimePow n := fun h => hn' hn.1 h hn.2
      rw [ArithmeticFunction.vonMangoldt_apply, if_neg this]

lemma R_bound (x b : ℕ) :
    ∑ n ∈ (Finset.Ioc x b).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n ≤
      (((Finset.Ioc x b).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card : ℝ) * Real.log b := by
  rw [← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
  refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact Real.log_le_log hn0 (by exact_mod_cast hn.1.2)

lemma prime_log_bounds (x b : ℕ) (y : ℝ) (hx : 1 ≤ x) (hb : (b : ℝ) ≤ x + y) :
    (((Finset.Ioc x b).filter Nat.Prime).card : ℝ) * Real.log x ≤
      ∑ n ∈ (Finset.Ioc x b).filter Nat.Prime, Real.log n ∧
    ∑ n ∈ (Finset.Ioc x b).filter Nat.Prime, Real.log n ≤
      (((Finset.Ioc x b).filter Nat.Prime).card : ℝ) * (Real.log x + y / x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  constructor
  · rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    have : (x : ℝ) < n := by exact_mod_cast hn.1.1
    exact Real.log_le_log hx0 this.le
  · rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    have h1 : (n : ℝ) ≤ x + y := le_trans (by exact_mod_cast hn.1.2) hb
    have hn0 : (0 : ℝ) < n := by
      have := hn.2.pos; exact_mod_cast this
    have hy : 0 ≤ y / x := by
      have : (x : ℝ) < n := by exact_mod_cast hn.1.1
      apply div_nonneg _ hx0.le; linarith
    calc Real.log n ≤ Real.log (x + y) := Real.log_le_log hn0 h1
      _ = Real.log x + Real.log (1 + y / x) := by
          rw [← Real.log_mul hx0.ne' (by linarith)]; congr 1; field_simp
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + y / x by linarith)
          linarith

lemma alg (N T y L0 δ : ℝ) (hL : 1 ≤ L0) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (h1 : N * L0 ≤ T) (h2 : T ≤ N * (L0 + δ)) : |N - y / L0| ≤ |T - y| + δ * T := by
  have hL0 : 0 < L0 := by linarith
  have hNT : N ≤ T := by nlinarith
  have hT : 0 ≤ T := by linarith
  have h3 : |N * L0 - y| ≤ |T - y| + δ * T := by
    rw [abs_le]
    constructor
    · have := le_abs_self (T - y)
      have := neg_abs_le (T - y)
      nlinarith [mul_le_mul_of_nonneg_left hNT hδ, abs_nonneg (T - y)]
    · have := le_abs_self (T - y)
      nlinarith [mul_nonneg hδ hT, abs_nonneg (T - y)]
  have e : N - y / L0 = (N * L0 - y) / L0 := by field_simp
  rw [e, abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
  nlinarith [abs_nonneg (N * L0 - y)]

lemma natlog_le (b : ℕ) (hb : 1 ≤ b) : (Nat.log 2 b : ℝ) ≤ 2 * Real.log b := by
  have h1 : 2 ^ Nat.log 2 b ≤ b := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 b) ≤ b := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 b) ≤ Real.log b := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have := Real.log_two_gt_d9
  have hK : (0 : ℝ) ≤ Nat.log 2 b := by positivity
  nlinarith

/-- The pointwise ψ → π step. -/
lemma pointwise (X y E : ℝ) (x : ℕ) (hX : 3 ≤ X) (hxX : X ≤ x) (hx2 : (x : ℝ) ≤ 2 * X)
    (hy : 0 ≤ y) (hyX : y ≤ X) (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : y / x ≤ E)
    (herr : Real.log (2 * X) + 2 * Real.log (3 * X) ^ 2 * (y / Real.sqrt X + 1) ≤ y * E)
    (hψ : |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y| ≤ y * E) :
    |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) - y / Real.log x| ≤
      4 * y * E := by
  set b := ⌊(x : ℝ) + y⌋₊ with hbdef
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ x := by linarith
    exact_mod_cast this
  have hx0 : (0 : ℝ) < x := by linarith
  have hxb : x ≤ b := Nat.le_floor (by linarith)
  have hb : (b : ℝ) ≤ x + y := Nat.floor_le (by linarith)
  have hb1 : 1 ≤ b := le_trans hx1 hxb
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  have hlogb : Real.log b ≤ Real.log (3 * X) := Real.log_le_log hb0 (by linarith)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb1)
  rw [decomp x b hxb] at hψ
  rw [pi_sub x b hxb]
  set P : ℝ := (((Finset.Ioc x b).filter Nat.Prime).card : ℝ) with hP
  set θ := ∑ n ∈ (Finset.Ioc x b).filter Nat.Prime, Real.log n with hθ
  set R := ∑ n ∈ (Finset.Ioc x b).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
    ArithmeticFunction.vonMangoldt n with hR
  set Λx := ArithmeticFunction.vonMangoldt x with hΛx
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hΛ0 : 0 ≤ Λx := ArithmeticFunction.vonMangoldt_nonneg
  have hΛle : Λx ≤ Real.log (2 * X) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hx0 hx2)
  have hRle : R ≤ 2 * Real.log (3 * X) ^ 2 * (y / Real.sqrt X + 1) := by
    have h1 := R_bound x b
    have h2 := pp_count x b y hx1 hy hb
    have h3 := natlog_le b hb1
    have hsq : y / Real.sqrt x ≤ y / Real.sqrt X :=
      div_le_div_of_nonneg_left hy (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt hxX)
    set c := (((Finset.Ioc x b).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card : ℝ)
    have hc0 : 0 ≤ c := by positivity
    have hw : 0 ≤ y / Real.sqrt X + 1 := by positivity
    have hK0 : (0 : ℝ) ≤ Nat.log 2 b := by positivity
    have h4 : c ≤ 2 * Real.log (3 * X) * (y / Real.sqrt X + 1) := by
      refine h2.trans ?_
      have : (Nat.log 2 b : ℝ) ≤ 2 * Real.log (3 * X) := by linarith
      calc (Nat.log 2 b : ℝ) * (y / Real.sqrt x + 1)
          ≤ (Nat.log 2 b : ℝ) * (y / Real.sqrt X + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hK0
        _ ≤ _ := mul_le_mul_of_nonneg_right this hw
    calc R ≤ c * Real.log b := h1
      _ ≤ (2 * Real.log (3 * X) * (y / Real.sqrt X + 1)) * Real.log (3 * X) :=
          mul_le_mul h4 hlogb hlogb0 (by nlinarith)
      _ = _ := by ring
  obtain ⟨hb1', hb2'⟩ := prime_log_bounds x b y hx1 hb
  have hP0 : 0 ≤ P := by positivity
  have key := alg P θ y (Real.log x) (y / x) hlogx (by positivity) hP0 hb1' hb2'
  have hS : |θ - y| ≤ 2 * y * E := by
    have := abs_le.1 hψ
    rw [abs_le]; constructor <;> nlinarith
  have hθle : θ ≤ 2 * y := by
    have := (abs_le.1 hψ).2
    have hE1 : y * E ≤ y := by nlinarith
    nlinarith
  have hθ0 : 0 ≤ θ := le_trans (mul_nonneg hP0 (by linarith)) hb1'
  have : y / x * θ ≤ E * (2 * y) := mul_le_mul hδ hθle hθ0 hE0.le
  linarith

lemma eventually_aux : ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X →
    3 ≤ X ∧ Real.log X ^ (1 / 4 : ℝ) ≤ Real.log X / 100 ∧ 1000 ≤ X ^ ((1 : ℝ) / 50) := by
  have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h3 : ∀ᶠ x : ℝ in atTop, 100 ≤ Real.log x ^ ((3 : ℝ) / 4) :=
    (((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3 / 4)).comp
      Real.tendsto_log_atTop)).eventually_ge_atTop 100
  have h4 : ∀ᶠ x : ℝ in atTop, 1000 ≤ x ^ ((1 : ℝ) / 50) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 50)).eventually_ge_atTop 1000
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 ((eventually_ge_atTop 3).and (h2.and (h3.and h4)))
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx₁ x hx
  refine ⟨a1, ?_, a4⟩
  have hl : 0 < Real.log x := by linarith
  have : Real.log x = Real.log x ^ (1 / 4 : ℝ) * Real.log x ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hl]; norm_num
  have hLx : 0 ≤ Real.log x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hl.le _
  nlinarith

lemma err_ok (X y E : ℝ) (hX : 3 ≤ X) (hX50 : 1000 ≤ X ^ ((1 : ℝ) / 50))
    (hy : X ^ ((2 : ℝ) / 15) ≤ y) (hE : X ^ (-(1 : ℝ) / 100) ≤ E) :
    Real.log (2 * X) + 2 * Real.log (3 * X) ^ 2 * (y / Real.sqrt X + 1) ≤ y * E := by
  have hX0 : (0 : ℝ) < X := by linarith
  set l := Real.log (3 * X) with hl
  have hl1 : 1 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hl2 : Real.log (2 * X) ≤ l := Real.log_le_log (by linarith) (by linarith)
  have hlA : l ≤ X ^ ((1 : ℝ) / 25) / 10 := by
    have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 3 * X by linarith)
      (show (0:ℝ) < 1 / 50 by norm_num)
    rw [Real.mul_rpow (by norm_num) hX0.le] at h1
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 50) ≤ 2 := by
      have : (3 : ℝ) ^ ((1 : ℝ) / 50) ≤ 3 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_one] at this
      -- crude: 3^(1/50) ≤ 2 since 3 ≤ 2^50
      have h' : (3 : ℝ) ^ ((1 : ℝ) / 50) ≤ (2 ^ (50 : ℝ)) ^ ((1 : ℝ) / 50) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      rw [← Real.rpow_mul (by norm_num)] at h'
      norm_num at h'
      exact h'
    have e : X ^ ((1 : ℝ) / 25) = X ^ ((1 : ℝ) / 50) * X ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_add hX0]; norm_num
    have hp : 0 ≤ X ^ ((1 : ℝ) / 50) := Real.rpow_nonneg hX0.le _
    rw [e]
    have : l ≤ 100 * X ^ ((1 : ℝ) / 50) := by
      calc l ≤ 3 ^ ((1 : ℝ) / 50) * X ^ ((1 : ℝ) / 50) / (1 / 50) := h1
        _ ≤ 2 * X ^ ((1 : ℝ) / 50) / (1 / 50) := by gcongr
        _ = 100 * X ^ ((1 : ℝ) / 50) := by ring
    nlinarith
  have hp25 : 0 ≤ X ^ ((1 : ℝ) / 25) := Real.rpow_nonneg hX0.le _
  have hl2sq : l ^ 2 ≤ X ^ ((2 : ℝ) / 25) / 100 := by
    have e : X ^ ((2 : ℝ) / 25) = X ^ ((1 : ℝ) / 25) * X ^ ((1 : ℝ) / 25) := by
      rw [← Real.rpow_add hX0]; norm_num
    rw [e]; nlinarith
  have hsq : Real.sqrt X = X ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow X
  have hsqpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hX0.le _) hy
  have hX1 : 1 ≤ X := by linarith
  -- term 1
  have hT1 : 2 * l ^ 2 * (y / Real.sqrt X) ≤ y * E / 50 := by
    have hk : X ^ ((2 : ℝ) / 25) ≤ X ^ (-(1 : ℝ) / 100) * Real.sqrt X := by
      rw [hsq, ← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have : 2 * l ^ 2 ≤ E * Real.sqrt X / 50 := by
      have : X ^ (-(1 : ℝ) / 100) * Real.sqrt X ≤ E * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hE hsqpos.le
      linarith
    calc 2 * l ^ 2 * (y / Real.sqrt X) ≤ E * Real.sqrt X / 50 * (y / Real.sqrt X) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = y * E / 50 := by field_simp
  -- term 2
  have hT2 : Real.log (2 * X) + 2 * l ^ 2 ≤ y * E / 2 := by
    have h1 : X ^ ((2 : ℝ) / 25) ≤ X ^ ((2 : ℝ) / 15) * X ^ (-(1 : ℝ) / 100) := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have h2 : X ^ ((2 : ℝ) / 15) * X ^ (-(1 : ℝ) / 100) ≤ y * E :=
      mul_le_mul hy hE (Real.rpow_nonneg hX0.le _) hy0
    nlinarith
  have hyE : 0 ≤ y * E :=
    mul_nonneg hy0 (le_trans (Real.rpow_nonneg hX0.le _) hE)
  rw [mul_add, mul_one]
  linarith

lemma exp_ratio (X : ℝ) (x : ℕ) (hX : 1 ≤ X) (hxX : X ≤ x) (hx2 : (x : ℝ) ≤ 2 * X) :
    Real.exp (-Real.log X ^ (1 / 4 : ℝ)) ≤ 3 * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  set a := Real.log X ^ (1 / 4 : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hlX _
  have ha4 : a ^ 4 = Real.log X := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hlX]; norm_num
  have hlx : Real.log x ≤ (a + 1) ^ 4 := by
    have h1 : Real.log x ≤ Real.log (2 * X) := Real.log_le_log (by linarith) hx2
    rw [Real.log_mul (by norm_num) hX0.ne'] at h1
    have := Real.log_two_lt_d9
    nlinarith [pow_nonneg ha0 2, pow_nonneg ha0 3]
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL : Real.log x ^ (1 / 4 : ℝ) ≤ a + 1 := by
    calc Real.log x ^ (1 / 4 : ℝ) ≤ ((a + 1) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlx0 hlx (by norm_num)
      _ = a + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have : Real.exp (-a) ≤ Real.exp 1 * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have := Real.exp_one_lt_d9
  have := Real.exp_pos (-Real.log x ^ (1 / 4 : ℝ))
  nlinarith

theorem primes_in_almost_all_short_intervals_dev :
    ∃ C' : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ y : ℝ,
      y ∈ Set.Icc (X ^ (2 / 15 + ε)) (X ^ (0.99 : ℝ)) →
      ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) <
            |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) - y / Real.log x|).card ≤
        C' * X * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) := by
  refine ⟨1, fun ε hε => ?_⟩
  obtain ⟨X₀, hX₀⟩ := psi_exceptional ε hε
  obtain ⟨X₁, hX₁⟩ := eventually_aux
  refine ⟨12, max X₀ X₁, fun X hX y hy => ?_⟩
  have hXa : X₀ ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨hX3, hLX, hX50⟩ := hX₁ X (le_trans (le_max_right _ _) hX)
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  obtain ⟨hy1, hy2⟩ := hy
  have hyl : X ^ ((2 : ℝ) / 15) ≤ y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hy1
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hX0.le _) hyl
  have hyX : y ≤ X := by
    refine hy2.trans ?_
    calc X ^ (0.99 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      _ = X := Real.rpow_one X
  set E := Real.exp (-Real.log X ^ (1 / 4 : ℝ)) with hEdef
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hL0 : 0 ≤ Real.log X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hlogX _
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE : X ^ (-(1 : ℝ) / 100) ≤ E := by
    rw [Real.rpow_def_of_pos hX0, hEdef]
    apply Real.exp_le_exp.2
    linarith
  have hsub : ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          (12 : ℝ) * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) <
            |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) - y / Real.log x|) ⊆
      ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          y * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) <
            |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y|) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxI, hlt⟩ := hx
    refine ⟨hxI, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    rw [Finset.mem_Icc] at hxI
    have hxX : X ≤ x := Nat.ceil_le.1 hxI.1
    have hx2 : (x : ℝ) ≤ 2 * X := (Nat.le_floor_iff (by linarith)).1 hxI.2
    have hx0 : (0 : ℝ) < x := by linarith
    have hδ : y / x ≤ E := by
      refine le_trans ?_ hE
      have e : X ^ (-(1 : ℝ) / 100) = X ^ (0.99 : ℝ) / X := by
        have := Real.rpow_sub hX0 (0.99 : ℝ) 1
        rw [Real.rpow_one] at this
        rw [← this]; norm_num
      rw [e]
      calc y / x ≤ y / X := div_le_div_of_nonneg_left hy0 hX0 hxX
        _ ≤ _ := div_le_div_of_nonneg_right hy2 hX0.le
    have hpt := pointwise X y E x hX3 hxX hx2 hy0 hyX hE0 hE1 hδ
      (err_ok X y E hX3 hX50 hyl hE) hle
    have hr := exp_ratio X x hX1 hxX hx2
    have : 4 * y * E ≤ 12 * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * y by linarith)
      linarith
    linarith
  calc (((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          (12 : ℝ) * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) <
            |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) -
              y / Real.log x|).card : ℝ)
      ≤ (((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          y * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) <
            |(∑ n ∈ Finset.Icc x ⌊(x : ℝ) + y⌋₊, ArithmeticFunction.vonMangoldt n) - y|).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ X * Real.exp (-2 * Real.log X ^ (1 / 4 : ℝ)) := hX₀ X hXa y ⟨hy1, hy2⟩
    _ ≤ 1 * X * E := by
        rw [one_mul, hEdef]
        apply mul_le_mul_of_nonneg_left _ hX0.le
        exact Real.exp_le_exp.2 (by linarith)

end GuthMaynardS1213.C14.PartG
end

section
namespace GuthMaynardS1213.C14
alias primes_in_almost_all_short_intervals_dev := GuthMaynardS1213.C14.PartG.primes_in_almost_all_short_intervals_dev

end GuthMaynardS1213.C14
end

theorem solution :
    ∃ C' : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ y : ℝ,
      y ∈ Set.Icc (X ^ (2 / 15 + ε)) (X ^ (0.99 : ℝ)) →
      ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) <
            |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) - y / Real.log x|).card ≤
        C' * X * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) :=
  GuthMaynardS1213.C14.primes_in_almost_all_short_intervals_dev
