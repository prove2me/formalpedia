-- Prove2me | solution 1 for MasulloRH.padic_log_fourier_compact_test
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:03:54.614674+00:00
-- url     : https://prove2.me/submissions/9a3a429a-f58a-4a11-b760-720a5fc87d9b

import Mathlib
import Theorems.Thm_MasulloRH_padic_log_fourier_away_from_origin_ball

/-
Haar scaling and shell lemmas adapted from the Prove2Me Apache-2.0 proof
by lll, submission 41fd4c8f-fb18-4544-94b6-3abef11cea1b, on the rational
prime-place trace term. The additive character and shifted-unit Fourier
calculation below are additional arguments for the principal value.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set Metric
open scoped Topology ContDiff NNReal ENNReal Pointwise

namespace MasulloAudit.PadicTest

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

/-- In `ℚ_[p]`, norms below `1` are at most `p⁻¹`. -/
lemma norm_le_inv_of_lt_one {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rw [Padic.norm_eq_zpow_neg_valuation h0] at hx ⊢
  have h1 : -x.valuation < 0 := by
    by_contra h
    push Not at h
    have := one_le_zpow₀ (one_lt_p (p := p)).le h
    linarith
  calc (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega)
    _ = (p : ℝ)⁻¹ := zpow_neg_one _

lemma ball_decomp :
    closedBall (0 : ℚ_[p]) 1 = ⋃ n ∈ Finset.range p, closedBall (n : ℚ_[p]) (p : ℝ)⁻¹ := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range z
    refine ⟨n, hn, norm_le_inv_of_lt_one ?_⟩
    have : ‖z - (n : ℤ_[p])‖ < 1 := PadicInt.mem_nonunits.mp hmem
    simpa [PadicInt.norm_def] using this
  · rintro ⟨n, -, hn⟩
    have h1 : ‖(n : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (n : ℤ)
    have h2 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_lt_p (p := p)).le
    calc ‖x‖ = ‖(x - n) + n‖ := by ring_nf
      _ ≤ max ‖x - n‖ ‖(n : ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (hn.trans h2) h1

lemma ball_disjoint :
    (↑(Finset.range p) : Set ℕ).PairwiseDisjoint
      (fun n : ℕ => closedBall (n : ℚ_[p]) (p : ℝ)⁻¹) := by
  intro n hn m hm hnm
  simp only [Finset.coe_range, mem_Iio] at hn hm
  rw [Function.onFun, Set.disjoint_left]
  intro x hxn hxm
  rw [mem_closedBall, dist_eq_norm] at hxn hxm
  have hlt : ‖(((n : ℤ) - m : ℤ) : ℚ_[p])‖ < 1 := by
    have : ‖(n : ℚ_[p]) - m‖ ≤ (p : ℝ)⁻¹ := by
      calc ‖(n : ℚ_[p]) - m‖ = ‖(x - m) + (n - x)‖ := by ring_nf
        _ ≤ max ‖x - m‖ ‖(n : ℚ_[p]) - x‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ _ := max_le hxm (by rw [norm_sub_rev]; exact hxn)
    have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
    push_cast
    linarith
  rw [Padic.norm_intCast_lt_one_iff] at hlt
  apply hnm
  have := Int.eq_zero_of_abs_lt_dvd hlt (by
    rw [abs_lt]; constructor <;> omega)
  omega

variable [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]

/-- The unit `p ∈ ℚ_[p]ˣ`. -/
noncomputable def pu : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)

lemma unit_smul_set (u : ℚ_[p]ˣ) (s : Set ℚ_[p]) : u • s = (u : ℚ_[p]) • s := by
  ext x; simp [Set.mem_smul_set, Units.smul_def]

lemma ball_pos : μ (closedBall (0 : ℚ_[p]) 1) ≠ 0 :=
  (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).measure_ne_zero μ
    ⟨0, by simp⟩

lemma ball_fin : μ (closedBall (0 : ℚ_[p]) 1) ≠ (⊤ : ℝ≥0∞) :=
  (isCompact_closedBall _ _).measure_lt_top.ne

include μ in
lemma char_pu : distribHaarChar ℚ_[p] (pu (p := p)) = (p : ℝ≥0)⁻¹ := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (ball_pos μ) (ball_fin μ)
  have hsm : (pu (p := p)) • closedBall (0 : ℚ_[p]) 1 = closedBall 0 (p : ℝ)⁻¹ := by
    rw [unit_smul_set, _root_.smul_closedBall _ _ zero_le_one]
    simp [pu]
  rw [hsm]
  have hdec := congrArg μ (ball_decomp (p := p))
  rw [measure_biUnion_finset ball_disjoint (fun _ _ => measurableSet_closedBall)] at hdec
  simp_rw [Measure.addHaar_closedBall_center] at hdec
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdec
  rw [hdec, ← mul_assoc]
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [ENNReal.coe_inv (by exact_mod_cast hp.out.ne_zero), ENNReal.coe_natCast,
    ENNReal.inv_mul_cancel hp0 (ENNReal.natCast_ne_top p), one_mul]

include μ in
lemma char_pu_zpow (k : ℤ) :
    distribHaarChar ℚ_[p] ((pu (p := p)) ^ (-k)) = (p : ℝ≥0) ^ k := by
  rw [map_zpow' _ ?_, char_pu μ, inv_zpow', neg_neg]
  intro x
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

/-- The shells `{‖x‖ = p^k}`. -/
lemma shell_eq (k : ℤ) :
    ((pu (p := p)) ^ (-k)) • sphere (0 : ℚ_[p]) 1 = sphere 0 ((p : ℝ) ^ k) := by
  rw [unit_smul_set, smul_sphere' (Units.ne_zero _)]
  simp [pu]

lemma shell_measure (k : ℤ) :
    μ (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)) = ((p : ℝ≥0) ^ k : ℝ≥0) * μ (sphere 0 1) := by
  rw [← shell_eq, ← distribHaarChar_mul, char_pu_zpow μ]

lemma shell_real (k : ℤ) :
    μ.real (sphere (0 : ℚ_[p]) ((p : ℝ) ^ k)) = (p : ℝ) ^ k * μ.real (sphere 0 1) := by
  simp [Measure.real, shell_measure μ k, ENNReal.toReal_mul]

lemma shell_fin (r : ℝ) : μ (sphere (0 : ℚ_[p]) r) ≠ (⊤ : ℝ≥0∞) :=
  ((isCompact_closedBall (0 : ℚ_[p]) r).measure_lt_top.trans_le'
    (measure_mono sphere_subset_closedBall)).ne

lemma unit_sphere_pos : 0 < μ.real (sphere (0 : ℚ_[p]) 1) := by
  apply ENNReal.toReal_pos _ (shell_fin μ 1)
  exact (IsUltrametricDist.isOpen_sphere 0 one_ne_zero).measure_ne_zero μ ⟨1, by simp⟩


/-! ## Finite-place Fourier calculation -/

private lemma add_mem_closedBall_zero_iff {r : ℝ} {a : ℚ_[p]}
    (ha : a ∈ closedBall (0 : ℚ_[p]) r) (x : ℚ_[p]) :
    x + a ∈ closedBall (0 : ℚ_[p]) r ↔ x ∈ closedBall (0 : ℚ_[p]) r := by
  simp only [mem_closedBall, dist_eq_norm, sub_zero] at ha ⊢
  constructor
  · intro hx
    calc
      ‖x‖ = ‖(x + a) + (-a)‖ := by rw [add_neg_cancel_right]
      _ ≤ max ‖x + a‖ ‖-a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le hx (by simpa using ha)
  · intro hx
    exact (IsUltrametricDist.norm_add_le_max x a).trans (max_le hx ha)

private lemma char_integral_closedBall_eq_zero
    (ψ : AddChar ℚ_[p] Circle) {r : ℝ} {a : ℚ_[p]}
    (ha : a ∈ closedBall (0 : ℚ_[p]) r) (y : ℚ_[p]) (hne : ψ (a * y) ≠ 1) :
    (∫ x in closedBall (0 : ℚ_[p]) r, (ψ (x * y) : ℂ) ∂μ) = 0 := by
  let f : ℚ_[p] → ℂ := (closedBall (0 : ℚ_[p]) r).indicator (fun x ↦ (ψ (x * y) : ℂ))
  have hShift := integral_add_right_eq_self (μ := μ) f a
  have hPoint : (fun x ↦ f (x + a)) = fun x ↦ (ψ (a * y) : ℂ) * f x := by
    funext x
    have he := add_mem_closedBall_zero_iff ha x
    by_cases hx : x ∈ closedBall (0 : ℚ_[p]) r
    · dsimp only [f]
      rw [indicator_of_mem hx, indicator_of_mem (he.mpr hx), add_mul,
        AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
    · dsimp only [f]
      rw [indicator_of_notMem hx, indicator_of_notMem (he.not.mpr hx), mul_zero]
  rw [hPoint, integral_const_mul] at hShift
  have hn : (ψ (a * y) : ℂ) - 1 ≠ 0 := by
    intro he
    apply hne
    apply Circle.coe_injective
    rw [Circle.coe_one]
    exact sub_eq_zero.mp he
  have hf : (∫ x, f x ∂μ) = 0 := by
    have he : ((ψ (a * y) : ℂ) - 1) * (∫ x, f x ∂μ) = 0 := by
      rw [sub_mul, one_mul, hShift, sub_self]
    exact (mul_eq_zero.mp he).resolve_left hn
  simpa only [f, integral_indicator measurableSet_closedBall] using hf

private lemma char_integral_unitBall (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (y : ℚ_[p]) :
    (∫ x in closedBall (0 : ℚ_[p]) 1, (ψ (x * y) : ℂ) ∂μ) =
      if ‖y‖ ≤ 1 then 1 else 0 := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [if_pos hy]
    calc
      _ = ∫ _ in closedBall (0 : ℚ_[p]) 1, (1 : ℂ) ∂μ := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro x hx
        have hx₁ : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hx
        have hxy : ‖x * y‖ ≤ 1 := by
          rw [norm_mul]
          exact mul_le_one₀ hx₁ (norm_nonneg _) hy
        change (ψ (x * y) : ℂ) = 1
        exact congrArg (fun z : Circle ↦ (z : ℂ)) ((hψ _).mpr hxy)
      _ = _ := by simp [Measure.real, hμ]
  · rw [if_neg hy]
    exact char_integral_closedBall_eq_zero μ ψ (a := 1) (by simp [mem_closedBall, dist_eq_norm])
      y (by simpa using (hψ y).not.mpr hy)

private lemma integral_smallBall_scaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℚ_[p] → E) :
    (∫ x in closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹, f x ∂μ) =
      (p : ℝ)⁻¹ • ∫ x in closedBall (0 : ℚ_[p]) 1, f ((p : ℚ_[p]) * x) ∂μ := by
  let u := pu (p := p)
  let e : ℚ_[p] ≃ᵐ ℚ_[p] := (Homeomorph.smul u).toMeasurableEquiv
  have hchar : distribHaarChar ℚ_[p] u⁻¹ = (p : ℝ≥0) := by
    simpa [u] using char_pu_zpow μ (1 : ℤ)
  have hPre (s : Set ℚ_[p]) : e ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have hMap : Measure.map e μ = (p : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, hPre, ← distribHaarChar_mul μ, hchar, Measure.smul_apply,
      smul_eq_mul, ENNReal.coe_natCast]
  have he (x : ℚ_[p]) : e x = (p : ℚ_[p]) * x := rfl
  have hpre : e ⁻¹' closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹ = closedBall 0 1 := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero, he, norm_mul, Padic.norm_p]
    have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (p_pos (p := p))
    calc
      (p : ℝ)⁻¹ * ‖x‖ ≤ (p : ℝ)⁻¹ ↔ (p : ℝ)⁻¹ * ‖x‖ ≤ (p : ℝ)⁻¹ * 1 := by simp
      _ ↔ ‖x‖ ≤ 1 := mul_le_mul_iff_right₀ hp0
  have hi := setIntegral_map_equiv (μ := μ) e f (closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹)
  rw [hMap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_natCast, hpre] at hi
  simp_rw [he] at hi
  rw [← hi, smul_smul, inv_mul_cancel₀ (p_pos (p := p)).ne', one_smul]


/-! ## The logarithmic integral on the unit ball -/

private lemma log_norm_on_shell {n : ℕ} {x : ℚ_[p]}
    (hx : x ∈ sphere (0 : ℚ_[p]) ((p : ℝ) ^ (-(n : ℤ)))) :
    Real.log ‖x‖ = -(n : ℝ) * Real.log p := by
  rw [mem_sphere, dist_eq_norm, sub_zero] at hx
  rw [hx, Real.log_zpow, Int.cast_neg, Int.cast_natCast]

private lemma closedBall_zero_eq_union_shells :
    closedBall (0 : ℚ_[p]) 1 =
      (⋃ n : ℕ, sphere (0 : ℚ_[p]) ((p : ℝ) ^ (-(n : ℤ)))) ∪ {0} := by
  ext x
  simp only [mem_union, mem_iUnion, mem_singleton_iff, mem_closedBall, mem_sphere,
    dist_eq_norm, sub_zero]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with h | hx0
    · exact Or.inr h
    · have hnorm := Padic.norm_eq_zpow_neg_valuation hx0
      have hval : 0 ≤ x.valuation := by
        by_contra! h
        have hlt := zpow_lt_zpow_right₀ (one_lt_p (p := p)) (show (0 : ℤ) < -x.valuation by omega)
        rw [zpow_zero, ← hnorm] at hlt
        exact hlt.not_ge hx
      exact Or.inl ⟨x.valuation.toNat, by rwa [Int.toNat_of_nonneg hval]⟩
  · rintro (⟨n, hn⟩ | rfl)
    · rw [hn]
      have h := zpow_le_zpow_right₀ (one_lt_p (p := p)).le (show -(n : ℤ) ≤ 0 by omega)
      simpa only [zpow_zero] using h
    · simp

private lemma integrableOn_log_norm_unitBall :
    IntegrableOn (fun x : ℚ_[p] ↦ Real.log ‖x‖) (closedBall (0 : ℚ_[p]) 1) μ := by
  let S := fun n : ℕ ↦ sphere (0 : ℚ_[p]) ((p : ℝ) ^ (-(n : ℤ)))
  have hInt (n : ℕ) : IntegrableOn (fun x : ℚ_[p] ↦ Real.log ‖x‖) (S n) μ := by
    apply Integrable.congr (integrableOn_const (C := -(n : ℝ) * Real.log p) (shell_fin μ _))
    filter_upwards [ae_restrict_mem (μ := μ) (isClosed_sphere.measurableSet : MeasurableSet (S n))] with x hx
    exact (log_norm_on_shell hx).symm
  have hSum : Summable (fun n : ℕ ↦ ∫ x in S n, ‖Real.log ‖x‖‖ ∂μ) := by
    let q := (p : ℝ)⁻¹
    have hq : 0 ≤ q := inv_nonneg.mpr (p_pos (p := p)).le
    have hq₁ : ‖q‖ < 1 := by
      rw [Real.norm_of_nonneg hq]
      exact inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
    have hs := (summable_pow_mul_geometric_of_norm_lt_one (r := q) 1 hq₁).mul_left
      (Real.log p * μ.real (sphere (0 : ℚ_[p]) 1))
    apply hs.congr
    intro n
    have hx (x : ℚ_[p]) (hx : x ∈ S n) : ‖Real.log ‖x‖‖ = (n : ℝ) * Real.log p := by
      rw [Real.norm_eq_abs, log_norm_on_shell hx, neg_mul, abs_neg,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (one_lt_p (p := p)).le))]
    have he : (∫ x in S n, ‖Real.log ‖x‖‖ ∂μ) =
        ∫ _ in S n, (n : ℝ) * Real.log p ∂μ :=
      setIntegral_congr_fun isClosed_sphere.measurableSet hx
    rw [he, setIntegral_const, smul_eq_mul]
    dsimp only [S]
    rw [shell_real μ]
    simp only [zpow_neg, zpow_natCast, ← inv_pow, pow_one, q]
    ring
  rw [closedBall_zero_eq_union_shells]
  apply (integrableOn_iUnion_of_summable_integral_norm hInt hSum).union
  exact integrableOn_singleton (hx := (isCompact_singleton (x := (0 : ℚ_[p]))).measure_lt_top)

private lemma log_norm_unitBall_weighted_identity :
    (1 - (p : ℝ)⁻¹) * (∫ x in closedBall (0 : ℚ_[p]) 1, Real.log ‖x‖ ∂μ) =
      -(p : ℝ)⁻¹ * Real.log p * μ.real (closedBall (0 : ℚ_[p]) 1) := by
  let O := closedBall (0 : ℚ_[p]) 1
  let B := closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹
  have hB : B ⊆ O := closedBall_subset_closedBall
    (inv_le_one_of_one_le₀ (one_lt_p (p := p)).le)
  have hOInt : IntegrableOn (fun x : ℚ_[p] ↦ Real.log ‖x‖) O μ :=
    integrableOn_log_norm_unitBall μ
  have hD : (∫ x in O \ B, Real.log ‖x‖ ∂μ) = 0 := by
    refine (setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
      (g := fun _ ↦ 0) ?_).trans (by simp)
    intro x hx
    have hxO : ‖x‖ ≤ 1 := by simpa [O, mem_closedBall, dist_eq_norm] using hx.1
    have hxB : ¬ ‖x‖ ≤ (p : ℝ)⁻¹ := by
      simpa [B, mem_closedBall, dist_eq_norm] using hx.2
    have hx₁ := le_antisymm hxO (le_of_not_gt (fun h ↦ hxB (norm_le_inv_of_lt_one h)))
    change Real.log ‖x‖ = 0
    rw [hx₁, Real.log_one]
  have hI : (∫ x in O, Real.log ‖x‖ ∂μ) =
      ∫ x in B, Real.log ‖x‖ ∂μ := by
    have hUnion : B ∪ (O \ B) = O := union_sdiff_cancel hB
    have hdisj : Disjoint B (O \ B) := disjoint_sdiff_right
    rw [← hUnion, setIntegral_union hdisj (measurableSet_closedBall.diff measurableSet_closedBall)
      (hOInt.mono_set hB) (hOInt.mono_set sdiff_subset), hD, add_zero]
  have hS := integral_smallBall_scaling μ (fun x : ℚ_[p] ↦ Real.log ‖x‖)
  change (∫ x in B, Real.log ‖x‖ ∂μ) = (p : ℝ)⁻¹ •
    ∫ x in O, Real.log ‖(p : ℚ_[p]) * x‖ ∂μ at hS
  have hae : ∀ᵐ x : ℚ_[p] ∂μ.restrict O, x ≠ 0 := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  have hEq : (∫ x in O, Real.log ‖(p : ℚ_[p]) * x‖ ∂μ) =
      ∫ x in O, Real.log ‖x‖ - Real.log p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [norm_mul, Padic.norm_p,
      Real.log_mul (inv_ne_zero (p_pos (p := p)).ne') (norm_ne_zero_iff.mpr hx),
      Real.log_inv]
    ring
  rw [hEq, integral_sub hOInt (integrableOn_const (ball_fin μ)),
    setIntegral_const, smul_eq_mul, smul_eq_mul] at hS
  change (1 - (p : ℝ)⁻¹) * (∫ x in O, Real.log ‖x‖ ∂μ) = _
  have h := hI.trans hS
  nlinarith only [h]



private lemma disjoint_subcover {ι X : Type*} (B : ι → Set X)
    (hB : ∀ i j, B i ⊆ B j ∨ B j ⊆ B i ∨ Disjoint (B i) (B j)) (S : Finset ι) :
    ∃ T : Finset ι, T ⊆ S ∧ (↑T : Set ι).PairwiseDisjoint B ∧
      ∀ x : X, (∃ i ∈ S, x ∈ B i) → ∃ i ∈ T, x ∈ B i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨T,hTS,hPair,hCov⟩ := ih
    by_cases hContain : ∃ j ∈ T, B a ⊆ B j
    · obtain ⟨j,hj,haj⟩ := hContain
      refine ⟨T, hTS.trans (Finset.subset_insert _ _), hPair, ?_⟩
      intro x hx
      obtain ⟨i,hi,hi'⟩ := hx
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨j,hj,haj hi'⟩
      · exact hCov x ⟨i,hi,hi'⟩
    · let U := T.filter (fun j ↦ Disjoint (B a) (B j))
      have hUS : U ⊆ S := (Finset.filter_subset _ _).trans hTS
      refine ⟨insert a U, Finset.insert_subset_insert _ hUS, ?_, ?_⟩
      · intro i hi j hj hij
        change Disjoint (B i) (B j)
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hi) with rfl | hI
        · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hj) with rfl | hJ
          · exact (hij rfl).elim
          · exact (Finset.mem_filter.mp hJ).2
        · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hj) with rfl | hJ
          · exact (Finset.mem_filter.mp hI).2.symm
          · exact hPair (Finset.mem_coe.mpr (Finset.mem_filter.mp hI).1)
              (Finset.mem_coe.mpr (Finset.mem_filter.mp hJ).1) hij
      · intro x hx
        obtain ⟨i,hi,hi'⟩ := hx
        rcases Finset.mem_insert.mp hi with he | hi
        · subst i
          exact ⟨a,Finset.mem_insert_self _ _,hi'⟩
        · obtain ⟨j,hj,hj'⟩ := hCov x ⟨i,hi,hi'⟩
          rcases hB a j with h | h | h
          · exact (hContain ⟨j,hj,h⟩).elim
          · exact ⟨a,Finset.mem_insert_self _ _,h hj'⟩
          · exact ⟨j,Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hj,h⟩),hj'⟩

private lemma locallyConstant_closedBall_zpow (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (a : ℚ_[p]) :
    ∃ k : ℤ, ∀ x ∈ closedBall a ((p:ℝ)^k), f x = f a := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hf.eventually_eq a)
  have hq0 : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr (p_pos (p := p)).le
  have hq1 : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have he : ∀ᶠ n : ℕ in Filter.atTop, ((p:ℝ)⁻¹)^n < r := h.eventually (Iio_mem_nhds hr)
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨-(n:ℤ), ?_⟩
  intro x hx
  have hN : (p:ℝ)^(-(n:ℤ)) < r := by simpa only [zpow_neg,zpow_natCast,←inv_pow] using hn
  exact hsub (closedBall_subset_ball hN hx)

private lemma finite_disjoint_ball_cover_of_test (f : ℚ_[p] → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ (S : Finset (Function.support f)) (k : Function.support f → ℤ),
      (↑S : Set (Function.support f)).PairwiseDisjoint
        (fun a ↦ closedBall a.val ((p:ℝ)^(k a))) ∧
      (∀ a : Function.support f, ∀ x ∈ closedBall a.val ((p:ℝ)^(k a)), f x = f a.val) ∧
      ∀ x, f x ≠ 0 → ∃ a ∈ S, x ∈ closedBall a.val ((p:ℝ)^(k a)) := by
  classical
  have hClosed : IsClosed (Function.support f) := by
    have hOpen : IsOpen {x | f x = 0} := hf.isOpen_fiber 0
    change IsClosed {x | f x = 0}ᶜ
    exact hOpen.isClosed_compl
  have hK : IsCompact (Function.support f) := by
    rw [← hClosed.closure_eq]
    exact hfc
  choose k hk using fun a : Function.support f ↦ locallyConstant_closedBall_zpow f hf a.val
  let B (a : Function.support f) := closedBall a.val ((p:ℝ)^(k a))
  have hOpen (a : Function.support f) : IsOpen (B a) :=
    IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (p_pos (p := p)).ne')
  have hc : Function.support f ⊆ ⋃ a, B a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_closedBall_self (zpow_nonneg (p_pos (p := p)).le _)⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover B hOpen hc
  obtain ⟨T,_,hPair,hCover⟩ := disjoint_subcover B
    (fun i j ↦ IsUltrametricDist.closedBall_subset_trichotomy
      i.val j.val ((p:ℝ)^(k i)) ((p:ℝ)^(k j))) S
  refine ⟨T,k,hPair,hk,fun x hx ↦ hCover x ?_⟩
  have hX := hS (Function.mem_support.mpr hx)
  simp only [mem_iUnion] at hX
  obtain ⟨i,hi,hi'⟩ := hX
  exact ⟨i,hi,hi'⟩


private lemma measureReal_closedBall_zpow (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1)
    (a : ℚ_[p]) (k : ℤ) : μ.real (closedBall a ((p:ℝ)^k)) = (p:ℝ)^k := by
  let u := pu (p := p)^(-k)
  have hR : ‖(u:ℚ_[p])‖ = (p:ℝ)^k := by
    rw [show u = pu (p := p)^(-k) from rfl, Units.val_zpow_eq_zpow_val, norm_zpow]
    change ‖(p:ℚ_[p])‖ ^ (-k) = _
    rw [Padic.norm_p,inv_zpow,zpow_neg,inv_inv]
  have hB : u • closedBall (0:ℚ_[p]) 1 = closedBall 0 ((p:ℝ)^k) := by
    rw [unit_smul_set,_root_.smul_closedBall _ _ zero_le_one]
    simp [hR]
  rw [Measure.real, Measure.addHaar_closedBall_center, ← hB,
    ← distribHaarChar_mul μ, show distribHaarChar ℚ_[p] u = (p:ℝ≥0)^k from char_pu_zpow μ k,
    hμ, mul_one, ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_natCast]

private lemma norm_eq_center_of_mem_smallBall {a x : ℚ_[p]} {r : ℝ}
    (hr : r < ‖a‖) (hx : x ∈ closedBall a r) : ‖x‖ = ‖a‖ := by
  have hxa : ‖x-a‖ < ‖a‖ := (show ‖x-a‖ ≤ r by simpa [mem_closedBall,dist_eq_norm] using hx).trans_lt hr
  have hax : ‖a-x‖ < ‖a‖ := by rw [norm_sub_rev]; exact hxa
  apply le_antisymm
  · calc
      ‖x‖ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x-a‖ ‖a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = _ := max_eq_right hxa.le
  · by_contra! ht
    have hA : ‖a‖ ≤ max ‖a-x‖ ‖x‖ := by
      simpa only [sub_add_cancel] using IsUltrametricDist.norm_add_le_max (a-x) x
    exact (max_lt hax ht).not_ge hA

private noncomputable def padicAdditiveFourier (ψ : AddChar ℚ_[p] Circle)
    (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ :=
  ∫ x, f x*(ψ (x*y) : ℂ) ∂μ

private noncomputable def padicLogIntegrand (ψ : AddChar ℚ_[p] Circle)
    (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ :=
  (Real.log ‖y‖ : ℂ)*padicAdditiveFourier μ ψ f y

private noncomputable def unitBallTest : ℚ_[p] → ℂ :=
  (closedBall (0:ℚ_[p]) 1).indicator (fun _ ↦ 1)

private lemma unitBallTest_isLocallyConstant : IsLocallyConstant (unitBallTest (p := p)) := by
  let O := closedBall (0:ℚ_[p]) 1
  have hO := IsUltrametricDist.isOpen_closedBall (0:ℚ_[p]) one_ne_zero
  refine (IsLocallyConstant.iff_exists_open _).mpr (fun x ↦ ?_)
  by_cases hx : x ∈ O
  · refine ⟨O,hO,hx,fun y hy ↦ ?_⟩
    rw [unitBallTest,indicator_of_mem hy, indicator_of_mem hx]
  · refine ⟨Oᶜ,isClosed_closedBall.isOpen_compl,hx,fun y hy ↦ ?_⟩
    rw [unitBallTest,indicator_of_notMem hy, indicator_of_notMem hx]

private lemma unitBallTest_hasCompactSupport : HasCompactSupport (unitBallTest (p := p)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
    (support_indicator_subset)

private lemma padicAdditiveFourier_indicator (ψ : AddChar ℚ_[p] Circle)
    {S : Set ℚ_[p]} (hS : MeasurableSet S) (c : ℂ) (y : ℚ_[p]) :
    padicAdditiveFourier μ ψ (S.indicator (fun _ ↦ c)) y =
      c*(∫ x in S, (ψ (x*y) : ℂ) ∂μ) := by
  unfold padicAdditiveFourier
  have hPoint : (fun x : ℚ_[p] ↦ S.indicator (fun _ ↦ c) x*(ψ (x*y) : ℂ)) =
      S.indicator (fun x ↦ c*(ψ (x*y) : ℂ)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx,indicator_of_mem hx]
    · rw [indicator_of_notMem hx,indicator_of_notMem hx,zero_mul]
  rw [hPoint,integral_indicator hS,integral_const_mul]

private lemma padic_unitBall_log_integral (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1) :
    Integrable (padicLogIntegrand μ ψ (unitBallTest (p := p))) μ ∧
      (∫ y, padicLogIntegrand μ ψ (unitBallTest (p := p)) y ∂μ) =
        ((-Real.log p / ((p:ℝ)-1) : ℝ) : ℂ) := by
  let O := closedBall (0:ℚ_[p]) 1
  have he : padicLogIntegrand μ ψ (unitBallTest (p := p)) =
      O.indicator (fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ)) := by
    funext y
    change (Real.log ‖y‖ : ℂ)*padicAdditiveFourier μ ψ (O.indicator (fun _ ↦ 1)) y = _
    rw [padicAdditiveFourier_indicator μ ψ measurableSet_closedBall, one_mul,
      char_integral_unitBall μ ψ hψ hμ]
    by_cases hy : ‖y‖ ≤ 1
    · have hm : y ∈ O := by simpa [O,mem_closedBall,dist_eq_norm] using hy
      rw [if_pos hy, indicator_of_mem hm, mul_one]
    · have hm : y ∉ O := by simpa [O,mem_closedBall,dist_eq_norm] using hy
      rw [if_neg hy, indicator_of_notMem hm, mul_zero]
  rw [he]
  have hI : IntegrableOn (fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ)) O μ :=
    (integrableOn_log_norm_unitBall μ).ofReal (𝕜 := ℂ)
  refine ⟨hI.integrable_indicator measurableSet_closedBall, ?_⟩
  rw [integral_indicator measurableSet_closedBall]
  have hMean : (∫ y in O, Real.log ‖y‖ ∂μ) = -Real.log p/((p:ℝ)-1) := by
    have h := log_norm_unitBall_weighted_identity μ
    rw [show μ.real (closedBall (0:ℚ_[p]) 1) = 1 by simp [Measure.real,hμ], mul_one] at h
    apply (eq_div_iff (sub_ne_zero.mpr (one_lt_p (p := p)).ne')).mpr
    field_simp [(p_pos (p := p)).ne'] at h
    dsimp only [O]
    nlinarith only [h]
  have hEq : (∫ y in O, (Real.log ‖y‖ : ℂ) ∂μ) =
      (↑(∫ y in O, Real.log ‖y‖ ∂μ) : ℂ) := integral_ofReal (𝕜 := ℂ)
  rw [hEq,hMean]


private lemma integrable_padic_fourier_mul (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (y : ℚ_[p]) {f : ℚ_[p] → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x : ℚ_[p] ↦ f x*(ψ (x*y) : ℂ)) μ :=
  (hf.mul (continuous_subtype_val.comp (hcont.comp (continuous_id.mul_const y)))).integrable_of_hasCompactSupport
    hfc.mul_right

private lemma padic_log_fourier_off_origin_test
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (hf0 : f 0 = 0) :
    Integrable (padicLogIntegrand μ ψ f) μ ∧
      Integrable (fun x : ℚ_[p] ↦ f x/(‖x‖:ℂ)) μ ∧
      (∫ y, padicLogIntegrand μ ψ f y ∂μ) =
        -(Real.log p/(1-(p:ℝ)⁻¹) : ℝ) * ∫ x, f x/(‖x‖:ℂ) ∂μ := by
  classical
  obtain ⟨S,k,hPair,hLocal,hCover⟩ := finite_disjoint_ball_cover_of_test f hf hfc
  let B (i : Function.support f) := closedBall i.val ((p:ℝ)^(k i))
  let χ (i : Function.support f) : ℚ_[p] → ℂ := (B i).indicator (fun _ ↦ f i.val)
  have hMeas (i : Function.support f) : MeasurableSet (B i) := measurableSet_closedBall
  have hEq : f = fun x ↦ ∑ i ∈ S, χ i x := by
    funext x
    by_cases hx : f x = 0
    · rw [hx]
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hN : x ∉ B i := by
        intro h
        exact (Function.mem_support.mp i.prop) ((hLocal i x h).symm.trans hx)
      exact indicator_of_notMem hN _
    · obtain ⟨i,hi,hBall⟩ := hCover x hx
      rw [Finset.sum_eq_single_of_mem i hi]
      · have hLocal' := hLocal i x hBall
        dsimp only [χ]
        rw [indicator_of_mem (show x ∈ B i from hBall)]
        exact hLocal' 
      · intro j hj hji
        have hN : x ∉ B j := fun h ↦
          (Set.disjoint_left.mp (hPair (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hji.symm)) hBall h
        exact indicator_of_notMem hN _
  have hAway (i : Function.support f) : (p:ℝ)^(k i) < ‖i.val‖ := by
    apply lt_of_not_ge
    intro h
    have hi : (0:ℚ_[p]) ∈ B i := by simpa [B,mem_closedBall,dist_eq_norm] using h
    exact (Function.mem_support.mp i.prop) ((hLocal i 0 hi).symm.trans hf0)
  let A (i : Function.support f) (y : ℚ_[p]) : ℂ :=
    (Real.log ‖y‖ : ℂ) * ∫ x in B i, (ψ (x*y) : ℂ) ∂μ
  let R : ℂ := -(Real.log p/(1-(p:ℝ)⁻¹) : ℝ)
  have hBall (i : Function.support f) :
      Integrable (A i) μ ∧ (∫ y, A i y ∂μ) = R*(((p:ℝ)^(k i)/‖i.val‖ : ℝ) : ℂ) :=
    MasulloRH.padic_log_fourier_away_from_origin_ball μ ψ hcont hψ hμ i.val (k i) (hAway i)
  have hχmul (i : Function.support f) (y : ℚ_[p]) :
      Integrable (fun x : ℚ_[p] ↦ χ i x*(ψ (x*y) : ℂ)) μ := by
    have hI : IntegrableOn (fun x : ℚ_[p] ↦ (ψ (x*y) : ℂ)) (B i) μ :=
      (continuous_subtype_val.comp (hcont.comp (continuous_id.mul_const y))).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
    have hIC : IntegrableOn (fun x : ℚ_[p] ↦ f i.val*(ψ (x*y) : ℂ)) (B i) μ :=
      hI.const_mul _
    refine (hIC.integrable_indicator (hMeas i)).congr ?_
    filter_upwards [] with x
    by_cases hx : x ∈ B i <;> simp [χ,Set.indicator,hx]
  have hFT (y : ℚ_[p]) : padicAdditiveFourier μ ψ f y =
      ∑ i ∈ S, f i.val*(∫ x in B i, (ψ (x*y) : ℂ) ∂μ) := by
    calc
      _ = ∫ x, (∑ i ∈ S, χ i x*(ψ (x*y) : ℂ)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [congrFun hEq x, Finset.sum_mul]
      _ = ∑ i ∈ S, padicAdditiveFourier μ ψ (χ i) y :=
        integral_finsetSum S (fun i _ ↦ hχmul i y)
      _ = _ := Finset.sum_congr rfl (fun i _ ↦ padicAdditiveFourier_indicator μ ψ (hMeas i) _ _)
  have hT : padicLogIntegrand μ ψ f = fun y ↦ ∑ i ∈ S, f i.val*A i y := by
    funext y
    rw [padicLogIntegrand,hFT,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    unfold A
    ring
  have hTI : Integrable (padicLogIntegrand μ ψ f) μ := by
    rw [hT]
    exact integrable_finsetSum S (fun i _ ↦ (hBall i).1.const_mul _)
  let Q (i : Function.support f) := (B i).indicator (fun _ ↦ f i.val/(‖i.val‖:ℂ))
  have hQ (i : Function.support f) (x : ℚ_[p]) : χ i x/(‖x‖:ℂ) = Q i x := by
    by_cases hx : x ∈ B i
    · simp only [Q,χ,indicator_of_mem hx, norm_eq_center_of_mem_smallBall (hAway i) hx]
    · simp only [Q,χ,indicator_of_notMem hx,zero_div]
  have hQEq : (fun x : ℚ_[p] ↦ f x/(‖x‖:ℂ)) = fun x ↦ ∑ i ∈ S, Q i x := by
    funext x
    rw [congrFun hEq x, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ ↦ hQ i x)
  have hQI (i : Function.support f) : Integrable (Q i) μ :=
    (integrableOn_const ((isCompact_closedBall (x := i.val) (r := (p:ℝ)^(k i))).measure_lt_top.ne)
      : IntegrableOn (fun _ : ℚ_[p] ↦ f i.val/(‖i.val‖:ℂ)) (B i) μ).integrable_indicator (hMeas i)
  have hQVal (i : Function.support f) :
      (∫ x, Q i x ∂μ) = (((p:ℝ)^(k i) : ℝ) : ℂ)*(f i.val/(‖i.val‖:ℂ)) := by
    dsimp only [Q]
    rw [integral_indicator (hMeas i),setIntegral_const,measureReal_closedBall_zpow μ hμ,
      Algebra.smul_def]
    rfl
  refine ⟨hTI, ?_, ?_⟩
  · rw [hQEq]
    exact integrable_finsetSum S (fun i _ ↦ hQI i)
  · change (∫ y, padicLogIntegrand μ ψ f y ∂μ) = R*(∫ x, f x/(‖x‖:ℂ) ∂μ)
    rw [hT,hQEq,integral_finsetSum S (fun i _ ↦ (hBall i).1.const_mul (f i.val)),
      integral_finsetSum S (fun i _ ↦ hQI i), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [integral_const_mul,(hBall i).2,hQVal,Complex.ofReal_div]
    ring


private lemma logIntegrand_add_const_mul
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    {f g : ℚ_[p] → ℂ} (hF : Continuous f) (hG : Continuous g)
    (hFC : HasCompactSupport f) (hGC : HasCompactSupport g) (c : ℂ) :
    padicLogIntegrand μ ψ (fun x ↦ f x+c*g x) =
      fun y ↦ padicLogIntegrand μ ψ f y+c*padicLogIntegrand μ ψ g y := by
  funext y
  have hF' := integrable_padic_fourier_mul μ ψ hcont y hF hFC
  have hG' := (integrable_padic_fourier_mul μ ψ hcont y hG hGC).const_mul c
  have he : (fun x : ℚ_[p] ↦ (f x+c*g x)*(ψ (x*y) : ℂ)) =
      fun x : ℚ_[p] ↦ f x*(ψ (x*y) : ℂ)+c*(g x*(ψ (x*y) : ℂ)) := by
    funext x
    ring
  unfold padicLogIntegrand padicAdditiveFourier
  rw [he,integral_add hF' hG',integral_const_mul]
  ring

/-- Exact rational p-adic logarithmic Fourier distribution on a compactly supported
locally constant test, including the origin coefficient. -/
theorem padic_log_fourier_compact_test_aux (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    let g := fun x : ℚ_[p] ↦ f x-f 0*unitBallTest (p := p) x
    Integrable (padicLogIntegrand μ ψ f) μ ∧
      Integrable (fun x : ℚ_[p] ↦ g x/(‖x‖:ℂ)) μ ∧
      (∫ y, padicLogIntegrand μ ψ f y ∂μ) =
        -(Real.log p/(1-(p:ℝ)⁻¹) : ℝ)*(∫ x, g x/(‖x‖:ℂ) ∂μ)
          - ((Real.log p/((p:ℝ)-1) : ℝ) : ℂ)*f 0 := by
  let O := unitBallTest (p := p)
  let g (x : ℚ_[p]) := f x-f 0*O x
  have hOL : IsLocallyConstant O := unitBallTest_isLocallyConstant
  have hOC : HasCompactSupport O := unitBallTest_hasCompactSupport
  have hgL : IsLocallyConstant g := hf.sub ((IsLocallyConstant.const (f 0)).mul hOL)
  have hgC : HasCompactSupport g := hfc.sub hOC.mul_left
  have hg0 : g 0 = 0 := by simp [g,O,unitBallTest]
  obtain ⟨hgI,hgQ,hgVal⟩ := padic_log_fourier_off_origin_test μ ψ hcont hψ hμ g hgL hgC hg0
  obtain ⟨hOI,hOVal⟩ := padic_unitBall_log_integral μ ψ hψ hμ
  have hF : f = fun x : ℚ_[p] ↦ g x+f 0*O x := by
    funext x
    unfold g
    ring
  have hLog := logIntegrand_add_const_mul μ ψ hcont hgL.continuous hOL.continuous hgC hOC (f 0)
  rw [← hF] at hLog
  dsimp only
  rw [hLog]
  refine ⟨hgI.add (hOI.const_mul _),hgQ,?_⟩
  rw [integral_add hgI (hOI.const_mul _), integral_const_mul,hgVal,hOVal]
  push_cast
  ring

end MasulloAudit.PadicTest

open MeasureTheory
open scoped Topology

theorem solution {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    let g := fun x : ℚ_[p] ↦ f x-f 0*(Metric.closedBall (0 : ℚ_[p]) 1).indicator (fun _ ↦ (1:ℂ)) x
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) * ∫ x, f x * (ψ (x*y) : ℂ) ∂μ
    Integrable F μ ∧ Integrable (fun x : ℚ_[p] ↦ g x/(‖x‖:ℂ)) μ ∧
      (∫ y, F y ∂μ) =
        -(Real.log p/(1-(p : ℝ)⁻¹) : ℝ) * (∫ x, g x/(‖x‖:ℂ) ∂μ) -
        ((Real.log p/((p:ℝ)-1) : ℝ) : ℂ) * f 0 := by
  exact MasulloAudit.PadicTest.padic_log_fourier_compact_test_aux μ ψ hcont hψ hμ f hf hfc
