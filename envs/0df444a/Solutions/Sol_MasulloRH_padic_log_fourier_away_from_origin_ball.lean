-- Prove2me | solution 1 for MasulloRH.padic_log_fourier_away_from_origin_ball
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:51:41.043602+00:00
-- url     : https://prove2.me/submissions/481b4eff-93f9-4349-a02d-83e9f3dd0281

import Mathlib

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

namespace MasulloAudit.PadicUnits

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


private def ballPow (k : ℤ) : Set ℚ_[p] := closedBall 0 ((p : ℝ)^k)

private lemma mem_ballPow {k : ℤ} {x : ℚ_[p]} :
    x ∈ ballPow (p := p) k ↔ ‖x‖ ≤ (p : ℝ)^k := by
  simp [ballPow, mem_closedBall, dist_eq_norm]

private lemma measurableSet_ballPow (k : ℤ) : MeasurableSet (ballPow (p := p) k) :=
  measurableSet_closedBall

private lemma ballPow_zero : ballPow (p := p) 0 = closedBall 0 1 := by simp [ballPow]

private lemma ballPow_mono {k l : ℤ} (h : k ≤ l) : ballPow (p := p) k ⊆ ballPow l :=
  closedBall_subset_closedBall (zpow_le_zpow_right₀ (one_lt_p (p := p)).le h)

private lemma ballPow_sdiff_eq_sphere (k : ℤ) :
    ballPow (p := p) k \ ballPow (k-1) = sphere 0 ((p : ℝ)^k) := by
  ext x
  simp only [mem_sdiff, mem_ballPow, mem_sphere, dist_eq_norm, sub_zero]
  by_cases hx : x = 0
  · subst x
    have hp := zpow_pos (p_pos (p := p)) k
    simp [hp.ne, (zpow_pos (p_pos (p := p)) (k-1)).le]
  rw [Padic.norm_eq_zpow_neg_valuation hx]
  have hMono := zpow_right_strictMono₀ (one_lt_p (p := p))
  change ((p : ℝ)^(-x.valuation) ≤ (p : ℝ)^k ∧
    ¬ (p : ℝ)^(-x.valuation) ≤ (p : ℝ)^(k-1)) ↔ (p : ℝ)^(-x.valuation) = (p : ℝ)^k
  rw [hMono.le_iff_le, hMono.le_iff_le, hMono.injective.eq_iff]
  omega

private lemma norm_p_unit_zpow (k : ℤ) :
    ‖((pu (p := p) ^ (-k) : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ)^k := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  change ‖(p : ℚ_[p])‖ ^ (-k) = (p : ℝ)^k
  rw [Padic.norm_p, inv_zpow, zpow_neg, inv_inv]

private lemma integral_ballPow_scaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℚ_[p] → E) (k : ℤ) :
    (∫ x in ballPow (p := p) k, f x ∂μ) =
      ((p : ℝ)^k) • ∫ x in closedBall (0 : ℚ_[p]) 1,
        f (((pu (p := p) ^ (-k) : ℚ_[p]ˣ) : ℚ_[p]) * x) ∂μ := by
  let u := pu (p := p) ^ (-k)
  let e : ℚ_[p] ≃ᵐ ℚ_[p] := (Homeomorph.smul u).toMeasurableEquiv
  have hchar : distribHaarChar ℚ_[p] u⁻¹ = (p : ℝ≥0)^(-k) := by
    simpa only [u, inv_zpow, zpow_neg, neg_neg, inv_inv] using char_pu_zpow μ (-k)
  have hPre (s : Set ℚ_[p]) : e ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have hMap : Measure.map e μ = (((p : ℝ≥0)^(-k) : ℝ≥0) : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, hPre, ← distribHaarChar_mul μ, hchar,
      Measure.smul_apply, smul_eq_mul]
  have he (x : ℚ_[p]) : e x = (u : ℚ_[p]) * x := rfl
  have hu : ‖(u : ℚ_[p])‖ = (p : ℝ)^k := norm_p_unit_zpow k
  have hpre : e ⁻¹' ballPow (p := p) k = closedBall 0 1 := by
    ext x
    simp only [mem_preimage, mem_ballPow, mem_closedBall, dist_eq_norm, sub_zero, he, norm_mul, hu]
    have hp0 : 0 < (p : ℝ)^k := zpow_pos (p_pos (p := p)) k
    calc
      _ ↔ (p : ℝ)^k * ‖x‖ ≤ (p : ℝ)^k * 1 := by rw [mul_one]
      _ ↔ _ := mul_le_mul_iff_right₀ hp0
  have hi := setIntegral_map_equiv (μ := μ) e f (ballPow (p := p) k)
  rw [hMap, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, hpre] at hi
  simp only [NNReal.coe_zpow, NNReal.coe_natCast, he] at hi
  rw [← hi, smul_smul, ← zpow_add₀ (p_pos (p := p)).ne', add_neg_cancel, zpow_zero, one_smul]

private lemma char_integral_ballPow (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (k : ℤ) (y : ℚ_[p]) :
    (∫ x in ballPow (p := p) k, (ψ (x*y) : ℂ) ∂μ) =
      if ‖y‖ ≤ (p : ℝ)^(-k) then (((p : ℝ)^k : ℝ) : ℂ) else 0 := by
  let u : ℚ_[p] := ↑(pu (p := p) ^ (-k))
  rw [integral_ballPow_scaling μ _ k]
  have hEq : (fun x : ℚ_[p] ↦ (ψ ((u*x)*y) : ℂ)) = fun x ↦ (ψ (x*(u*y)) : ℂ) := by
    funext x
    congr 2
    ring
  change _ • (∫ x in closedBall (0 : ℚ_[p]) 1, (ψ ((u*x)*y) : ℂ) ∂μ) = _
  rw [hEq, char_integral_unitBall μ ψ hψ hμ, norm_mul, show ‖u‖ = (p : ℝ)^k from norm_p_unit_zpow k]
  have hIff : (p : ℝ)^k * ‖y‖ ≤ 1 ↔ ‖y‖ ≤ (p : ℝ)^(-k) := by
    rw [zpow_neg, ← one_div, le_div_iff₀ (zpow_pos (p_pos (p := p)) k), mul_comm]
  simp only [hIff]
  split_ifs <;> simp [Algebra.smul_def]


private noncomputable def logChar (ψ : AddChar ℚ_[p] Circle) (x : ℚ_[p]) : ℂ :=
  (Real.log ‖x‖ : ℂ) * (ψ (-x) : ℂ)

private noncomputable def baseLog (ψ : AddChar ℚ_[p] Circle) (k : ℤ) : ℂ :=
  ∫ x in ballPow (p := p) k, logChar ψ x ∂μ

private lemma integrableOn_log_norm_ballPow (k : ℤ) :
    IntegrableOn (fun x : ℚ_[p] ↦ Real.log ‖x‖) (ballPow (p := p) k) μ := by
  let O := closedBall (0 : ℚ_[p]) 1
  let B := ballPow (p := p) k
  let D := B \ O
  have hO := integrableOn_log_norm_unitBall μ
  have hM : Measurable (fun x : ℚ_[p] ↦ Real.log ‖x‖) := Real.measurable_log.comp measurable_norm
  have hD : IntegrableOn (fun x : ℚ_[p] ↦ Real.log ‖x‖) D μ := by
    have hFin : μ D ≠ ⊤ :=
      ((isCompact_closedBall (0:ℚ_[p]) ((p:ℝ)^k)).measure_lt_top.trans_le'
        (measure_mono (sdiff_subset : D ⊆ B))).ne
    refine (integrableOn_const (C := Real.log ((p : ℝ)^k)) hFin).mono'
      hM.aestronglyMeasurable ?_
    have hDm : MeasurableSet D := (measurableSet_ballPow k).diff measurableSet_closedBall
    filter_upwards [ae_restrict_mem (μ := μ) hDm] with x hx
    have hB := mem_ballPow.mp hx.1
    have hx1 : 1 < ‖x‖ := lt_of_not_ge (fun h ↦ hx.2 (by simpa [O, mem_closedBall, dist_eq_norm]))
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1.le)]
    exact Real.log_le_log (zero_lt_one.trans hx1) hB
  apply (hO.union hD).mono_set
  intro x hx
  by_cases h : x ∈ O
  · exact Or.inl h
  · exact Or.inr ⟨hx, h⟩

private lemma integrableOn_logChar_ballPow (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ) (k : ℤ) :
    IntegrableOn (logChar ψ) (ballPow (p := p) k) μ := by
  have hM : Measurable (logChar ψ) := by
    unfold logChar
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_norm)).mul
      (continuous_subtype_val.comp (hcont.comp continuous_neg)).measurable
  refine (integrableOn_log_norm_ballPow μ k).norm.mono' hM.aestronglyMeasurable ?_
  filter_upwards [] with x
  simp [logChar, Circle.norm_coe]

private lemma baseLog_zero (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) :
    baseLog μ ψ 0 =
      ↑(∫ x in closedBall (0 : ℚ_[p]) 1, Real.log ‖x‖ ∂μ) := by
  unfold baseLog
  rw [ballPow_zero]
  have he : (∫ x in closedBall (0 : ℚ_[p]) 1, (Real.log ‖x‖ : ℂ) ∂μ) =
      ↑(∫ x in closedBall (0 : ℚ_[p]) 1, Real.log ‖x‖ ∂μ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [← he]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x hx
  have hp : ψ (-x) = 1 := (hψ _).mpr (by simpa [mem_closedBall, dist_eq_norm] using hx)
  simp [logChar, hp]

private lemma baseLog_nonpos (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) {k : ℤ} (hk : k ≤ 0) :
    baseLog μ ψ k = (((p : ℝ)^k : ℝ) : ℂ) *
      (baseLog μ ψ 0 + ((k : ℝ) * Real.log p : ℝ)) := by
  let u : ℚ_[p] := ↑(pu (p := p)^(-k))
  have hu : ‖u‖ = (p : ℝ)^k := norm_p_unit_zpow k
  unfold baseLog at ⊢
  rw [integral_ballPow_scaling μ _ k, ballPow_zero]
  change ((p : ℝ)^k) • (∫ x in closedBall (0 : ℚ_[p]) 1, logChar ψ (u*x) ∂μ) =
    ↑((p : ℝ)^k) * ((∫ x in closedBall (0 : ℚ_[p]) 1, logChar ψ x ∂μ) + ↑((k : ℝ)*Real.log p))
  have hA : ∀ᵐ x : ℚ_[p] ∂μ.restrict (closedBall 0 1), x ≠ 0 := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  have hMem : ∀ᵐ x : ℚ_[p] ∂μ.restrict (closedBall 0 1), x ∈ closedBall (0 : ℚ_[p]) 1 :=
    ae_restrict_mem measurableSet_closedBall
  have hEq : (∫ x in closedBall (0 : ℚ_[p]) 1, logChar ψ (u*x) ∂μ) =
      ∫ x in closedBall (0 : ℚ_[p]) 1, ((k : ℝ)*Real.log p : ℂ) + (Real.log ‖x‖ : ℂ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hA,hMem] with x hx hx₁
    have hxU : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hx₁
    have hu1 : ‖u‖ ≤ 1 := hu ▸ (zpow_le_one_of_nonpos₀ (one_lt_p (p := p)).le hk)
    have hψu : ψ (-(u*x)) = 1 := (hψ _).mpr (by
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ hu1 (norm_nonneg _) hxU)
    rw [logChar, hψu, Circle.coe_one, mul_one, norm_mul, hu,
      Real.log_mul (zpow_ne_zero _ (p_pos (p := p)).ne') (norm_ne_zero_iff.mpr hx), Real.log_zpow]
    push_cast
    rfl
  have hI : Integrable (fun x : ℚ_[p] ↦ (Real.log ‖x‖ : ℂ))
      (μ.restrict (closedBall (0:ℚ_[p]) 1)) :=
    (integrableOn_log_norm_unitBall μ).ofReal (𝕜 := ℂ)
  have hC : IntegrableOn (fun _ : ℚ_[p] ↦ ((k : ℝ)*Real.log p : ℂ))
      (closedBall (0:ℚ_[p]) 1) μ := integrableOn_const (ball_fin μ)
  have hR : (∫ x in closedBall (0 : ℚ_[p]) 1, logChar ψ x ∂μ) =
      ∫ x in closedBall (0 : ℚ_[p]) 1, (Real.log ‖x‖ : ℂ) ∂μ := by
    rw [← ballPow_zero, ← baseLog, baseLog_zero μ ψ hψ, ballPow_zero]
    exact (integral_ofReal (𝕜 := ℂ)).symm
  rw [hEq, integral_add hC hI, setIntegral_const, hR, show μ.real (closedBall (0:ℚ_[p]) 1) = 1 by
    simp [Measure.real, hμ], one_smul, Algebra.smul_def]
  push_cast
  ring


private noncomputable def charArea (ψ : AddChar ℚ_[p] Circle) (k : ℤ) : ℂ :=
  ∫ x in ballPow (p := p) k, (ψ (-x) : ℂ) ∂μ

private lemma charArea_eq (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (k : ℤ) :
    charArea μ ψ k = if k ≤ 0 then (((p:ℝ)^k : ℝ) : ℂ) else 0 := by
  have h := char_integral_ballPow μ ψ hψ hμ k (-1)
  simp only [mul_neg, mul_one, norm_neg, norm_one] at h
  have he : (1 : ℝ) ≤ (p : ℝ)^(-k) ↔ k ≤ 0 := by
    rw [← zpow_zero (p : ℝ) (G := ℝ), (zpow_right_strictMono₀ (one_lt_p (p := p))).le_iff_le]
    omega
  simpa only [charArea, he] using h

private lemma baseLog_sub_pred (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ) (k : ℤ) :
    baseLog μ ψ k - baseLog μ ψ (k-1) =
      ((k : ℝ) * Real.log p : ℂ) * (charArea μ ψ k - charArea μ ψ (k-1)) := by
  let B := ballPow (p := p) k
  let A := ballPow (p := p) (k-1)
  let D := B \ A
  have hAB : A ⊆ B := ballPow_mono (by omega)
  have hDm : MeasurableSet D := (measurableSet_ballPow k).diff (measurableSet_ballPow (k-1))
  have hC : IntegrableOn (fun x : ℚ_[p] ↦ (ψ (-x) : ℂ)) B μ :=
    (continuous_subtype_val.comp (hcont.comp continuous_neg)).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hL := integrableOn_logChar_ballPow μ ψ hcont k
  have hLead :
      (∫ x in D, logChar ψ x ∂μ) =
        ((k : ℝ) * Real.log p : ℂ) * ∫ x in D, (ψ (-x) : ℂ) ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hDm
    intro x hx
    have hx' : ‖x‖ = (p : ℝ)^k := by
      have hS : x ∈ sphere (0:ℚ_[p]) ((p:ℝ)^k) := ballPow_sdiff_eq_sphere (p := p) k ▸ hx
      simpa [mem_sphere, dist_eq_norm] using hS
    rw [logChar, hx', Real.log_zpow]
    push_cast
    rfl
  rw [setIntegral_sdiff (measurableSet_ballPow (p := p) (k-1)) hL hAB,
    setIntegral_sdiff (measurableSet_ballPow (p := p) (k-1)) hC hAB] at hLead
  exact hLead

private lemma baseLog_pos (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) {k : ℤ} (hk : 0 < k) :
    baseLog μ ψ k = baseLog μ ψ 0 - (Real.log p : ℂ) := by
  have step_one := baseLog_sub_pred μ ψ hcont 1
  rw [show (1:ℤ)-1=0 by norm_num, charArea_eq μ ψ hψ hμ, charArea_eq μ ψ hψ hμ] at step_one
  simp only [show ¬ (1:ℤ) ≤ 0 by omega, show (0:ℤ) ≤ 0 by omega, if_false,
    if_true, zpow_zero, Complex.ofReal_one, Int.cast_one, one_mul,
    zero_sub, mul_neg, mul_one] at step_one
  have init : baseLog μ ψ 1 = baseLog μ ψ 0 - (Real.log p : ℂ) := by
    linear_combination step_one
  have hStep {k : ℤ} (hk : 1 < k) : baseLog μ ψ k = baseLog μ ψ (k-1) := by
    have hh := baseLog_sub_pred μ ψ hcont k
    rw [charArea_eq μ ψ hψ hμ, charArea_eq μ ψ hψ hμ,
      if_neg (by omega), if_neg (by omega), sub_self, mul_zero, sub_eq_zero] at hh
    exact hh
  have hN (n : ℕ) : baseLog μ ψ ((n:ℤ)+1) = baseLog μ ψ 0 - (Real.log p : ℂ) := by
    induction n with
    | zero => simpa using init
    | succ n IH =>
      rw [hStep (by omega), show ((n+1:ℕ):ℤ)+1-1 = (n:ℤ)+1 by omega]
      exact IH
  exact (show ((k-1).toNat:ℤ)+1 = k by omega) ▸ hN (k-1).toNat

private lemma baseLog_weighted (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) :
    (1 - ((p : ℝ)⁻¹ : ℂ)) * baseLog μ ψ 0 = -((p : ℝ)⁻¹ : ℂ) * (Real.log p : ℂ) := by
  rw [baseLog_zero μ ψ hψ]
  have h := log_norm_unitBall_weighted_identity μ
  rw [show μ.real (closedBall (0:ℚ_[p]) 1) = 1 by simp [Measure.real, hμ], mul_one] at h
  exact_mod_cast h


/-- The distribution character at any nonzero p-adic multiplier is its norm. -/
private lemma distribHaarChar_padic_zpow (u : ℚ_[p]ˣ) (j : ℤ)
    (hNorm : ‖(u : ℚ_[p])‖ = (p : ℝ)^j) (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1) :
    distribHaarChar ℚ_[p] u = (p:ℝ≥0)^j := by
  let O := closedBall (0:ℚ_[p]) 1
  have hD (a : ℚ_[p]ˣ) : a • O = closedBall (0:ℚ_[p]) ‖(a:ℚ_[p])‖ := by
    rw [unit_smul_set, _root_.smul_closedBall _ _ zero_le_one]
    simp
  have hEq : u • O = (pu (p := p)^(-j)) • O := by
    rw [hD,hD,hNorm,norm_p_unit_zpow j]
  have hm := congrArg μ hEq
  rw [← distribHaarChar_mul μ, ← distribHaarChar_mul μ, char_pu_zpow μ, show μ O = 1 from hμ,
    mul_one, mul_one] at hm
  exact ENNReal.coe_injective hm

private lemma integral_ballPow_comp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℚ_[p]ˣ) (j k : ℤ) (hNorm : ‖(u:ℚ_[p])‖ = (p:ℝ)^j)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1) (f : ℚ_[p] → E) :
    (∫ y in ballPow (p := p) k, f ((u:ℚ_[p])*y) ∂μ) =
      ((p:ℝ)^(-j)) • ∫ z in ballPow (p := p) (j+k), f z ∂μ := by
  let e : ℚ_[p] ≃ᵐ ℚ_[p] := (Homeomorph.smul u).toMeasurableEquiv
  have hn : ‖((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = (p:ℝ)^(-j) := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hNorm, zpow_neg]
  have hc := distribHaarChar_padic_zpow μ u⁻¹ (-j) hn hμ
  have hPre (s : Set ℚ_[p]) : e ⁻¹' s = u⁻¹ • s := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have hMap : Measure.map e μ = (((p:ℝ≥0)^(-j) : ℝ≥0) : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, hPre, ← distribHaarChar_mul μ, hc,
      Measure.smul_apply, smul_eq_mul]
  have he (y : ℚ_[p]) : e y = (u:ℚ_[p])*y := rfl
  have hB : e ⁻¹' ballPow (p := p) (j+k) = ballPow k := by
    ext y
    simp only [mem_preimage, mem_ballPow, he, norm_mul, hNorm, zpow_add₀ (p_pos (p := p)).ne']
    exact mul_le_mul_iff_right₀ (zpow_pos (p_pos (p := p)) j)
  have hi := setIntegral_map_equiv (μ := μ) e f (ballPow (p := p) (j+k))
  rw [hMap, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, hB] at hi
  simpa only [NNReal.coe_zpow, NNReal.coe_natCast, he] using hi.symm

private lemma integral_char_translatedBall (ψ : AddChar ℚ_[p] Circle) (a y : ℚ_[p])
    (k : ℤ) :
    (∫ x in closedBall a ((p:ℝ)^k), (ψ (x*y) : ℂ) ∂μ) =
      (ψ (a*y) : ℂ) * ∫ x in ballPow (p := p) k, (ψ (x*y) : ℂ) ∂μ := by
  let f (x : ℚ_[p]) := (ψ (x*y) : ℂ)
  let A := closedBall a ((p:ℝ)^k)
  have hi := integral_add_right_eq_self (μ := μ) (A.indicator f) a
  have he : (fun x : ℚ_[p] ↦ A.indicator f (x+a)) =
      (ballPow (p := p) k).indicator (fun x ↦ (ψ (a*y) : ℂ)*f x) := by
    funext x
    have hM : x+a ∈ A ↔ x ∈ ballPow (p := p) k := by
      simp [A,mem_closedBall,dist_eq_norm,mem_ballPow]
    by_cases hx : x ∈ ballPow (p := p) k
    · rw [indicator_of_mem hx, indicator_of_mem (hM.mpr hx)]
      unfold f
      rw [add_mul, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
    · rw [indicator_of_notMem hx, indicator_of_notMem (hM.not.mpr hx)]
  rw [he, integral_indicator (measurableSet_ballPow (p := p) k),
    integral_indicator (show MeasurableSet A from measurableSet_closedBall), integral_const_mul] at hi
  exact hi.symm

/-- The normalized additive transform of the indicator of a compact ball. -/
noncomputable def offsetBallFourier (ψ : AddChar ℚ_[p] Circle) (a : ℚ_[p]) (k : ℤ) (y : ℚ_[p]) : ℂ :=
  ∫ x in closedBall a ((p:ℝ)^k), (ψ (x*y) : ℂ) ∂μ

private lemma offsetBallFourier_eq (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (a y : ℚ_[p]) (k : ℤ) :
    offsetBallFourier μ ψ a k y =
      (ψ (a*y) : ℂ) * (if ‖y‖ ≤ (p:ℝ)^(-k) then (((p:ℝ)^k:ℝ):ℂ) else 0) := by
  rw [offsetBallFourier,integral_char_translatedBall, char_integral_ballPow μ ψ hψ hμ]


private lemma offsetBall_log_integral (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (a : ℚ_[p]) (k : ℤ) :
    Integrable (fun y ↦ (Real.log ‖y‖ : ℂ)*offsetBallFourier μ ψ a k y) μ ∧
    (∫ y, (Real.log ‖y‖ : ℂ)*offsetBallFourier μ ψ a k y ∂μ) =
      (((p : ℝ)^k : ℝ) : ℂ) *
        ∫ y in ballPow (p := p) (-k), (Real.log ‖y‖ : ℂ)*(ψ (a*y) : ℂ) ∂μ := by
  let f (y : ℚ_[p]) := (Real.log ‖y‖ : ℂ)*(ψ (a*y) : ℂ)
  have hM : Measurable f := by
    unfold f
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_norm)).mul
      (continuous_subtype_val.comp (hcont.comp (continuous_const.mul continuous_id))).measurable
  have hI : IntegrableOn f (ballPow (p := p) (-k)) μ := by
    refine (integrableOn_log_norm_ballPow μ (-k)).norm.mono' hM.aestronglyMeasurable ?_
    filter_upwards [] with y
    simp [f, Circle.norm_coe]
  have he : (fun y ↦ (Real.log ‖y‖ : ℂ)*offsetBallFourier μ ψ a k y) =
      fun y ↦ (((p : ℝ)^k : ℝ) : ℂ) * (ballPow (p := p) (-k)).indicator f y := by
    funext y
    rw [offsetBallFourier_eq μ ψ hψ hμ]
    simp only [indicator,mem_ballPow,f]
    split_ifs <;> ring
  rw [he]
  refine ⟨(hI.integrable_indicator (measurableSet_ballPow _)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_indicator (measurableSet_ballPow _)]

private lemma baseLog_positive_normalized (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) {j : ℤ} (hj : 0 < j) :
    baseLog μ ψ j = -(Real.log p / (1-(p:ℝ)⁻¹) : ℝ) := by
  rw [baseLog_pos μ ψ hcont hψ hμ hj]
  have hW := baseLog_weighted μ ψ hψ hμ
  have hd : 0 < 1-(p:ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
  let d : ℝ := 1-(p:ℝ)⁻¹
  let L : ℂ := Real.log (p:ℝ)
  have hD : (d:ℂ) = 1-((p:ℝ):ℂ)⁻¹ := by
    simp only [d, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  have hD0 : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hKey : (baseLog μ ψ 0-L)*(d:ℂ) = -L := by
    rw [hD]
    unfold L
    linear_combination hW
  change baseLog μ ψ 0-L = -((Real.log (p:ℝ)/d : ℝ) : ℂ)
  rw [Complex.ofReal_div, ← neg_div]
  exact (eq_div_iff hD0).mpr hKey

/-- Away from the pole the logarithmic Fourier distribution equals its
ordinary rational p-adic kernel on every compact ball. -/
theorem padic_log_fourier_away_from_origin_ball
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (a : ℚ_[p]) (k : ℤ)
    (ha : (p : ℝ)^k < ‖a‖) :
    Integrable (fun y ↦ (Real.log ‖y‖ : ℂ)*offsetBallFourier μ ψ a k y) μ ∧
    (∫ y, (Real.log ‖y‖ : ℂ)*offsetBallFourier μ ψ a k y ∂μ) =
      -(Real.log p/(1-(p:ℝ)⁻¹) : ℝ)*(((p:ℝ)^k/‖a‖ : ℝ) : ℂ) := by
  obtain ⟨hI,hEq⟩ := offsetBall_log_integral μ ψ hcont hψ hμ a k
  refine ⟨hI,hEq.trans ?_⟩
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp ((zpow_pos (p_pos (p := p)) k).trans ha).ne'
  let j := -a.valuation
  have haj : ‖a‖ = (p:ℝ)^j := Padic.norm_eq_zpow_neg_valuation ha0
  have hj : k < j := (zpow_right_strictMono₀ (one_lt_p (p := p))).lt_iff_lt.mp
    (show (p:ℝ)^k < (p:ℝ)^j from haj ▸ ha)
  let u : ℚ_[p]ˣ := Units.mk0 (-a) (neg_ne_zero.mpr ha0)
  have hu : ‖(u : ℚ_[p])‖ = (p:ℝ)^j := (norm_neg a).trans haj
  let c : ℂ := ((j:ℝ)*Real.log p : ℂ)
  let g (z : ℚ_[p]) := logChar ψ z - c*(ψ (-z) : ℂ)
  have hAE : ∀ᵐ y : ℚ_[p] ∂μ.restrict (ballPow (p := p) (-k)), y ≠ 0 := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  have hReplace :
      (∫ y in ballPow (p := p) (-k), (Real.log ‖y‖ : ℂ)*(ψ (a*y) : ℂ) ∂μ) =
        ∫ y in ballPow (p := p) (-k), g ((u : ℚ_[p])*y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hAE] with y hy
    dsimp only [g, c, logChar, u, Units.val_mk0]
    rw [neg_mul, neg_neg, norm_neg, norm_mul, haj,
      Real.log_mul (zpow_ne_zero _ (p_pos (p := p)).ne') (norm_ne_zero_iff.mpr hy), Real.log_zpow]
    push_cast
    ring
  have hC : IntegrableOn (fun z : ℚ_[p] ↦ (ψ (-z) : ℂ)) (ballPow (p := p) (j-k)) μ :=
    (continuous_subtype_val.comp (hcont.comp continuous_neg)).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hF : (∫ z in ballPow (p := p) (j-k), g z ∂μ) = baseLog μ ψ (j-k) := by
    unfold g
    rw [integral_sub (integrableOn_logChar_ballPow μ ψ hcont _) (hC.const_mul _),
      integral_const_mul]
    change baseLog μ ψ (j-k) - c*charArea μ ψ (j-k) = _
    rw [charArea_eq μ ψ hψ hμ, if_neg (by omega), mul_zero, sub_zero]
  rw [hReplace, integral_ballPow_comp_mul μ u j (-k) hu hμ g, ← sub_eq_add_neg,
    hF, baseLog_positive_normalized μ ψ hcont hψ hμ (by omega), haj,
    Algebra.smul_def, zpow_neg, div_eq_mul_inv]
  push_cast
  ring

end MasulloAudit.PadicUnits

open MeasureTheory
open scoped Topology

theorem solution {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (a : ℚ_[p]) (k : ℤ) (ha : (p : ℝ)^k < ‖a‖) :
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x in Metric.closedBall a ((p : ℝ)^k), (ψ (x*y) : ℂ) ∂μ)
    Integrable F μ ∧ (∫ y, F y ∂μ) =
      -(Real.log p/(1-(p : ℝ)⁻¹) : ℝ)*(((p : ℝ)^k/‖a‖ : ℝ) : ℂ) := by
  exact MasulloAudit.PadicUnits.padic_log_fourier_away_from_origin_ball μ ψ hcont hψ hμ a k ha
