-- Prove2me | solution 1 for MasulloRH.padic_unit_connes_principal_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:37:41.011686+00:00
-- url     : https://prove2.me/submissions/d24a5d1a-0fee-450d-8ee6-f4650b027247

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


/-- The Fourier transform tested in the principal value
`- μ(𝒪) ∫ log ‖y‖ · û(y) dμ(y)` of Appendix B.4.4. -/
noncomputable def shiftedUnitFourier (ψ : AddChar ℚ_[p] Circle) (y : ℚ_[p]) : ℂ :=
  ∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ

private lemma norm_of_mem_outerShell {y : ℚ_[p]} (h₁ : 1 < ‖y‖) (hp : ‖y‖ ≤ (p : ℝ)) :
    ‖y‖ = (p : ℝ) := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h₁
    linarith only [h₁]
  rw [Padic.norm_eq_zpow_neg_valuation hy] at *
  have hpos : 0 < -y.valuation := by
    by_contra! h
    have hle := zpow_le_zpow_right₀ (one_lt_p (p := p)).le h
    rw [zpow_zero] at hle
    exact h₁.not_ge hle
  have hle : -y.valuation ≤ 1 := by
    by_contra! h
    have hlt := zpow_lt_zpow_right₀ (one_lt_p (p := p)) h
    rw [zpow_one] at hlt
    exact hlt.not_ge hp
  rw [show -y.valuation = 1 by omega, zpow_one]

/-- The shifted unit set is the unit ball with the coset `-1 + p𝒪` removed. -/
private lemma shiftedUnit_eq_diff :
    {x : ℚ_[p] | ‖1 + x‖ = 1} = closedBall 0 1 \
      ((fun x : ℚ_[p] ↦ x + 1) ⁻¹' closedBall 0 (p : ℝ)⁻¹) := by
  ext x
  simp only [mem_ofPred_eq, mem_sdiff, mem_preimage, mem_closedBall, dist_eq_norm, sub_zero]
  have hq := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
  have hle (hx : ‖x‖ ≤ 1) : ‖1 + x‖ ≤ 1 := by
    simpa only [norm_one, max_eq_left hx] using IsUltrametricDist.norm_add_le_max (1 : ℚ_[p]) x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have he := IsUltrametricDist.norm_add_le_max (1 + x) (-1 : ℚ_[p])
      simpa [hx] using he
    · rw [add_comm x, hx]
      exact hq.not_ge
  · rintro ⟨hx, hx'⟩
    exact le_antisymm (hle hx) (le_of_not_gt fun h ↦ hx' <|
      by simpa only [add_comm x 1] using norm_le_inv_of_lt_one h)

private lemma shiftedBall_subset_unitBall :
    ((fun x : ℚ_[p] ↦ x + 1) ⁻¹' closedBall 0 (p : ℝ)⁻¹) ⊆ closedBall 0 1 := by
  intro x hx
  have hx' : ‖x + 1‖ ≤ 1 := by
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero] at hx
    exact hx.trans (inv_le_one_of_one_le₀ (one_lt_p (p := p)).le)
  simp only [mem_closedBall, dist_eq_norm, sub_zero]
  have he := IsUltrametricDist.norm_add_le_max (x + 1) (-1 : ℚ_[p])
  simpa [max_eq_right hx'] using he

private lemma shiftedBall_character_integral (ψ : AddChar ℚ_[p] Circle)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) (y : ℚ_[p]) :
    (∫ x in (fun x : ℚ_[p] ↦ x + 1) ⁻¹' closedBall 0 (p : ℝ)⁻¹,
      (ψ (x * y) : ℂ) ∂μ) =
      if ‖y‖ ≤ (p : ℝ) then ((p : ℝ)⁻¹ : ℂ) * (ψ (-y) : ℂ) else 0 := by
  let B := closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹
  let U := (fun x : ℚ_[p] ↦ x + 1) ⁻¹' B
  have hUm : MeasurableSet U := measurableSet_closedBall.preimage (measurable_id.add_const _)
  have hTranslate :
      (∫ x in U, (ψ (x * y) : ℂ) ∂μ) = ∫ x in B, (ψ ((x - 1) * y) : ℂ) ∂μ := by
    rw [← integral_indicator hUm, ← integral_indicator measurableSet_closedBall]
    have he := integral_add_right_eq_self (μ := μ)
      (U.indicator (fun x ↦ (ψ (x * y) : ℂ))) (-1)
    rw [← he]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change U.indicator (fun x ↦ (ψ (x * y) : ℂ)) (x + (-1)) =
        B.indicator (fun x ↦ (ψ ((x - 1) * y) : ℂ)) x
      by_cases hx : x ∈ B
      · have ht : x + (-1) ∈ U := by simpa only [U, mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx
        rw [indicator_of_mem ht, indicator_of_mem hx, sub_eq_add_neg]
      · have ht : x + (-1) ∉ U := by simpa only [U, mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx
        rw [indicator_of_notMem ht, indicator_of_notMem hx]
  have hShift (x : ℚ_[p]) : (ψ ((x - 1) * y) : ℂ) = (ψ (-y) : ℂ) * (ψ (x * y) : ℂ) := by
    rw [sub_mul, one_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hyp : ‖(p : ℚ_[p]) * y‖ ≤ 1 ↔ ‖y‖ ≤ (p : ℝ) := by
    rw [norm_mul, Padic.norm_p]
    calc
      (p : ℝ)⁻¹ * ‖y‖ ≤ 1 ↔ (p : ℝ)⁻¹ * ‖y‖ ≤ (p : ℝ)⁻¹ * p := by
        rw [inv_mul_cancel₀ (p_pos (p := p)).ne']
      _ ↔ ‖y‖ ≤ (p : ℝ) := mul_le_mul_iff_right₀ (inv_pos.mpr (p_pos (p := p)))
  have hScaling := integral_smallBall_scaling μ (fun x : ℚ_[p] ↦ (ψ (x * y) : ℂ))
  simp only [mul_assoc, mul_left_comm (p : ℚ_[p]), char_integral_unitBall μ ψ hψ hμ, hyp] at hScaling
  rw [hTranslate]
  simp_rw [hShift]
  rw [integral_const_mul, hScaling]
  split_ifs <;> simp [Algebra.smul_def, mul_comm]

/-- With a conductor-zero additive character and `μ(𝒪) = 1`, the Fourier
transform of the shifted unit indicator has only two ball contributions. -/
theorem shiftedUnitFourier_eq (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1)
    (y : ℚ_[p]) :
    shiftedUnitFourier μ ψ y =
      (if ‖y‖ ≤ 1 then 1 else 0) -
        (if ‖y‖ ≤ (p : ℝ) then ((p : ℝ)⁻¹ : ℂ) * (ψ (-y) : ℂ) else 0) := by
  have hcont' : Continuous (fun x : ℚ_[p] ↦ (ψ (x * y) : ℂ)) :=
    continuous_subtype_val.comp (hcont.comp (continuous_id.mul_const _))
  have hU : MeasurableSet ((fun x : ℚ_[p] ↦ x + 1) ⁻¹' closedBall 0 (p : ℝ)⁻¹) :=
    measurableSet_closedBall.preimage (measurable_id.add_const _)
  rw [shiftedUnitFourier, shiftedUnit_eq_diff, setIntegral_sdiff hU
    (hcont'.continuousOn.integrableOn_compact (isCompact_closedBall _ _)) shiftedBall_subset_unitBall,
    char_integral_unitBall μ ψ hψ hμ, shiftedBall_character_integral μ ψ hψ hμ]

private lemma outerShell_character_integral (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) :
    (∫ y in closedBall (0 : ℚ_[p]) (p : ℝ) \ closedBall 0 1, (ψ (-y) : ℂ) ∂μ) = -1 := by
  have hcont' : Continuous (fun y : ℚ_[p] ↦ (ψ (-y) : ℂ)) :=
    continuous_subtype_val.comp (hcont.comp continuous_neg)
  have hball :
      (∫ y in closedBall (0 : ℚ_[p]) (p : ℝ), (ψ (-y) : ℂ) ∂μ) = 0 := by
    have hmem : (p : ℚ_[p])⁻¹ ∈ closedBall (0 : ℚ_[p]) (p : ℝ) := by
      simp [mem_closedBall, dist_eq_norm, norm_inv, Padic.norm_p]
    have hne : ψ ((p : ℚ_[p])⁻¹ * (-1)) ≠ 1 := (hψ _).not.mpr <| by
      rw [mul_neg, mul_one, norm_neg, norm_inv, Padic.norm_p, inv_inv]
      exact (one_lt_p (p := p)).not_ge
    simpa only [mul_neg, mul_one] using char_integral_closedBall_eq_zero μ ψ hmem (-1) hne
  have hunit :
      (∫ y in closedBall (0 : ℚ_[p]) 1, (ψ (-y) : ℂ) ∂μ) = 1 := by
    simpa using char_integral_unitBall μ ψ hψ hμ (-1)
  rw [setIntegral_sdiff measurableSet_closedBall
    (hcont'.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    (closedBall_subset_closedBall (one_lt_p (p := p)).le), hball, hunit, zero_sub]


/-- The logarithmic Fourier integral of the shifted unit indicator vanishes
at every rational prime. The outer shell contribution cancels the integral
over the unit ball. Consequently, the Connes principal value of a radial
test with this finite-place restriction vanishes. -/
theorem padic_unit_connes_principal_value_zero (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) :
    Integrable (fun y ↦ (Real.log ‖y‖ : ℂ) * shiftedUnitFourier μ ψ y) μ ∧
    (∫ y, (Real.log ‖y‖ : ℂ) * shiftedUnitFourier μ ψ y ∂μ) = 0 := by
  let O := closedBall (0 : ℚ_[p]) 1
  let P := closedBall (0 : ℚ_[p]) (p : ℝ)
  let q := (p : ℝ)⁻¹
  let f := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) * shiftedUnitFourier μ ψ y
  let D := P \ O
  have hOP : O ⊆ P := closedBall_subset_closedBall (one_lt_p (p := p)).le
  have hDm : MeasurableSet D := measurableSet_closedBall.diff measurableSet_closedBall
  have hO (y : ℚ_[p]) (hy : y ∈ O) :
      f y = ((1 - q : ℝ) : ℂ) * (Real.log ‖y‖ : ℂ) := by
    have hy' : ‖y‖ ≤ 1 := by simpa only [O, mem_closedBall, dist_eq_norm, sub_zero] using hy
    have hyP : ‖y‖ ≤ (p : ℝ) := hy'.trans (one_lt_p (p := p)).le
    have hpψ : (ψ (-y) : ℂ) = 1 :=
      congrArg (fun z : Circle ↦ (z : ℂ)) ((hψ _).mpr (by simpa only [norm_neg] using hy'))
    dsimp only [f]
    rw [shiftedUnitFourier_eq μ ψ hcont hψ hμ, if_pos hy', if_pos hyP, hpψ, mul_one]
    dsimp only [q]
    push_cast
    ring
  have hD (y : ℚ_[p]) (hy : y ∈ D) :
      f y = (-(q * Real.log p) : ℝ) * (ψ (-y) : ℂ) := by
    have hP : ‖y‖ ≤ (p : ℝ) := by simpa only [P, mem_closedBall, dist_eq_norm, sub_zero] using hy.1
    have hO : ¬ ‖y‖ ≤ 1 := by simpa only [O, mem_closedBall, dist_eq_norm, sub_zero] using hy.2
    dsimp only [f]
    rw [shiftedUnitFourier_eq μ ψ hcont hψ hμ, if_neg hO, if_pos hP,
      norm_of_mem_outerShell (lt_of_not_ge hO) hP]
    dsimp only [q]
    push_cast
    ring
  have hOf : IntegrableOn f O μ := by
    refine (Integrable.congr ((integrableOn_log_norm_unitBall μ).ofReal.const_mul
      (((1 - q : ℝ)) : ℂ)) ?_)
    filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_closedBall : MeasurableSet O)] with y hy
    exact (hO y hy).symm
  have hDf : IntegrableOn f D μ := by
    have hC : Continuous (fun y : ℚ_[p] ↦ (ψ (-y) : ℂ)) :=
      continuous_subtype_val.comp (hcont.comp continuous_neg)
    have hI : IntegrableOn (fun y : ℚ_[p] ↦ (ψ (-y) : ℂ)) P μ :=
      hC.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    refine (Integrable.congr ((hI.mono_set (sdiff_subset : D ⊆ P)).const_mul
      ((-(q * Real.log p) : ℝ) : ℂ)) ?_)
    filter_upwards [ae_restrict_mem (μ := μ) hDm] with y hy
    exact (hD y hy).symm
  have hOut (y : ℚ_[p]) (hy : y ∉ P) : f y = 0 := by
    have hyP : ¬ ‖y‖ ≤ (p : ℝ) := by simpa only [P, mem_closedBall, dist_eq_norm, sub_zero] using hy
    have hyO : ¬ ‖y‖ ≤ 1 := fun h ↦ hyP (h.trans (one_lt_p (p := p)).le)
    simp only [f, shiftedUnitFourier_eq μ ψ hcont hψ hμ, if_neg hyO, if_neg hyP, sub_self, mul_zero]
  have hUnion : O ∪ D = P := union_sdiff_cancel hOP
  have hPInt : IntegrableOn f P μ := hUnion ▸ hOf.union hDf
  have hf : Integrable f μ := by
    refine (hPInt.integrable_indicator measurableSet_closedBall).congr ?_
    exact Filter.Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ P
      · exact indicator_of_mem hy _
      · rw [indicator_of_notMem hy, hOut y hy]
  refine ⟨hf, ?_⟩
  change (∫ y, f y ∂μ) = 0
  have hAll : (∫ y, f y ∂μ) = ∫ y in P, f y ∂μ := by
    rw [← integral_indicator measurableSet_closedBall]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ P
      · exact (indicator_of_mem hy _).symm
      · rw [indicator_of_notMem hy, hOut y hy])
  have hhO := setIntegral_congr_fun (μ := μ) (measurableSet_closedBall : MeasurableSet O) hO
  have hhD := setIntegral_congr_fun (μ := μ) hDm hD
  rw [hAll, ← hUnion, setIntegral_union disjoint_sdiff_right hDm hOf hDf, hhO, hhD,
    integral_const_mul, integral_const_mul, integral_complex_ofReal,
    outerShell_character_integral μ ψ hcont hψ hμ]
  have hMean := log_norm_unitBall_weighted_identity μ
  have hμreal : μ.real O = 1 := by simp [Measure.real, O, hμ]
  change (1 - q) * (∫ y in O, Real.log ‖y‖ ∂μ) = -q * Real.log p * μ.real O at hMean
  rw [hμreal, mul_one] at hMean
  have hZero : (1 - q) * (∫ y in O, Real.log ‖y‖ ∂μ) +
      (-(q * Real.log p)) * (-1) = 0 := by
    rw [hMean]
    ring
  exact_mod_cast hZero

end MasulloAudit.PadicUnits

theorem solution
    {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) :
    let f : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ)
    Integrable f μ ∧ (∫ y, f y ∂μ) = 0 := by
  exact MasulloAudit.PadicUnits.padic_unit_connes_principal_value_zero μ ψ hcont hψ hμ
