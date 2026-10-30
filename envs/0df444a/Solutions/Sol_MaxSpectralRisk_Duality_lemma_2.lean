-- Prove2me | solution 1 for MaxSpectralRisk.Duality.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:57:35.771446+00:00
-- url     : https://prove2.me/submissions/c09f8221-7357-4c0f-9d85-8c5090f88524

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRL2Aux

variable {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π] {L : W → ℝ}

lemma int_pos (hL : Integrable L π) (b : ℝ) : Integrable (fun p => max (L p - b) 0) π :=
  (hL.sub (integrable_const b)).pos_part

/-- Subgradient inequality for `φ(b) = E[(L - b)₊]` with slope `-π(S)`, for any measurable `S`
with `{b < L} ⊆ S ⊆ {b ≤ L}`. -/
lemma phi_subgrad (hL : Integrable L π) {b : ℝ} {S : Set W} (hS : MeasurableSet S)
    (h1 : ∀ p, b < L p → p ∈ S) (h2 : ∀ p ∈ S, b ≤ L p) (b' : ℝ) :
    ∫ p, max (L p - b) 0 ∂π - π.real S * (b' - b) ≤ ∫ p, max (L p - b') 0 ∂π := by
  have hind : Integrable (S.indicator fun _ => b' - b) π :=
    (integrable_const (b' - b)).indicator hS
  have : ∫ p, max (L p - b) 0 ∂π - π.real S * (b' - b) =
      ∫ p, (max (L p - b) 0 - S.indicator (fun _ => b' - b) p) ∂π := by
    rw [integral_sub (int_pos hL b) hind, integral_indicator_const _ hS, smul_eq_mul]
  rw [this]
  refine integral_mono ((int_pos hL b).sub hind) (int_pos hL b') fun p => ?_
  by_cases hp : p ∈ S
  · simp only [Set.indicator_of_mem hp]
    rw [max_eq_left (by linarith [h2 p hp])]
    linarith [le_max_left (L p - b') 0]
  · simp only [Set.indicator_of_notMem hp, sub_zero]
    have : L p ≤ b := le_of_not_gt fun h => hp (h1 p h)
    rw [max_eq_right (by linarith)]
    exact le_max_right _ _

lemma phi_right (hLm : Measurable L) (hL : Integrable L π) (b : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ p, max (L p - (b + h)) 0 ∂π - ∫ p, max (L p - b) 0 ∂π ≤
      -h * π.real {p | b + h < L p} := by
  set S := {p | b + h < L p}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hLm
  have hind : Integrable (S.indicator fun _ => -h) π := (integrable_const (-h)).indicator hS
  rw [← integral_sub (int_pos hL _) (int_pos hL b), mul_comm, ← smul_eq_mul,
    ← integral_indicator_const _ hS]
  refine integral_mono ((int_pos hL _).sub (int_pos hL b)) hind fun p => ?_
  by_cases hp : p ∈ S
  · simp only [Set.indicator_of_mem hp]
    have : b + h < L p := hp
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · simp only [Set.indicator_of_notMem hp]
    have : L p ≤ b + h := le_of_not_gt hp
    rw [max_eq_right (by linarith)]
    linarith [le_max_right (L p - b) 0]

lemma phi_left (hLm : Measurable L) (hL : Integrable L π) (b : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ p, max (L p - (b - h)) 0 ∂π - ∫ p, max (L p - b) 0 ∂π ≤
      h * π.real {p | b - h < L p} := by
  set S := {p | b - h < L p}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hLm
  have hind : Integrable (S.indicator fun _ => h) π := (integrable_const h).indicator hS
  rw [← integral_sub (int_pos hL _) (int_pos hL b), mul_comm, ← smul_eq_mul,
    ← integral_indicator_const _ hS]
  refine integral_mono ((int_pos hL _).sub (int_pos hL b)) hind fun p => ?_
  by_cases hp : p ∈ S
  · simp only [Set.indicator_of_mem hp]
    have := abs_max_sub_max_le_abs (L p - (b - h)) (L p - b) 0
    rw [show L p - (b - h) - (L p - b) = h by ring, abs_of_pos hh] at this
    exact (le_abs_self _).trans this
  · simp only [Set.indicator_of_notMem hp]
    have : L p ≤ b - h := le_of_not_gt hp
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp

lemma tendsto_right (hLm : Measurable L) (b : ℝ) :
    Tendsto (fun n : ℕ => π.real {p | b + 1 / ((n : ℝ) + 1) < L p}) atTop
      (𝓝 (π.real {p | b < L p})) := by
  have hmono : Monotone (fun n : ℕ => {p | b + 1 / ((n : ℝ) + 1) < L p}) := by
    intro n m hnm p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    linarith
  have hU : (⋃ n : ℕ, {p | b + 1 / ((n : ℝ) + 1) < L p}) = {p | b < L p} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hp)
      exact ⟨n, by linarith⟩
  have := tendsto_measure_iUnion_atTop (μ := π) hmono
  rw [hU] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top π _)).comp this

lemma tendsto_left (hLm : Measurable L) (b : ℝ) :
    Tendsto (fun n : ℕ => π.real {p | b - 1 / ((n : ℝ) + 1) < L p}) atTop
      (𝓝 (π.real {p | b ≤ L p})) := by
  have hanti : Antitone (fun n : ℕ => {p | b - 1 / ((n : ℝ) + 1) < L p}) := by
    intro n m hnm p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    linarith
  have hI : (⋂ n : ℕ, {p | b - 1 / ((n : ℝ) + 1) < L p}) = {p | b ≤ L p} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := h n
      linarith
    · intro hp n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have := tendsto_measure_iInter_atTop (μ := π)
    (fun n => (measurableSet_lt measurable_const hLm).nullMeasurableSet) hanti
    ⟨0, measure_ne_top π _⟩
  rw [hI] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top π _)).comp this

end MSRL2Aux

open MSRL2Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (π : Measure (X × Y)) [IsProbabilityMeasure π]
    (L : X × Y → ℝ) (hLm : Measurable L) (hL : Integrable L π) :
    ConvexOn ℝ Set.univ (fun b => g α b π L) ∧
    Tendsto (fun b => g α b π L) atTop atTop ∧
    Tendsto (fun b => g α b π L) atBot atTop ∧
    (∀ b : ℝ, {s : ℝ | ∀ b' : ℝ, g α b π L + s * (b' - b) ≤ g α b' π L} =
      Set.Icc (1 - (1 - α)⁻¹ * π.real {p | b ≤ L p}) (1 - (1 - α)⁻¹ * π.real {p | b < L p})) ∧
    {b : ℝ | ∀ b' : ℝ, g α b π L ≤ g α b' π L} =
      {b : ℝ | π.real {p | b < L p} ≤ 1 - α ∧ 1 - α ≤ π.real {p | b ≤ L p}} := by
  have h1α : 0 < 1 - α := by linarith [hα.2]
  set c := (1 - α)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 h1α
  have hc1 : 1 < c := by
    rw [hc]; exact one_lt_inv_iff₀.2 ⟨h1α, by linarith [hα.1]⟩
  have hφnn : ∀ b, 0 ≤ ∫ p, max (L p - b) 0 ∂π := fun b =>
    integral_nonneg fun p => le_max_right _ _
  -- convexity
  have hconv : ConvexOn ℝ Set.univ (fun b => g α b π L) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have key : ∫ p, max (L p - (a * x + b * y)) 0 ∂π ≤
        a * ∫ p, max (L p - x) 0 ∂π + b * ∫ p, max (L p - y) 0 ∂π := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((int_pos hL x).const_mul a) ((int_pos hL y).const_mul b)]
      refine integral_mono (int_pos hL _) (((int_pos hL x).const_mul a).add
        ((int_pos hL y).const_mul b)) fun p => ?_
      have e : L p - (a * x + b * y) = a * (L p - x) + b * (L p - y) := by
        linear_combination (-(L p)) * hab
      show max (L p - (a * x + b * y)) 0 ≤ a * max (L p - x) 0 + b * max (L p - y) 0
      rw [e]
      exact max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
        (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
    simp only [g, smul_eq_mul]
    have := mul_le_mul_of_nonneg_left key hc0.le
    nlinarith
  -- coercivity
  have htop : Tendsto (fun b => g α b π L) atTop atTop := by
    refine tendsto_atTop_mono (fun b => ?_) tendsto_id
    show b ≤ b + c * ∫ p, max (L p - b) 0 ∂π
    have := mul_nonneg hc0.le (hφnn b)
    linarith
  have hbot : Tendsto (fun b => g α b π L) atBot atTop := by
    have hlow : ∀ b, c * ∫ p, L p ∂π + (1 - c) * b ≤ g α b π L := by
      intro b
      show _ ≤ b + c * ∫ p, max (L p - b) 0 ∂π
      have : ∫ p, L p ∂π - b ≤ ∫ p, max (L p - b) 0 ∂π := by
        have hsI : Integrable (fun p => L p - b) π := hL.sub (integrable_const b)
        have h := integral_mono hsI (int_pos hL b) (fun p => le_max_left (L p - b) 0)
        rw [integral_sub hL (integrable_const b)] at h
        simpa using h
      nlinarith
    refine tendsto_atTop_mono hlow ?_
    exact tendsto_atTop_add_const_left _ _
      (tendsto_id.const_mul_atBot_of_neg (by linarith : 1 - c < 0))
  -- subdifferential
  have hcα : c * (1 - α) = 1 := by rw [hc]; exact inv_mul_cancel₀ h1α.ne'
  have hsub : ∀ b : ℝ, {s : ℝ | ∀ b' : ℝ, g α b π L + s * (b' - b) ≤ g α b' π L} =
      Set.Icc (1 - c * π.real {p | b ≤ L p}) (1 - c * π.real {p | b < L p}) := by
    intro b
    have hsg : ∀ S : Set (X × Y), MeasurableSet S → (∀ p, b < L p → p ∈ S) →
        (∀ p ∈ S, b ≤ L p) → ∀ b', g α b π L + (1 - c * π.real S) * (b' - b) ≤ g α b' π L := by
      intro S hS h1 h2 b'
      have := mul_le_mul_of_nonneg_left (phi_subgrad hL hS h1 h2 b') hc0.le
      simp only [g]
      rw [← hc]
      nlinarith
    have hge := hsg {p | b ≤ L p} (measurableSet_le measurable_const hLm)
      (fun p h => le_of_lt h) (fun p h => h)
    have hgt := hsg {p | b < L p} (measurableSet_lt measurable_const hLm)
      (fun p h => h) (fun p h => le_of_lt h)
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · intro hs
      constructor
      · by_contra hlt
        push Not at hlt
        have hlim := tendsto_left (π := π) hLm b
        have htarget : π.real {p | b ≤ L p} < (1 - s) / c := by
          rw [lt_div_iff₀ hc0]; linarith
        obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ htarget).exists
        set h : ℝ := 1 / ((n : ℝ) + 1) with hh
        have hpos : 0 < h := by positivity
        have hPn : c * π.real {p | b - h < L p} < 1 - s := by
          rw [lt_div_iff₀ hc0] at hn; linarith
        have hb' := hs (b - h)
        have hφ := mul_le_mul_of_nonneg_left (phi_left (π := π) hLm hL b hpos) hc0.le
        have hm := mul_lt_mul_of_pos_left hPn hpos
        simp only [g] at hb'
        rw [← hc] at hb'
        nlinarith
      · by_contra hlt
        push Not at hlt
        have hlim := tendsto_right (π := π) hLm b
        have htarget : (1 - s) / c < π.real {p | b < L p} := by
          rw [div_lt_iff₀ hc0]; linarith
        obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 _ htarget).exists
        set h : ℝ := 1 / ((n : ℝ) + 1) with hh
        have hpos : 0 < h := by positivity
        have hPn : 1 - s < c * π.real {p | b + h < L p} := by
          rw [div_lt_iff₀ hc0] at hn; linarith
        have hb' := hs (b + h)
        have hφ := mul_le_mul_of_nonneg_left (phi_right (π := π) hLm hL b hpos) hc0.le
        have hm := mul_lt_mul_of_pos_left hPn hpos
        simp only [g] at hb'
        rw [← hc] at hb'
        nlinarith
    · rintro ⟨hs1, hs2⟩ b'
      rcases le_total b b' with h | h
      · have := mul_le_mul_of_nonneg_right hs2 (sub_nonneg.2 h)
        linarith [hgt b']
      · have := mul_le_mul_of_nonpos_right hs1 (sub_nonpos.2 h)
        linarith [hge b']
  refine ⟨hconv, htop, hbot, hsub, ?_⟩
  ext b
  have key := Set.ext_iff.1 (hsub b) 0
  simp only [Set.mem_setOf_eq, Set.mem_Icc, zero_mul, add_zero] at key
  simp only [Set.mem_setOf_eq]
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith [measureReal_nonneg (μ := π) (s := {p | b < L p})]
    · nlinarith [measureReal_nonneg (μ := π) (s := {p | b ≤ L p})]
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith [measureReal_nonneg (μ := π) (s := {p | b ≤ L p})]
    · nlinarith [measureReal_nonneg (μ := π) (s := {p | b < L p})]
