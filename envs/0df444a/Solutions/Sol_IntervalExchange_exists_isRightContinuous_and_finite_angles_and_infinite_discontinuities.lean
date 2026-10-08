-- Prove2me | solution 1 for IntervalExchange.exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:26:03.424603+00:00
-- url     : https://prove2.me/submissions/ec413fee-a484-42ef-9605-c2fc2f8d0ece

import Mathlib
import Definitions.Def_IntervalExchange

namespace IntervalExchange

namespace IETReadingsP1

open Filter Topology

/-- The index `N(t)`: for `u = fract(2t)/2 ∈ [0,1/2)`, `N = ⌊1/(1/2 - u)⌋`. -/
noncomputable def N (t : ℝ) : ℕ := ⌊2 / (1 - Int.fract (2 * t))⌋₊

/-- The angle at `t`: `1/2` on the arcs with odd index, `0` elsewhere. -/
noncomputable def a (t : ℝ) : ℝ := if Odd (N t) then 1 / 2 else 0

lemma N_add_half (t : ℝ) : N (t + 1 / 2) = N t := by
  unfold N
  rw [show 2 * (t + 1 / 2) = 2 * t + 1 by ring, Int.fract_add_one]

lemma a_add_half (t : ℝ) : a (t + 1 / 2) = a t := by
  unfold a; rw [N_add_half]

lemma a_add_one (t : ℝ) : a (t + 1) = a t := by
  rw [show t + 1 = t + 1 / 2 + 1 / 2 by ring, a_add_half, a_add_half]

lemma a_add_a (t : ℝ) : a (t + a t) = a t := by
  by_cases h : Odd (N t)
  · have : a t = 1 / 2 := if_pos h
    rw [this, a_add_half, this]
  · have : a t = 0 := if_neg h
    rw [this, add_zero, this]

/-- The lift of `g` to `ℝ`. -/
noncomputable def gt (t : ℝ) : UnitAddCircle := ((t + a t : ℝ) : UnitAddCircle)

lemma gt_periodic : Function.Periodic gt 1 := by
  intro t
  unfold gt
  rw [a_add_one, show t + 1 + a t = (t + a t) + 1 by ring, AddCircle.coe_add,
    AddCircle.coe_period, add_zero]

noncomputable def g : UnitAddCircle → UnitAddCircle := gt_periodic.lift

lemma g_coe (t : ℝ) : g (t : UnitAddCircle) = ((t + a t : ℝ) : UnitAddCircle) :=
  gt_periodic.lift_coe t

lemma g_involutive : Function.Involutive g := by
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [g_coe, g_coe, a_add_a, add_assoc]
  by_cases h : Odd (N t)
  · have : a t = 1 / 2 := if_pos h
    rw [this, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, AddCircle.coe_add,
      AddCircle.coe_period, add_zero]
  · have : a t = 0 := if_neg h
    rw [this, add_zero, add_zero]

/-- `N` is locally constant from the right. -/
lemma N_eventually (s : ℝ) : ∀ᶠ t in 𝓝[≥] (0 : ℝ), N (s + t) = N s := by
  set f0 := Int.fract (2 * s) with hf0
  have h0 : 0 ≤ f0 := Int.fract_nonneg _
  have h1 : f0 < 1 := Int.fract_lt_one _
  set k := N s with hk
  have hc : 2 / (1 - f0) < k + 1 := Nat.lt_floor_add_one _
  have hcont : ContinuousAt (fun t : ℝ => 2 / (1 - f0 - 2 * t)) 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp; linarith
  have hlim := hcont.tendsto
  simp only [mul_zero, sub_zero] at hlim
  have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), 2 / (1 - f0 - 2 * t) < k + 1 :=
    hlim.eventually (Iio_mem_nhds hc)
  have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), t < (1 - f0) / 2 := Iio_mem_nhds (by linarith)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
    with t ht1 ht2 ht3
  have ht3 : (0 : ℝ) ≤ t := ht3
  have hfr : Int.fract (2 * (s + t)) = f0 + 2 * t := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊2 * s⌋, ?_⟩
    rw [hf0, Int.fract]; ring
  unfold N
  rw [hfr, Nat.floor_eq_iff (by apply div_nonneg <;> linarith)]
  refine ⟨?_, by rw [show 1 - (f0 + 2 * t) = 1 - f0 - 2 * t by ring]; exact ht1⟩
  calc (k : ℝ) ≤ 2 / (1 - f0) := Nat.floor_le (by apply div_nonneg <;> linarith)
    _ ≤ 2 / (1 - (f0 + 2 * t)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma N_of_mem (t : ℝ) (n : ℕ) (hn : 2 ≤ n) (ht1 : 1 / 2 - 1 / (n : ℝ) ≤ t)
    (ht2 : t < 1 / 2 - 1 / ((n : ℝ) + 1)) : N t = n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
  have ht0 : 0 ≤ t := by linarith
  have h3 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hfr : Int.fract (2 * t) = 2 * t := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
  unfold N
  rw [hfr, Nat.floor_eq_iff (by apply div_nonneg <;> linarith)]
  have hd : 0 < 1 - 2 * t := by linarith
  constructor
  · rw [le_div_iff₀ hd]
    have := mul_le_mul_of_nonneg_left ht1 hpos.le
    field_simp at this ⊢
    nlinarith
  · rw [div_lt_iff₀ hd]
    have hn1 : (0 : ℝ) < n + 1 := by linarith
    have := mul_lt_mul_of_pos_left ht2 hn1
    field_simp at this ⊢
    nlinarith


lemma a_eq_zero_of_even {t : ℝ} (h : ¬ Odd (N t)) : a t = 0 := if_neg h

lemma a_eq_half_of_odd {t : ℝ} (h : Odd (N t)) : a t = 1 / 2 := if_pos h

/-- The discontinuity points `1/2 - 1/(2k+3)`. -/
noncomputable def sk (k : ℕ) : ℝ := 1 / 2 - 1 / (2 * (k : ℝ) + 3)

lemma N_sk (k : ℕ) : N (sk k) = 2 * k + 3 := by
  apply N_of_mem _ _ (by omega)
  · push_cast; unfold sk; rfl
  · push_cast; unfold sk
    have : 1 / (2 * (k : ℝ) + 3 + 1) < 1 / (2 * (k : ℝ) + 3) := by
      apply one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith

lemma left_eventually (k : ℕ) : ∀ᶠ t in 𝓝[<] (sk k), a t = 0 := by
  have hlt : 1 / 2 - 1 / (2 * (k : ℝ) + 2) < sk k := by
    unfold sk
    have : 1 / (2 * (k : ℝ) + 3) < 1 / (2 * (k : ℝ) + 2) := by
      apply one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlt), self_mem_nhdsWithin] with t h1 h2
  have h1 : 1 / 2 - 1 / (2 * (k : ℝ) + 2) < t := h1
  have h2 : t < sk k := h2
  apply a_eq_zero_of_even
  rw [N_of_mem t (2 * k + 2) (by omega) (by push_cast; linarith)
    (by push_cast; unfold sk at h2; rw [show 2 * (k : ℝ) + 2 + 1 = 2 * k + 3 by ring]; exact h2)]
  rw [Nat.not_odd_iff_even]
  exact ⟨k + 1, by ring⟩

lemma not_continuousAt (k : ℕ) : ¬ ContinuousAt g (sk k : UnitAddCircle) := by
  intro hc
  have hq : Tendsto (fun t : ℝ => (t : UnitAddCircle)) (𝓝[<] (sk k)) (𝓝 (sk k : UnitAddCircle)) :=
    (continuous_quotient_mk'.tendsto (sk k)).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => g (t : UnitAddCircle)) (𝓝[<] (sk k))
      (𝓝 (g (sk k : UnitAddCircle))) := hc.tendsto.comp hq
  have h2 : Tendsto (fun t : ℝ => g (t : UnitAddCircle)) (𝓝[<] (sk k))
      (𝓝 (sk k : UnitAddCircle)) := by
    apply hq.congr'
    filter_upwards [left_eventually k] with t ht
    rw [g_coe, ht, add_zero]
  have := tendsto_nhds_unique h1 h2
  rw [g_coe, a_eq_half_of_odd (by rw [N_sk]; exact ⟨k + 1, by ring⟩)] at this
  have hs0 : 0 ≤ sk k := by
    unfold sk
    have : 1 / (2 * (k : ℝ) + 3) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hs1 : sk k < 1 / 2 := by
    unfold sk
    have : 0 < 1 / (2 * (k : ℝ) + 3) := by positivity
    linarith
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := (1 : ℝ))
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩] at this
  linarith

end IETReadingsP1

open IETReadingsP1 Filter Topology in
theorem chk_exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities :
    ∃ g : Equiv.Perm UnitAddCircle,
      IsRightContinuous g ∧ (angles g).Finite ∧ ¬ {x | ¬ ContinuousAt g x}.Finite := by
  refine ⟨g_involutive.toPerm, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [Function.Involutive.coe_toPerm]
    have he : (fun t : ℝ => g ((s : UnitAddCircle) + (t : UnitAddCircle))) =ᶠ[𝓝[≥] (0 : ℝ)]
        fun t : ℝ => (((s + t) + a s : ℝ) : UnitAddCircle) := by
      filter_upwards [N_eventually s] with t ht
      rw [← AddCircle.coe_add, g_coe]
      unfold a; rw [ht]
    have hz : g ((s : UnitAddCircle) + ((0 : ℝ) : UnitAddCircle)) =
        (((s + 0) + a s : ℝ) : UnitAddCircle) := by
      rw [← AddCircle.coe_add, g_coe, add_zero]
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ he hz
    exact (continuous_quotient_mk'.comp (by fun_prop)).continuousWithinAt
  · apply Set.Finite.subset (s := ({0, (((1 : ℝ) / 2 : ℝ) : UnitAddCircle)} : Set UnitAddCircle))
      (Set.toFinite _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [Function.Involutive.coe_toPerm]
    change g (t : UnitAddCircle) - (t : UnitAddCircle) ∈ _
    rw [g_coe, ← AddCircle.coe_sub, add_sub_cancel_left]
    unfold a
    split_ifs
    · simp
    · simp
  · intro hfin
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (sk k : UnitAddCircle)) _ _ hfin
    · intro i j hij
      have hb : ∀ k : ℕ, sk k ∈ Set.Ico (0 : ℝ) (0 + 1) := by
        intro k
        unfold sk
        have : 1 / (2 * (k : ℝ) + 3) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num) (by linarith)
        have : 0 < 1 / (2 * (k : ℝ) + 3) := by positivity
        constructor <;> linarith
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hb i) (hb j)).1 hij
      unfold sk at this
      have : (2 * (i : ℝ) + 3) = 2 * j + 3 := by
        have h := this
        field_simp at h
        linarith
      exact_mod_cast (by linarith : (i : ℝ) = j)
    · intro k
      exact not_continuousAt k

end IntervalExchange


open IntervalExchange in
theorem solution :
    ∃ g : Equiv.Perm UnitAddCircle,
      IsRightContinuous g ∧ (angles g).Finite ∧ ¬ {x | ¬ ContinuousAt g x}.Finite :=
  IntervalExchange.chk_exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities
