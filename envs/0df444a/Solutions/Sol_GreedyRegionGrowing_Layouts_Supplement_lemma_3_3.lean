-- Prove2me | solution 1 for GreedyRegionGrowing.Layouts.Supplement.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:33:40.077667+00:00
-- url     : https://prove2.me/submissions/b4163f3b-ca67-468a-aa79-d254aebcdc65

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity Filter Topology Set
attribute [local instance] Classical.propDecidable

theorem GRG33_base (V c : ℝ → ℝ) (κ x y m q : ℝ) (hκ : 0 ≤ κ) (hx : 0 < x) (hxy : x < y)
    (hVpos : ∀ r, 0 < r → 0 < V r) (hmono : MonotoneOn V (Set.Ioi 0))
    (haff : ∀ r ∈ Set.Ioo x y, V r = m * r + q)
    (hder : ∀ r ∈ Set.Ioo x y, HasDerivAt V (c r) r) (hc0 : ∀ r ∈ Set.Ioo x y, 0 ≤ c r)
    (hbig : ∀ r ∈ Set.Ioo x y, κ * V r < c r) :
    κ * (y - x) ≤ Real.log (V y) - Real.log (V x) := by
  have hcm : ∀ r ∈ Set.Ioo x y, c r = m := by
    intro r hr
    have hL : HasDerivAt (fun s => m * s + q) m r := by
      simpa using ((hasDerivAt_id r).const_mul m).add_const q
    have hev : V =ᶠ[𝓝 r] (fun s => m * s + q) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs using haff s hs
    exact (hder r hr).unique (hL.congr_of_eventuallyEq hev)
  have hmid : (x + y) / 2 ∈ Set.Ioo x y := ⟨by linarith, by linarith⟩
  have hm0 : 0 ≤ m := by rw [← hcm _ hmid]; exact hc0 _ hmid
  set L : ℝ → ℝ := fun s => m * s + q with hLdef
  have hLc : Continuous L := by fun_prop
  have hVxL : V x ≤ L x := by
    refine ge_of_tendsto (hLc.tendsto x |>.mono_left (nhdsWithin_le_nhds (s := Set.Ioi x))) ?_
    filter_upwards [Ioo_mem_nhdsGT hxy] with r hr
    rw [show L r = V r from (haff r hr).symm]
    exact hmono (show (0:ℝ) < x from hx) (show (0:ℝ) < r by linarith [hr.1]) hr.1.le
  have hVyL : L y ≤ V y := by
    refine le_of_tendsto (hLc.tendsto y |>.mono_left (nhdsWithin_le_nhds (s := Set.Iio y))) ?_
    filter_upwards [Ioo_mem_nhdsLT hxy] with r hr
    rw [show L r = V r from (haff r hr).symm]
    exact hmono (show (0:ℝ) < r by linarith [hr.1]) (show (0:ℝ) < y by linarith) hr.2.le
  have hmy : κ * L y ≤ m := by
    refine le_of_tendsto ((hLc.tendsto y).const_mul κ |>.mono_left (nhdsWithin_le_nhds (s := Set.Iio y))) ?_
    filter_upwards [Ioo_mem_nhdsLT hxy] with r hr
    have := hbig r hr
    rw [haff r hr, hcm r hr] at this
    exact this.le
  have hVx := hVpos x hx
  have hLx : 0 < L x := lt_of_lt_of_le hVx hVxL
  have hLxy : L x ≤ L y := by simp only [hLdef]; nlinarith
  have hLy : 0 < L y := lt_of_lt_of_le hLx hLxy
  have hVy : 0 < V y := lt_of_lt_of_le hLy hVyL
  have h1 : Real.log (L y) - Real.log (L x) ≤ Real.log (V y) - Real.log (V x) := by
    have := Real.log_le_log hLy hVyL
    have := Real.log_le_log hVx hVxL
    linarith
  have h2 : 1 - (L y / L x)⁻¹ ≤ Real.log (L y / L x) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hLy hLx)
  rw [Real.log_div hLy.ne' hLx.ne', inv_div] at h2
  have h3 : κ * (y - x) ≤ 1 - L x / L y := by
    rw [show 1 - L x / L y = (L y - L x) / L y by field_simp]
    rw [le_div_iff₀ hLy]
    have : L y - L x = m * (y - x) := by simp only [hLdef]; ring
    rw [this]
    have hyx : 0 ≤ y - x := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hmy hyx]
  linarith

theorem GRG33_ind (V c : ℝ → ℝ) (E : Finset ℝ) (κ a b : ℝ) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hVpos : ∀ r, 0 < r → 0 < V r) (hmono : MonotoneOn V (Set.Ioi 0))
    (hpiece : ∀ x y, 0 < x → x < y → (∀ e ∈ E, e ∉ Set.Ioo x y) →
        ∃ m q : ℝ, ∀ r ∈ Set.Ioo x y, V r = m*r+q)
    (hderiv : ∀ r, 0 < r → r ∉ E → 0 ≤ c r ∧ HasDerivAt V (c r) r)
    (hbig : ∀ r ∈ Set.Ioo a b, r ∉ E → κ * V r < c r) :
    ∀ n : ℕ, ∀ x y, a ≤ x → x < y → y ≤ b →
      (E.filter (fun e => e ∈ Set.Ioo x y)).card = n →
      κ * (y - x) ≤ Real.log (V y) - Real.log (V x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hax hxy hyb hcard
  by_cases hE : ∃ e ∈ E, e ∈ Set.Ioo x y
  · obtain ⟨e, heE, hexy⟩ := hE
    have hlt1 : (E.filter (fun e' => e' ∈ Set.Ioo x e)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨e, Finset.mem_filter.mpr ⟨heE, hexy⟩, ?_⟩
        intro h; exact lt_irrefl e (Finset.mem_filter.mp h).2.2
      · intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2.1, lt_trans hz.2.2 hexy.2⟩
    have hlt2 : (E.filter (fun e' => e' ∈ Set.Ioo e y)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨e, Finset.mem_filter.mpr ⟨heE, hexy⟩, ?_⟩
        intro h; exact lt_irrefl e (Finset.mem_filter.mp h).2.1
      · intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, lt_trans hexy.1 hz.2.1, hz.2.2⟩
    have h1 := ih _ hlt1 x e hax hexy.1 (by linarith [hexy.2]) rfl
    have h2 := ih _ hlt2 e y (by linarith [hexy.1]) hexy.2 hyb rfl
    linarith
  · push Not at hE
    obtain ⟨m, q, hmq⟩ := hpiece x y (by linarith) hxy hE
    have hrE : ∀ r ∈ Set.Ioo x y, r ∉ E := fun r hr hrE => hE r hrE hr
    apply GRG33_base V c κ x y m q hκ (by linarith) hxy hVpos hmono hmq
    · intro r hr; exact (hderiv r (by linarith [hr.1]) (hrE r hr)).2
    · intro r hr; exact (hderiv r (by linarith [hr.1]) (hrE r hr)).1
    · intro r hr
      exact hbig r ⟨by linarith [hr.1], by linarith [hr.2]⟩ (hrE r hr)

theorem solution (V c : ℝ → ℝ) (E : Finset ℝ) (a b : ℝ)
    (hV : (∀ r, 0 < r → 0 < V r) ∧
      MonotoneOn V (Set.Ioi 0) ∧
      (∀ x y, 0 < x → x < y → (∀ e ∈ E, e ∉ Set.Ioo x y) →
        ∃ m q : ℝ, ∀ r ∈ Set.Ioo x y, V r = m*r+q) ∧
      (∀ r, 0 < r → r ∉ E → 0 ≤ c r ∧ HasDerivAt V (c r) r))
    (ha : 0 < a) (hab : a < b) :
  ∃ r ∈ Set.Ioo a b, r ∉ E ∧
    c r ≤ (Int.ceil (Real.logb 2 (2*V b/V a)) : ℝ)/(b-a)*V r := by
  obtain ⟨hVpos, hmono, hpiece, hderiv⟩ := hV
  set K : ℝ := (Int.ceil (Real.logb 2 (2*V b/V a)) : ℝ) with hK
  have hVa := hVpos a ha
  have hVb := hVpos b (by linarith)
  have hVab : V a ≤ V b := hmono (show (0:ℝ) < a from ha) (show (0:ℝ) < b by linarith) hab.le
  have hz : 2 ≤ 2 * V b / V a := by rw [le_div_iff₀ hVa]; linarith
  have hlog1 : 1 ≤ Real.logb 2 (2 * V b / V a) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hz
  have hKge : Real.logb 2 (2 * V b / V a) ≤ K := Int.le_ceil _
  have hK0 : 0 ≤ K := by linarith
  have hba : 0 < b - a := by linarith
  set κ := K / (b - a) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg hK0 hba.le
  by_contra hcon
  push Not at hcon
  have hbig : ∀ r ∈ Set.Ioo a b, r ∉ E → κ * V r < c r := fun r hr hrE => hcon r hr hrE
  have hmain := GRG33_ind V c E κ a b hκ0 ha hVpos hmono hpiece hderiv hbig _ a b le_rfl hab le_rfl rfl
  have hκK : κ * (b - a) = K := by rw [hκ]; field_simp
  rw [hκK] at hmain
  -- V b / V a ≥ exp K ≥ 2^K ≥ 2 V b / V a
  have hexp : Real.exp K ≤ V b / V a := by
    rw [← Real.exp_log (div_pos hVb hVa), Real.exp_le_exp, Real.log_div hVb.ne' hVa.ne']
    exact hmain
  have h2K : (2:ℝ) ^ K ≤ Real.exp K := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  have hzK : 2 * V b / V a ≤ (2:ℝ) ^ K := by
    calc 2 * V b / V a = (2:ℝ) ^ (Real.logb 2 (2 * V b / V a)) := by
          rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
      _ ≤ (2:ℝ) ^ K := Real.rpow_le_rpow_of_exponent_le (by norm_num) hKge
  have : 2 * V b / V a ≤ V b / V a := le_trans hzK (le_trans h2K hexp)
  have hpos : 0 < V b / V a := div_pos hVb hVa
  have : 2 * V b / V a = 2 * (V b / V a) := by ring
  linarith
