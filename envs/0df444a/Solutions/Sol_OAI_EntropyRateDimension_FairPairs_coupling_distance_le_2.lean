-- Prove2me | solution 2 for OAI.EntropyRateDimension.FairPairs.coupling_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:29:35.021322+00:00
-- url     : https://prove2.me/submissions/3fe937f7-9193-4ae4-88a4-c920d6ca64f5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean:L336-L391
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FairPairs.coupling_distance_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem total_le_capacity {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ capacity ν ℓ :=
  le_csSup (totals_bddAbove ν ℓ) ⟨w, hw, rfl⟩

theorem sum_first_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.1 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (x, y) then q x y else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem sum_second_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.2 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (y, x) then q y x else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem coupling_incident {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    {x : ℝ} (hx : x ∈ ν.support) :
    incident (ν := ν) (ℓ := ℓ) (fun e => 2 * π e.val.1 e.val.2) x =
      ∑ y ∈ ν.support, if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧
        |y - x| < (2 : ℝ) ^ (1 - ℓ) then π x y else 0 := by
  classical
  simp only [incident, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Finset.sum_coe_sort (ν.edges ℓ) (fun e : ℝ × ℝ =>
    (if e.1 = x then π e.1 e.2 else 0) + (if e.2 = x then π e.1 e.2 else 0)),
    Finset.sum_add_distrib]
  unfold Law.edges
  rw [sum_first_endpoint _ _ _ hx, sum_second_endpoint _ _ _ hx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← hsym x hx y hy]
  rcases lt_trichotomy x y with h | h | h
  · have hxy : ¬y < x := not_lt.mpr h.le
    simp [h, hxy, abs_of_pos (sub_pos.mpr h)]
  · subst y
    have hp : 0 < (2 : ℝ) ^ (-ℓ) := zpow_pos (by norm_num) _
    simp only [lt_self_iff_false, false_and, ite_false, sub_self, abs_zero, not_le.mpr hp, add_zero]
  · have hxy : ¬x < y := not_lt.mpr h.le
    have habs : |y - x| = x - y := by rw [abs_of_neg (sub_neg.mpr h)]; ring
    simp [h, hxy, habs]

theorem coupling_band_le_capacity {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support,
      if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
      then π x y else 0) ≤ capacity ν ℓ := by
  classical
  let w : ν.edges ℓ → ℝ := fun e => 2 * π e.val.1 e.val.2
  have hw : Feasible w := by
    constructor
    · intro e
      exact mul_nonneg (by norm_num) (hπ _ (edge_mem_left e) _ (edge_mem_right e))
    · intro x hx
      rw [coupling_incident ℓ π hsym hx]
      apply le_trans _ (hrow x hx)
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · exact le_rfl
      · exact hπ x hx y hy
  calc
    _ = ∑ x ∈ ν.support, incident w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (coupling_incident ℓ π hsym hx).symm
    _ = ∑ e, w e := incident_sum w
    _ ≤ capacity ν ℓ := total_le_capacity hw

theorem mem_bandIndex {u : ℝ} (hu : 0 < u) :
    (2 : ℝ) ^ (-bandIndex u) ≤ u ∧ u < (2 : ℝ) ^ (1 - bandIndex u) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  constructor
  · rw [← Real.rpow_intCast]
    apply (Real.le_logb_iff_rpow_le hb hu).mp
    simpa only [bandIndex, neg_neg] using Int.floor_le (Real.logb 2 u)
  · rw [← Real.rpow_intCast]
    apply (Real.logb_lt_iff_lt_rpow hb hu).mp
    simpa only [bandIndex, sub_neg_eq_add, Int.cast_add, Int.cast_one, add_comm] using
      Int.lt_floor_add_one (Real.logb 2 u)

theorem coupling_distance_le {ν : Law} (π : ℝ → ℝ → ℝ) (R : ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x)
    (hdiam : ∀ x ∈ ν.support, ∀ y ∈ ν.support, R < |y - x| → π x y = 0) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support, π x y * |y - x|) ≤
      ∑ ℓ ∈ ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
        (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R), (2 : ℝ) ^ (1 - ℓ) * capacity ν ℓ := by
  classical
  let B := ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
    (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R)
  let cost := fun (ℓ : ℤ) (x y : ℝ) =>
    if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
    then π x y else 0
  have hcost : ∀ ℓ x y, x ∈ ν.support → y ∈ ν.support → 0 ≤ cost ℓ x y := by
    intro ℓ x y hx hy
    dsimp [cost]
    split_ifs <;> first | exact hπ x hx y hy | exact le_rfl
  calc
    _ ≤ ∑ x ∈ ν.support, ∑ y ∈ ν.support,
        ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) * cost ℓ x y := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hd : |y - x| = 0
      · rw [hd, mul_zero]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      by_cases hR : R < |y - x|
      · rw [hdiam x hx y hy hR, zero_mul]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      have hu : 0 < |y - x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
      have hb := mem_bandIndex hu
      have hm : bandIndex |y - x| ∈ B := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩,
          hb.1.trans (le_of_not_gt hR)⟩
      apply le_trans _ (Finset.single_le_sum (fun ℓ _ =>
        mul_nonneg (zpow_pos (by norm_num) _).le (hcost ℓ x y hx hy)) hm)
      dsimp only [cost]
      rw [ite_eq_left hb]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.2.le (hπ x hx y hy)
    _ = ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) *
        ∑ x ∈ ν.support, ∑ y ∈ ν.support, cost ℓ x y := by
      conv_lhs =>
        arg 2
        intro x
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ℓ _
      apply mul_le_mul_of_nonneg_left (coupling_band_le_capacity ℓ π hπ hsym hrow)
      exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le

end FairPairs

end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.FairPairs.coupling_distance_le := @_root_.OAI.EntropyRateDimension.FairPairs.coupling_distance_le
