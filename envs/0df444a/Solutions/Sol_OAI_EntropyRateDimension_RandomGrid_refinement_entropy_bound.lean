-- Prove2me | solution 1 for OAI.EntropyRateDimension.RandomGrid.refinement_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:43:43.329208+00:00
-- url     : https://prove2.me/submissions/67cd9c41-2097-4a4b-ac85-d4e68714ebbe

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean:L127-L234
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.RandomGrid.refinement_entropy_bound. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_binEntropy_bits_le_three_sqrt
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_rare_flag
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_event_union_bound
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_no_large_coordinate
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_two_exceptions_bound
import Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_circle_norm_le_of_floor_ne

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem cell_change_margin {δ x m : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (h : cell δ u x ≠ cell δ u m) :
    δ * dist u (-(m / δ : ℝ) : AddCircle (1 : ℝ)) ≤ |x - m| := by
  have hn := circle_norm_le_of_floor_ne (Ne.symm h)
  have he : ((m / δ + shift u : ℝ) : AddCircle (1 : ℝ)) =
      u + (m / δ : ℝ) := by
    rw [AddCircle.coe_add]
    simp only [shift, AddCircle.coe_equivIco, add_comm]
  change ‖((m / δ + shift u : ℝ) : AddCircle (1 : ℝ))‖ ≤ _ at hn
  rw [he] at hn
  have habs : |x / δ + shift u - (m / δ + shift u)| = |x - m| / δ := by
    rw [show x / δ + shift u - (m / δ + shift u) = (x - m) / δ by ring,
      abs_div, abs_of_pos hδ]
  rw [habs] at hn
  rw [dist_eq_norm, sub_neg_eq_add]
  simpa only [mul_comm] using (le_div_iff₀ hδ).mp hn

theorem cell_mem_interval {δ x m : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (hx : |x-m| ≤ 4*δ) :
    cell δ u x ∈ Finset.Icc (cell δ u m - 5) (cell δ u m + 5) := by
  apply Finset.mem_Icc.mpr
  have hxm := (abs_le.mp hx)
  have hdiv : |x/δ + shift u - (m/δ + shift u)| ≤ 4 := by
    rw [show x/δ + shift u - (m/δ + shift u) = (x-m)/δ by ring,
      abs_div, abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hx
  have hx1 := Int.floor_le (x/δ+shift u)
  have hx2 := Int.lt_floor_add_one (x/δ+shift u)
  have hm1 := Int.floor_le (m/δ+shift u)
  have hm2 := Int.lt_floor_add_one (m/δ+shift u)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hdiv
  constructor <;> unfold cell
  · have : (⌊m/δ+shift u⌋ : ℝ) - 5 ≤ (⌊x/δ+shift u⌋ : ℝ) := by linarith
    exact_mod_cast this
  · have : (⌊x/δ+shift u⌋ : ℝ) ≤ (⌊m/δ+shift u⌋ : ℝ) + 5 := by linarith
    exact_mod_cast this

theorem grid_alphabet_bound {α : Type uα} (s : Finset α) (k : ℕ)
    (v : α → Fin k → ℝ) (m : Fin k → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (u : AddCircle (1 : ℝ)) (hs : s.Nonempty)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ) :
    Real.log (s.image (fun x i => cell δ u (v x i))).card ≤
      4*k*Real.log 2 := by
  classical
  let T := Fintype.piFinset (fun i : Fin k => Finset.Icc (cell δ u (m i)-5) (cell δ u (m i)+5))
  have hcard : (s.image (fun x i => cell δ u (v x i))).card ≤ 11^k := by
    calc
      _ ≤ T.card := Finset.card_le_card (by
        intro f hf
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
        apply Fintype.mem_piFinset.mpr
        intro i
        exact cell_mem_interval hδ u (hv x hx i))
      _ = 11^k := by
        simp only [T, Fintype.card_piFinset, Int.card_Icc]
        simp [show ∀ n : ℤ, n + 5 + 1 - (n-5) = 11 by intro n; ring]
  have hcpos : (0 : ℝ) < (s.image (fun x i => cell δ u (v x i))).card := by
    exact_mod_cast Finset.card_pos.mpr (hs.image _)
  have hb : Real.log (s.image (fun x i => cell δ u (v x i))).card ≤ Real.log ((16 : ℝ)^k) := by
    apply Real.log_le_log hcpos
    have he : (s.image (fun x i => cell δ u (v x i))).card ≤ 16^k :=
      hcard.trans (Nat.pow_le_pow_left (by norm_num) k)
    exact_mod_cast he
  calc
    _ ≤ _ := hb
    _ = 4*k*Real.log 2 := by
      rw [Real.log_pow, show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
      ring

theorem refinement_entropy_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (v : α → Fin k → ℝ) (m : Fin k → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (u : AddCircle (1 : ℝ)) (a : ℝ)
    (hmargin : ∀ i, a ≤ δ * dist u (-(m i/δ : ℝ) : AddCircle (1 : ℝ)))
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ)
    (hind : ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| ∧ a/(4*k) ≤ |v x j-m j| then p x else 0) =
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0) *
      (∑ x ∈ s, if a/(4*k) ≤ |v x j-m j| then p x else 0)) :
    FiniteEntropy.conditionalEntropy s p (fun x i => cell δ u (v x i)) (fun x => ∑ i, v x i) ≤
      11*k*(∑ i, ∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0)*Real.log 2 := by
  classical
  let Ex := fun (i : Fin k) x => a/(4*k) ≤ |v x i-m i|
  let E : α → Bool := fun x => decide (∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x)
  let B : ℝ → Prop := fun y => a/2 ≤ |y-∑ i, m i|
  let Y := fun x => ∑ i, v x i
  let C := fun x i => cell δ u (v x i)
  let t := ∑ i, ∑ x ∈ s, if Ex i x then p x else 0
  let q := ∑ x ∈ s, if ∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x then p x else 0
  let b := ∑ x ∈ s, if B (Y x) then p x else 0
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hq : 0 ≤ q := by
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hb : 0 ≤ b := by
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hq1 : q ≤ 1 := by
    rw [← hp1]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs <;> first | exact le_rfl | exact hp x hx
  have htq : q ≤ t^2 ∧ q ≤ t := by
    convert FiniteEntropy.two_exceptions_bound s p Ex hp hind using 2 <;>
      apply Finset.sum_congr rfl <;> intro x hx <;> split_ifs <;> rfl
  have hbt : b ≤ t := by
    apply le_trans _ (FiniteEntropy.event_union_bound s p Ex hp)
    apply Finset.sum_le_sum
    intro x hx
    by_cases hbx : B (Y x)
    · rw [ite_eq_left hbx]
      have he : ∃ i, Ex i x := by
        by_contra hn
        have hi : ∀ i, |v x i-m i| < a/(4*k) := by
          intro i
          exact lt_of_not_ge (fun h => hn ⟨i,h⟩)
        have ha : 0 < a := by
          have h := (abs_nonneg (v x ⟨0,by omega⟩-m ⟨0,by omega⟩)).trans_lt (hi ⟨0,by omega⟩)
          exact (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4*k)).mp h
        have hh : |∑ i, (v x i-m i)| ≤ a/4 := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          calc
            (∑ i, |v x i-m i|) ≤ ∑ _i : Fin k, a/(4*k) :=
              Finset.sum_le_sum (fun i _ => (hi i).le)
            _ = a/4 := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
        dsimp only [B,Y] at hbx
        rw [Finset.sum_sub_distrib] at hh
        linarith
      rw [ite_eq_left he]
    · rw [ite_eq_right hbx]
      split_ifs <;> first | exact hp x hx | exact le_rfl
  have hflag := FiniteEntropy.conditionalEntropy_rare_flag s p C Y E B
    (fun i => cell δ u (m i)) hp hp1 ?_
  · have heq : FiniteEntropy.mass s p E true = q := by
      simp only [FiniteEntropy.mass, Finset.sum_filter, E, decide_eq_true_eq, q]
    have hbeq : (∑ x ∈ s.filter (fun x => B (Y x)), p x) = b := by
      simp only [Finset.sum_filter, b]
    rw [heq, hbeq] at hflag
    have hs : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hp1
      norm_num at hp1
    have hcard := grid_alphabet_bound s k v m hδ u hs hv
    have hm := mul_le_mul_of_nonneg_left hcard (add_nonneg hq hb)
    have hsqrt : Real.sqrt q ≤ t := (Real.sqrt_le_left ht).mpr htq.1
    have hbin : Real.binEntropy q ≤ 3*t*Real.log 2 := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
      exact (FiniteEntropy.binEntropy_bits_le_three_sqrt hq hq1).trans (by linarith)
    have hqb : q+b ≤ 2*t := by linarith [htq.2]
    have hqb' := mul_le_mul_of_nonneg_right hqb
      (by positivity : 0 ≤ 4*(k : ℝ)*Real.log 2)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlast := mul_nonneg (sub_nonneg.mpr hk1) (mul_nonneg ht (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    change FiniteEntropy.conditionalEntropy s p C Y ≤ 11*k*t*Real.log 2
    nlinarith
  · intro x hx hEx hBx
    have hm : |∑ i, (v x i-m i)| < a/2 := by
      simpa only [Finset.sum_sub_distrib] using lt_of_not_ge hBx
    have ha : 0 < a := by linarith [abs_nonneg (∑ i, (v x i-m i))]
    have hn : ¬∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x := by
      simpa only [E, decide_eq_false_iff_not] using hEx
    funext i
    by_contra hne
    have hfar := hmargin i |>.trans (cell_change_margin hδ u hne)
    have hnear := FiniteEntropy.no_large_coordinate (fun i => v x i-m i) ha
      (by simpa only [Fintype.card_fin] using hn) hm i
    linarith

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.RandomGrid.refinement_entropy_bound.{uα} := @_root_.OAI.EntropyRateDimension.RandomGrid.refinement_entropy_bound.{uα}
