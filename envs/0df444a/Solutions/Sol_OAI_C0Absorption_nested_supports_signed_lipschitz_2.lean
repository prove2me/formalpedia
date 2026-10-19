-- Prove2me | solution 2 for OAI.C0Absorption.nested_supports_signed_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:49:45.340235+00:00
-- url     : https://prove2.me/submissions/6f08ae69-bed8-4614-85cb-b37dad6d1ee7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean:L145-L217
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.nested_supports_signed_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Theorems.Thm_OAI_C0Absorption_lipschitz_convex_subtype_of_local

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem eventually_zero_of_not_tsupport {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) : ∀ᶠ y in nhds x, f y = 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

theorem nested_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    (n : ℕ) (u b : Fin n → B → ℝ) (e : Fin n → ℝ)
    (C : Fin n → Set B) (K : ℝ≥0) (Kb : Fin n → ℝ≥0)
    (_hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith (Kb i) (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x * b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x = e i)
    (hnest : ∀ i j, i < j → tsupport (u j) ⊆ C i)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith (K + ∑ i, ‖e i‖₊ * Kb i)
      (fun x => ∑ i, ε i * (u i x * b i x)) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hF i).continuous)
  intro x
  let H : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ tsupport (u i))
  by_cases hH : H.Nonempty
  · let j := H.max' hH
    have hj : x ∈ tsupport (u j) := (Finset.mem_filter.mp (H.max'_mem hH)).2
    have he (i) (hij : i < j) : ∀ᶠ y in nhds x, u i y = e i := by
      filter_upwards [(hC i).mem_nhds (hnest i j hij hj)] with y hy
      exact hc i y hy
    have hz (i) (hji : j < i) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      have hiH : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact (not_lt_of_ge (H.le_max' i hiH)) hji
    have hall : ∀ᶠ y in nhds x, ∀ i,
        (i < j → u i y = e i) ∧ (j < i → u i y = 0) := by
      apply Filter.eventually_all.mpr
      intro i
      rcases lt_trichotomy i j with hij | rfl | hji
      · filter_upwards [he i hij] with y hy
        exact ⟨fun _ => hy, fun h => (not_lt_of_ge hij.le h).elim⟩
      · exact Filter.Eventually.of_forall (by simp)
      · filter_upwards [hz i hji] with y hy
        exact ⟨fun h => (not_lt_of_ge hji.le h).elim, fun _ => hy⟩
    filter_upwards [hall] with y hy
    have hi (i : Fin n) :
        dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) ≤
          ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hx := (he i hij).self_of_nhds
        rw [hx, (hy i).1 hij, ite_eq_right (ne_of_lt hij), zero_add,
          Real.dist_eq, ← mul_sub, ← mul_sub, abs_mul, abs_mul, hε i, one_mul]
        calc
          |e i| * |b i x - b i y| ≤ |e i| * (Kb i * dist x y) := by
            apply mul_le_mul_of_nonneg_left ((hb i).dist_le_mul x y) (abs_nonneg _)
          _ = |e i| * Kb i * dist x y := by ring
      · rw [ite_eq_left rfl, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul,
          ← Real.dist_eq]
        exact ((hF j).dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (dist_nonneg))
      · rw [(hz i hji).self_of_nhds, (hy i).2 hji]
        simp only [zero_mul, mul_zero, dist_self]
        positivity
    calc
      dist (∑ i, ε i * (u i x * b i x)) (∑ i, ε i * (u i y * b i y))
          ≤ ∑ i, dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) :=
        dist_sum_sum_le _ _ _
      _ ≤ ∑ i, ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = (K + ∑ i, ‖e i‖₊ * Kb i : ℝ≥0) * dist x y := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp [Real.norm_eq_abs]
  · have hz (i : Fin n) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      exact hH ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    have hx (i : Fin n) : u i x = 0 := (hz i).self_of_nhds
    simp only [hx, hy, zero_mul, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

noncomputable section

end

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.nested_supports_signed_lipschitz := @_root_.OAI.C0Absorption.nested_supports_signed_lipschitz
