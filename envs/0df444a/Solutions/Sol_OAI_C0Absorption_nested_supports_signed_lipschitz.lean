-- Prove2me | solution 1 for OAI.C0Absorption.nested_supports_signed_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:28:22.204259+00:00
-- url     : https://prove2.me/submissions/a574c9b3-ce8c-4910-a50a-88403daa1762

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology
theorem h41_lip_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  by_cases hne : IsEmpty B
  · exact LipschitzWith.of_dist_le_mul (fun x _ => (hne.false x).elim)
  rw [not_isEmpty_iff] at hne
  obtain ⟨b⟩ := hne
  let F : E → Y := fun x => if h : x ∈ B then f ⟨x, h⟩ else f b
  have hres : B.restrict F = f := by
    funext x; simp [F, Set.restrict, x.2]
  have hFc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_restrict]; change Continuous (B.restrict F); rw [hres]; exact hf
  have hFl : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (F x) (F y) ≤ K * dist x y := by
    intro x hx
    rw [← map_nhds_subtype_val ⟨x, hx⟩, Filter.eventually_map]
    filter_upwards [hloc ⟨x, hx⟩] with y hy
    simpa [F, hx, y.2, Subtype.dist_eq] using hy
  have : LipschitzWith K (B.restrict F) := (lipschitzOn_convex_of_local hB hFc hFl).to_restrict
  rwa [hres] at this

theorem solution {E : Type*}
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
  have hcont : Continuous (fun x => ∑ i, ε i * (u i x * b i x)) := by
    have := fun i => (hF i).continuous
    fun_prop
  apply h41_lip_local hB hcont
  intro x
  let P : Fin n → Prop := fun i => x ∈ tsupport (u i)
  let N : Set B := (⋂ i ∈ Finset.univ.filter (fun i => ∃ j, i < j ∧ P j), C i) ∩
    ⋂ i ∈ Finset.univ.filter (fun i => ¬ P i), (tsupport (u i))ᶜ
  have hNo : IsOpen N := (isOpen_biInter_finset (fun i _ => hC i)).inter
    (isOpen_biInter_finset (fun i _ => (isClosed_tsupport _).isOpen_compl))
  have hxN : x ∈ N := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_iInter, Finset.mem_filter]
      rintro i ⟨-, j, hij, hj⟩
      exact hnest i j hij hj
    · simp only [Set.mem_iInter, Finset.mem_filter]
      rintro i ⟨-, hi⟩; exact hi
  filter_upwards [hNo.mem_nhds hxN] with y hy
  set T := Finset.univ.filter (fun i => P i ∧ ¬ ∃ j, i < j ∧ P j)
  have hT : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [T, Finset.mem_filter] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hi.2.2 ⟨j, h, hj.2.1⟩
    · exact hj.2.2 ⟨i, h, hi.2.1⟩
  have hterm : ∀ i, |ε i * (u i x * b i x) - ε i * (u i y * b i y)| ≤
      ‖e i‖ * Kb i * dist x y + (if i ∈ T then (K:ℝ) * dist x y else 0) := by
    intro i
    rw [← mul_sub, abs_mul, hε i, one_mul]
    have hd : 0 ≤ ‖e i‖ * Kb i * dist x y := by positivity
    by_cases h1 : ∃ j, i < j ∧ P j
    · have hxC : x ∈ C i := by obtain ⟨j, hij, hj⟩ := h1; exact hnest i j hij hj
      have hyC : y ∈ C i := by
        have := hy.1; simp only [Set.mem_iInter, Finset.mem_filter] at this
        exact this i ⟨Finset.mem_univ _, h1⟩
      rw [hc i x hxC, hc i y hyC, ← mul_sub, abs_mul, ← Real.dist_eq, Real.norm_eq_abs, mul_assoc]
      have := (hb i).dist_le_mul x y
      have hT' : i ∉ T := by simp [T, h1]
      rw [if_neg hT', add_zero]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    · by_cases h2 : P i
      · have hT' : i ∈ T := by simp only [T, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h2, h1⟩
        rw [if_pos hT', ← Real.dist_eq]
        have := (hF i).dist_le_mul x y
        linarith
      · have hyi : y ∉ tsupport (u i) := by
          have := hy.2; simp only [Set.mem_iInter, Finset.mem_filter] at this
          exact this i ⟨Finset.mem_univ _, h2⟩
        rw [image_eq_zero_of_notMem_tsupport h2, image_eq_zero_of_notMem_tsupport hyi]
        simp only [zero_mul, sub_self, abs_zero]
        split_ifs <;> positivity
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ i, (ε i * (u i x * b i x) - ε i * (u i y * b i y))|
      ≤ ∑ i, |ε i * (u i x * b i x) - ε i * (u i y * b i y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (‖e i‖ * Kb i * dist x y + (if i ∈ T then (K:ℝ) * dist x y else 0)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, ‖e i‖ * Kb i) * dist x y + T.card * ((K:ℝ) * dist x y) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ i, ‖e i‖ * Kb i) * dist x y + 1 * ((K:ℝ) * dist x y) := by
        gcongr; exact_mod_cast hT
    _ = ((K + ∑ i, ‖e i‖₊ * Kb i : ℝ≥0) : ℝ) * dist x y := by
        push_cast; ring

