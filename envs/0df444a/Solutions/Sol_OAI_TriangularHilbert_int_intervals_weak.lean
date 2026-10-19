-- Prove2me | solution 1 for OAI.TriangularHilbert.int_intervals_weak
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:02:06.459344+00:00
-- url     : https://prove2.me/submissions/6483716b-1529-427e-83da-52abd2d957cf

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak

open OAI OAI.TriangularHilbert
open scoped BigOperators
theorem h43_sel {κ : Type*} {X : Type*} (s : Finset κ) (B : κ → Set X)
  (δ : κ → ℝ) (hne : ∀ a ∈ s, (B a).Nonempty) :
  ∃ u : Finset κ, u ⊆ s ∧
    (∀ a ∈ u, ∀ b ∈ u, a ≠ b → Disjoint (B a) (B b)) ∧
    ∀ a ∈ s, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ δ b := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨∅, by simp, by simp, by simp [hs]⟩
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image δ hs
    set s' := s.filter (fun b => Disjoint (B a) (B b)) with hs'
    have haB := hne a ha
    have hsub : s' ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : a ∈ s' := heq ▸ ha
      rw [Finset.mem_filter] at this
      obtain ⟨x, hx⟩ := haB
      exact Set.disjoint_left.mp this.2 hx hx
    obtain ⟨u', hu's, hu'd, hu'c⟩ := ih s' hsub (fun b hb => hne b (Finset.filter_subset _ _ hb))
    have hau' : a ∉ u' := by
      intro h
      have := Finset.mem_filter.mp (hu's h)
      obtain ⟨x, hx⟩ := haB
      exact Set.disjoint_left.mp this.2 hx hx
    refine ⟨insert a u', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact Finset.filter_subset _ _ (hu's hx)
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxa | hxu <;> rcases Finset.mem_insert.mp hy with hya | hyu
      · exact absurd (hxa.trans hya.symm) hxy
      · subst hxa; exact (Finset.mem_filter.mp (hu's hyu)).2
      · subst hya; exact (Finset.mem_filter.mp (hu's hxu)).2.symm
      · exact hu'd x hxu y hyu hxy
    · intro c hc
      by_cases hd : Disjoint (B a) (B c)
      · obtain ⟨b, hb, h1, h2⟩ := hu'c c (Finset.mem_filter.mpr ⟨hc, hd⟩)
        exact ⟨b, Finset.mem_insert_of_mem hb, h1, h2⟩
      · refine ⟨a, Finset.mem_insert_self _ _, ?_, hmax c hc⟩
        rw [Set.not_disjoint_iff_nonempty_inter] at hd
        rwa [Set.inter_comm]

theorem solution (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (r : ℤ → ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ∀ n ∈ s, ρ * (2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    ρ * (s.card:ℝ) ≤ 3 * ∑ m ∈ D, f m := by
  classical
  obtain ⟨u, hus, hud, huc⟩ := h43_sel s (fun n => ((intInterval n (r n) : Finset ℤ) : Set ℤ))
    (fun n => (r n : ℝ)) (fun a _ => ⟨a, by simp [intInterval]⟩)
  have hcov : s ⊆ u.biUnion (fun b => intInterval b (2 * r b)) := by
    intro a ha
    obtain ⟨b, hb, ⟨x, hx1, hx2⟩, hab⟩ := huc a ha
    have hab' : r a ≤ r b := by exact_mod_cast hab
    simp only [Finset.coe_Icc, intInterval, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hx1 hx2
    rw [Finset.mem_biUnion]
    refine ⟨b, hb, ?_⟩
    simp only [intInterval, Finset.mem_Icc]; push_cast; omega
  have hcard : (s.card : ℝ) ≤ ∑ b ∈ u, (4 * (r b : ℝ) + 1) := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_biUnion_le (s := u) (t := fun b => intInterval b (2 * r b))
    have h3 : ∀ b ∈ u, (intInterval b (2 * r b)).card = 4 * r b + 1 := by
      intro b _; simp only [intInterval, Int.card_Icc]; omega
    rw [Finset.sum_congr rfl h3] at h2
    have := h1.trans h2
    have h4 : ((s.card : ℕ) : ℝ) ≤ ((∑ b ∈ u, (4 * r b + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h4; exact h4
  have hdisj : (u : Set ℤ).PairwiseDisjoint (fun b => D ∩ intInterval b (r b)) := by
    intro a ha b hb hab
    have := hud a ha b hb hab
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro x hx y hy hxy; subst hxy
    exact Set.disjoint_left.mp this (Finset.mem_coe.mpr (Finset.mem_inter.mp hx).2) (Finset.mem_coe.mpr (Finset.mem_inter.mp hy).2)
  calc ρ * (s.card : ℝ) ≤ ρ * ∑ b ∈ u, (4 * (r b : ℝ) + 1) := mul_le_mul_of_nonneg_left hcard hρ
    _ ≤ ∑ b ∈ u, 3 * (ρ * (2 * (r b : ℝ) + 1)) := by
        rw [Finset.mul_sum]; refine Finset.sum_le_sum fun b _ => ?_
        have : (0:ℝ) ≤ r b := by positivity
        nlinarith
    _ ≤ ∑ b ∈ u, 3 * ∑ m ∈ D ∩ intInterval b (r b), f m := by
        refine Finset.sum_le_sum fun b hb => ?_
        exact mul_le_mul_of_nonneg_left (hav b (hus hb)) (by norm_num)
    _ = 3 * ∑ m ∈ u.biUnion (fun b => D ∩ intInterval b (r b)), f m := by
        rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ 3 * ∑ m ∈ D, f m := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m hm _ => hf m hm)
        intro m hm; rw [Finset.mem_biUnion] at hm; obtain ⟨b, -, hb⟩ := hm; exact (Finset.mem_inter.mp hb).1

