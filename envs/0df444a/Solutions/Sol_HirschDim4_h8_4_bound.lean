-- Prove2me | solution 1 for HirschDim4.h8_4_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:02:45.517912+00:00
-- url     : https://prove2.me/submissions/74efdfba-2b1b-460d-a0e0-77ab9f76f3f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting
import Theorems.Thm_LefebvreVariations_dim4_spindle_eight_facets
import Theorems.Thm_LefebvreVariations_dim4_common_facet_eight_facets

set_option autoImplicit false

open scoped RealInnerProductSpace
open Hirsch Filter Topology

variable {d n : ℕ}


private noncomputable def tset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

private lemma mem_tset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : i ∈ tset a b x ↔ ⟪a i, x⟫ = b i := by
  classical
  unfold tset; simp

private lemma perturb (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) {z : EuclideanSpace ℝ (Fin d)}
    (hz : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, z⟫ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ x + ε • z ∈ Hpoly a b ∧ x - ε • z ∈ Hpoly a b := by
  have key : ∀ i, ∀ᶠ ε in 𝓝 (0:ℝ), ⟪a i, x + ε • z⟫ ≤ b i ∧ ⟪a i, x - ε • z⟫ ≤ b i := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine Eventually.of_forall fun ε => ?_
      simp [inner_add_right, inner_sub_right, inner_smul_right, hz i hi, hi]
    · have hlt : ⟪a i, x⟫ < b i := lt_of_le_of_ne (hx i) hi
      have c1 : Continuous (fun ε : ℝ => ⟪a i, x + ε • z⟫) := by fun_prop
      have c2 : Continuous (fun ε : ℝ => ⟪a i, x - ε • z⟫) := by fun_prop
      have t1 := c1.tendsto 0
      have t2 := c2.tendsto 0
      simp only [zero_smul, add_zero, sub_zero] at t1 t2
      exact (t1.eventually (Iio_mem_nhds hlt)).and (t2.eventually (Iio_mem_nhds hlt)) |>.mono
        fun ε h => ⟨le_of_lt h.1, le_of_lt h.2⟩
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 key)
  have hd : dist (δ / 2) (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  exact ⟨δ / 2, by positivity, fun i => (h hd i).1, fun i => (h hd i).2⟩

/-- A nonzero vector orthogonal to a family of fewer than `d` vectors. -/
private lemma exists_orth (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s.card < d) :
    ∃ z : EuclideanSpace ℝ (Fin d), z ≠ 0 ∧ ∀ v ∈ s, ⟪v, z⟫ = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (s : Set _)
  have h1 : Module.finrank ℝ K ≤ s.card := finrank_span_finset_le_card s
  have h2 := K.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at h2
  have hne : Kᗮ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h2
    omega
  obtain ⟨z, hzK, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨z, hz0, fun v hv => ?_⟩
  exact (Submodule.mem_orthogonal K z).1 hzK v (Submodule.subset_span hv)

private lemma open_mid (x z : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    x ∈ openSegment ℝ (x + ε • z) (x - ε • z) := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [smul_add, smul_sub, smul_smul]; module

/-- An extreme point has at least `d` tight rows. -/
private lemma card_tset_of_extreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Set.extremePoints ℝ (Hpoly a b)) :
    d ≤ (tset a b x).card := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz0, hz⟩ := exists_orth ((tset a b x).image a)
    (lt_of_le_of_lt Finset.card_image_le hlt)
  obtain ⟨ε, hε, hp, hm⟩ := perturb a b hx.1 (z := z) (fun i hi =>
    hz _ (Finset.mem_image_of_mem a ((mem_tset a b x i).2 hi)))
  have := hx.2 hp hm (open_mid x z ε)
  have : ε • z = 0 := by
    have h' : x + ε • z - x = 0 := by rw [this, sub_self]
    simpa using h'
  rcases smul_eq_zero.1 this with h | h
  · exact hε.ne' h
  · exact hz0 h


private lemma reach_self (P : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
    Reach P k u u :=
  ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩

/-- Two vertices with no common tight row, in a polyhedron with `n ≤ 2d` rows, form a spindle. -/
private lemma isSpindle_of_disjoint (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hn : n ≤ 2 * d) {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hne : u ≠ v) (hdisj : ¬ ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) :
    SantosHirsch.Counter.IsSpindle a b u v := by
  classical
  refine ⟨hne, hu, hv, fun i => ?_⟩
  have hdisj' : Disjoint (tset a b u) (tset a b v) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact hdisj ⟨i, (mem_tset a b u i).1 h1, (mem_tset a b v i).1 h2⟩
  constructor
  · intro h h'
    exact hdisj ⟨i, h, h'⟩
  · intro h
    by_contra hcon
    have hiu : i ∉ tset a b u := fun hh => hcon ((mem_tset a b u i).1 hh)
    have hiv : i ∉ tset a b v := fun hh => h ((mem_tset a b v i).1 hh)
    have hsub : tset a b u ∪ tset a b v ⊆ Finset.univ.erase i := by
      intro j hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      rcases Finset.mem_union.1 hj with h1 | h1
      · exact hiu h1
      · exact hiv h1
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin] at h1
    have := card_tset_of_extreme a b hu
    have := card_tset_of_extreme a b hv
    have : 0 < n := Fin.pos i
    omega

/-- The case split behind the reductions: a pair of vertices either shares a facet or is a spindle. -/
private lemma reach_of_cases (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hn : n ≤ 2 * d) (k : ℕ)
    (hspin : ∀ u v, SantosHirsch.Counter.IsSpindle a b u v → Reach (Hpoly a b) k u v)
    (hcomm : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) → Reach (Hpoly a b) k u v) :
    ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      Reach (Hpoly a b) k u v := by
  intro u hu v hv
  by_cases heq : u = v
  · subst heq; exact reach_self _ _ _
  by_cases hc : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i
  · exact hcomm u hu v hv hc
  · exact hspin u v (isSpindle_of_disjoint a b hn hu hv heq hc)

/-- Case split without the spindle conversion: a pair shares a facet or not. -/
private lemma reach_of_split (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (k : ℕ)
    (hdisj : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      ¬ (∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) → Reach (Hpoly a b) k u v)
    (hcomm : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) → Reach (Hpoly a b) k u v) :
    ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      Reach (Hpoly a b) k u v := by
  intro u hu v hv
  by_cases hc : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i
  · exact hcomm u hu v hv hc
  · exact hdisj u hu v hv hc

theorem solution (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 4 :=
  reach_of_cases a b (by norm_num) 4
    (fun u v hsp => LefebvreVariations.dim4_spindle_eight_facets a b u v hfp hbd hsp)
    (fun u hu v hv hc => LefebvreVariations.dim4_common_facet_eight_facets a b u v hfp hbd hu hv hc)
