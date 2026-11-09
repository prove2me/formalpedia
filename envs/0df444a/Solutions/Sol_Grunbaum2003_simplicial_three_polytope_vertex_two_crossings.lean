-- Prove2me | solution 1 for Grunbaum2003.simplicial_three_polytope_vertex_two_crossings
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:24:53.952064+00:00
-- url     : https://prove2.me/submissions/d86aad92-bdd0-4caa-a2f8-ed656e91378e

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_simplicial_facet_exposed_vertices_and_cardinality
import Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
import Theorems.Thm_Grunbaum2003_exists_facet_above_edge_improving_dual
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open scoped BigOperators
open Classical
open Grunbaum2003

section

def dot3' (x y : Fin 3 → ℝ) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def cross3 (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

lemma dual_apply_fin_three (g : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ) :
    g x = g (Pi.single 0 1) * x 0 + g (Pi.single 1 1) * x 1 + g (Pi.single 2 1) * x 2 := by
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 + x 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

lemma cross3_orthogonal_and_norm (l u : Fin 3 → ℝ) (hlu : dot3' l u = 0) :
    dot3' (cross3 l u) u = 0 ∧
    dot3' (cross3 l u) l = 0 ∧
    dot3' (cross3 l u) (cross3 l u) = dot3' l l * dot3' u u := by
  dsimp [dot3', cross3] at hlu ⊢
  refine ⟨by ring, by ring, ?_⟩
  calc (l 1 * u 2 - l 2 * u 1) * (l 1 * u 2 - l 2 * u 1) +
        (l 2 * u 0 - l 0 * u 2) * (l 2 * u 0 - l 0 * u 2) +
        (l 0 * u 1 - l 1 * u 0) * (l 0 * u 1 - l 1 * u 0)
      = (l 0 * l 0 + l 1 * l 1 + l 2 * l 2) * (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) -
        (l 0 * u 0 + l 1 * u 1 + l 2 * u 2) ^ 2 := by ring
    _ = (l 0 * l 0 + l 1 * l 1 + l 2 * l 2) * (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) := by
        rw [hlu]; ring

lemma cross3_gram_identity (l u g d : Fin 3 → ℝ) (hlu : dot3' l u = 0) (hgu : dot3' g u = 0) :
    dot3' (cross3 l u) (cross3 l u) * dot3' g d =
      dot3' u u * dot3' g l * dot3' l d + dot3' g (cross3 l u) * dot3' (cross3 l u) d := by
  dsimp [dot3', cross3] at hlu hgu ⊢
  calc ((l 1 * u 2 - l 2 * u 1) * (l 1 * u 2 - l 2 * u 1) +
        (l 2 * u 0 - l 0 * u 2) * (l 2 * u 0 - l 0 * u 2) +
        (l 0 * u 1 - l 1 * u 0) * (l 0 * u 1 - l 1 * u 0)) *
        (g 0 * d 0 + g 1 * d 1 + g 2 * d 2)
      = (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) * (g 0 * l 0 + g 1 * l 1 + g 2 * l 2) *
          (l 0 * d 0 + l 1 * d 1 + l 2 * d 2) +
        (g 0 * (l 1 * u 2 - l 2 * u 1) + g 1 * (l 2 * u 0 - l 0 * u 2) +
          g 2 * (l 0 * u 1 - l 1 * u 0)) *
          ((l 1 * u 2 - l 2 * u 1) * d 0 + (l 2 * u 0 - l 0 * u 2) * d 1 +
            (l 0 * u 1 - l 1 * u 0) * d 2) +
        ((l 0 * l 0 + l 1 * l 1 + l 2 * l 2) * (g 0 * u 0 + g 1 * u 1 + g 2 * u 2) -
          (l 0 * u 0 + l 1 * u 1 + l 2 * u 2) * (g 0 * l 0 + g 1 * l 1 + g 2 * l 2)) *
          (u 0 * d 0 + u 1 * d 1 + u 2 * d 2) -
        (l 0 * u 0 + l 1 * u 1 + l 2 * u 2) * (g 0 * u 0 + g 1 * u 1 + g 2 * u 2) *
          (l 0 * d 0 + l 1 * d 1 + l 2 * d 2) := by ring
    _ = (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) * (g 0 * l 0 + g 1 * l 1 + g 2 * l 2) *
          (l 0 * d 0 + l 1 * d 1 + l 2 * d 2) +
        (g 0 * (l 1 * u 2 - l 2 * u 1) + g 1 * (l 2 * u 0 - l 0 * u 2) +
          g 2 * (l 0 * u 1 - l 1 * u 0)) *
          ((l 1 * u 2 - l 2 * u 1) * d 0 + (l 2 * u 0 - l 0 * u 2) * d 1 +
            (l 0 * u 1 - l 1 * u 0) * d 2) := by
        rw [hlu, hgu]; ring

lemma dot3'_self_le_zero_imp (v : Fin 3 → ℝ) (h : dot3' v v ≤ 0) :
    v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  dsimp [dot3'] at h
  have h0 := mul_self_nonneg (v 0)
  have h1 := mul_self_nonneg (v 1)
  have h2 := mul_self_nonneg (v 2)
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma exposed_eq_convexHull_filter_3d {n : ℕ} (s : Finset (Fin n → ℝ)) {F : Set (Fin n → ℝ)}
    [DecidablePred (· ∈ F)]
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F) :
    F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨l, hFl⟩ := hF ⟨x, hx⟩
    have hxP : x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := by
      rw [hFl] at hx; exact hx.1
    have hxl : ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x := by
      rw [hFl] at hx; exact hx.2
    rw [Finset.convexHull_eq] at hxP ⊢
    rcases hxP with ⟨w, hw0, hw1, hcm⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hcm
    have hcm' : ∑ z ∈ s, w z • z = x := hcm
    have h_zero : ∀ y ∈ s, y ∉ F → w y = 0 := by
      intro y hy hyF
      by_contra hwy
      have hwy_pos : 0 < w y := lt_of_le_of_ne (hw0 y hy) (Ne.symm hwy)
      have hyP : y ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := subset_convexHull ℝ _ hy
      have hlt : l y < l x := by
        refine lt_of_le_of_ne (hxl y hyP) (fun heq => hyF ?_)
        rw [hFl]
        exact ⟨hyP, fun z hz => by linarith [hxl z hz]⟩
      have hsum_lt : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l x := by
        apply Finset.sum_lt_sum
        · intro z hz
          exact mul_le_mul_of_nonneg_left (hxl z (subset_convexHull ℝ _ hz)) (hw0 z hz)
        · exact ⟨y, hy, mul_lt_mul_of_pos_left hlt hwy_pos⟩
      have hsum_eq : ∑ z ∈ s, w z * l z = l x := by
        calc ∑ z ∈ s, w z * l z = ∑ z ∈ s, l (w z • z) := by
              refine Finset.sum_congr rfl (fun z _ => ?_)
              rw [l.map_smul, smul_eq_mul]
          _ = l (∑ z ∈ s, w z • z) := (map_sum l _ _).symm
          _ = l x := by rw [hcm']
      have hsum_rhs : ∑ z ∈ s, w z * l x = l x := by
        rw [← Finset.sum_mul, hw1, one_mul]
      linarith
    have h_sum1 : ∑ y ∈ s.filter (· ∈ F), w y = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' =>
        h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)))
    refine ⟨w, fun y hy => hw0 y (Finset.mem_of_mem_filter y hy), h_sum1, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id h_sum1]
    change ∑ y ∈ s.filter (· ∈ F), w y • y = x
    rw [← hcm']
    exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' => by
      rw [h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)), zero_smul])
  · refine convexHull_min ?_ (hF.convex (convex_convexHull ℝ _))
    intro x hx
    exact (Finset.mem_filter.1 hx).2

lemma isExposed_of_eq_max_on_finset_3d {n : ℕ} (s : Finset (Fin n → ℝ))
    (l : StrongDual ℝ (Fin n → ℝ)) (M : ℝ)
    (hle : ∀ y ∈ s, l y ≤ M) (hm : ∃ y₀ ∈ s, l y₀ = M) :
    let P := convexHull ℝ (s : Set (Fin n → ℝ))
    let F := convexHull ℝ ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
    (∀ x ∈ P, l x ≤ M) ∧
    F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} ∧
    IsExposed ℝ P F := by
  intro P F
  rcases hm with ⟨y₀, hy₀, hy₀M⟩
  have hP_le : ∀ x ∈ P, l x ≤ M := by
    have hsub : (s : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | l x ≤ M} := fun y hy => hle y hy
    have hconv : Convex ℝ {x : Fin n → ℝ | l x ≤ M} :=
      convex_halfSpace_le (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_sub_P : F ⊆ P := convexHull_mono (by
    intro y hy
    exact (Finset.mem_filter.1 hy).1)
  have hF_eq_M : ∀ x ∈ F, l x = M := by
    have hsub : ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | l x = M} := fun y hy => (Finset.mem_filter.1 hy).2
    have hconv : Convex ℝ {x : Fin n → ℝ | l x = M} :=
      convex_hyperplane (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_eq : F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    apply Set.Subset.antisymm
    · intro x hx
      refine ⟨hF_sub_P hx, fun y hy => ?_⟩
      linarith [hP_le y hy, hF_eq_M x hx]
    · intro x hx
      have hExp : IsExposed ℝ P {z ∈ P | ∀ y ∈ P, l y ≤ l z} := fun _ => ⟨l, rfl⟩
      have hfilt := exposed_eq_convexHull_filter_3d s hExp
      rw [hfilt] at hx
      refine convexHull_mono ?_ hx
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      refine Finset.mem_filter.2 ⟨hy'.1, le_antisymm (hle y hy'.1) ?_⟩
      have h1 : l y₀ ≤ l y := hy'.2.2 y₀ (subset_convexHull ℝ _ hy₀)
      linarith
  refine ⟨hP_le, hF_eq, fun _ => ⟨l, hF_eq⟩⟩

lemma isExposed_trans_of_convexHull_3d {n : ℕ} (s : Finset (Fin n → ℝ))
    {F G : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F)
    (hG : IsExposed ℝ F G) :
    IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) G := by
  intro hGne
  have hGF : G ⊆ F := hG.subset
  have hFne : F.Nonempty := hGne.mono hGF
  have hFs : F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    exposed_eq_convexHull_filter_3d s hF
  have hGs : G = convexHull ℝ (((s.filter (· ∈ F)).filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    have hG' : IsExposed ℝ (convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) G := by
      rwa [← hFs]
    exact exposed_eq_convexHull_filter_3d (s.filter (· ∈ F)) hG'
  have hfilt_eq : (s.filter (· ∈ F)).filter (· ∈ G) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_assoc, and_congr_right_iff]
    intro _
    exact ⟨fun h => h.2, fun h => ⟨hGF h, h⟩⟩
  have hGs' : G = convexHull ℝ ((s.filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    hGs.trans (by rw [hfilt_eq])
  have hsG_ne : (s.filter (· ∈ G)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hGs', hemp, Finset.coe_empty, convexHull_empty] at hGne
    exact Set.not_nonempty_empty hGne
  rcases hsG_ne with ⟨y₀, hy₀⟩
  have hy₀_mem : y₀ ∈ s ∧ y₀ ∈ G := Finset.mem_filter.1 hy₀
  have hy₀F : y₀ ∈ F := hGF hy₀_mem.2
  obtain ⟨l, hFl⟩ := hF hFne
  obtain ⟨m, hGm⟩ := hG hGne
  let M_l : ℝ := l y₀
  let M_m : ℝ := m y₀
  have hl_le : ∀ y ∈ s, l y ≤ M_l := by
    intro y hy
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x} := by
      rw [← hFl]; exact hy₀F
    exact hy₀'.2 y (subset_convexHull ℝ _ hy)
  have hl_lt : ∀ y ∈ s, y ∉ F → l y < M_l := by
    intro y hy hyF
    refine lt_of_le_of_ne (hl_le y hy) (fun heq => hyF ?_)
    rw [hFl]
    refine ⟨subset_convexHull ℝ _ hy, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hy₀F
    linarith [hy₀'.2 z hz]
  have hl_eq : ∀ y ∈ s, y ∈ F → l y = M_l := by
    intro y hy hyF
    have hy' : y ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hyF
    exact le_antisymm (hl_le y hy) (hy'.2 y₀ (subset_convexHull ℝ _ hy₀_mem.1))
  have hm_le : ∀ y ∈ s, y ∈ F → m y ≤ M_m := by
    intro y _ hyF
    have hy₀' : y₀ ∈ {x ∈ F | ∀ z ∈ F, m z ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    exact hy₀'.2 y hyF
  have hm_lt : ∀ y ∈ s, y ∈ F → y ∉ G → m y < M_m := by
    intro y hy hyF hyG
    refine lt_of_le_of_ne (hm_le y hy hyF) (fun heq => hyG ?_)
    rw [hGm]
    refine ⟨hyF, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    linarith [hy₀'.2 z hz]
  have hm_eq : ∀ y ∈ s, y ∈ G → m y = M_m := by
    intro y hy hyG
    have hy' : y ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hyG
    exact le_antisymm (hm_le y hy (hGF hyG)) (hy'.2 y₀ hy₀F)
  let term : (Fin n → ℝ) → ℝ := fun z => (1 + (m z - M_m) ^ 2) / (M_l - l z)
  let C : ℝ := 1 + ∑ y ∈ s.filter (· ∉ F), term y
  let h : StrongDual ℝ (Fin n → ℝ) := C • l + m
  have hh_val : ∀ y ∈ s, (y ∈ G → h y = C * M_l + M_m) ∧ (y ∉ G → h y < C * M_l + M_m) := by
    intro y hy
    change (y ∈ G → C * l y + m y = C * M_l + M_m) ∧ (y ∉ G → C * l y + m y < C * M_l + M_m)
    refine ⟨fun hyG => by rw [hl_eq y hy (hGF hyG), hm_eq y hy hyG], fun hyG => ?_⟩
    by_cases hyF : y ∈ F
    · rw [hl_eq y hy hyF]
      linarith [hm_lt y hy hyF hyG]
    · have hy_mem : y ∈ s.filter (· ∉ F) := Finset.mem_filter.2 ⟨hy, hyF⟩
      have hpos : 0 < M_l - l y := sub_pos.2 (hl_lt y hy hyF)
      have hterm_le : term y ≤ ∑ z ∈ s.filter (· ∉ F), term z := by
        refine Finset.single_le_sum (fun z hz => ?_) hy_mem
        have hz' := Finset.mem_filter.1 hz
        have hzpos : 0 < M_l - l z := sub_pos.2 (hl_lt z hz'.1 hz'.2)
        dsimp [term]
        positivity
      have hC_gt : (1 + (m y - M_m) ^ 2) / (M_l - l y) < C := by
        change term y < 1 + ∑ z ∈ s.filter (· ∉ F), term z
        linarith
      have hmul : 1 + (m y - M_m) ^ 2 < C * (M_l - l y) :=
        (div_lt_iff₀ hpos).1 hC_gt
      have hsq : m y - M_m < 1 + (m y - M_m) ^ 2 := by
        nlinarith [(sq_nonneg (m y - M_m - 1 / 2))]
      linarith
  have hh_le : ∀ y ∈ s, h y ≤ C * M_l + M_m := by
    intro y hy
    by_cases hyG : y ∈ G
    · exact le_of_eq ((hh_val y hy).1 hyG)
    · exact le_of_lt ((hh_val y hy).2 hyG)
  have hh_eq_G : s.filter (fun y => h y = C * M_l + M_m) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hy
    exact ⟨fun heq => by_contra (fun hyG => ne_of_lt ((hh_val y hy).2 hyG) heq),
      fun hyG => (hh_val y hy).1 hyG⟩
  have hexp := isExposed_of_eq_max_on_finset_3d s h (C * M_l + M_m) hh_le
    ⟨y₀, hy₀_mem.1, (hh_val y₀ hy₀_mem.1).1 hy₀_mem.2⟩
  rcases hexp with ⟨_, _, hExp⟩
  rw [hh_eq_G, ← hGs'] at hExp
  exact hExp hGne

lemma sum_filter_card_eq_mul_card {α β : Type*} (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [∀ a, DecidablePred (R a)] [∀ b, DecidablePred (fun a => R a b)] (k : ℕ)
    (hB : ∀ b ∈ B, (A.filter (fun a => R a b)).card = k) :
    ∑ a ∈ A, (B.filter (fun b => R a b)).card = k * B.card := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b₀ s hb₀ ih =>
    have hs : ∀ b ∈ s, (A.filter (fun a => R a b)).card = k :=
      fun b hb => hB b (Finset.mem_insert_of_mem hb)
    have hb₀_card : (A.filter (fun a => R a b₀)).card = k :=
      hB b₀ (Finset.mem_insert_self b₀ s)
    have hstep : ∀ a ∈ A,
        ((insert b₀ s).filter (fun b => R a b)).card =
          (if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card := by
      intro a _
      rw [Finset.filter_insert]
      split_ifs with hR
      · rw [Finset.card_insert_of_notMem (fun hm => hb₀ (Finset.mem_of_mem_filter b₀ hm))]
        omega
      · omega
    calc ∑ a ∈ A, ((insert b₀ s).filter (fun b => R a b)).card
        = ∑ a ∈ A, ((if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card) :=
          Finset.sum_congr rfl hstep
      _ = (∑ a ∈ A, if R a b₀ then 1 else 0) + ∑ a ∈ A, (s.filter (fun b => R a b)).card :=
          Finset.sum_add_distrib
      _ = (A.filter (fun a => R a b₀)).card + k * s.card := by
          rw [← Finset.card_filter, ih hs]
      _ = k * (insert b₀ s).card := by
          rw [hb₀_card, Finset.card_insert_of_notMem hb₀]
          ring

lemma sum_le_two_eq_two_mul_card_two_add_card_one {α : Type*} (s : Finset α) (d : α → ℕ)
    (hd : ∀ x ∈ s, d x ≤ 2) :
    ∑ x ∈ s, d x =
      2 * (s.filter (fun x => d x = 2)).card + (s.filter (fun x => d x = 1)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ x ∈ s, d x ≤ 2 := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have hda : d a ≤ 2 := hd a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, ih hs, Finset.filter_insert, Finset.filter_insert]
    have hda_cases : d a = 0 ∨ d a = 1 ∨ d a = 2 := by omega
    rcases hda_cases with h0 | h1 | h2
    · simp [h0]
    · simp [h1, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega
    · simp [h2, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega

def dot3 (x y : Fin 3 → ℝ) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

lemma exists_dual_eq_on_pair_lt_third {P : Set (Fin 3 → ℝ)}
    (v : Fin 3 → Fin 3 → ℝ)
    (hv_inj : Function.Injective v)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ m : StrongDual ℝ (Fin 3 → ℝ), m (v j) = m (v i) ∧ m (v k) < m (v i) := by
  have hSub := (@Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.1
    3 P v hv_inj hv_exp).1
  let d₁ : Fin 3 → ℝ := v j - v i
  let d₂ : Fin 3 → ℝ := v k - v i
  have hd₁_ne : d₁ ≠ 0 := sub_ne_zero.2 (hv_inj.ne hij.symm)
  have hd₁_pos : 0 < dot3 d₁ d₁ := by
    by_contra hle
    have h0 : d₁ 0 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    have h1 : d₁ 1 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    have h2 : d₁ 2 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    apply hd₁_ne
    ext r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
  let t : ℝ := dot3 d₁ d₂ / dot3 d₁ d₁
  let w : Fin 3 → ℝ := d₂ - t • d₁
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hd₂_eq : d₂ = t • d₁ := sub_eq_zero.1 hw0
    have hvk_eq : v k = (1 - t) • v i + t • v j := by
      ext r
      have hr := congr_fun hd₂_eq r
      change v k r - v i r = t * (v j r - v i r) at hr
      change v k r = (1 - t) * v i r + t * v j r
      linarith
    have hnot_in : ∀ (a b c : Fin 3), a ≠ b → c ≠ a → c ≠ b →
        v c ∉ convexHull ℝ (v '' (({a, b} : Finset (Fin 3)) : Set (Fin 3))) := by
      intro a b c hab hca hcb hmem
      have h_inter : v c ∈ convexHull ℝ (v '' (({a, b} : Finset (Fin 3)) : Set (Fin 3))) ∩
          {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hmem, hv_exp c⟩
      rw [hSub {a, b}] at h_inter
      rcases h_inter with ⟨r, hr, hvr⟩
      have hrc : r = c := hv_inj hvr
      subst hrc
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact hca rfl
      · exact hcb rfl
    rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
    · let s : ℝ := -t / (1 - t)
      have h1mt : 0 < 1 - t := by linarith
      have hs0 : 0 ≤ s := div_nonneg (by linarith) (le_of_lt h1mt)
      have hs1 : 0 ≤ 1 - s := by
        have h_eq : 1 - s = 1 / (1 - t) := by
          dsimp [s]
          field_simp [ne_of_gt h1mt]
          ring
        rw [h_eq]
        positivity
      have hvi_eq : v i = (1 - s) • v k + s • v j := by
        ext r
        have hr := congr_fun hvk_eq r
        change v k r = (1 - t) * v i r + t * v j r at hr
        change v i r = (1 - s) * v k r + s * v j r
        dsimp [s]
        field_simp [ne_of_gt h1mt]
        linarith
      have hvi_mem : v i ∈ convexHull ℝ (v '' (({k, j} : Finset (Fin 3)) : Set (Fin 3))) := by
        rw [hvi_eq]
        refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
          hs1 hs0 (by ring))
        · exact ⟨k, by simp, rfl⟩
        · exact ⟨j, by simp, rfl⟩
      exact hnot_in k j i hjk.symm hik hij hvi_mem
    · rw [ht_zero, sub_zero, one_smul, zero_smul, add_zero] at hvk_eq
      exact hik (hv_inj hvk_eq.symm)
    · rcases le_or_gt t 1 with ht_le1 | ht_gt1
      · have hvk_mem : v k ∈ convexHull ℝ (v '' (({i, j} : Finset (Fin 3)) : Set (Fin 3))) := by
          rw [hvk_eq]
          refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
            (by linarith) (le_of_lt ht_pos) (by ring))
          · exact ⟨i, by simp, rfl⟩
          · exact ⟨j, by simp, rfl⟩
        exact hnot_in i j k hij hik.symm hjk.symm hvk_mem
      · let s : ℝ := 1 / t
        have hs0 : 0 ≤ s := by positivity
        have hs1 : 0 ≤ 1 - s := by
          have h_eq : 1 - s = (t - 1) / t := by
            dsimp [s]
            field_simp [ne_of_gt ht_pos]
          rw [h_eq]
          exact div_nonneg (by linarith) (le_of_lt ht_pos)
        have hvj_eq : v j = (1 - s) • v i + s • v k := by
          ext r
          have hr := congr_fun hvk_eq r
          change v k r = (1 - t) * v i r + t * v j r at hr
          change v j r = (1 - s) * v i r + s * v k r
          dsimp [s]
          field_simp [ne_of_gt ht_pos]
          linarith
        have hvj_mem : v j ∈ convexHull ℝ (v '' (({i, k} : Finset (Fin 3)) : Set (Fin 3))) := by
          rw [hvj_eq]
          refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
            hs1 hs0 (by ring))
          · exact ⟨i, by simp, rfl⟩
          · exact ⟨k, by simp, rfl⟩
        exact hnot_in i k j hik hij.symm hjk hvj_mem
  have hw_pos : 0 < dot3 w w := by
    by_contra hle
    have h0 : w 0 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h1 : w 1 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h2 : w 2 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    apply hw_ne
    ext r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
  let m : StrongDual ℝ (Fin 3 → ℝ) :=
    -w 0 • ContinuousLinearMap.proj 0 - w 1 • ContinuousLinearMap.proj 1 -
      w 2 • ContinuousLinearMap.proj 2
  have hm_val : ∀ x : Fin 3 → ℝ, m x = -dot3 w x := by
    intro x
    change -w 0 * x 0 - w 1 * x 1 - w 2 * x 2 = -(w 0 * x 0 + w 1 * x 1 + w 2 * x 2)
    ring
  have htmul : t * dot3 d₁ d₁ = dot3 d₁ d₂ := div_mul_cancel₀ _ (ne_of_gt hd₁_pos)
  have hwd₁ : dot3 w d₁ = 0 := by
    change (d₂ 0 - t * d₁ 0) * d₁ 0 + (d₂ 1 - t * d₁ 1) * d₁ 1 + (d₂ 2 - t * d₁ 2) * d₁ 2 = 0
    dsimp [dot3] at htmul
    linarith
  have hwd₂ : dot3 w d₂ = dot3 w w := by
    calc dot3 w d₂
        = (d₂ 0 - t * d₁ 0) * d₂ 0 + (d₂ 1 - t * d₁ 1) * d₂ 1 + (d₂ 2 - t * d₁ 2) * d₂ 2 := rfl
      _ = ((d₂ 0 - t * d₁ 0) ^ 2 + (d₂ 1 - t * d₁ 1) ^ 2 + (d₂ 2 - t * d₁ 2) ^ 2) +
          t * ((d₂ 0 - t * d₁ 0) * d₁ 0 + (d₂ 1 - t * d₁ 1) * d₁ 1 + (d₂ 2 - t * d₁ 2) * d₁ 2) := by ring
      _ = dot3 w w + t * dot3 w d₁ := by dsimp [dot3, w]; ring
      _ = dot3 w w := by rw [hwd₁, mul_zero, add_zero]
  refine ⟨m, ?_, ?_⟩
  · have hdiff : m (v j) - m (v i) = -dot3 w d₁ := by
      rw [hm_val (v j), hm_val (v i)]
      dsimp [dot3, d₁]
      ring
    linarith
  · have hdiff : m (v k) - m (v i) = -dot3 w d₂ := by
      rw [hm_val (v k), hm_val (v i)]
      dsimp [dot3, d₂]
      ring
    linarith

lemma exists_third_fin3 (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · refine ⟨2, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨1, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨2, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · exact False.elim (hij rfl)
  · refine ⟨0, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨1, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨0, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · exact False.elim (hij rfl)

lemma simplicial_facet_pair_is_edge {P : Set (Fin 3 → ℝ)} (V : Finset (Fin 3 → ℝ))
    (hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)))
    {F : Set (Fin 3 → ℝ)} (hF_exp : IsExposed ℝ P F)
    (v : Fin 3 → Fin 3 → ℝ) (hv_inj : Function.Injective v)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (hF_eq : F = convexHull ℝ (Set.range v))
    (i j : Fin 3) (hij : i ≠ j) :
    let E := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
    E.Nonempty ∧ IsExposed ℝ P E ∧
    Module.finrank ℝ (affineSpan ℝ E).direction = 1 ∧
    E ⊆ F ∧
    E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = {v i, v j} := by
  intro E
  obtain ⟨k, hik, hjk, hall⟩ := exists_third_fin3 i j hij
  obtain ⟨m, hmj, hmk⟩ := exists_dual_eq_on_pair_lt_third v hv_inj hv_exp i j k hij hik hjk
  let s_F : Finset (Fin 3 → ℝ) := Finset.univ.image v
  have hs_F_coe : (s_F : Set (Fin 3 → ℝ)) = Set.range v := by
    simp [s_F]
  have hF_sF : F = convexHull ℝ (s_F : Set (Fin 3 → ℝ)) := by
    rw [hF_eq, hs_F_coe]
  have hm_le : ∀ y ∈ s_F, m y ≤ m (v i) := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨r, _, rfl⟩
    rcases hall r with rfl | rfl | rfl
    · exact le_rfl
    · exact le_of_eq hmj
    · exact le_of_lt hmk
  have hfilt : s_F.filter (fun y => m y = m (v i)) = {v i, v j} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, heq⟩
      rcases Finset.mem_image.1 hy with ⟨r, _, rfl⟩
      rcases hall r with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (ne_of_lt hmk heq)
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_image_of_mem v (Finset.mem_univ i), rfl⟩
      · exact ⟨Finset.mem_image_of_mem v (Finset.mem_univ j), hmj⟩
  have hexp_F := (isExposed_of_eq_max_on_finset_3d s_F m (m (v i)) hm_le
    ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i), rfl⟩).2.2
  rw [← hF_sF, hfilt] at hexp_F
  simp only [Finset.coe_insert, Finset.coe_singleton] at hexp_F
  have hF_exp_V : IsExposed ℝ (convexHull ℝ (V : Set (Fin 3 → ℝ))) F := by
    rwa [← hP_eq_V]
  have hE_exp_P : IsExposed ℝ P E := by
    rw [hP_eq_V]
    exact isExposed_trans_of_convexHull_3d V hF_exp_V hexp_F
  have hE_ne : E.Nonempty := ⟨v i, subset_convexHull ℝ _ (by simp)⟩
  have hE_dim : Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
    dsimp [E]
    rw [affineSpan_convexHull, direction_affineSpan, vectorSpan_pair ℝ (v i) (v j)]
    exact finrank_span_singleton (vsub_ne_zero.2 (hv_inj.ne hij))
  have hE_sub_F : E ⊆ F := by
    rw [hF_eq]
    refine convexHull_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
  have hSub := (@Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.1
    3 P v hv_inj hv_exp).1 {i, j}
  have h_img : v '' (({i, j} : Finset (Fin 3)) : Set (Fin 3)) = ({v i, v j} : Set (Fin 3 → ℝ)) := by
    ext x
    simp [eq_comm]
  rw [h_img] at hSub
  exact ⟨hE_ne, hE_exp_P, hE_dim, hE_sub_F, hSub⟩

lemma simplicial_facet_incident_edge_dichotomy {P : Set (Fin 3 → ℝ)}
    (hHull : {x : Fin 3 → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}))
    {F : Set (Fin 3 → ℝ)}
    (v : Fin 3 → Fin 3 → ℝ)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (hFV : F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = Set.range v)
    (i j k : Fin 3)
    (hall : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k)
    {E : Set (Fin 3 → ℝ)}
    (hE : E.Nonempty ∧ IsExposed ℝ P E ∧ Module.finrank ℝ (affineSpan ℝ E).direction = 1)
    (hEF : E ⊆ F) (hviE : v i ∈ E) :
    E = convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ)) ∨
      E = convexHull ℝ ({v i, v k} : Set (Fin 3 → ℝ)) := by
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  obtain ⟨a, b, ha, hb, hab, hEV, hE_eq⟩ := (hEdgePair hHull E hE.2.1).1 ⟨hE.1, hE.2.2⟩
  have hvi_in : v i ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hviE, hv_exp i⟩
  rw [hEV] at hvi_in
  have hex_u : ∃ u : Fin 3 → ℝ, u ≠ v i ∧
      u ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} ∧
      E = convexHull ℝ ({v i, u} : Set (Fin 3 → ℝ)) := by
    rcases Set.mem_insert_iff.1 hvi_in with hvia | hvib
    · subst hvia
      refine ⟨b, hab.symm, ?_, hE_eq⟩
      rw [hEV]; simp
    · have hvib' : v i = b := Set.mem_singleton_iff.1 hvib
      subst hvib'
      refine ⟨a, hab, ?_, ?_⟩
      · rw [hEV]; simp
      · rw [Set.pair_comm (v i) a]; exact hE_eq
  rcases hex_u with ⟨u, hu_ne, hu_EV, hE_u⟩
  have hu_FV : u ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hEF hu_EV.1, hu_EV.2⟩
  rw [hFV] at hu_FV
  rcases hu_FV with ⟨r, rfl⟩
  rcases hall r with rfl | rfl | rfl
  · exact False.elim (hu_ne rfl)
  · exact Or.inl hE_u
  · exact Or.inr hE_u

lemma simplicial_facet_vertex_degree_and_pair_edge {P : Set (Fin 3 → ℝ)}
    (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)))
    (ℰ : Finset (Set (Fin 3 → ℝ)))
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    {F : Set (Fin 3 → ℝ)}
    (hF : F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    (∀ a ∈ V, ∀ b ∈ V, a ∈ F → b ∈ F → a ≠ b →
      convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ∈ ℰ ∧
      convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ⊆ F ∧
      convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = {a, b}) ∧
    (∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
      let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
      (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
      ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
        (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x))) := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
  obtain ⟨v, _, hv_inj, hv_exp, hF_eq, hFV, _⟩ :=
    Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality hP hHull F
      hF.1 hF.2.1 (by omega)
  have hPair : ∀ i j : Fin 3, i ≠ j →
      let E := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
      E ∈ ℰ ∧ E ⊆ F ∧ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = {v i, v j} := by
    intro i j hij
    have hp := simplicial_facet_pair_is_edge V hP_eq_V hF.2.1 v hv_inj hv_exp hF_eq i j hij
    have hmem : convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ)) ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    exact ⟨hmem, hp.2.2.2.1, hp.2.2.2.2⟩
  refine ⟨?_, fun l x hxV => ?_⟩
  · intro a haV b hbV haF hbF hab
    have ha_FV : a ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
      refine ⟨haF, ?_⟩; rw [← hV_coe]; exact haV
    have hb_FV : b ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
      refine ⟨hbF, ?_⟩; rw [← hV_coe]; exact hbV
    rw [hFV] at ha_FV hb_FV
    rcases ha_FV with ⟨i, rfl⟩
    rcases hb_FV with ⟨j, rfl⟩
    have hij : i ≠ j := fun heq => hab (congr_arg v heq)
    exact hPair i j hij
  · intro ℰ_x
    by_cases hxF : x ∈ F
    · have hx_FV : x ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
        refine ⟨hxF, ?_⟩
        rw [← hV_coe]
        exact hxV
      rw [hFV] at hx_FV
      rcases hx_FV with ⟨i, rfl⟩
      let j : Fin 3 := if i = 0 then 1 else 0
      have hij : i ≠ j := by fin_cases i <;> decide
      obtain ⟨k, hik, hjk, hall⟩ := exists_third_fin3 i j hij
      let E₁ := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
      let E₂ := convexHull ℝ ({v i, v k} : Set (Fin 3 → ℝ))
      have hE₁ := hPair i j hij
      have hE₂ := hPair i k hik
      have hE₁₂_ne : E₁ ≠ E₂ := by
        intro heq
        have hj_in : v j ∈ E₁ ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hE₁.2.2]; simp
        rw [heq, hE₂.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] at hj_in
        rcases hj_in with h | h
        · exact hij (hv_inj h).symm
        · exact hjk (hv_inj h)
      have hsub : ℰ_x.filter (fun E => E ⊆ F) ⊆ {E₁, E₂} := by
        intro E hE
        simp only [Finset.mem_filter, ℰ_x] at hE
        have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
            Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
          rw [← Finset.mem_coe, hℰ_coe] at hE
          exact hE.1.1
        have hdic := simplicial_facet_incident_edge_dichotomy hHull v hv_exp hFV
          i j k hall hE_set hE.2 hE.1.2.1
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hdic
      have hcard_le2 : (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 := by
        calc (ℰ_x.filter (fun E => E ⊆ F)).card
            ≤ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))).card := Finset.card_le_card hsub
          _ = 2 := Finset.card_pair hE₁₂_ne
      refine ⟨hcard_le2, ?_⟩
      constructor
      · intro hcard2
        have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
          Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hE₁₂_ne, hcard2])
        have hE₁_in : E₁ ∈ ℰ_x.filter (fun E => E ⊆ F) := by rw [heq_pair]; simp
        have hE₂_in : E₂ ∈ ℰ_x.filter (fun E => E ⊆ F) := by rw [heq_pair]; simp
        simp only [Finset.mem_filter, ℰ_x] at hE₁_in hE₂_in
        have hvj_V : v j ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hv_exp j
        have hvk_V : v k ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hv_exp k
        have hlj : l (v j) ≤ l (v i) :=
          hE₁_in.1.2.2 (v j) hvj_V (subset_convexHull ℝ _ (by simp))
        have hlk : l (v k) ≤ l (v i) :=
          hE₂_in.1.2.2 (v k) hvk_V (subset_convexHull ℝ _ (by simp))
        refine ⟨hxF, fun w hwV hwF => ?_⟩
        have hw_FV : w ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
          refine ⟨hwF, ?_⟩
          rw [← hV_coe]; exact hwV
        rw [hFV] at hw_FV
        rcases hw_FV with ⟨r, rfl⟩
        rcases hall r with rfl | rfl | rfl
        · exact le_rfl
        · exact hlj
        · exact hlk
      · rintro ⟨_, hle_F⟩
        have hpair_sub : ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) ⊆ ℰ_x.filter (fun E => E ⊆ F) := by
          intro E hE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hE
          simp only [Finset.mem_filter, ℰ_x]
          rcases hE with rfl | rfl
          · refine ⟨⟨hE₁.1, subset_convexHull ℝ _ (by simp), fun w hwV hwE => ?_⟩, hE₁.2.1⟩
            exact hle_F w hwV (hE₁.2.1 hwE)
          · refine ⟨⟨hE₂.1, subset_convexHull ℝ _ (by simp), fun w hwV hwE => ?_⟩, hE₂.2.1⟩
            exact hle_F w hwV (hE₂.2.1 hwE)
        have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
          Finset.Subset.antisymm hsub hpair_sub
        rw [heq_pair, Finset.card_pair hE₁₂_ne]
    · have hemp : ℰ_x.filter (fun E => E ⊆ F) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro E hE hEF
        simp only [Finset.mem_filter, ℰ_x] at hE
        exact hxF (hEF hE.2.1)
      rw [hemp, Finset.card_empty]
      exact ⟨by omega, ⟨by omega, fun h => False.elim (hxF h.1)⟩⟩

lemma finset_eq_triple_of_card_three {α : Type*} [DecidableEq α]
    {S : Finset α} {a b c : α} (hcard : S.card = 3)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    S = {a, b, c} := by
  have hsub : ({a, b, c} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard_triple : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hca.symm]),
      Finset.card_pair hcb.symm]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

lemma facet_filter_vertices_card_eq_three
    {P : Set (Fin 3 → ℝ)} (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)))
    {F : Set (Fin 3 → ℝ)} [DecidablePred (· ∈ F)]
    (hF : F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    F = convexHull ℝ ((V.filter (· ∈ F) : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) ∧
    (V.filter (· ∈ F)).card = 3 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
  have hF_hull : F = convexHull ℝ ((V.filter (· ∈ F) : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
    have hExp' : IsExposed ℝ (convexHull ℝ (V : Set (Fin 3 → ℝ))) F := hP_eq_V ▸ hF.2.1
    exact exposed_eq_convexHull_filter_3d V hExp'
  obtain ⟨_, _, _, _, _, _, hncard⟩ :=
    Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality hP hHull F
      hF.1 hF.2.1 (by omega)
  have hcoe_eq : ((V.filter (· ∈ F) : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) =
      F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    rw [← Finset.mem_coe, hV_coe]
    exact and_comm
  have hcard : (V.filter (· ∈ F)).card = 3 := by
    rw [← Set.ncard_coe_finset, hcoe_eq]
    exact hncard
  exact ⟨hF_hull, hcard⟩

noncomputable def crossing_point (l : StrongDual ℝ (Fin 3 → ℝ)) (x u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ((l v - l x) / (l v - l u)) • u + ((l x - l u) / (l v - l u)) • v

lemma crossing_point_props {P : Set (Fin 3 → ℝ)} (hP_conv : Convex ℝ P)
    (l : StrongDual ℝ (Fin 3 → ℝ)) (x u v : Fin 3 → ℝ)
    (huP : u ∈ P) (hvP : v ∈ P)
    (hu_lt : l u < l x) (hv_gt : l x < l v) :
    crossing_point l x u v ∈ P ∧
    l (crossing_point l x u v) = l x ∧
    (∀ m : StrongDual ℝ (Fin 3 → ℝ), m u < m x → m v < m x →
      m (crossing_point l x u v) < m x) ∧
    (∀ g : StrongDual ℝ (Fin 3 → ℝ), g u ≤ g x → g v ≤ g x →
      g (crossing_point l x u v) ≤ g x ∧
      (g (crossing_point l x u v) = g x ↔ g u = g x ∧ g v = g x)) := by
  let t₁ : ℝ := (l v - l x) / (l v - l u)
  let t₂ : ℝ := (l x - l u) / (l v - l u)
  have hvu_pos : 0 < l v - l u := by linarith
  have ht₁_pos : 0 < t₁ := div_pos (by linarith) hvu_pos
  have ht₂_pos : 0 < t₂ := div_pos (by linarith) hvu_pos
  have ht₁₂ : t₁ + t₂ = 1 := by
    dsimp [t₁, t₂]
    field_simp [ne_of_gt hvu_pos]
    ring
  have hcp_def : crossing_point l x u v = t₁ • u + t₂ • v := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcp_def]
    exact hP_conv huP hvP (le_of_lt ht₁_pos) (le_of_lt ht₂_pos) ht₁₂
  · rw [hcp_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    dsimp [t₁, t₂]
    field_simp [ne_of_gt hvu_pos]
    ring
  · intro m hmu hmv
    rw [hcp_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : t₁ * m u < t₁ * m x := mul_lt_mul_of_pos_left hmu ht₁_pos
    have h2 : t₂ * m v < t₂ * m x := mul_lt_mul_of_pos_left hmv ht₂_pos
    have h3 : t₁ * m x + t₂ * m x = m x := by rw [← add_mul, ht₁₂, one_mul]
    linarith
  · intro g hgu hgv
    rw [hcp_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : t₁ * g u ≤ t₁ * g x := mul_le_mul_of_nonneg_left hgu (le_of_lt ht₁_pos)
    have h2 : t₂ * g v ≤ t₂ * g x := mul_le_mul_of_nonneg_left hgv (le_of_lt ht₂_pos)
    have h3 : t₁ * g x + t₂ * g x = g x := by rw [← add_mul, ht₁₂, one_mul]
    refine ⟨by linarith, ?_⟩
    constructor
    · intro heq
      constructor <;> by_contra hne
      · have hlt : g u < g x := lt_of_le_of_ne hgu hne
        have h1' : t₁ * g u < t₁ * g x := mul_lt_mul_of_pos_left hlt ht₁_pos
        linarith
      · have hlt : g v < g x := lt_of_le_of_ne hgv hne
        have h2' : t₂ * g v < t₂ * g x := mul_lt_mul_of_pos_left hlt ht₂_pos
        linarith
    · rintro ⟨hu, hv⟩
      rw [hu, hv, h3]

lemma pair_eq_max_or_min_of_strict_gram {α : Type*} [DecidableEq α]
    {Pi_set : Finset α} {p₀ p_min p_max p_alt : α}
    {τ_norm gl β : ℝ} {m_pos g_diff σ : α → ℝ}
    (hτ_pos : 0 < τ_norm)
    (hm_pos : ∀ p ∈ Pi_set, 0 < m_pos p)
    (hp₀ : p₀ ∈ Pi_set) (hp_min : p_min ∈ Pi_set) (hp_max : p_max ∈ Pi_set)
    (hp_alt : p_alt ∈ Pi_set) (hne_alt : p_alt ≠ p₀)
    (hσ_min : σ p_min ≤ σ p₀) (hσ_max : σ p₀ ≤ σ p_max)
    (hg_zero : g_diff p₀ = 0)
    (hg_neg : ∀ p ∈ Pi_set, p ≠ p₀ → g_diff p < 0)
    (hgram : ∀ p ∈ Pi_set, τ_norm * g_diff p = m_pos p * (gl + β * σ p)) :
    p₀ = p_max ∨ p₀ = p_min := by
  have hp₀_gram := hgram p₀ hp₀
  rw [hg_zero, mul_zero] at hp₀_gram
  have hmp₀_pos := hm_pos p₀ hp₀
  have hgl_zero : gl + β * σ p₀ = 0 :=
    (mul_eq_zero.1 hp₀_gram.symm).resolve_left (ne_of_gt hmp₀_pos)
  have hgl_eq : gl = -β * σ p₀ := by linarith
  have hrel_neg : ∀ p ∈ Pi_set, p ≠ p₀ → β * (σ p - σ p₀) < 0 := by
    intro p hp hne
    have hgr := hgram p hp
    rw [hgl_eq] at hgr
    have h1 : m_pos p * (-β * σ p₀ + β * σ p) = m_pos p * (β * (σ p - σ p₀)) := by ring
    rw [h1] at hgr
    have hlhs : τ_norm * g_diff p < 0 := mul_neg_of_pos_of_neg hτ_pos (hg_neg p hp hne)
    rw [hgr] at hlhs
    have hmp := hm_pos p hp
    nlinarith
  have halt_neg := hrel_neg p_alt hp_alt hne_alt
  rcases lt_trichotomy β 0 with hβ_neg | rfl | hβ_pos
  · right
    by_contra hne
    have hmin_neg := hrel_neg p_min hp_min (Ne.symm hne)
    have hnonneg : 0 ≤ β * (σ p_min - σ p₀) :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_lt hβ_neg) (by linarith)
    linarith
  · rw [zero_mul] at halt_neg
    exact False.elim (lt_irrefl 0 halt_neg)
  · left
    by_contra hne
    have hmax_neg := hrel_neg p_max hp_max (Ne.symm hne)
    have hnonneg : 0 ≤ β * (σ p_max - σ p₀) :=
      mul_nonneg (le_of_lt hβ_pos) (by linarith)
    linarith

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2})
    (hTwoFacets : ∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) :
    ∀ (l : StrongDual ℝ (Fin 3 → ℝ)),
      (∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y) →
      ∀ x ∈ V,
        (∃ E_down ∈ ℰ, x ∈ E_down ∧ ∃ u ∈ V, u ∈ E_down ∧ l u < l x) →
        (∃ E_up ∈ ℰ, x ∈ E_up ∧ ∃ u ∈ V, u ∈ E_up ∧ l x < l u) →
        (ℱ.filter (fun F =>
          ((ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)).filter
            (fun E => E ⊆ F)).card = 1)).card = 2 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 3 P
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  have hImpFacet := Grunbaum2003.exists_facet_above_edge_improving_dual P hP V ℰ ℱ hV_coe hℰ_coe hℱ_coe
  let V_set : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
  have hV_sub_P : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
  have hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)) := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    rw [Set.inter_eq_self_of_subset_right hV_sub_P] at h1
    dsimp [V_set] at h1
    rw [← hV_coe] at h1
    exact h1
  have hP_conv : Convex ℝ P := by
    rw [hP_eq_V]
    exact convex_convexHull ℝ _
  have hV_ge4 : 4 ≤ V.card := by
    have hCardV : faceCount P 0 = V.card := by
      rw [hVBound.1, ← hV_coe, Set.ncard_coe_finset]
    rw [← hCardV]
    exact hVBound.2 hP.1
  have hFacetProp : ∀ F ∈ ℱ,
      (∀ a ∈ V, ∀ b ∈ V, a ∈ F → b ∈ F → a ≠ b →
        convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ∈ ℰ ∧
        convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ⊆ F ∧
        convexHull ℝ ({a, b} : Set (Fin 3 → ℝ)) ∩ V_set = {a, b}) ∧
      (∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
        let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
        (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
        ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
          (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x))) := by
    intro F hF
    have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
      rw [← Finset.mem_coe, hℱ_coe] at hF; exact hF
    exact simplicial_facet_vertex_degree_and_pair_edge hP V hV_coe hP_eq_V ℰ hℰ_coe hF_set
  intro l hl_inj x hxV ⟨E_down, hE_down_mem, hx_E_down, u_dn, hu_dn_V, hu_dn_E, hl_dn⟩
    ⟨E_up, hE_up_mem, hx_E_up, u_up, hu_up_V, hu_up_E, hl_up⟩
  let ℰ_x : Finset (Set (Fin 3 → ℝ)) :=
    ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
  let ℱ_x : Finset (Set (Fin 3 → ℝ)) :=
    ℱ.filter (fun F => x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)
  let ℱ_cross : Finset (Set (Fin 3 → ℝ)) :=
    ℱ.filter (fun F => (ℰ_x.filter (fun E => E ⊆ F)).card = 1)
  change ℱ_cross.card = 2
  have h_double : 2 * ℰ_x.card = 2 * ℱ_x.card + ℱ_cross.card := by
    have h_lhs : ∑ F ∈ ℱ, (ℰ_x.filter (fun E => E ⊆ F)).card = 2 * ℰ_x.card :=
      sum_filter_card_eq_mul_card ℱ ℰ_x (fun F E => E ⊆ F) 2
        (fun E hE => hTwoFacets E (Finset.mem_of_mem_filter E hE))
    have h_rhs : ∑ F ∈ ℱ, (ℰ_x.filter (fun E => E ⊆ F)).card =
        2 * (ℱ.filter (fun F => (ℰ_x.filter (fun E => E ⊆ F)).card = 2)).card + ℱ_cross.card :=
      sum_le_two_eq_two_mul_card_two_add_card_one ℱ
        (fun F => (ℰ_x.filter (fun E => E ⊆ F)).card)
        (fun F hF => ((hFacetProp F hF).2 l x hxV).1)
    have h_filt_eq : ℱ.filter (fun F => (ℰ_x.filter (fun E => E ⊆ F)).card = 2) = ℱ_x := by
      ext F
      simp only [Finset.mem_filter, ℱ_x, and_congr_right_iff]
      intro hF
      exact ((hFacetProp F hF).2 l x hxV).2
    rw [h_filt_eq] at h_rhs
    omega
  have hxExp : IsExposed ℝ P {x} := by rw [← Finset.mem_coe, hV_coe] at hxV; exact hxV
  have hxP : x ∈ P := hV_sub_P hxExp
  obtain ⟨m_x, hmx_eq⟩ := hxExp (Set.singleton_nonempty x)
  have hx_mx : x ∈ {z ∈ P | ∀ y ∈ P, m_x y ≤ m_x z} := hmx_eq ▸ Set.mem_singleton x
  have hmx_lt : ∀ w ∈ V, w ≠ x → 0 < m_x x - m_x w := by
    intro w hwV hwx
    have hwExp : IsExposed ℝ P {w} := by rw [← Finset.mem_coe, hV_coe] at hwV; exact hwV
    have hwP : w ∈ P := hV_sub_P hwExp
    have hle : m_x w ≤ m_x x := hx_mx.2 w hwP
    have hlt : m_x w < m_x x := by
      refine lt_of_le_of_ne hle (fun heq => hwx ?_)
      have hw_in : w ∈ ({x} : Set (Fin 3 → ℝ)) := by
        rw [hmx_eq]
        exact ⟨hwP, fun y hy => by linarith [hx_mx.2 y hy]⟩
      exact Set.mem_singleton_iff.1 hw_in
    linarith
  have hc_ge_one : 1 ≤ ℱ_cross.card := by
    let U_down : Finset (Fin 3 → ℝ) :=
      V.filter (fun u => l u < l x ∧ ∃ E ∈ ℰ, x ∈ E ∧ u ∈ E)
    have hu_dn_mem : u_dn ∈ U_down :=
      Finset.mem_filter.2 ⟨hu_dn_V, hl_dn, E_down, hE_down_mem, hx_E_down, hu_dn_E⟩
    let ρ : (Fin 3 → ℝ) → ℝ := fun w => (l w - l x) / (m_x x - m_x w)
    have hρ_mul : ∀ w ∈ V, w ≠ x → l w - l x = ρ w * (m_x x - m_x w) := by
      intro w hwV hwx
      dsimp [ρ]
      exact (div_mul_cancel₀ _ (ne_of_gt (hmx_lt w hwV hwx))).symm
    obtain ⟨u₀, hu₀_mem, hρ_max⟩ := U_down.exists_max_image ρ ⟨u_dn, hu_dn_mem⟩
    rcases Finset.mem_filter.1 hu₀_mem with ⟨hu₀_V, hl_u₀_lt, E₀, hE₀_mem, hx_E₀, hu₀_E₀⟩
    have hu₀_ne_x : u₀ ≠ x := fun heq => (ne_of_lt hl_u₀_lt) (congr_arg l heq)
    have hu_up_ne_x : u_up ≠ x := fun heq => (ne_of_gt hl_up) (congr_arg l heq)
    let h_tilde : StrongDual ℝ (Fin 3 → ℝ) := l + ρ u₀ • m_x
    have hh_tilde_diff : ∀ w ∈ V, w ≠ x →
        h_tilde w - h_tilde x = (m_x x - m_x w) * (ρ w - ρ u₀) := by
      intro w hwV hwx
      have hlw := hρ_mul w hwV hwx
      change (l w + ρ u₀ * m_x w) - (l x + ρ u₀ * m_x x) = (m_x x - m_x w) * (ρ w - ρ u₀)
      linarith
    have hh_tilde_u₀ : h_tilde u₀ = h_tilde x := by
      have h1 := hh_tilde_diff u₀ hu₀_V hu₀_ne_x
      rw [sub_self, mul_zero] at h1
      linarith
    have hρ_u₀_neg : ρ u₀ < 0 :=
      div_neg_of_neg_of_pos (by linarith) (hmx_lt u₀ hu₀_V hu₀_ne_x)
    have hρ_up_pos : 0 < ρ u_up :=
      div_pos (by linarith) (hmx_lt u_up hu_up_V hu_up_ne_x)
    have hh_tilde_up : h_tilde x < h_tilde u_up := by
      have h1 := hh_tilde_diff u_up hu_up_V hu_up_ne_x
      have h2 : 0 < (m_x x - m_x u_up) * (ρ u_up - ρ u₀) :=
        mul_pos (hmx_lt u_up hu_up_V hu_up_ne_x) (by linarith)
      linarith
    obtain ⟨F₀, hF₀_mem, hE₀_sub_F₀, c₀, hc₀_V, hc₀_F₀, hh_tilde_c₀⟩ :=
      hImpFacet E₀ hE₀_mem x hxV u₀ hu₀_V hx_E₀ hu₀_E₀ hu₀_ne_x.symm
        h_tilde hh_tilde_u₀ ⟨u_up, hu_up_V, hh_tilde_up⟩
    have hc₀_ne_x : c₀ ≠ x := fun heq => (ne_of_lt hh_tilde_c₀) (congr_arg h_tilde heq).symm
    have hρ_c₀_gt : ρ u₀ < ρ c₀ := by
      have h1 := hh_tilde_diff c₀ hc₀_V hc₀_ne_x
      have hpos := hmx_lt c₀ hc₀_V hc₀_ne_x
      have h2 : 0 < (m_x x - m_x c₀) * (ρ c₀ - ρ u₀) := by linarith
      nlinarith
    have hxc₀_edge := (hFacetProp F₀ hF₀_mem).1 x hxV c₀ hc₀_V (hE₀_sub_F₀ hx_E₀) hc₀_F₀ hc₀_ne_x.symm
    have hlc₀_gt : l x < l c₀ := by
      by_contra hle
      have hlt : l c₀ < l x :=
        lt_of_le_of_ne (not_lt.1 hle) (fun heq => hc₀_ne_x (hl_inj c₀ hc₀_V x hxV heq))
      have hc₀_in_U : c₀ ∈ U_down :=
        Finset.mem_filter.2 ⟨hc₀_V, hlt, convexHull ℝ ({x, c₀} : Set (Fin 3 → ℝ)),
          hxc₀_edge.1, subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp)⟩
      have hle_ρ := hρ_max c₀ hc₀_in_U
      linarith
    have hE₀_set : E₀.Nonempty ∧ IsExposed ℝ P E₀ ∧
        Module.finrank ℝ (affineSpan ℝ E₀).direction = 1 := by
      rw [← Finset.mem_coe, hℰ_coe] at hE₀_mem; exact hE₀_mem
    obtain ⟨a, b, ha, hb, hab, hE₀V, _⟩ := (hEdgePair hHull E₀ hE₀_set.2.1).1 ⟨hE₀_set.1, hE₀_set.2.2⟩
    have hx_ab : x = a ∨ x = b := by
      have hm : x ∈ E₀ ∩ V_set := ⟨hx_E₀, hxExp⟩
      rw [hE₀V] at hm; simpa using hm
    have hu₀_ab : u₀ = a ∨ u₀ = b := by
      have hu₀_exp : IsExposed ℝ P {u₀} := by rw [← Finset.mem_coe, hV_coe] at hu₀_V; exact hu₀_V
      have hm : u₀ ∈ E₀ ∩ V_set := ⟨hu₀_E₀, hu₀_exp⟩
      rw [hE₀V] at hm; simpa using hm
    have hE₀_in_ℰx : E₀ ∈ ℰ_x.filter (fun E => E ⊆ F₀) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hE₀_mem, hx_E₀, ?_⟩, hE₀_sub_F₀⟩
      intro w hwV hwE₀
      have hwExp : IsExposed ℝ P {w} := by rw [← Finset.mem_coe, hV_coe] at hwV; exact hwV
      have hm : w ∈ E₀ ∩ V_set := ⟨hwE₀, hwExp⟩
      rw [hE₀V] at hm
      rcases Set.mem_insert_iff.1 hm with rfl | hwb
      · rcases hx_ab with rfl | rfl
        · exact le_rfl
        · rcases hu₀_ab with rfl | rfl
          · exact le_of_lt hl_u₀_lt
          · exact False.elim (hu₀_ne_x rfl)
      · rw [Set.mem_singleton_iff.1 hwb]
        rcases hx_ab with rfl | rfl
        · rcases hu₀_ab with rfl | rfl
          · exact False.elim (hu₀_ne_x rfl)
          · exact le_of_lt hl_u₀_lt
        · exact le_rfl
    have hcard_pos : 1 ≤ (ℰ_x.filter (fun E => E ⊆ F₀)).card :=
      Finset.card_pos.2 ⟨E₀, hE₀_in_ℰx⟩
    have hcard_le2 : (ℰ_x.filter (fun E => E ⊆ F₀)).card ≤ 2 :=
      ((hFacetProp F₀ hF₀_mem).2 l x hxV).1
    have hcard_ne2 : (ℰ_x.filter (fun E => E ⊆ F₀)).card ≠ 2 := by
      intro hcard2
      have h_all_le := (((hFacetProp F₀ hF₀_mem).2 l x hxV).2).1 hcard2
      have h1 := h_all_le.2 c₀ hc₀_V hc₀_F₀
      linarith
    have hF₀_cross : F₀ ∈ ℱ_cross :=
      Finset.mem_filter.2 ⟨hF₀_mem, by omega⟩
    exact Finset.card_pos.2 ⟨F₀, hF₀_cross⟩
  have hc_le_two : ℱ_cross.card ≤ 2 := by
    let V_minus : Finset (Fin 3 → ℝ) := V.filter (fun u => l u < l x)
    let V_plus : Finset (Fin 3 → ℝ) := V.filter (fun v => l x < l v)
    let Pi_set : Finset ((Fin 3 → ℝ) × (Fin 3 → ℝ)) := V_minus ×ˢ V_plus
    have hu_dn_minus : u_dn ∈ V_minus := Finset.mem_filter.2 ⟨hu_dn_V, hl_dn⟩
    have hu_up_plus : u_up ∈ V_plus := Finset.mem_filter.2 ⟨hu_up_V, hl_up⟩
    have hPi_set_ne : Pi_set.Nonempty := ⟨(u_dn, u_up), Finset.mem_product.2 ⟨hu_dn_minus, hu_up_plus⟩⟩
    have hPi_set_card_ge2 : 2 ≤ Pi_set.card := by
      have hsub_er : V.erase x ⊆ V_minus ∪ V_plus := by
        intro w hw
        have hwx : w ≠ x := (Finset.mem_erase.1 hw).1
        have hwV : w ∈ V := (Finset.mem_erase.1 hw).2
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases lt_trichotomy (l w) (l x) with hlt | heq | hgt
        · exact Or.inl ⟨hwV, hlt⟩
        · exact False.elim (hwx (hl_inj w hwV x hxV heq))
        · exact Or.inr ⟨hwV, hgt⟩
      have hcard_er : 3 ≤ (V.erase x).card := by
        rw [Finset.card_erase_of_mem hxV]; omega
      have hcard_un : (V.erase x).card ≤ V_minus.card + V_plus.card :=
        (Finset.card_le_card hsub_er).trans (Finset.card_union_le V_minus V_plus)
      have hm_ge1 : 1 ≤ V_minus.card := Finset.card_pos.2 ⟨u_dn, hu_dn_minus⟩
      have hp_ge1 : 1 ≤ V_plus.card := Finset.card_pos.2 ⟨u_up, hu_up_plus⟩
      dsimp [Pi_set]
      rw [Finset.card_product]
      nlinarith
    let l_vec : Fin 3 → ℝ := fun i => l (Pi.single i 1)
    let m_vec : Fin 3 → ℝ := fun i => m_x (Pi.single i 1)
    have hl_dot : ∀ z : Fin 3 → ℝ, l z = dot3' l_vec z := fun z => dual_apply_fin_three l z
    have hm_dot : ∀ z : Fin 3 → ℝ, m_x z = dot3' m_vec z := fun z => dual_apply_fin_three m_x z
    have hl_pos : 0 < dot3' l_vec l_vec := by
      have hpos : 0 < l x - l u_dn := by linarith
      rw [hl_dot x, hl_dot u_dn] at hpos
      by_contra hle
      obtain ⟨hl0, hl1, hl2⟩ := dot3'_self_le_zero_imp l_vec (not_lt.1 hle)
      dsimp [dot3'] at hpos
      rw [hl0, hl1, hl2] at hpos
      linarith
    let m_perp : StrongDual ℝ (Fin 3 → ℝ) :=
      dot3' l_vec l_vec • m_x - dot3' m_vec l_vec • l
    let m_perp_vec : Fin 3 → ℝ := fun i => m_perp (Pi.single i 1)
    have hm_perp_dot : ∀ z : Fin 3 → ℝ, m_perp z = dot3' m_perp_vec z :=
      fun z => dual_apply_fin_three m_perp z
    have hm_perp_val : ∀ z : Fin 3 → ℝ,
        m_perp z = dot3' l_vec l_vec * m_x z - dot3' m_vec l_vec * l z :=
      fun _ => rfl
    have hm_perp_orth : dot3' m_perp_vec l_vec = 0 := by
      have h0 : m_perp_vec 0 = dot3' l_vec l_vec * m_vec 0 - dot3' m_vec l_vec * l_vec 0 := rfl
      have h1 : m_perp_vec 1 = dot3' l_vec l_vec * m_vec 1 - dot3' m_vec l_vec * l_vec 1 := rfl
      have h2 : m_perp_vec 2 = dot3' l_vec l_vec * m_vec 2 - dot3' m_vec l_vec * l_vec 2 := rfl
      dsimp [dot3']
      rw [h0, h1, h2]
      dsimp [dot3']
      ring
    have hPi_set_props : ∀ uv ∈ Pi_set,
        let cp := crossing_point l x uv.1 uv.2
        cp ∈ P ∧ l cp = l x ∧ 0 < m_perp x - m_perp cp ∧
        (∀ g : StrongDual ℝ (Fin 3 → ℝ), g uv.1 ≤ g x → g uv.2 ≤ g x →
          g cp ≤ g x ∧ (g cp = g x ↔ g uv.1 = g x ∧ g uv.2 = g x)) := by
      intro uv huv
      rcases Finset.mem_product.1 huv with ⟨hu_m, hv_p⟩
      rcases Finset.mem_filter.1 hu_m with ⟨huV, hu_lt⟩
      rcases Finset.mem_filter.1 hv_p with ⟨hvV, hv_gt⟩
      have huExp : IsExposed ℝ P {uv.1} := by rw [← Finset.mem_coe, hV_coe] at huV; exact huV
      have hvExp : IsExposed ℝ P {uv.2} := by rw [← Finset.mem_coe, hV_coe] at hvV; exact hvV
      have hu_ne : uv.1 ≠ x := fun heq => (ne_of_lt hu_lt) (congr_arg l heq)
      have hv_ne : uv.2 ≠ x := fun heq => (ne_of_gt hv_gt) (congr_arg l heq)
      obtain ⟨hcp_P, hl_cp, hm_cp, hg_cp⟩ :=
        crossing_point_props hP_conv l x uv.1 uv.2 (hV_sub_P huExp) (hV_sub_P hvExp) hu_lt hv_gt
      have hmx_cp : m_x (crossing_point l x uv.1 uv.2) < m_x x :=
        hm_cp m_x (by linarith [hmx_lt uv.1 huV hu_ne]) (by linarith [hmx_lt uv.2 hvV hv_ne])
      have hm_perp_pos : 0 < m_perp x - m_perp (crossing_point l x uv.1 uv.2) := by
        rw [hm_perp_val x, hm_perp_val (crossing_point l x uv.1 uv.2), hl_cp]
        have h1 : (dot3' l_vec l_vec * m_x x - dot3' m_vec l_vec * l x) -
            (dot3' l_vec l_vec * m_x (crossing_point l x uv.1 uv.2) - dot3' m_vec l_vec * l x) =
            dot3' l_vec l_vec * (m_x x - m_x (crossing_point l x uv.1 uv.2)) := by ring
        rw [h1]
        exact mul_pos hl_pos (by linarith)
      exact ⟨hcp_P, hl_cp, hm_perp_pos, hg_cp⟩
    have hm_perp_vec_pos : 0 < dot3' m_perp_vec m_perp_vec := by
      have hp0 := (hPi_set_props (u_dn, u_up) (Finset.mem_product.2 ⟨hu_dn_minus, hu_up_plus⟩)).2.2.1
      rw [hm_perp_dot x, hm_perp_dot (crossing_point l x u_dn u_up)] at hp0
      by_contra hle
      obtain ⟨h0, h1, h2⟩ := dot3'_self_le_zero_imp m_perp_vec (not_lt.1 hle)
      dsimp [dot3'] at hp0
      rw [h0, h1, h2] at hp0
      linarith
    let τ_vec : Fin 3 → ℝ := cross3 m_perp_vec l_vec
    let τ : StrongDual ℝ (Fin 3 → ℝ) :=
      τ_vec 0 • ContinuousLinearMap.proj 0 +
      τ_vec 1 • ContinuousLinearMap.proj 1 +
      τ_vec 2 • ContinuousLinearMap.proj 2
    have hτ_dot : ∀ z : Fin 3 → ℝ, τ z = dot3' τ_vec z := by
      intro z
      change τ_vec 0 * z 0 + τ_vec 1 * z 1 + τ_vec 2 * z 2 = dot3' τ_vec z
      rfl
    obtain ⟨_, _, hτ_norm⟩ := cross3_orthogonal_and_norm m_perp_vec l_vec hm_perp_orth
    have hτ_pos : 0 < dot3' τ_vec τ_vec := by
      rw [hτ_norm]
      exact mul_pos hm_perp_vec_pos hl_pos
    let m_pos : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ :=
      fun uv => m_perp x - m_perp (crossing_point l x uv.1 uv.2)
    let σ_pair : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ :=
      fun uv => (τ (crossing_point l x uv.1 uv.2) - τ x) / m_pos uv
    have hσ_pair_mul : ∀ uv ∈ Pi_set,
        τ (crossing_point l x uv.1 uv.2) - τ x = σ_pair uv * m_pos uv := by
      intro uv huv
      dsimp [σ_pair]
      exact (div_mul_cancel₀ _ (ne_of_gt (hPi_set_props uv huv).2.2.1)).symm
    obtain ⟨uv_max, huv_max, hσ_max⟩ := Pi_set.exists_max_image σ_pair hPi_set_ne
    obtain ⟨uv_min, huv_min, hσ_min⟩ := Pi_set.exists_min_image σ_pair hPi_set_ne
    let F_cand_max : Set (Fin 3 → ℝ) :=
      convexHull ℝ (({x, uv_max.1, uv_max.2} : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ))
    let F_cand_min : Set (Fin 3 → ℝ) :=
      convexHull ℝ (({x, uv_min.1, uv_min.2} : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ))
    have hsub_two : ℱ_cross ⊆ {F_cand_max, F_cand_min} := by
      intro F hF_cross
      rcases Finset.mem_filter.1 hF_cross with ⟨hF_mem, hF_card1⟩
      have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF_mem; exact hF_mem
      obtain ⟨hF_hull, hF_v_card3⟩ :=
        facet_filter_vertices_card_eq_three hP V hV_coe hP_eq_V hF_set
      obtain ⟨E₁, hE₁_in⟩ := Finset.card_pos.1 (by omega : 0 < (ℰ_x.filter (fun E => E ⊆ F)).card)
      rcases Finset.mem_filter.1 hE₁_in with ⟨hE₁_x, hE₁_sub_F⟩
      rcases Finset.mem_filter.1 hE₁_x with ⟨hE₁_mem, hx_E₁, hE₁_le⟩
      have hxF : x ∈ F := hE₁_sub_F hx_E₁
      have hE₁_set : E₁.Nonempty ∧ IsExposed ℝ P E₁ ∧
          Module.finrank ℝ (affineSpan ℝ E₁).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE₁_mem; exact hE₁_mem
      obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hE₁V, _⟩ :=
        (hEdgePair hHull E₁ hE₁_set.2.1).1 ⟨hE₁_set.1, hE₁_set.2.2⟩
      have hx_ab₁ : x = a₁ ∨ x = b₁ := by
        have hm : x ∈ E₁ ∩ V_set := ⟨hx_E₁, hxExp⟩
        rw [hE₁V] at hm; simpa using hm
      have hex_uF : ∃ u_F ∈ V, u_F ∈ F ∧ u_F ≠ x ∧ l u_F < l x := by
        rcases hx_ab₁ with rfl | rfl
        · have hb₁V : b₁ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb₁
          have hb₁E₁ : b₁ ∈ E₁ := by
            have hm : b₁ ∈ E₁ ∩ V_set := by rw [hE₁V]; simp
            exact hm.1
          have hlt : l b₁ < l x :=
            lt_of_le_of_ne (hE₁_le b₁ hb₁V hb₁E₁) (fun heq => hab₁.symm (hl_inj b₁ hb₁V x hxV heq))
          exact ⟨b₁, hb₁V, hE₁_sub_F hb₁E₁, hab₁.symm, hlt⟩
        · have ha₁V : a₁ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact ha₁
          have ha₁E₁ : a₁ ∈ E₁ := by
            have hm : a₁ ∈ E₁ ∩ V_set := by rw [hE₁V]; simp
            exact hm.1
          have hlt : l a₁ < l x :=
            lt_of_le_of_ne (hE₁_le a₁ ha₁V ha₁E₁) (fun heq => hab₁ (hl_inj a₁ ha₁V x hxV heq))
          exact ⟨a₁, ha₁V, hE₁_sub_F ha₁E₁, hab₁, hlt⟩
      rcases hex_uF with ⟨u_F, hu_F_V, hu_F_F, hu_F_ne_x, hl_uF_lt⟩
      have hex_vF : ∃ v_F ∈ V, v_F ∈ F ∧ v_F ≠ x ∧ v_F ≠ u_F := by
        by_contra hno
        have hsub_pair : V.filter (· ∈ F) ⊆ {x, u_F} := by
          intro w hw
          rcases Finset.mem_filter.1 hw with ⟨hwV, hwF⟩
          rw [Finset.mem_insert, Finset.mem_singleton]
          by_contra hne
          have hwx : w ≠ x := fun h => hne (Or.inl h)
          have hwu : w ≠ u_F := fun h => hne (Or.inr h)
          exact hno ⟨w, hwV, hwF, hwx, hwu⟩
        have hle := Finset.card_le_card hsub_pair
        rw [hF_v_card3, Finset.card_pair hu_F_ne_x.symm] at hle
        omega
      rcases hex_vF with ⟨v_F, hv_F_V, hv_F_F, hv_F_ne_x, hv_F_ne_uF⟩
      have hF_verts : V.filter (· ∈ F) = {x, u_F, v_F} :=
        finset_eq_triple_of_card_three hF_v_card3
          (Finset.mem_filter.2 ⟨hxV, hxF⟩)
          (Finset.mem_filter.2 ⟨hu_F_V, hu_F_F⟩)
          (Finset.mem_filter.2 ⟨hv_F_V, hv_F_F⟩)
          hu_F_ne_x.symm hv_F_ne_x hv_F_ne_uF
      have hl_vF_gt : l x < l v_F := by
        by_contra hle
        have h_all_le : ∀ w ∈ V, w ∈ F → l w ≤ l x := by
          intro w hwV hwF
          have hw_in : w ∈ V.filter (· ∈ F) := Finset.mem_filter.2 ⟨hwV, hwF⟩
          rw [hF_verts] at hw_in
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw_in
          rcases hw_in with rfl | rfl | rfl
          · exact le_rfl
          · exact le_of_lt hl_uF_lt
          · exact not_lt.1 hle
        have hcard2 : (ℰ_x.filter (fun E => E ⊆ F)).card = 2 :=
          (((hFacetProp F hF_mem).2 l x hxV).2).2 ⟨hxF, h_all_le⟩
        omega
      have huv_F_mem : (u_F, v_F) ∈ Pi_set :=
        Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hu_F_V, hl_uF_lt⟩,
          Finset.mem_filter.2 ⟨hv_F_V, hl_vF_gt⟩⟩
      have hPi_set_er_ne : (Pi_set.erase (u_F, v_F)).Nonempty := by
        apply Finset.card_pos.1
        rw [Finset.card_erase_of_mem huv_F_mem]
        omega
      rcases hPi_set_er_ne with ⟨uv_alt, huv_alt_er⟩
      have huv_alt_ne : uv_alt ≠ (u_F, v_F) := (Finset.mem_erase.1 huv_alt_er).1
      have huv_alt_mem : uv_alt ∈ Pi_set := (Finset.mem_erase.1 huv_alt_er).2
      obtain ⟨g, hFg⟩ := hF_set.2.1 hF_set.1
      have hx_g : x ∈ {z ∈ P | ∀ y ∈ P, g y ≤ g z} := hFg ▸ hxF
      have huF_g : u_F ∈ {z ∈ P | ∀ y ∈ P, g y ≤ g z} := hFg ▸ hu_F_F
      have hvF_g : v_F ∈ {z ∈ P | ∀ y ∈ P, g y ≤ g z} := hFg ▸ hv_F_F
      have hg_le_V : ∀ w ∈ V, g w ≤ g x := by
        intro w hwV
        have hwExp : IsExposed ℝ P {w} := by rw [← Finset.mem_coe, hV_coe] at hwV; exact hwV
        exact hx_g.2 w (hV_sub_P hwExp)
      have hg_uF_eq : g u_F = g x := le_antisymm (hg_le_V u_F hu_F_V) (huF_g.2 x hxP)
      have hg_vF_eq : g v_F = g x := le_antisymm (hg_le_V v_F hv_F_V) (hvF_g.2 x hxP)
      let g_diff : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ :=
        fun uv => g (crossing_point l x uv.1 uv.2) - g x
      have hg_zero : g_diff (u_F, v_F) = 0 := by
        have hcp := (hPi_set_props (u_F, v_F) huv_F_mem).2.2.2 g
          (hg_le_V u_F hu_F_V) (hg_le_V v_F hv_F_V)
        have heq := hcp.2.2 ⟨hg_uF_eq, hg_vF_eq⟩
        dsimp [g_diff]
        linarith
      have hg_neg : ∀ uv ∈ Pi_set, uv ≠ (u_F, v_F) → g_diff uv < 0 := by
        intro uv huv hne
        rcases Finset.mem_product.1 huv with ⟨hu_m, hv_p⟩
        rcases Finset.mem_filter.1 hu_m with ⟨huV, hu_lt⟩
        rcases Finset.mem_filter.1 hv_p with ⟨hvV, hv_gt⟩
        have hcp := (hPi_set_props uv huv).2.2.2 g (hg_le_V uv.1 huV) (hg_le_V uv.2 hvV)
        dsimp [g_diff]
        refine sub_neg.2 (lt_of_le_of_ne hcp.1 (fun heq => hne ?_))
        obtain ⟨hgu_eq, hgv_eq⟩ := hcp.2.1 heq
        have huExp : IsExposed ℝ P {uv.1} := by rw [← Finset.mem_coe, hV_coe] at huV; exact huV
        have hvExp : IsExposed ℝ P {uv.2} := by rw [← Finset.mem_coe, hV_coe] at hvV; exact hvV
        have huF_in : uv.1 ∈ F := by
          rw [hFg]; exact ⟨hV_sub_P huExp, fun y hy => by linarith [hx_g.2 y hy]⟩
        have hvF_in : uv.2 ∈ F := by
          rw [hFg]; exact ⟨hV_sub_P hvExp, fun y hy => by linarith [hx_g.2 y hy]⟩
        have hu_mem_filt : uv.1 ∈ V.filter (· ∈ F) := Finset.mem_filter.2 ⟨huV, huF_in⟩
        have hv_mem_filt : uv.2 ∈ V.filter (· ∈ F) := Finset.mem_filter.2 ⟨hvV, hvF_in⟩
        rw [hF_verts] at hu_mem_filt hv_mem_filt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem_filt hv_mem_filt
        have hu_eq : uv.1 = u_F := by
          rcases hu_mem_filt with h1 | h1 | h1
          · exfalso; rw [h1] at hu_lt; exact lt_irrefl _ hu_lt
          · exact h1
          · exfalso; rw [h1] at hu_lt; linarith
        have hv_eq : uv.2 = v_F := by
          rcases hv_mem_filt with h2 | h2 | h2
          · exfalso; rw [h2] at hv_gt; exact lt_irrefl _ hv_gt
          · exfalso; rw [h2] at hv_gt; linarith
          · exact h2
        exact Prod.ext hu_eq hv_eq
      let g_vec : Fin 3 → ℝ := fun i => g (Pi.single i 1)
      have hg_dot : ∀ z : Fin 3 → ℝ, g z = dot3' g_vec z := fun z => dual_apply_fin_three g z
      have hgram_pair : ∀ uv ∈ Pi_set,
          dot3' τ_vec τ_vec * g_diff uv =
            m_pos uv * (-dot3' l_vec l_vec * dot3' m_perp_vec g_vec +
              dot3' τ_vec g_vec * σ_pair uv) := by
        intro uv huv
        let d : Fin 3 → ℝ := crossing_point l x uv.1 uv.2 - x
        have hl_cp := (hPi_set_props uv huv).2.1
        have hdl : dot3' d l_vec = 0 := by
          have h1 : l d = dot3' l_vec d := hl_dot d
          dsimp [d] at h1
          rw [map_sub, hl_cp, sub_self] at h1
          dsimp [dot3', d] at h1 ⊢
          linarith
        have hgram := cross3_gram_identity m_perp_vec l_vec d g_vec hm_perp_orth hdl
        have hdg : dot3' d g_vec = g_diff uv := by
          have h1 : g d = dot3' g_vec d := hg_dot d
          dsimp [d, g_diff] at h1 ⊢
          rw [map_sub] at h1
          dsimp [dot3'] at h1 ⊢
          linarith
        have hdm : dot3' d m_perp_vec = -m_pos uv := by
          have h1 : m_perp d = dot3' m_perp_vec d := hm_perp_dot d
          dsimp [d, m_pos] at h1 ⊢
          rw [map_sub] at h1
          dsimp [dot3'] at h1 ⊢
          linarith
        have hdτ : dot3' d τ_vec = σ_pair uv * m_pos uv := by
          have h1 : τ d = dot3' τ_vec d := hτ_dot d
          dsimp [d] at h1
          rw [map_sub, hσ_pair_mul uv huv] at h1
          dsimp [dot3', d] at h1 ⊢
          linarith
        dsimp [τ_vec] at hdτ ⊢
        rw [hdg, hdm, hdτ] at hgram
        linarith
      rcases pair_eq_max_or_min_of_strict_gram hτ_pos
          (fun uv huv => (hPi_set_props uv huv).2.2.1)
          huv_F_mem huv_min huv_max huv_alt_mem huv_alt_ne
          (hσ_min (u_F, v_F) huv_F_mem) (hσ_max (u_F, v_F) huv_F_mem)
          hg_zero hg_neg hgram_pair with heq_max | heq_min
      · rw [Finset.mem_insert, Finset.mem_singleton]
        left
        have hu_eq : u_F = uv_max.1 := congr_arg Prod.fst heq_max
        have hv_eq : v_F = uv_max.2 := congr_arg Prod.snd heq_max
        rw [hF_hull, hF_verts, hu_eq, hv_eq]
      · rw [Finset.mem_insert, Finset.mem_singleton]
        right
        have hu_eq : u_F = uv_min.1 := congr_arg Prod.fst heq_min
        have hv_eq : v_F = uv_min.2 := congr_arg Prod.snd heq_min
        rw [hF_hull, hF_verts, hu_eq, hv_eq]
    calc ℱ_cross.card
        ≤ ({F_cand_max, F_cand_min} : Finset (Set (Fin 3 → ℝ))).card :=
          Finset.card_le_card hsub_two
      _ ≤ (({F_cand_min} : Finset (Set (Fin 3 → ℝ)))).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]
  omega

end
