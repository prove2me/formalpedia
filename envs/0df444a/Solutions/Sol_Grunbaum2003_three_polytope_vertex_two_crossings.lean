-- Prove2me | solution 1 for Grunbaum2003.three_polytope_vertex_two_crossings
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:52:54.5592+00:00
-- url     : https://prove2.me/submissions/03bc5bd3-af71-4636-8c2b-c2eb11291b4e

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
import Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

lemma one_lt_finrank_vectorSpan_of_three_points {F : Set (Fin 3 → ℝ)}
    {a b c : Fin 3 → ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hab : a ≠ b)
    (m : StrongDual ℝ (Fin 3 → ℝ)) (hm_ab : m b = m a) (hm_ca : m c < m a) :
    1 < Module.finrank ℝ (vectorSpan ℝ F) := by
  have hab_sub : ({a, b} : Set (Fin 3 → ℝ)) ⊆ F := by
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hxb
    · exact ha
    · rw [Set.mem_singleton_iff.1 hxb]; exact hb
  have hspan_le : Submodule.span ℝ {a -ᵥ b} ≤ vectorSpan ℝ F := by
    rw [← vectorSpan_pair ℝ a b]
    exact vectorSpan_mono ℝ hab_sub
  have hca_dir : c -ᵥ a ∈ vectorSpan ℝ F := vsub_mem_vectorSpan ℝ hc ha
  have hca_not_span : c -ᵥ a ∉ Submodule.span ℝ {a -ᵥ b} := by
    intro hmem
    rcases Submodule.mem_span_singleton.1 hmem with ⟨t, ht⟩
    have hm_ca_eq : m (c - a) = t * m (a - b) := by
      have h1 := congr_arg m ht
      simpa [vsub_eq_sub, map_smul, smul_eq_mul] using h1.symm
    rw [map_sub, map_sub, hm_ab, sub_self, mul_zero] at hm_ca_eq
    linarith
  have h1 : Module.finrank ℝ (Submodule.span ℝ {a -ᵥ b}) = 1 :=
    finrank_span_singleton (vsub_ne_zero.2 hab)
  have hle := Submodule.finrank_mono hspan_le
  have hne : Module.finrank ℝ (Submodule.span ℝ {a -ᵥ b}) ≠ Module.finrank ℝ (vectorSpan ℝ F) := by
    intro heq
    have hsub_eq := Submodule.eq_of_le_of_finrank_le hspan_le (le_of_eq heq.symm)
    exact hca_not_span (hsub_eq.symm ▸ hca_dir)
  omega

lemma finrank_two_of_three_points_and_strict_Dual {F : Set (Fin 3 → ℝ)}
    {a b c w_out : Fin 3 → ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hab : a ≠ b)
    (m : StrongDual ℝ (Fin 3 → ℝ)) (hm_ab : m b = m a) (hm_ca : m c < m a)
    (g : StrongDual ℝ (Fin 3 → ℝ)) (hg_F : ∀ x ∈ F, g x = g a) (hg_out : g w_out < g a) :
    Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
  rw [direction_affineSpan]
  have h1_lt := one_lt_finrank_vectorSpan_of_three_points ha hb hc hab m hm_ab hm_ca
  have hdir_le_ker : vectorSpan ℝ F ≤ LinearMap.ker g.toLinearMap := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      vsub_eq_sub, map_sub]
    rw [hg_F x hx, hg_F y hy, sub_self]
  have h_le2 : Module.finrank ℝ (vectorSpan ℝ F) ≤ 2 := by
    have h_le : Module.finrank ℝ (vectorSpan ℝ F) ≤
        Module.finrank ℝ (LinearMap.ker g.toLinearMap) :=
      Submodule.finrank_mono hdir_le_ker
    have htop_dim : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) = 3 := by
      rw [finrank_top, Module.finrank_fin_fun]
    have hker_le_top : Module.finrank ℝ (LinearMap.ker g.toLinearMap) ≤
        Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) :=
      Submodule.finrank_mono le_top
    have hker_ne_top : Module.finrank ℝ (LinearMap.ker g.toLinearMap) ≠
        Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) := by
      intro heq
      have htop_eq := Submodule.eq_of_le_of_finrank_le le_top (le_of_eq heq.symm)
      have hmem : w_out - a ∈ LinearMap.ker g.toLinearMap := by rw [htop_eq]; trivial
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub] at hmem
      linarith
    omega
  omega

lemma facet_eq_of_three_points {P F₁ F₂ : Set (Fin 3 → ℝ)}
    (hF₁_exp : IsExposed ℝ P F₁) (hF₂_exp : IsExposed ℝ P F₂)
    (hF₁_dim : Module.finrank ℝ (affineSpan ℝ F₁).direction = 2)
    (hF₂_dim : Module.finrank ℝ (affineSpan ℝ F₂).direction = 2)
    {a b c : Fin 3 → ℝ}
    (ha₁ : a ∈ F₁) (hb₁ : b ∈ F₁) (hc₁ : c ∈ F₁)
    (ha₂ : a ∈ F₂) (hb₂ : b ∈ F₂) (hc₂ : c ∈ F₂)
    (hab : a ≠ b)
    (m : StrongDual ℝ (Fin 3 → ℝ)) (hm_ab : m b = m a) (hm_ca : m c < m a) :
    F₁ = F₂ := by
  let S : Set (Fin 3 → ℝ) := {a, b, c}
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hcS : c ∈ S := by simp [S]
  have h1_lt : 1 < Module.finrank ℝ (vectorSpan ℝ S) :=
    one_lt_finrank_vectorSpan_of_three_points haS hbS hcS hab m hm_ab hm_ca
  have hS_sub₁ : S ⊆ F₁ := by
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    · exact ha₁
    · rcases Set.mem_insert_iff.1 hx' with rfl | hx''
      · exact hb₁
      · rw [Set.mem_singleton_iff.1 hx'']; exact hc₁
  have hS_sub₂ : S ⊆ F₂ := by
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    · exact ha₂
    · rcases Set.mem_insert_iff.1 hx' with rfl | hx''
      · exact hb₂
      · rw [Set.mem_singleton_iff.1 hx'']; exact hc₂
  rw [direction_affineSpan] at hF₁_dim hF₂_dim
  have hvs₁ : vectorSpan ℝ S = vectorSpan ℝ F₁ :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hS_sub₁) (by omega)
  have hvs₂ : vectorSpan ℝ S = vectorSpan ℝ F₂ :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hS_sub₂) (by omega)
  have hvs_eq : vectorSpan ℝ F₁ = vectorSpan ℝ F₂ := hvs₁.symm.trans hvs₂
  have h_sub_of_vs : ∀ {G H : Set (Fin 3 → ℝ)}, IsExposed ℝ P G → IsExposed ℝ P H →
      a ∈ G → a ∈ H → vectorSpan ℝ G = vectorSpan ℝ H → H ⊆ G := by
    intro G H hG hH haG haH hvs y hyH
    obtain ⟨g, hGg⟩ := hG ⟨a, haG⟩
    have ha_mem : a ∈ {x ∈ P | ∀ z ∈ P, g z ≤ g x} := hGg ▸ haG
    have hconst_G : ∀ x ∈ G, g x = g a := by
      intro x hxG
      have hx_mem : x ∈ {z ∈ P | ∀ w ∈ P, g w ≤ g z} := hGg ▸ hxG
      exact le_antisymm (ha_mem.2 x hx_mem.1) (hx_mem.2 a ha_mem.1)
    have hker : vectorSpan ℝ G ≤ LinearMap.ker g.toLinearMap := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro v ⟨x, hx, z, hz, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        vsub_eq_sub, map_sub]
      rw [hconst_G x hx, hconst_G z hz, sub_self]
    have hy_mem_vs : y -ᵥ a ∈ vectorSpan ℝ G := by
      rw [hvs]
      exact vsub_mem_vectorSpan ℝ hyH haH
    have hy_ker := hker hy_mem_vs
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] at hy_ker
    rw [hGg]
    exact ⟨hH.subset hyH, fun z hz => by linarith [ha_mem.2 z hz]⟩
  exact Set.Subset.antisymm
    (h_sub_of_vs hF₂_exp hF₁_exp ha₂ ha₁ hvs_eq.symm)
    (h_sub_of_vs hF₁_exp hF₂_exp ha₁ ha₂ hvs_eq)

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

theorem face_eq_of_le_of_finrank_le {n : ℕ} {P : Set (Fin n → ℝ)} (G F : PolytopeFace P)
    (hG : G.val.Nonempty) (hle : G ≤ F)
    (hdim : Module.finrank ℝ (affineSpan ℝ F.val).direction ≤
      Module.finrank ℝ (affineSpan ℝ G.val).direction) : G = F := by
  obtain ⟨g, hg⟩ := hG
  obtain ⟨l, hl⟩ := G.property ⟨g, hg⟩
  rw [direction_affineSpan, direction_affineSpan] at hdim
  have hgG := hg
  rw [hl] at hgG
  have hconst : ∀ x ∈ G.val, l x = l g := by
    intro x hx
    rw [hl] at hx
    exact le_antisymm (hgG.2 x hx.1) (hx.2 g hgG.1)
  have hker : vectorSpan ℝ G.val ≤ LinearMap.ker (l : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp [hconst a ha, hconst b hb]
  have hspan : vectorSpan ℝ G.val = vectorSpan ℝ F.val :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hle) hdim
  have hFconst : ∀ y ∈ F.val, l y = l g := by
    intro y hy
    have hmem : y -ᵥ g ∈ vectorSpan ℝ F.val := vsub_mem_vectorSpan ℝ hy (hle hg)
    rw [← hspan] at hmem
    have := hker hmem
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] at this
    linarith
  apply le_antisymm hle
  intro y hy
  have hyP : y ∈ P := F.property.subset hy
  rw [hl]
  refine ⟨hyP, fun z hz => ?_⟩
  rw [hFconst y hy]
  exact hgG.2 z hz

theorem exists_exposed_vertex_in_face {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (F : PolytopeFace P) (hF : F.val.Nonempty) :
    ∃ v ∈ F.val, IsExposed ℝ P {v} := by
  have hHull := (polytope_face_eq_convexHull_exposed_vertices n P hP).2 F
  have h_inter : (F.val ∩ {x : Fin n → ℝ | IsExposed ℝ P {x}}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, convexHull_empty] at hHull
    rw [hHull] at hF
    exact Set.not_nonempty_empty hF
  rcases h_inter with ⟨v, hvF, hvExp⟩
  exact ⟨v, hvF, hvExp⟩

theorem exists_improving_dual_of_finrank_lt {n : ℕ} {P : Set (Fin n → ℝ)}
    (G K : PolytopeFace P) (v : Fin n → ℝ) (hvG : v ∈ G.val)
    (hlt : Module.finrank ℝ (affineSpan ℝ G.val).direction <
      Module.finrank ℝ (affineSpan ℝ K.val).direction) :
    ∃ g : StrongDual ℝ (Fin n → ℝ),
      (∀ x ∈ G.val, g x = g v) ∧ (∃ z ∈ K.val, (-g) v < (-g) z) := by
  have hnot_sub : ¬ (K.val ⊆ G.val) := by
    intro hsub
    have hle_dim : Module.finrank ℝ (affineSpan ℝ K.val).direction ≤
        Module.finrank ℝ (affineSpan ℝ G.val).direction := by
      rw [direction_affineSpan, direction_affineSpan]
      exact Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    omega
  obtain ⟨z, hzK, hzG⟩ := Set.not_subset.1 hnot_sub
  obtain ⟨g, hGg⟩ := G.property ⟨v, hvG⟩
  have hv_mem : v ∈ {w ∈ P | ∀ y ∈ P, g y ≤ g w} := hGg ▸ hvG
  have hconst : ∀ x ∈ G.val, g x = g v := by
    intro x hx
    have hx_mem : x ∈ {w ∈ P | ∀ y ∈ P, g y ≤ g w} := hGg ▸ hx
    exact le_antisymm (hv_mem.2 x hx_mem.1) (hx_mem.2 v hv_mem.1)
  have hzP : z ∈ P := K.property.subset hzK
  have hgz_lt : g z < g v := by
    refine lt_of_le_of_ne (hv_mem.2 z hzP) (fun heq => hzG ?_)
    rw [hGg]
    exact ⟨hzP, fun y hy => by linarith [hv_mem.2 y hy]⟩
  refine ⟨g, hconst, z, hzK, ?_⟩
  change -g v < -g z
  linarith

def botSkeletonFace (P : Set (Fin 3 → ℝ)) (k : ℕ) : SkeletonFace P k :=
  ⟨⟨∅, isExposed_empty⟩, Or.inl rfl⟩

def atomSkeletonFace (P : Set (Fin 3 → ℝ)) (k : ℕ)
    (v : Fin 3 → ℝ) (hv : IsExposed ℝ P {v}) : SkeletonFace P k :=
  ⟨⟨{v}, hv⟩, Or.inr (by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k)⟩

theorem isBot_iff {P : Set (Fin 3 → ℝ)}
    (B : SkeletonFace P 1) :
    (∀ X : SkeletonFace P 1, B ≤ X) ↔ B = botSkeletonFace P 1 := by
  constructor
  · intro hAll
    apply Subtype.ext
    apply Subtype.ext
    change B.val.val = ∅
    by_contra hne
    rcases Set.nonempty_iff_ne_empty.2 hne with ⟨x, hx⟩
    exact hAll (botSkeletonFace P 1) hx
  · rintro rfl X
    exact Set.empty_subset _

theorem isAtom_iff {P : Set (Fin 3 → ℝ)} (hP : IsDPolytope P)
    (A : SkeletonFace P 1) :
    (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
      ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) ↔
    ∃ (v : Fin 3 → ℝ) (hv : IsExposed ℝ P {v}), A = atomSkeletonFace P 1 v hv := by
  simp only [isBot_iff]
  constructor
  · rintro ⟨hneBot, hMin⟩
    have hAne : A.val.val.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hEmpty
      apply hneBot
      exact Subtype.ext (Subtype.ext hEmpty)
    obtain ⟨v, hvA, hvExp⟩ := exists_exposed_vertex_in_face hP A.val hAne
    refine ⟨v, hvExp, ?_⟩
    let V : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
    have hVA : V ≤ A := Set.singleton_subset_iff.2 hvA
    rcases eq_or_lt_of_le hVA with hEq | hLt
    · exact hEq.symm
    · have hVbot := hMin V hLt
      have hv_empty : v ∈ (∅ : Set (Fin 3 → ℝ)) := by
        change v ∈ (botSkeletonFace P 1).val.val
        rw [← hVbot]
        exact Set.mem_singleton v
      exact False.elim hv_empty
  · rintro ⟨v, hvExp, rfl⟩
    refine ⟨?_, ?_⟩
    · intro hEq
      have hv_empty : v ∈ (∅ : Set (Fin 3 → ℝ)) := by
        change v ∈ (botSkeletonFace P 1).val.val
        rw [← hEq]
        exact Set.mem_singleton v
      exact hv_empty
    · intro X hXA
      have hXsub : X.val.val ⊆ {v} := hXA.1
      rcases Set.subset_singleton_iff_eq.1 hXsub with hEmpty | hSing
      · exact Subtype.ext (Subtype.ext hEmpty)
      · exfalso
        apply hXA.2
        change {v} ⊆ X.val.val
        rw [hSing]

theorem isEdge_iff (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (E : SkeletonFace P 1) :
    (∀ X : SkeletonFace P 1, E ≤ X → X = E) ↔
    (E.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 1) := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ P).direction = 3 := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  have hPne : P.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, direction_affineSpan, vectorSpan_empty, finrank_bot] at hTop_dim
    omega
  constructor
  · intro hMax
    have hEne : E.val.val.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      obtain ⟨v, _, hvExp⟩ := exists_exposed_vertex_in_face hP TopP hPne
      let U : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
      have hEU : E ≤ U := by
        change E.val.val ⊆ {v}
        rw [hemp]
        exact Set.empty_subset _
      have hEq := hMax U hEU
      have hv_in : v ∈ E.val.val := by
        rw [← hEq]
        exact Set.mem_singleton v
      rw [hemp] at hv_in
      exact hv_in
    refine ⟨hEne, ?_⟩
    rcases E.property with hEmpty | hEle
    · rw [hEmpty] at hEne
      exact False.elim (Set.not_nonempty_empty hEne)
    · by_contra hne1
      have h0 : Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 0 := by omega
      obtain ⟨v, hvE, hvExp⟩ := exists_exposed_vertex_in_face hP E.val hEne
      let V : PolytopeFace P := ⟨{v}, hvExp⟩
      have hV_eq : V = E.val := by
        apply face_eq_of_le_of_finrank_le V E.val (Set.singleton_nonempty v)
          (Set.singleton_subset_iff.2 hvE)
        rw [h0]
        exact Nat.zero_le _
      obtain ⟨g, _, hex_z⟩ := exists_improving_dual_of_finrank_lt E.val TopP v hvE (by
        change Module.finrank ℝ (affineSpan ℝ E.val.val).direction <
          Module.finrank ℝ (affineSpan ℝ P).direction
        omega)
      obtain ⟨G', _, hG'ne, hG'1, _, _, hvG', _, _⟩ :=
        improving_edge_and_global_facet_from_ridge_pairs.1 hP TopP v hvExp (E.val.property.subset hvE) (-g) hex_z
      let U : SkeletonFace P 1 := ⟨G', Or.inr (by omega)⟩
      have hEU : E ≤ U := by
        change E.val.val ⊆ G'.val
        have hVE : E.val.val = {v} := congrArg Subtype.val hV_eq.symm
        rw [hVE]
        exact Set.singleton_subset_iff.2 hvG'
      have hEq := hMax U hEU
      have hDimEq : Module.finrank ℝ (affineSpan ℝ G'.val).direction =
          Module.finrank ℝ (affineSpan ℝ E.val.val).direction := by
        rw [congrArg (fun S : SkeletonFace P 1 => S.val.val) hEq]
      omega
  · rintro ⟨hEne, hE1⟩ X hEX
    have hXne : X.val.val.Nonempty := hEne.mono hEX
    rcases X.property with hEmpty | hXle
    · rw [hEmpty] at hXne
      exact False.elim (Set.not_nonempty_empty hXne)
    · have hEq : E.val = X.val :=
        face_eq_of_le_of_finrank_le E.val X.val hEne hEX (by omega)
      exact Subtype.ext hEq.symm

lemma facet_vertex_two_edges_and_degree {P : Set (Fin 3 → ℝ)}
    (hP : IsDPolytope P)
    (V : Finset (Fin 3 → ℝ))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (ℰ : Finset (Set (Fin 3 → ℝ)))
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    {F : Set (Fin 3 → ℝ)}
    (hF : F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    (∀ x ∈ V, x ∈ F →
      ∃ E₁ E₂ : Set (Fin 3 → ℝ),
        E₁ ∈ ℰ ∧ E₂ ∈ ℰ ∧ E₁ ≠ E₂ ∧ x ∈ E₁ ∧ x ∈ E₂ ∧ E₁ ⊆ F ∧ E₂ ⊆ F ∧
        ℰ.filter (fun E => x ∈ E ∧ E ⊆ F) = {E₁, E₂}) ∧
    ∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
      let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
      (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
      ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
        (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)) := by
  have hCycle := three_polytope_facet_is_induced_nonseparating_cycle P hP
    ⟨F, hF.2.1⟩ ⟨hF.1, hF.2.2⟩
  have hTwoEdges : ∀ x ∈ V, x ∈ F →
      ∃ E₁ E₂ : Set (Fin 3 → ℝ),
        E₁ ∈ ℰ ∧ E₂ ∈ ℰ ∧ E₁ ≠ E₂ ∧ x ∈ E₁ ∧ x ∈ E₂ ∧ E₁ ⊆ F ∧ E₂ ⊆ F ∧
        ℰ.filter (fun E => x ∈ E ∧ E ⊆ F) = {E₁, E₂} := by
    intro x hxV hxF
    have hxExp : IsExposed ℝ P {x} := by
      change x ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
      rw [← hV_coe]; exact hxV
    let A : SkeletonFace P 1 := atomSkeletonFace P 1 x hxExp
    have hA_atom : ¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y :=
      (isAtom_iff hP A).2 ⟨x, hxExp, rfl⟩
    have hA_C : A.val ≤ ⟨F, hF.2.1⟩ := Set.singleton_subset_iff.2 hxF
    obtain ⟨E₁, E₂, hE₁_edge, hE₂_edge, hE₁_F, hE₂_F, hE₁₂_ne, hAE₁, hAE₂, hUniq⟩ :=
      hCycle.2.1.2 A hA_atom hA_C
    have hE₁_dim := (isEdge_iff P hP E₁).1 hE₁_edge
    have hE₂_dim := (isEdge_iff P hP E₂).1 hE₂_edge
    have hE₁_mem : E₁.val.val ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hE₁_dim.1, E₁.val.property, hE₁_dim.2⟩
    have hE₂_mem : E₂.val.val ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hE₂_dim.1, E₂.val.property, hE₂_dim.2⟩
    have hE₁₂_val_ne : E₁.val.val ≠ E₂.val.val := by
      intro heq
      exact hE₁₂_ne (Subtype.ext (Subtype.ext heq))
    have hxE₁ : x ∈ E₁.val.val := hAE₁ (Set.mem_singleton x)
    have hxE₂ : x ∈ E₂.val.val := hAE₂ (Set.mem_singleton x)
    refine ⟨E₁.val.val, E₂.val.val, hE₁_mem, hE₂_mem, hE₁₂_val_ne, hxE₁, hxE₂, hE₁_F, hE₂_F, ?_⟩
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hS_mem, hxS, hSF⟩
      have hS_set : S.Nonempty ∧ IsExposed ℝ P S ∧
          Module.finrank ℝ (affineSpan ℝ S).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hS_mem; exact hS_mem
      let ES : SkeletonFace P 1 := ⟨⟨S, hS_set.2.1⟩, Or.inr (le_of_eq hS_set.2.2)⟩
      have hES_edge : ∀ X : SkeletonFace P 1, ES ≤ X → X = ES :=
        (isEdge_iff P hP ES).2 ⟨hS_set.1, hS_set.2.2⟩
      have hAES : A ≤ ES := Set.singleton_subset_iff.2 hxS
      rcases hUniq ES hES_edge hSF hAES with h1 | h2
      · exact Or.inl (congrArg (fun T : SkeletonFace P 1 => T.val.val) h1)
      · exact Or.inr (congrArg (fun T : SkeletonFace P 1 => T.val.val) h2)
    · rintro (rfl | rfl)
      · exact ⟨hE₁_mem, hxE₁, hE₁_F⟩
      · exact ⟨hE₂_mem, hxE₂, hE₂_F⟩
  refine ⟨hTwoEdges, fun l x hxV => ?_⟩
  intro ℰ_x
  by_cases hxF : x ∈ F
  · obtain ⟨E₁, E₂, hE₁_mem, hE₂_mem, hE₁₂_ne, hxE₁, hxE₂, hE₁_F, hE₂_F, hfilt_F⟩ :=
      hTwoEdges x hxV hxF
    have hsub : ℰ_x.filter (fun E => E ⊆ F) ⊆ {E₁, E₂} := by
      rw [← hfilt_F]
      intro E hE
      simp only [Finset.mem_filter, ℰ_x] at hE ⊢
      exact ⟨hE.1.1, hE.1.2.1, hE.2⟩
    have hcard_le2 : (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 := by
      calc (ℰ_x.filter (fun E => E ⊆ F)).card
          ≤ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))).card := Finset.card_le_card hsub
        _ = 2 := Finset.card_pair hE₁₂_ne
    refine ⟨hcard_le2, ?_⟩
    constructor
    · intro hcard2
      have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hE₁₂_ne, hcard2])
      refine ⟨hxF, fun w hwV hwF => ?_⟩
      by_contra hnot_le
      have hlt : l x < l w := lt_of_not_ge hnot_le
      have hxExp : IsExposed ℝ P {x} := by
        change x ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
        rw [← hV_coe]; exact hxV
      obtain ⟨E_up, b, hE_up_ne, hE_up_dim, hE_up_F, hb_exp, hx_E_up, hb_E_up, hl_lt_b⟩ :=
        improving_edge_and_global_facet_from_ridge_pairs.1 hP ⟨F, hF.2.1⟩ x hxExp hxF l ⟨w, hwF, hlt⟩
      have hE_up_mem : E_up.val ∈ ℰ := by
        rw [← Finset.mem_coe, hℰ_coe]
        exact ⟨hE_up_ne, E_up.property, hE_up_dim⟩
      have hE_up_in_pair : E_up.val ∈ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) := by
        rw [← hfilt_F]
        exact Finset.mem_filter.2 ⟨hE_up_mem, hx_E_up, hE_up_F⟩
      rw [← heq_pair] at hE_up_in_pair
      have hE_up_in_x : E_up.val ∈ ℰ_x := (Finset.mem_filter.1 hE_up_in_pair).1
      have hb_V : b ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb_exp
      have hlb_le : l b ≤ l x := (Finset.mem_filter.1 hE_up_in_x).2.2 b hb_V hb_E_up
      linarith
    · rintro ⟨_, hle_F⟩
      have hpair_sub : ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) ⊆ ℰ_x.filter (fun E => E ⊆ F) := by
        intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        simp only [Finset.mem_filter, ℰ_x]
        rcases hE with rfl | rfl
        · refine ⟨⟨hE₁_mem, hxE₁, fun w hwV hwE => hle_F w hwV (hE₁_F hwE)⟩, hE₁_F⟩
        · refine ⟨⟨hE₂_mem, hxE₂, fun w hwV hwE => hle_F w hwV (hE₂_F hwE)⟩, hE₂_F⟩
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

lemma improving_slope_endpoint {V' : Finset (Fin 3 → ℝ)}
    {l h : StrongDual ℝ (Fin 3 → ℝ)} {a w_min w_max w_hi : Fin 3 → ℝ}
    {τ_norm α β : ℝ} {σ : (Fin 3 → ℝ) → ℝ}
    (hτ_pos : 0 < τ_norm)
    (hl_lt : ∀ w ∈ V', 0 < l a - l w)
    (hw_min : w_min ∈ V') (hw_max : w_max ∈ V') (hw_hi : w_hi ∈ V')
    (hσ_min : σ w_min ≤ σ w_hi) (hσ_max : σ w_hi ≤ σ w_max)
    (hh_hi : h a < h w_hi)
    (hh_gram : ∀ w ∈ V', τ_norm * (h w - h a) = (l a - l w) * (α + β * σ w)) :
    h a < h w_max ∨ h a < h w_min := by
  have hgram_hi := hh_gram w_hi hw_hi
  have hl_hi := hl_lt w_hi hw_hi
  have hlhs_hi : 0 < τ_norm * (h w_hi - h a) := mul_pos hτ_pos (by linarith)
  rw [hgram_hi] at hlhs_hi
  have h_pos_hi : 0 < α + β * σ w_hi := by nlinarith
  rcases le_or_gt 0 β with hβ_nonneg | hβ_neg
  · left
    have h_pos_max : 0 < α + β * σ w_max := by nlinarith
    have hgram_max := hh_gram w_max hw_max
    have hl_max := hl_lt w_max hw_max
    have hrhs_max : 0 < (l a - l w_max) * (α + β * σ w_max) := mul_pos hl_max h_pos_max
    rw [← hgram_max] at hrhs_max
    nlinarith
  · right
    have h_pos_min : 0 < α + β * σ w_min := by nlinarith
    have hgram_min := hh_gram w_min hw_min
    have hl_min := hl_lt w_min hw_min
    have hrhs_min : 0 < (l a - l w_min) * (α + β * σ w_min) := mul_pos hl_min h_pos_min
    rw [← hgram_min] at hrhs_min
    nlinarith

lemma exists_facet_above_edge_improving_dual_general
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2}) :
    ∀ E ∈ ℰ, ∀ a₀ ∈ V, ∀ b₀ ∈ V, a₀ ∈ E → b₀ ∈ E → a₀ ≠ b₀ →
      ∀ (h : StrongDual ℝ (Fin 3 → ℝ)), h b₀ = h a₀ →
      (∃ w ∈ V, h a₀ < h w) →
      ∃ F ∈ ℱ, E ⊆ F ∧ ∃ c ∈ V, c ∈ F ∧ h a₀ < h c := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 3 P
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  let V_set : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
  have hV_sub_P : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
  have hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)) := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    rw [Set.inter_eq_self_of_subset_right hV_sub_P] at h1
    dsimp [V_set] at h1
    rw [← hV_coe] at h1
    exact h1
  have hV_ge4 : 4 ≤ V.card := by
    have hCardV : faceCount P 0 = V.card := by
      rw [hVBound.1, ← hV_coe, Set.ncard_coe_finset]
    rw [← hCardV]
    exact hVBound.2 hP
  intro E hE a₀ ha₀V b₀ hb₀V ha₀E hb₀E ha₀b₀ h hh_ab₀ ⟨w_hi, hw_hiV, hh_hi₀⟩
  have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
      Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
    rw [← Finset.mem_coe, hℰ_coe] at hE; exact hE
  obtain ⟨a, b, ha, hb, hab, hEV, hE_eq_ab⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
  have ha₀_exp : IsExposed ℝ P {a₀} := by rw [← Finset.mem_coe, hV_coe] at ha₀V; exact ha₀V
  have hb₀_exp : IsExposed ℝ P {b₀} := by rw [← Finset.mem_coe, hV_coe] at hb₀V; exact hb₀V
  have ha₀_pair : a₀ = a ∨ a₀ = b := by
    have hm : a₀ ∈ E ∩ V_set := ⟨ha₀E, ha₀_exp⟩
    rw [hEV] at hm
    simpa using hm
  have hb₀_pair : b₀ = a ∨ b₀ = b := by
    have hm : b₀ ∈ E ∩ V_set := ⟨hb₀E, hb₀_exp⟩
    rw [hEV] at hm
    simpa using hm
  have hh_a_eq : h a = h a₀ ∧ h b = h a := by
    rcases ha₀_pair with rfl | rfl <;> rcases hb₀_pair with rfl | rfl
    · exact False.elim (ha₀b₀ rfl)
    · exact ⟨rfl, hh_ab₀⟩
    · exact ⟨hh_ab₀, hh_ab₀.symm⟩
    · exact False.elim (ha₀b₀ rfl)
  have hh_ab : h b = h a := hh_a_eq.2
  have hh_hi : h a < h w_hi := by linarith [hh_a_eq.1, hh_hi₀]
  have haV : a ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact ha
  have hbV : b ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb
  have haE : a ∈ E := by
    have h : a ∈ E ∩ V_set := by rw [hEV]; simp
    exact h.1
  have hbE : b ∈ E := by
    have h : b ∈ E ∩ V_set := by rw [hEV]; simp
    exact h.1
  have haP : a ∈ P := hV_sub_P ha
  have hbP : b ∈ P := hV_sub_P hb
  obtain ⟨l, hEl⟩ := hE_set.2.1 hE_set.1
  have ha_mem : a ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hEl ▸ haE
  have hb_mem : b ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hEl ▸ hbE
  have hl_ab : l b = l a := le_antisymm (ha_mem.2 b hbP) (hb_mem.2 a haP)
  let V' : Finset (Fin 3 → ℝ) := (V.erase b).erase a
  have hV'_card : 2 ≤ V'.card := by
    have ha_erb : a ∈ V.erase b := Finset.mem_erase.2 ⟨hab, haV⟩
    dsimp [V']
    rw [Finset.card_erase_of_mem ha_erb, Finset.card_erase_of_mem hbV]
    omega
  have hV'_ne : V'.Nonempty := Finset.card_pos.1 (by omega)
  have hl_lt : ∀ w ∈ V', 0 < l a - l w := by
    intro w hw'
    have hwa : w ≠ a := (Finset.mem_erase.1 hw').1
    have hwb : w ≠ b := (Finset.mem_erase.1 (Finset.mem_erase.1 hw').2).1
    have hwV : w ∈ V := (Finset.mem_erase.1 (Finset.mem_erase.1 hw').2).2
    have hwExp : IsExposed ℝ P {w} := by rw [← Finset.mem_coe, hV_coe] at hwV; exact hwV
    have hwP : w ∈ P := hV_sub_P hwExp
    have hle : l w ≤ l a := ha_mem.2 w hwP
    have hlt : l w < l a := by
      refine lt_of_le_of_ne hle (fun heq => ?_)
      have hwE : w ∈ E := by
        rw [hEl]
        exact ⟨hwP, fun y hy => by linarith [ha_mem.2 y hy]⟩
      have hwEV : w ∈ E ∩ V_set := ⟨hwE, hwExp⟩
      rw [hEV] at hwEV
      rcases hwEV with rfl | hwb'
      · exact hwa rfl
      · exact hwb (Set.mem_singleton_iff.1 hwb')
    linarith
  let l_vec : Fin 3 → ℝ := fun i => l (Pi.single i 1)
  let u : Fin 3 → ℝ := b - a
  let τ_vec : Fin 3 → ℝ := cross3 l_vec u
  let τ : StrongDual ℝ (Fin 3 → ℝ) :=
    τ_vec 0 • ContinuousLinearMap.proj 0 +
    τ_vec 1 • ContinuousLinearMap.proj 1 +
    τ_vec 2 • ContinuousLinearMap.proj 2
  have hl_dot : ∀ x : Fin 3 → ℝ, l x = dot3' l_vec x :=
    fun x => dual_apply_fin_three l x
  have hτ_dot : ∀ x : Fin 3 → ℝ, τ x = dot3' τ_vec x := by
    intro x
    change τ_vec 0 * x 0 + τ_vec 1 * x 1 + τ_vec 2 * x 2 = dot3' τ_vec x
    rfl
  have hlu : dot3' l_vec u = 0 := by
    rw [← hl_dot u]
    change l (b - a) = 0
    rw [map_sub, hl_ab, sub_self]
  obtain ⟨hτu, hτl, hτ_norm⟩ := cross3_orthogonal_and_norm l_vec u hlu
  have hτ_ab : τ b = τ a := by
    have h1 : τ (b - a) = dot3' τ_vec u := hτ_dot u
    rw [map_sub, hτu] at h1
    linarith
  have hu_pos : 0 < dot3' u u := by
    by_contra hle
    obtain ⟨hu0, hu1, hu2⟩ := dot3'_self_le_zero_imp u (not_lt.1 hle)
    change b 0 - a 0 = 0 at hu0
    change b 1 - a 1 = 0 at hu1
    change b 2 - a 2 = 0 at hu2
    apply hab
    ext i
    fin_cases i
    · change a 0 = b 0; linarith
    · change a 1 = b 1; linarith
    · change a 2 = b 2; linarith
  have hl_pos : 0 < dot3' l_vec l_vec := by
    rcases hV'_ne with ⟨w₀, hw₀⟩
    have hpos := hl_lt w₀ hw₀
    rw [hl_dot a, hl_dot w₀] at hpos
    by_contra hle
    obtain ⟨hl0, hl1, hl2⟩ := dot3'_self_le_zero_imp l_vec (not_lt.1 hle)
    dsimp [dot3'] at hpos
    rw [hl0, hl1, hl2] at hpos
    linarith
  have hτ_pos : 0 < dot3' τ_vec τ_vec := by
    rw [hτ_norm]
    exact mul_pos hl_pos hu_pos
  let σ : (Fin 3 → ℝ) → ℝ := fun w => (τ w - τ a) / (l a - l w)
  have hσ_mul : ∀ w ∈ V', τ w - τ a = σ w * (l a - l w) := by
    intro w hw'
    dsimp [σ]
    exact (div_mul_cancel₀ _ (ne_of_gt (hl_lt w hw'))).symm
  obtain ⟨w_max, hw_max, hσ_max⟩ := V'.exists_max_image σ hV'_ne
  obtain ⟨w_min, hw_min, hσ_min⟩ := V'.exists_min_image σ hV'_ne
  let g_plus : StrongDual ℝ (Fin 3 → ℝ) := σ w_max • l + τ
  let g_minus : StrongDual ℝ (Fin 3 → ℝ) := -σ w_min • l - τ
  have hg_plus_ab : g_plus b = g_plus a := by
    change σ w_max * l b + τ b = σ w_max * l a + τ a
    rw [hl_ab, hτ_ab]
  have hg_minus_ab : g_minus b = g_minus a := by
    change -σ w_min * l b - τ b = -σ w_min * l a - τ a
    rw [hl_ab, hτ_ab]
  have hg_plus_diff : ∀ w ∈ V', g_plus w - g_plus a = (l a - l w) * (σ w - σ w_max) := by
    intro w hw'
    have hτw := hσ_mul w hw'
    change (σ w_max * l w + τ w) - (σ w_max * l a + τ a) = (l a - l w) * (σ w - σ w_max)
    linarith
  have hg_minus_diff : ∀ w ∈ V', g_minus w - g_minus a = (l a - l w) * (σ w_min - σ w) := by
    intro w hw'
    have hτw := hσ_mul w hw'
    change (-σ w_min * l w - τ w) - (-σ w_min * l a - τ a) = (l a - l w) * (σ w_min - σ w)
    linarith
  have hσ_min_lt_max : σ w_min < σ w_max := by
    refine lt_of_le_of_ne (hσ_max w_min hw_min) (fun heq => ?_)
    have hg_V : ∀ w ∈ V, g_plus w = g_plus a := by
      intro w hwV
      by_cases hwa : w = a
      · rw [hwa]
      · by_cases hwb : w = b
        · rw [hwb, hg_plus_ab]
        · have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwa, Finset.mem_erase.2 ⟨hwb, hwV⟩⟩
          have hσ_eq : σ w = σ w_max := by
            have h1 := hσ_min w hw'
            have h2 := hσ_max w hw'
            linarith
          have hdiff := hg_plus_diff w hw'
          rw [hσ_eq, sub_self, mul_zero] at hdiff
          linarith
    have hg_P : ∀ x ∈ P, g_plus x = g_plus a := by
      rw [hP_eq_V]
      exact convexHull_min (fun w hw => hg_V w hw)
        (convex_hyperplane (g_plus : (Fin 3 → ℝ) →ₗ[ℝ] ℝ).isLinear (g_plus a))
    have hker : vectorSpan ℝ P ≤ LinearMap.ker g_plus.toLinearMap := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro v ⟨x, hx, y, hy, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        vsub_eq_sub, map_sub]
      rw [hg_P x hx, hg_P y hy, sub_self]
    have hvs_top : vectorSpan ℝ P = ⊤ := by
      rw [← direction_affineSpan, hP.2, AffineSubspace.direction_top]
    have hτ_ker : τ_vec ∈ LinearMap.ker g_plus.toLinearMap := by
      apply hker
      rw [hvs_top]
      trivial
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hτ_ker
    have hτ_val : g_plus τ_vec = σ w_max * dot3' l_vec τ_vec + dot3' τ_vec τ_vec := by
      change σ w_max * l τ_vec + τ τ_vec = σ w_max * dot3' l_vec τ_vec + dot3' τ_vec τ_vec
      rw [hl_dot τ_vec, hτ_dot τ_vec]
    have hlτ_zero : dot3' l_vec τ_vec = 0 := by
      dsimp [dot3'] at hτl ⊢; linarith
    rw [hτ_val, hlτ_zero, mul_zero, zero_add] at hτ_ker
    linarith
  have hg_plus_le : ∀ w ∈ V, g_plus w ≤ g_plus a := by
    intro w hwV
    by_cases hwa : w = a
    · rw [hwa]
    · by_cases hwb : w = b
      · rw [hwb, hg_plus_ab]
      · have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwa, Finset.mem_erase.2 ⟨hwb, hwV⟩⟩
        have hpos := hl_lt w hw'
        have hle := hσ_max w hw'
        have hdiff := hg_plus_diff w hw'
        have hnonpos : (l a - l w) * (σ w - σ w_max) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (by linarith)
        linarith
  have hg_minus_le : ∀ w ∈ V, g_minus w ≤ g_minus a := by
    intro w hwV
    by_cases hwa : w = a
    · rw [hwa]
    · by_cases hwb : w = b
      · rw [hwb, hg_minus_ab]
      · have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwa, Finset.mem_erase.2 ⟨hwb, hwV⟩⟩
        have hpos := hl_lt w hw'
        have hle := hσ_min w hw'
        have hdiff := hg_minus_diff w hw'
        have hnonpos : (l a - l w) * (σ w_min - σ w) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (by linarith)
        linarith
  let S_plus : Finset (Fin 3 → ℝ) := V.filter (fun y => g_plus y = g_plus a)
  let S_minus : Finset (Fin 3 → ℝ) := V.filter (fun y => g_minus y = g_minus a)
  let F_plus : Set (Fin 3 → ℝ) := convexHull ℝ (S_plus : Set (Fin 3 → ℝ))
  let F_minus : Set (Fin 3 → ℝ) := convexHull ℝ (S_minus : Set (Fin 3 → ℝ))
  obtain ⟨_, _, hF_plus_exp_V⟩ :=
    isExposed_of_eq_max_on_finset_3d V g_plus (g_plus a) hg_plus_le ⟨a, haV, rfl⟩
  obtain ⟨_, _, hF_minus_exp_V⟩ :=
    isExposed_of_eq_max_on_finset_3d V g_minus (g_minus a) hg_minus_le ⟨a, haV, rfl⟩
  have hF_plus_exp : IsExposed ℝ P F_plus := hP_eq_V.symm ▸ hF_plus_exp_V
  have hF_minus_exp : IsExposed ℝ P F_minus := hP_eq_V.symm ▸ hF_minus_exp_V
  have ha_Fp : a ∈ F_plus := subset_convexHull ℝ (S_plus : Set (Fin 3 → ℝ))
    (Finset.mem_filter.2 ⟨haV, rfl⟩)
  have hb_Fp : b ∈ F_plus := subset_convexHull ℝ (S_plus : Set (Fin 3 → ℝ))
    (Finset.mem_filter.2 ⟨hbV, hg_plus_ab⟩)
  have hwmax_V : w_max ∈ V := (Finset.mem_erase.1 (Finset.mem_erase.1 hw_max).2).2
  have hwmax_Fp : w_max ∈ F_plus := by
    apply subset_convexHull ℝ (S_plus : Set (Fin 3 → ℝ))
    refine Finset.mem_filter.2 ⟨hwmax_V, ?_⟩
    have hdiff := hg_plus_diff w_max hw_max
    linarith
  have ha_Fm : a ∈ F_minus := subset_convexHull ℝ (S_minus : Set (Fin 3 → ℝ))
    (Finset.mem_filter.2 ⟨haV, rfl⟩)
  have hb_Fm : b ∈ F_minus := subset_convexHull ℝ (S_minus : Set (Fin 3 → ℝ))
    (Finset.mem_filter.2 ⟨hbV, hg_minus_ab⟩)
  have hwmin_V : w_min ∈ V := (Finset.mem_erase.1 (Finset.mem_erase.1 hw_min).2).2
  have hwmin_Fm : w_min ∈ F_minus := by
    apply subset_convexHull ℝ (S_minus : Set (Fin 3 → ℝ))
    refine Finset.mem_filter.2 ⟨hwmin_V, ?_⟩
    have hdiff := hg_minus_diff w_min hw_min
    linarith
  have hg_plus_Fp : ∀ x ∈ F_plus, g_plus x = g_plus a :=
    convexHull_min (fun y hy => (Finset.mem_filter.1 hy).2)
      (convex_hyperplane (g_plus : (Fin 3 → ℝ) →ₗ[ℝ] ℝ).isLinear (g_plus a))
  have hg_minus_Fm : ∀ x ∈ F_minus, g_minus x = g_minus a :=
    convexHull_min (fun y hy => (Finset.mem_filter.1 hy).2)
      (convex_hyperplane (g_minus : (Fin 3 → ℝ) →ₗ[ℝ] ℝ).isLinear (g_minus a))
  have hg_plus_wmin_lt : g_plus w_min < g_plus a := by
    have hdiff := hg_plus_diff w_min hw_min
    have hpos := hl_lt w_min hw_min
    have hneg : (l a - l w_min) * (σ w_min - σ w_max) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have hg_minus_wmax_lt : g_minus w_max < g_minus a := by
    have hdiff := hg_minus_diff w_max hw_max
    have hpos := hl_lt w_max hw_max
    have hneg : (l a - l w_max) * (σ w_min - σ w_max) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have hFp_dim : Module.finrank ℝ (affineSpan ℝ F_plus).direction = 2 :=
    finrank_two_of_three_points_and_strict_Dual ha_Fp hb_Fp hwmax_Fp hab
      l hl_ab (by linarith [hl_lt w_max hw_max]) g_plus hg_plus_Fp hg_plus_wmin_lt
  have hFm_dim : Module.finrank ℝ (affineSpan ℝ F_minus).direction = 2 :=
    finrank_two_of_three_points_and_strict_Dual ha_Fm hb_Fm hwmin_Fm hab
      l hl_ab (by linarith [hl_lt w_min hw_min]) g_minus hg_minus_Fm hg_minus_wmax_lt
  have hFp_set : F_plus.Nonempty ∧ IsExposed ℝ P F_plus ∧
      Module.finrank ℝ (affineSpan ℝ F_plus).direction = 2 :=
    ⟨⟨a, ha_Fp⟩, hF_plus_exp, hFp_dim⟩
  have hFm_set : F_minus.Nonempty ∧ IsExposed ℝ P F_minus ∧
      Module.finrank ℝ (affineSpan ℝ F_minus).direction = 2 :=
    ⟨⟨a, ha_Fm⟩, hF_minus_exp, hFm_dim⟩
  have hFp_mem : F_plus ∈ ℱ := by rw [← Finset.mem_coe, hℱ_coe]; exact hFp_set
  have hFm_mem : F_minus ∈ ℱ := by rw [← Finset.mem_coe, hℱ_coe]; exact hFm_set
  have hE_sub_Fp : E ⊆ F_plus := by
    rw [hE_eq_ab]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hxb
    · exact ha_Fp
    · rw [Set.mem_singleton_iff.1 hxb]; exact hb_Fp
  have hE_sub_Fm : E ⊆ F_minus := by
    rw [hE_eq_ab]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hxb
    · exact ha_Fm
    · rw [Set.mem_singleton_iff.1 hxb]; exact hb_Fm
  have hw_hi_V' : w_hi ∈ V' := by
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hw_hiV⟩⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  let h_vec : Fin 3 → ℝ := fun i => h (Pi.single i 1)
  have hh_dot : ∀ x : Fin 3 → ℝ, h x = dot3' h_vec x :=
    fun x => dual_apply_fin_three h x
  have hhu : dot3' h_vec u = 0 := by
    rw [← hh_dot u]
    change h (b - a) = 0
    rw [map_sub, hh_ab, sub_self]
  have hh_gram : ∀ w ∈ V',
      dot3' τ_vec τ_vec * (h w - h a) =
        (l a - l w) * (-dot3' u u * dot3' h_vec l_vec + dot3' h_vec τ_vec * σ w) := by
    intro w hw'
    have hgram := cross3_gram_identity l_vec u h_vec (w - a) hlu hhu
    have hhd : dot3' h_vec (w - a) = h w - h a := by
      rw [← hh_dot (w - a), map_sub]
    have hld : dot3' l_vec (w - a) = -(l a - l w) := by
      rw [← hl_dot (w - a), map_sub]; ring
    have hτd : dot3' τ_vec (w - a) = σ w * (l a - l w) := by
      rw [← hτ_dot (w - a), map_sub, hσ_mul w hw']
    dsimp [τ_vec] at hτd ⊢
    rw [hhd, hld, hτd] at hgram
    linarith
  rcases improving_slope_endpoint hτ_pos hl_lt hw_min hw_max hw_hi_V'
      (hσ_min w_hi hw_hi_V') (hσ_max w_hi hw_hi_V') hh_hi hh_gram with h_max | h_min
  · exact ⟨F_plus, hFp_mem, hE_sub_Fp, w_max, hwmax_V, hwmax_Fp, by linarith [hh_a_eq.1, h_max]⟩
  · exact ⟨F_minus, hFm_mem, hE_sub_Fm, w_min, hwmin_V, hwmin_Fm, by linarith [hh_a_eq.1, h_min]⟩

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

lemma pair_max_or_min_zero_of_gram {α : Type*}
    {Pi_set : Finset α} {p₀ p_min p_max : α}
    {τ_norm gl β : ℝ} {m_pos g_diff σ : α → ℝ}
    (hτ_pos : 0 < τ_norm)
    (hm_pos : ∀ p ∈ Pi_set, 0 < m_pos p)
    (hp₀ : p₀ ∈ Pi_set) (hp_min : p_min ∈ Pi_set) (hp_max : p_max ∈ Pi_set)
    (hσ_min : σ p_min ≤ σ p₀) (hσ_max : σ p₀ ≤ σ p_max)
    (hg_nonpos : ∀ p ∈ Pi_set, g_diff p ≤ 0)
    (hg_zero : g_diff p₀ = 0)
    (hgram : ∀ p ∈ Pi_set, τ_norm * g_diff p = m_pos p * (gl + β * σ p)) :
    g_diff p_max = 0 ∨ g_diff p_min = 0 := by
  have hp₀_gram := hgram p₀ hp₀
  rw [hg_zero, mul_zero] at hp₀_gram
  have hmp₀_pos := hm_pos p₀ hp₀
  have hgl_zero : gl + β * σ p₀ = 0 :=
    (mul_eq_zero.1 hp₀_gram.symm).resolve_left (ne_of_gt hmp₀_pos)
  have hgl_eq : gl = -β * σ p₀ := by linarith
  have hrel : ∀ p ∈ Pi_set, τ_norm * g_diff p = m_pos p * (β * (σ p - σ p₀)) := by
    intro p hp
    rw [hgram p hp, hgl_eq]
    ring
  rcases le_or_gt 0 β with hβ_nonneg | hβ_neg
  · left
    have h1 := hrel p_max hp_max
    have hm := hm_pos p_max hp_max
    have hg := hg_nonpos p_max hp_max
    have h_nonneg : 0 ≤ m_pos p_max * (β * (σ p_max - σ p₀)) :=
      mul_nonneg (le_of_lt hm) (mul_nonneg hβ_nonneg (by linarith))
    have h_nonpos : τ_norm * g_diff p_max ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hτ_pos) hg
    nlinarith
  · right
    have h1 := hrel p_min hp_min
    have hm := hm_pos p_min hp_min
    have hg := hg_nonpos p_min hp_min
    have h_nonneg : 0 ≤ m_pos p_min * (β * (σ p_min - σ p₀)) :=
      mul_nonneg (le_of_lt hm) (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hβ_neg) (by linarith))
    have h_nonpos : τ_norm * g_diff p_min ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hτ_pos) hg
    nlinarith

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
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
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  have hImpFacet := exists_facet_above_edge_improving_dual_general P hP V ℰ ℱ hV_coe hℰ_coe hℱ_coe
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
  have hFacetProp : ∀ F ∈ ℱ,
      (∀ x ∈ V, x ∈ F →
        ∃ E₁ E₂ : Set (Fin 3 → ℝ),
          E₁ ∈ ℰ ∧ E₂ ∈ ℰ ∧ E₁ ≠ E₂ ∧ x ∈ E₁ ∧ x ∈ E₂ ∧ E₁ ⊆ F ∧ E₂ ⊆ F ∧
          ℰ.filter (fun E => x ∈ E ∧ E ⊆ F) = {E₁, E₂}) ∧
      (∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
        let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
        (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
        ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
          (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x))) := by
    intro F hF
    have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
      rw [← Finset.mem_coe, hℱ_coe] at hF; exact hF
    exact facet_vertex_two_edges_and_degree hP V hV_coe ℰ hℰ_coe hF_set
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
    obtain ⟨F₀, hF₀_mem, hE₀_sub_F₀, c₀, _, hc₀_F₀, hh_tilde_c₀⟩ :=
      hImpFacet E₀ hE₀_mem x hxV u₀ hu₀_V hx_E₀ hu₀_E₀ hu₀_ne_x.symm
        h_tilde hh_tilde_u₀ ⟨u_up, hu_up_V, hh_tilde_up⟩
    have hF₀_set : F₀.Nonempty ∧ IsExposed ℝ P F₀ ∧
        Module.finrank ℝ (affineSpan ℝ F₀).direction = 2 := by
      rw [← Finset.mem_coe, hℱ_coe] at hF₀_mem; exact hF₀_mem
    obtain ⟨E_c, c₁, hE_c_ne, hE_c_dim, hE_c_sub_F₀, hc₁_exp, hx_E_c, hc₁_E_c, hh_tilde_c₁⟩ :=
      improving_edge_and_global_facet_from_ridge_pairs.1 hP ⟨F₀, hF₀_set.2.1⟩
        x hxExp (hE₀_sub_F₀ hx_E₀) h_tilde ⟨c₀, hc₀_F₀, hh_tilde_c₀⟩
    have hE_c_mem : E_c.val ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hE_c_ne, E_c.property, hE_c_dim⟩
    have hc₁_V : c₁ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hc₁_exp
    have hc₁_F₀ : c₁ ∈ F₀ := hE_c_sub_F₀ hc₁_E_c
    have hc₁_ne_x : c₁ ≠ x := fun heq => (ne_of_lt hh_tilde_c₁) (congr_arg h_tilde heq).symm
    have hρ_c₁_gt : ρ u₀ < ρ c₁ := by
      have h1 := hh_tilde_diff c₁ hc₁_V hc₁_ne_x
      have hpos := hmx_lt c₁ hc₁_V hc₁_ne_x
      have h2 : 0 < (m_x x - m_x c₁) * (ρ c₁ - ρ u₀) := by linarith
      nlinarith
    have hlc₁_gt : l x < l c₁ := by
      by_contra hle
      have hlt : l c₁ < l x :=
        lt_of_le_of_ne (not_lt.1 hle) (fun heq => hc₁_ne_x (hl_inj c₁ hc₁_V x hxV heq))
      have hc₁_in_U : c₁ ∈ U_down :=
        Finset.mem_filter.2 ⟨hc₁_V, hlt, E_c.val, hE_c_mem, hx_E_c, hc₁_E_c⟩
      have hle_ρ := hρ_max c₁ hc₁_in_U
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
      have h1 := h_all_le.2 c₁ hc₁_V hc₁_F₀
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
    let ℱ_cross_max : Finset (Set (Fin 3 → ℝ)) :=
      ℱ_cross.filter (fun F => uv_max.1 ∈ F ∧ uv_max.2 ∈ F)
    let ℱ_cross_min : Finset (Set (Fin 3 → ℝ)) :=
      ℱ_cross.filter (fun F => uv_min.1 ∈ F ∧ uv_min.2 ∈ F)
    have hsub_union : ℱ_cross ⊆ ℱ_cross_max ∪ ℱ_cross_min := by
      intro F hF_cross
      rcases Finset.mem_filter.1 hF_cross with ⟨hF_mem, hF_card1⟩
      have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF_mem; exact hF_mem
      obtain ⟨E_dn_F, hE_dn_in⟩ := Finset.card_pos.1 (by omega : 0 < (ℰ_x.filter (fun E => E ⊆ F)).card)
      rcases Finset.mem_filter.1 hE_dn_in with ⟨hE_dn_x, hE_dn_sub_F⟩
      rcases Finset.mem_filter.1 hE_dn_x with ⟨hE_dn_mem, hx_E_dn_F, hE_dn_le⟩
      have hxF : x ∈ F := hE_dn_sub_F hx_E_dn_F
      obtain ⟨E₁, E₂, hE₁_mem, hE₂_mem, hE₁₂_ne, hxE₁, hxE₂, hE₁_F, hE₂_F, hfilt_F⟩ :=
        (hFacetProp F hF_mem).1 x hxV hxF
      have hE_dn_pair : E_dn_F = E₁ ∨ E_dn_F = E₂ := by
        have hm : E_dn_F ∈ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) := by
          rw [← hfilt_F]
          exact Finset.mem_filter.2 ⟨hE_dn_mem, hx_E_dn_F, hE_dn_sub_F⟩
        simpa using hm
      let E_up_F : Set (Fin 3 → ℝ) := if E_dn_F = E₁ then E₂ else E₁
      have hE_up_props : E_up_F ∈ ℰ ∧ x ∈ E_up_F ∧ E_up_F ⊆ F ∧ E_up_F ≠ E_dn_F := by
        dsimp [E_up_F]
        split_ifs with heq
        · subst heq
          exact ⟨hE₂_mem, hxE₂, hE₂_F, hE₁₂_ne.symm⟩
        · refine ⟨hE₁_mem, hxE₁, hE₁_F, Ne.symm heq⟩
      have hE_up_not_x : E_up_F ∉ ℰ_x := by
        intro hmem_x
        have hmem_filt : E_up_F ∈ ℰ_x.filter (fun E => E ⊆ F) :=
          Finset.mem_filter.2 ⟨hmem_x, hE_up_props.2.2.1⟩
        have hpair_sub : ({E_dn_F, E_up_F} : Finset (Set (Fin 3 → ℝ))) ⊆
            ℰ_x.filter (fun E => E ⊆ F) := by
          intro E hE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hE
          rcases hE with rfl | rfl
          · exact hE_dn_in
          · exact hmem_filt
        have hle := Finset.card_le_card hpair_sub
        rw [Finset.card_pair hE_up_props.2.2.2.symm, hF_card1] at hle
        omega
      have hex_vF : ∃ v_F ∈ V, v_F ∈ F ∧ l x < l v_F := by
        by_contra hno
        apply hE_up_not_x
        refine Finset.mem_filter.2 ⟨hE_up_props.1, hE_up_props.2.1, fun w hwV hwE => ?_⟩
        by_contra hgt
        exact hno ⟨w, hwV, hE_up_props.2.2.1 hwE, lt_of_not_ge hgt⟩
      rcases hex_vF with ⟨v_F, hv_F_V, hv_F_F, hl_vF_gt⟩
      have hE_dn_set : E_dn_F.Nonempty ∧ IsExposed ℝ P E_dn_F ∧
          Module.finrank ℝ (affineSpan ℝ E_dn_F).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE_dn_mem; exact hE_dn_mem
      obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hE_dn_V, _⟩ :=
        (hEdgePair hHull E_dn_F hE_dn_set.2.1).1 ⟨hE_dn_set.1, hE_dn_set.2.2⟩
      have hx_ab₁ : x = a₁ ∨ x = b₁ := by
        have hm : x ∈ E_dn_F ∩ V_set := ⟨hx_E_dn_F, hxExp⟩
        rw [hE_dn_V] at hm; simpa using hm
      have hex_uF : ∃ u_F ∈ V, u_F ∈ F ∧ l u_F < l x := by
        rcases hx_ab₁ with rfl | rfl
        · have hb₁V : b₁ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb₁
          have hb₁E : b₁ ∈ E_dn_F := by
            have hm : b₁ ∈ E_dn_F ∩ V_set := by rw [hE_dn_V]; simp
            exact hm.1
          have hlt : l b₁ < l x :=
            lt_of_le_of_ne (hE_dn_le b₁ hb₁V hb₁E) (fun heq => hab₁.symm (hl_inj b₁ hb₁V x hxV heq))
          exact ⟨b₁, hb₁V, hE_dn_sub_F hb₁E, hlt⟩
        · have ha₁V : a₁ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact ha₁
          have ha₁E : a₁ ∈ E_dn_F := by
            have hm : a₁ ∈ E_dn_F ∩ V_set := by rw [hE_dn_V]; simp
            exact hm.1
          have hlt : l a₁ < l x :=
            lt_of_le_of_ne (hE_dn_le a₁ ha₁V ha₁E) (fun heq => hab₁ (hl_inj a₁ ha₁V x hxV heq))
          exact ⟨a₁, ha₁V, hE_dn_sub_F ha₁E, hlt⟩
      rcases hex_uF with ⟨u_F, hu_F_V, hu_F_F, hl_uF_lt⟩
      have huv_F_mem : (u_F, v_F) ∈ Pi_set :=
        Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hu_F_V, hl_uF_lt⟩,
          Finset.mem_filter.2 ⟨hv_F_V, hl_vF_gt⟩⟩
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
      have hg_nonpos : ∀ uv ∈ Pi_set, g_diff uv ≤ 0 := by
        intro uv huv
        rcases Finset.mem_product.1 huv with ⟨hu_m, hv_p⟩
        have huV : uv.1 ∈ V := (Finset.mem_filter.1 hu_m).1
        have hvV : uv.2 ∈ V := (Finset.mem_filter.1 hv_p).1
        have hcp := (hPi_set_props uv huv).2.2.2 g (hg_le_V uv.1 huV) (hg_le_V uv.2 hvV)
        dsimp [g_diff]
        linarith [hcp.1]
      have hg_zero : g_diff (u_F, v_F) = 0 := by
        have hcp := (hPi_set_props (u_F, v_F) huv_F_mem).2.2.2 g
          (hg_le_V u_F hu_F_V) (hg_le_V v_F hv_F_V)
        have heq := hcp.2.2 ⟨hg_uF_eq, hg_vF_eq⟩
        dsimp [g_diff]
        linarith
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
      have hmem_of_g_diff_zero : ∀ uv ∈ Pi_set, g_diff uv = 0 → uv.1 ∈ F ∧ uv.2 ∈ F := by
        intro uv huv hzero
        rcases Finset.mem_product.1 huv with ⟨hu_m, hv_p⟩
        have huV : uv.1 ∈ V := (Finset.mem_filter.1 hu_m).1
        have hvV : uv.2 ∈ V := (Finset.mem_filter.1 hv_p).1
        have hcp := (hPi_set_props uv huv).2.2.2 g (hg_le_V uv.1 huV) (hg_le_V uv.2 hvV)
        have heq : g (crossing_point l x uv.1 uv.2) = g x := by
          dsimp [g_diff] at hzero; linarith
        obtain ⟨hgu_eq, hgv_eq⟩ := hcp.2.1 heq
        have huExp : IsExposed ℝ P {uv.1} := by rw [← Finset.mem_coe, hV_coe] at huV; exact huV
        have hvExp : IsExposed ℝ P {uv.2} := by rw [← Finset.mem_coe, hV_coe] at hvV; exact hvV
        refine ⟨?_, ?_⟩
        · rw [hFg]; exact ⟨hV_sub_P huExp, fun y hy => by linarith [hx_g.2 y hy]⟩
        · rw [hFg]; exact ⟨hV_sub_P hvExp, fun y hy => by linarith [hx_g.2 y hy]⟩
      rcases pair_max_or_min_zero_of_gram hτ_pos
          (fun uv huv => (hPi_set_props uv huv).2.2.1)
          huv_F_mem huv_min huv_max
          (hσ_min (u_F, v_F) huv_F_mem) (hσ_max (u_F, v_F) huv_F_mem)
          hg_nonpos hg_zero hgram_pair with hmax_zero | hmin_zero
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2
          ⟨hF_cross, hmem_of_g_diff_zero uv_max huv_max hmax_zero⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2
          ⟨hF_cross, hmem_of_g_diff_zero uv_min huv_min hmin_zero⟩))
    have hcard_pair_le1 : ∀ uv ∈ Pi_set,
        (ℱ_cross.filter (fun F => uv.1 ∈ F ∧ uv.2 ∈ F)).card ≤ 1 := by
      intro uv huv
      refine Finset.card_le_one.2 ?_
      intro F₁ hF₁ F₂ hF₂
      rcases Finset.mem_filter.1 hF₁ with ⟨hF₁_cr, hu₁, hv₁⟩
      rcases Finset.mem_filter.1 hF₂ with ⟨hF₂_cr, hu₂, hv₂⟩
      rcases Finset.mem_filter.1 hF₁_cr with ⟨hF₁_mem, hF₁_card1⟩
      rcases Finset.mem_filter.1 hF₂_cr with ⟨hF₂_mem, hF₂_card1⟩
      have hF₁_set : F₁.Nonempty ∧ IsExposed ℝ P F₁ ∧
          Module.finrank ℝ (affineSpan ℝ F₁).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF₁_mem; exact hF₁_mem
      have hF₂_set : F₂.Nonempty ∧ IsExposed ℝ P F₂ ∧
          Module.finrank ℝ (affineSpan ℝ F₂).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF₂_mem; exact hF₂_mem
      obtain ⟨E₁, hE₁_in⟩ := Finset.card_pos.1 (by omega : 0 < (ℰ_x.filter (fun E => E ⊆ F₁)).card)
      obtain ⟨E₂, hE₂_in⟩ := Finset.card_pos.1 (by omega : 0 < (ℰ_x.filter (fun E => E ⊆ F₂)).card)
      have hxF₁ : x ∈ F₁ := (Finset.mem_filter.1 hE₁_in).2
        (Finset.mem_filter.1 (Finset.mem_filter.1 hE₁_in).1).2.1
      have hxF₂ : x ∈ F₂ := (Finset.mem_filter.1 hE₂_in).2
        (Finset.mem_filter.1 (Finset.mem_filter.1 hE₂_in).1).2.1
      rcases Finset.mem_product.1 huv with ⟨hu_m, hv_p⟩
      have hu_lt : l uv.1 < l x := (Finset.mem_filter.1 hu_m).2
      have hv_gt : l x < l uv.2 := (Finset.mem_filter.1 hv_p).2
      let cp := crossing_point l x uv.1 uv.2
      have hcp_F₁ : cp ∈ F₁ :=
        (crossing_point_props (hF₁_set.2.1.convex hP_conv) l x uv.1 uv.2 hu₁ hv₁ hu_lt hv_gt).1
      have hcp_F₂ : cp ∈ F₂ :=
        (crossing_point_props (hF₂_set.2.1.convex hP_conv) l x uv.1 uv.2 hu₂ hv₂ hu_lt hv_gt).1
      have hprops := hPi_set_props uv huv
      have hx_ne_cp : x ≠ cp := by
        intro heq
        have hpos : 0 < m_perp x - m_perp cp := hprops.2.2.1
        rw [heq, sub_self] at hpos
        exact lt_irrefl 0 hpos
      exact facet_eq_of_three_points hF₁_set.2.1 hF₂_set.2.1 hF₁_set.2.2 hF₂_set.2.2
        hxF₁ hcp_F₁ hu₁ hxF₂ hcp_F₂ hu₂ hx_ne_cp l hprops.2.1 hu_lt
    have hmax_le1 : ℱ_cross_max.card ≤ 1 := hcard_pair_le1 uv_max huv_max
    have hmin_le1 : ℱ_cross_min.card ≤ 1 := hcard_pair_le1 uv_min huv_min
    have hunion_le : (ℱ_cross_max ∪ ℱ_cross_min).card ≤ ℱ_cross_max.card + ℱ_cross_min.card :=
      Finset.card_union_le _ _
    have hcr_le : ℱ_cross.card ≤ (ℱ_cross_max ∪ ℱ_cross_min).card :=
      Finset.card_le_card hsub_union
    omega
  omega

end
