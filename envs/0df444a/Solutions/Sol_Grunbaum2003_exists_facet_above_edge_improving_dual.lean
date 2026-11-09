-- Prove2me | solution 1 for Grunbaum2003.exists_facet_above_edge_improving_dual
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:16:44.473999+00:00
-- url     : https://prove2.me/submissions/bcc37c82-aefa-4e04-ad4b-d4a27f5b63fb

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_simplicial_facet_exposed_vertices_and_cardinality
import Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
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

lemma finrank_two_of_three_points_and_strict_Dual {F : Set (Fin 3 → ℝ)}
    {a b c w_out : Fin 3 → ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hab : a ≠ b)
    (m : StrongDual ℝ (Fin 3 → ℝ)) (hm_ab : m b = m a) (hm_ca : m c < m a)
    (g : StrongDual ℝ (Fin 3 → ℝ)) (hg_F : ∀ x ∈ F, g x = g a) (hg_out : g w_out < g a) :
    Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
  rw [direction_affineSpan]
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
  have h1_lt : 1 < Module.finrank ℝ (vectorSpan ℝ F) := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ {a -ᵥ b}) = 1 :=
      finrank_span_singleton (vsub_ne_zero.2 hab)
    have hle := Submodule.finrank_mono hspan_le
    have hne : Module.finrank ℝ (Submodule.span ℝ {a -ᵥ b}) ≠ Module.finrank ℝ (vectorSpan ℝ F) := by
      intro heq
      have hsub_eq := Submodule.eq_of_le_of_finrank_le hspan_le (le_of_eq heq.symm)
      exact hca_not_span (hsub_eq.symm ▸ hca_dir)
    omega
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

lemma dot3'_self_le_zero_imp (v : Fin 3 → ℝ) (h : dot3' v v ≤ 0) :
    v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  dsimp [dot3'] at h
  have h0 := mul_self_nonneg (v 0)
  have h1 := mul_self_nonneg (v 1)
  have h2 := mul_self_nonneg (v 2)
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

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

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
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
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
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
    exact hVBound.2 hP.1
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
      rw [← direction_affineSpan, hP.1.2, AffineSubspace.direction_top]
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

end
