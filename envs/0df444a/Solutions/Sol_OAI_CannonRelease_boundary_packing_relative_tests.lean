-- Prove2me | solution 1 for OAI.CannonRelease.boundary_packing_relative_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:08:40.653913+00:00
-- url     : https://prove2.me/submissions/10f8a2e9-13ee-4264-b290-585c09780a7b

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_disk_disjoint_of_interior
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_hull_geometry
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_univalent_triangles
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_exists_global_radius_constant
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_facialCycle_exists
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_packing_relative_modulus_cost
import Theorems.Thm_OAI_CannonRelease_boundary_uniform_circle_packing

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryHomeomorph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section

namespace CannonRelease
open CannonGraph CannonVisual

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_2_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma visualMetric_comparison (r s : BasedRay D) :
    @dist _ (visualMetricSpace D hδ).toDist (Quotient.mk' r) (Quotient.mk' s) ≤
        (preDist (visualExponent δ) r s : ℝ) ∧
      (preDist (visualExponent δ) r s : ℝ) ≤
        2 * @dist _ (visualMetricSpace D hδ).toDist (Quotient.mk' r) (Quotient.mk' s) :=
  ⟨visual_distance_le δ r s, preDist_le_twice_visual_distance D.connected hδ r s⟩

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

lemma translateRay_uniform (g : G) (r : BasedRay D) (n : ℕ) :
    D.graph.dist ((translateRay D ⟨δ,hδ⟩ g r).val n) (g*r.val n) ≤
      3*D.graph.dist 1 g+4*δ := by
  have h := asymptotic_rays_different_bases_uniform D.connected
    (finite_cayley_neighbors D.generators) hδ
    (translateRay D ⟨δ,hδ⟩ g r).val (fun n => g*r.val n)
    (translateRay D ⟨δ,hδ⟩ g r).property.2
    (fun i j => (D.dist_mul_left g _ _).trans (r.property.2 i j))
    (translateRay_spec D ⟨δ,hδ⟩ g r) n
  simpa only [(translateRay D ⟨δ,hδ⟩ g r).property.1, r.property.1, mul_one, CayleyData.graph] using h

end CannonRelease

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_VisualScale
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma product2_base_upper (hG : G.Connected) (o v x y : V) :
    product2 (G := G) o x y ≤ product2 (G := G) v x y + 2*G.dist o v := by
  have h₁ := product2_add_dist hG o x y
  have h₂ := product2_add_dist hG v x y
  have h₃ := @Connected.dist_triangle _ G o v x hG
  have h₄ := @Connected.dist_triangle _ G o v y hG
  omega

lemma product2_replace_endpoints (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (o a b a' b' : V)
    (ha : product2 (G := G) o a b + 2*(8*δ+6) < product2 (G := G) o a a')
    (hb : product2 (G := G) o a b + 2*(8*δ+6) < product2 (G := G) o b b') :
    product2 (G := G) o a b ≤ product2 (G := G) o a' b' + 2*(8*δ+6) ∧
    product2 (G := G) o a' b' ≤ product2 (G := G) o a b + 2*(8*δ+6) := by
  have h₁ := CannonVisual.product2_four hG hδ o a' a b b'
  have h₂ := CannonVisual.product2_four hG hδ o a a' b' b
  rw [product2_comm (o := o) (x := a') (y := a)] at h₁
  rw [product2_comm (o := o) (x := b') (y := b)] at h₂
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma product2_mul (g o x y : G) :
    product2 (G := D.graph) (g*o) (g*x) (g*y) = product2 (G := D.graph) o x y := by
  simp only [product2, D.dist_mul_left]

local instance instSetoidBasedRay_4_r693251_1 : Setoid (BasedRay D) := raySetoid D
omit [TopologicalSpace G] [DiscreteTopology G] in
include hδ in
lemma product2_ray_bounded {r s : BasedRay D} (h : ¬ (raySetoid D).r r s) :
    ∃ C : ℕ, ∀ n, product2 (G := D.graph) 1 (r.val n) (s.val n) ≤ C := by
  have hn : ∃ n, 2*δ < D.graph.dist (r.val n) (s.val n) := by
    by_contra hn
    push Not at hn
    exact h ⟨2*δ,hn⟩
  obtain ⟨k,hk⟩ := hn
  exact ⟨2*k+2*δ,product2_le_of_separated D.connected hδ r s hk⟩

lemma translated_mixed_product_large (g : G) (r : BasedRay D) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, C < product2 (G := D.graph) 1 (g*r.val n)
      ((translateRay D ⟨δ,hδ⟩ g r).val n) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  filter_upwards [Filter.eventually_ge_atTop (C+4*D.graph.dist 1 g+4*δ+1)] with n hn
  have hr := translateRay_uniform D hδ g r n
  have hp := product2_add_dist D.connected 1 (g*r.val n) (r'.val n)
  have ht := @SimpleGraph.Connected.dist_triangle _ D.graph g 1 (g*r.val n) D.connected
  have hg : D.graph.dist g (g*r.val n) = n := by
    simpa only [mul_one, r.property.1, Nat.dist_zero_left] using
      (D.dist_mul_left g 1 (r.val n)).trans (by simpa only [r.property.1, Nat.dist_zero_left] using r.property.2 0 n)
  have hr' : D.graph.dist 1 (r'.val n) = n := by
    simpa only [r'.property.1, Nat.dist_zero_left] using r'.property.2 0 n
  rw [hg, SimpleGraph.dist_comm (u := g) (v := 1)] at ht
  dsimp only [CayleyData.graph] at hr' hp
  rw [hr', SimpleGraph.dist_comm (u := g*r.val n) (v := r'.val n)] at hp
  change D.graph.dist (r'.val n) (g*r.val n) ≤ _ at hr
  change C < product2 (G := D.graph) 1 (g*r.val n) (r'.val n)
  dsimp only [CayleyData.graph] at *
  omega

lemma translated_product_independent_error (g : G) (r s : BasedRay D)
    (h : ¬ (raySetoid D).r r s) :
    ∀ᶠ n : ℕ in atTop,
      product2 (G := D.graph) 1 (g*r.val n) (g*s.val n) ≤
        product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
          ((translateRay D ⟨δ,hδ⟩ g s).val n) + 2*(8*δ+6) ∧
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
          ((translateRay D ⟨δ,hδ⟩ g s).val n) ≤
        product2 (G := D.graph) 1 (g*r.val n) (g*s.val n) + 2*(8*δ+6) := by
  obtain ⟨C,hC⟩ := product2_ray_bounded D hδ h
  let B := C + 2*D.graph.dist 1 g + 2*(8*δ+6)
  filter_upwards [translated_mixed_product_large D hδ g r B,
    translated_mixed_product_large D hδ g s B] with n hr hs
  have hp := product2_base_upper D.connected 1 g (g*r.val n) (g*s.val n)
  have he : product2 (G := D.graph) g (g*r.val n) (g*s.val n) =
      product2 (G := D.graph) 1 (r.val n) (s.val n) := by
    simpa only [mul_one] using product2_mul D g 1 (r.val n) (s.val n)
  dsimp only [CayleyData.graph] at hp he
  rw [he] at hp
  have hbound := hC n
  dsimp only [CayleyData.graph] at hbound
  apply product2_replace_endpoints D.connected hδ
  · dsimp [B] at hr
    dsimp only [CayleyData.graph] at *
    omega
  · dsimp [B] at hs
    dsimp only [CayleyData.graph] at *
    omega

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_prefix (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (r s : CannonVisual.Ray G o) {k n : ℕ} (hkn : k ≤ n) :
    product2 (G := G) o (r.val k) (s.val n) ≤
      min (2*k) (product2 (G := G) o (r.val n) (s.val n)) ∧
    min (2*k) (product2 (G := G) o (r.val n) (s.val n)) ≤
      product2 (G := G) o (r.val k) (s.val n) + (8*δ+6) := by
  have hr (j : ℕ) : G.dist o (r.val j) = j := by
    simpa only [r.property.1, Nat.dist_zero_left] using r.property.2 0 j
  have hs (j : ℕ) : G.dist o (s.val j) = j := by
    simpa only [s.property.1, Nat.dist_zero_left] using s.property.2 0 j
  have h₁ := product2_add_dist hG o (r.val k) (s.val n)
  have h₂ := product2_add_dist hG o (r.val n) (s.val n)
  have ht := @Connected.dist_triangle _ G (r.val n) (r.val k) (s.val n) hG
  rw [r.property.2, Nat.dist_eq_sub_of_le_right hkn] at ht
  rw [hr, hs] at h₁ h₂
  have hup := product2_le_twice_left hG o (r.val k) (s.val n)
  rw [hr] at hup
  have hself : product2 (G := G) o (r.val k) (r.val n) = 2*k := by
    unfold product2
    rw [hr,hr,r.property.2,Nat.dist_eq_sub_of_le hkn]
    omega
  have hlow := product2_hyperbolic hG hδ o (r.val k) (r.val n) (s.val n)
  rw [hself] at hlow
  constructor <;> omega

lemma product2_base_change (hG : G.Connected) (o v y z : V) :
    product2 (G := G) v y z + product2 (G := G) o v y + product2 (G := G) o v z =
      product2 (G := G) o y z + 2*G.dist o v := by
  have h₁ := product2_add_dist hG v y z
  have h₂ := product2_add_dist hG o v y
  have h₃ := product2_add_dist hG o v z
  have h₄ := product2_add_dist hG o y z
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_7_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma expansion_product_sums (x y z : BasedRay D) (k : ℕ)
    (hyz : ¬ (raySetoid D).r y z) :
    let g := (x.val k)⁻¹
    ∀ᶠ n : ℕ in atTop,
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g y).val n)
        ((translateRay D ⟨δ,hδ⟩ g z).val n) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (y.val n)) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (z.val n)) ≤
          product2 (G := D.graph) 1 (y.val n) (z.val n) + 2*k + 4*(8*δ+6) ∧
      product2 (G := D.graph) 1 (y.val n) (z.val n) + 2*k ≤
        product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g y).val n)
          ((translateRay D ⟨δ,hδ⟩ g z).val n) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (y.val n)) +
        min (2*k) (product2 (G := D.graph) 1 (x.val n) (z.val n)) + 2*(8*δ+6) := by
  let g := (x.val k)⁻¹
  filter_upwards [translated_product_independent_error D hδ g y z hyz,
    Filter.eventually_ge_atTop k] with n hn hkn
  have hy := product2_prefix D.connected hδ x y hkn
  have hz := product2_prefix D.connected hδ x z hkn
  have hid := product2_base_change D.connected 1 (x.val k) (y.val n) (z.val n)
  have hd : D.graph.dist 1 (x.val k) = k := by
    simpa only [x.property.1, Nat.dist_zero_left] using x.property.2 0 k
  have he : product2 (G := D.graph) 1 (g*y.val n) (g*z.val n) =
      product2 (G := D.graph) (x.val k) (y.val n) (z.val n) := by
    simpa only [g,inv_mul_cancel] using product2_mul D ((x.val k)⁻¹) (x.val k) (y.val n) (z.val n)
  dsimp only [CayleyData.graph] at *
  rw [hd] at hid
  rw [he] at hn
  dsimp only [g] at *
  constructor <;> omega

end CannonRelease

namespace CannonReal
lemma exp_neg_nat_min (ε : ℝ) (hε : 0 ≤ ε) (a b : ℕ) :
    Real.exp (-ε * (min a b : ℕ)) =
      max (Real.exp (-ε * (a : ℝ))) (Real.exp (-ε * (b : ℝ))) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_left]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hab) (neg_nonpos.mpr hε)
  · rw [min_eq_right hba, max_eq_right]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hba) (neg_nonpos.mpr hε)

lemma exp_expansion (ε : ℝ) (hε : 0 ≤ ε) (E A B C K k : ℕ)
    (h₁ : E + min (2*k) A + min (2*k) B ≤ C+2*k+4*K)
    (h₂ : C+2*k ≤ E+min (2*k) A+min (2*k) B+2*K) :
    Real.exp (-ε*(E:ℝ)) * max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(A:ℝ))) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(B:ℝ))) ≤
      Real.exp (ε*(2*K:ℕ)) * Real.exp (-ε*(2*k:ℕ)) * Real.exp (-ε*(C:ℝ)) ∧
    Real.exp (-ε*(2*k:ℕ)) * Real.exp (-ε*(C:ℝ)) ≤
      Real.exp (ε*(4*K:ℕ)) * (Real.exp (-ε*(E:ℝ)) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(A:ℝ))) *
        max (Real.exp (-ε*(2*k:ℕ))) (Real.exp (-ε*(B:ℝ)))) := by
  rw [← exp_neg_nat_min ε hε, ← exp_neg_nat_min ε hε]
  have h₁' : (E:ℝ) + (min (2*k) A : ℕ) + (min (2*k) B : ℕ) ≤
      (C:ℝ) + (2*k:ℕ) + (4*K:ℕ) := by exact_mod_cast h₁
  have h₂' : (C:ℝ)+(2*k:ℕ) ≤ (E:ℝ)+(min (2*k) A : ℕ)+(min (2*k) B : ℕ)+(2*K:ℕ) := by
    exact_mod_cast h₂
  constructor <;> repeat rw [← Real.exp_add]
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_exp.mpr
    nlinarith
end CannonReal

namespace CannonVisual
lemma visualScale_pos (δ k : ℕ) : 0 < visualScale δ k := Real.exp_pos _
end CannonVisual

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_8_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma preDist_expansion (x y z : BasedRay D) (k : ℕ)
    (hyz : ¬ (raySetoid D).r y z) :
    let g := (x.val k)⁻¹
    let R := visualScale δ k
    let E := (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g y)
      (translateRay D ⟨δ,hδ⟩ g z) : ℝ)
    let A := max R (preDist (visualExponent δ) x y : ℝ)
    let B := max R (preDist (visualExponent δ) x z : ℝ)
    E*A*B ≤ Real.exp (visualExponent δ * (2*(8*δ+6):ℕ))*R*(preDist (visualExponent δ) y z : ℝ) ∧
    R*(preDist (visualExponent δ) y z : ℝ) ≤ Real.exp (visualExponent δ * (4*(8*δ+6):ℕ))*(E*A*B) := by
  let g := (x.val k)⁻¹
  let y' := translateRay D ⟨δ,hδ⟩ g y
  let z' := translateRay D ⟨δ,hδ⟩ g z
  have hlim (r s : BasedRay D) : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_decay D.connected (visualExponent_pos δ).le r s)
  have he : ∀ᶠ n : ℕ in atTop,
      (decay (visualExponent δ) y' z' n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x y n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x z n : ℝ) ≤
      Real.exp (visualExponent δ * (2*(8*δ+6):ℕ))*visualScale δ k*(decay (visualExponent δ) y z n : ℝ) ∧
      visualScale δ k*(decay (visualExponent δ) y z n : ℝ) ≤
      Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)) *
        ((decay (visualExponent δ) y' z' n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x y n : ℝ) *
        max (visualScale δ k) (decay (visualExponent δ) x z n : ℝ)) := by
    filter_upwards [expansion_product_sums D hδ x y z k hyz] with n hn
    exact CannonReal.exp_expansion (visualExponent δ) (visualExponent_pos δ).le _ _ _ _ _ _ hn.1 hn.2
  have hf := ((hlim y' z').mul ((tendsto_const_nhds (x := visualScale δ k)).max (hlim x y))).mul
    ((tendsto_const_nhds (x := visualScale δ k)).max (hlim x z))
  constructor
  · exact le_of_tendsto_of_tendsto hf ((hlim y z).const_mul _) (he.mono fun _ h => h.1)
  · exact le_of_tendsto_of_tendsto ((hlim y z).const_mul _) (hf.const_mul _) (he.mono fun _ h => h.2)

end CannonRelease

namespace CannonReal
lemma max_le_twice_max {R d p : ℝ} (hR : 0 ≤ R) (hp : p ≤ 2*d) :
    max R p ≤ 2*max R d := by
  apply max_le
  · have := le_max_left R d
    nlinarith
  · exact hp.trans (mul_le_mul_of_nonneg_left (le_max_right R d) (by norm_num))

lemma mul_three_le {a b c A B C : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    a*b*c ≤ A*B*C :=
  mul_le_mul (mul_le_mul ha hb hb₀ hA) hc hc₀ (mul_nonneg hA hB)
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_9_r693251_1 : Setoid (BasedRay D) := raySetoid D
theorem visual_expansion_ray (r : BasedRay D) (k : ℕ) (y z : Boundary D) :
    let _ := visualMetricSpace D hδ
    let g := (r.val k)⁻¹
    let x : Boundary D := Quotient.mk' r
    let R := visualScale δ k
    let E := (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z)
    let A := max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) x y)
    let B := max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) x z)
    E*A*B ≤ (2*Real.exp (visualExponent δ * (2*(8*δ+6):ℕ)))*R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ∧
      R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ≤ (8*Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)))*(E*A*B) := by
  let _ := visualMetricSpace D hδ
  by_cases hyz : y = z
  · subst z
    simp only [dist_self,zero_mul,mul_zero,le_refl,and_self]
  induction y,z using Quotient.inductionOn₂ with | h a b =>
    let g := (r.val k)⁻¹
    let a' := translateRay D ⟨δ,hδ⟩ g a
    let b' := translateRay D ⟨δ,hδ⟩ g b
    let R := visualScale δ k
    have hR : 0 ≤ R := (visualScale_pos δ k).le
    have hab : ¬ (raySetoid D).r a b := fun h => hyz (Quotient.sound h)
    have hh := preDist_expansion D hδ r a b k hab
    have hc (s t : BasedRay D) := visualMetric_comparison D hδ s t
    have hm (s : BasedRay D) : max R (preDist (visualExponent δ) r s : ℝ) ≤
        2*max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' s : Boundary D)) :=
      CannonReal.max_le_twice_max hR (hc r s).2
    have hn₁ : 0 ≤ max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) := hR.trans (le_max_left _ _)
    have hn₂ : 0 ≤ max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)) := hR.trans (le_max_left _ _)
    have hp₁ : 0 ≤ max R (preDist (visualExponent δ) r a : ℝ) := hR.trans (le_max_left _ _)
    have hp₂ : 0 ≤ max R (preDist (visualExponent δ) r b : ℝ) := hR.trans (le_max_left _ _)
    have hlo := CannonReal.mul_three_le (hc a' b').1
      (max_le_max_left R (hc r a).1) (max_le_max_left R (hc r b).1)
      hn₁ hn₂ (NNReal.coe_nonneg _) hp₁
    have hup := CannonReal.mul_three_le (hc a' b').2 (hm a) (hm b)
      hp₁ hp₂ (mul_nonneg (by norm_num) dist_nonneg) (mul_nonneg (by norm_num) hn₁)
    change (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) *
        max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) * max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)) ≤
      (2*Real.exp (visualExponent δ * (2*(8*δ+6):ℕ)))*R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) ∧
      R*(@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) ≤
        (8*Real.exp (visualExponent δ * (4*(8*δ+6):ℕ)))*
          ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) *
            max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' a : Boundary D)) * max R ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' r : Boundary D) (Quotient.mk' b : Boundary D)))
    constructor
    · have h := (hlo.trans hh.1).trans (mul_le_mul_of_nonneg_left (hc a b).2
        (mul_nonneg (Real.exp_pos _).le hR))
      exact h.trans_eq (by ring)
    · have h := (mul_le_mul_of_nonneg_left (hc a b).1 hR).trans hh.2
      exact (h.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)).trans_eq (by ring)

end CannonRelease

namespace CannonVisual
lemma visualScale_eq_pow (δ k : ℕ) :
    visualScale δ k = (Real.exp (-(2*visualExponent δ)))^k := by
  rw [← Real.exp_nat_mul]
  unfold visualScale
  congr 1
  push_cast
  ring

lemma visualScale_near (δ : ℕ) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ∃ k : ℕ, r ≤ visualScale δ k ∧
      visualScale δ k ≤ Real.exp (2*visualExponent δ)*r := by
  have he := visualExponent_pos δ
  have hq : Real.exp (-(2*visualExponent δ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  obtain ⟨k,hk₁,hk₂⟩ := exists_nat_pow_near_of_lt_one hr hr₁ (Real.exp_pos _) hq
  refine ⟨k,by simpa [visualScale_eq_pow] using hk₂,?_⟩
  rw [pow_succ] at hk₁
  have h := mul_lt_mul_of_pos_right hk₁ (Real.exp_pos (2*visualExponent δ))
  have hex : Real.exp (-(2*visualExponent δ))*Real.exp (2*visualExponent δ) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [mul_assoc,hex,mul_one] at h
  simpa only [visualScale_eq_pow,mul_comm] using h.le

end CannonVisual

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryDist
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_10_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma boundaryDist_le_one (x y : Boundary D) : boundaryDist D hδ x y ≤ 1 := by
  induction x,y using Quotient.inductionOn₂ with | h r s =>
    dsimp only [boundaryDist, Quotient.mk', CayleyData.graph, Thin] at *
    apply (visualMetric_comparison D hδ r s).1.trans
    have hh := preDist_le_decay (visualExponent δ) r s 0
    have hh' : (preDist (visualExponent δ) r s : ℝ) ≤ (decay (visualExponent δ) r s 0 : ℝ) := by exact_mod_cast hh
    apply hh'.trans_eq
    simp [decay,product2,r.property.1,s.property.1]
    rfl

end CannonRelease

noncomputable section
open Set Metric Topology

namespace CannonPaths
variable {X : Type*} [MetricSpace X]

lemma joined_avoid_buffer {p u v : X} {r : ℝ}
    (h : JoinedIn {z | r < dist p z} u v) :
    ∃ s > r, JoinedIn {z | s < dist p z} u v := by
  obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set unitInterval).Nonempty)
    (continuous_const.dist h.somePath.continuous).continuousOn
  have hh : r < dist p (h.somePath t) := h.somePath_mem t
  refine ⟨(r+dist p (h.somePath t))/2,by linarith,h.somePath,fun a => ?_⟩
  have ha := ht (Set.mem_univ a)
  dsimp at ha ⊢
  linarith

variable [LocallyPathConnectedSpace X]

lemma isOpen_joined_avoid (r : ℝ) :
    IsOpen {t : X × X × X | JoinedIn {z | r < dist t.1 z} t.2.1 t.2.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨p,u,v⟩ h
  obtain ⟨s,hrs,hs⟩ := joined_avoid_buffer h
  let V := {z : X | s < dist p z}
  have hV : IsOpen V := isOpen_lt continuous_const (continuous_const.dist continuous_id)
  have hu : u ∈ pathComponentIn V u := mem_pathComponentIn_self hs.source_mem
  have hv : v ∈ pathComponentIn V v := mem_pathComponentIn_self hs.target_mem
  refine Filter.mem_of_superset (prod_mem_nhds (ball_mem_nhds p (sub_pos.mpr hrs))
    (prod_mem_nhds ((hV.pathComponentIn u).mem_nhds hu) ((hV.pathComponentIn v).mem_nhds hv))) ?_
  rintro ⟨p',u',v'⟩ ⟨hp',hu',hv'⟩
  have hj : JoinedIn V u' v' := hu'.symm.trans (hs.trans hv')
  apply hj.mono
  intro z hz
  have ht := dist_triangle p p' z
  have hp : dist p p' < s-r := by simpa only [mem_ball,dist_comm] using hp'
  dsimp [V] at hz ⊢
  linarith

theorem uniform_avoidance [CompactSpace X]
    (hpuncture : ∀ p : X, IsPathConnected ({p}ᶜ : Set X)) {e : ℝ} (he : 0 < e) :
    ∃ r > 0, ∀ p u v : X, e ≤ dist p u → e ≤ dist p v →
      JoinedIn {z | r < dist p z} u v := by
  classical
  let K : Set (X × X × X) := {t | e ≤ dist t.1 t.2.1 ∧ e ≤ dist t.1 t.2.2}
  have hK : IsCompact K := (IsClosed.inter
    (isClosed_le continuous_const (continuous_fst.dist (continuous_fst.comp continuous_snd)))
    (isClosed_le continuous_const (continuous_fst.dist (continuous_snd.comp continuous_snd)))).isCompact
  let V : {r : ℝ // 0 < r} → Set (X × X × X) := fun r =>
    {t | JoinedIn {z | r.val < dist t.1 z} t.2.1 t.2.2}
  have hcover : K ⊆ ⋃ r, V r := by
    rintro ⟨p,u,v⟩ ⟨hu,hv⟩
    have hpu : u ∈ ({p}ᶜ : Set X) := by
      simp only [mem_compl_iff,mem_singleton_iff]
      intro h; subst u; simp at hu; linarith
    have hpv : v ∈ ({p}ᶜ : Set X) := by
      simp only [mem_compl_iff,mem_singleton_iff]
      intro h; subst v; simp at hv; linarith
    have hj := (hpuncture p).joinedIn u hpu v hpv
    have hj' : JoinedIn {z | 0 < dist p z} u v := hj.mono (by
      intro z hz
      exact dist_pos.mpr (Ne.symm hz))
    obtain ⟨r,hr,hh⟩ := joined_avoid_buffer hj'
    exact mem_iUnion.mpr ⟨⟨r,hr⟩,hh⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V (fun r => isOpen_joined_avoid r.val) hcover

  let a : ℝ := ∏ t ∈ s, min 1 t.val
  have ha : 0 < a := Finset.prod_pos (fun t _ => lt_min (by norm_num) t.property)
  refine ⟨a,ha,fun p u v hu hv => ?_⟩
  obtain ⟨b,hb⟩ := mem_iUnion.mp (hs (show (p,u,v) ∈ K from ⟨hu,hv⟩))
  obtain ⟨hb,hh⟩ := mem_iUnion.mp hb
  have hab : a ≤ b.val := (Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr hb)
    (fun t _ => (le_min (by norm_num) t.property.le)) (fun t _ _ => min_le_left _ _)).trans ?_
  · exact hh.mono (fun z hz => lt_of_le_of_lt hab hz)
  · simp only [Finset.prod_singleton]
    exact min_le_right _ _

end CannonPaths
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTwo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPaths

lemma sphere_locallyPathConnected : LocallyPathConnectedSpace SphereTwo := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  exact ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) SphereTwo

lemma sphere_punctured_pathConnected (p : SphereTwo) :
    IsPathConnected ({p}ᶜ : Set SphereTwo) := by
  have hc := (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere p)).continuous
  have hh := isPathConnected_range hc
  have he : Set.range (stereographic (norm_eq_of_mem_sphere p)).symm = {p}ᶜ :=
    range_stereographic_symm (norm_eq_of_mem_sphere p) p.property
  rw [← he]
  exact hh

lemma sphere_pathConnected : PathConnectedSpace SphereTwo := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  simp

end CannonPaths

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_ImageAwayPuncture
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPaths
open Set Metric

variable {X : Type*} [MetricSpace X]

lemma image_away_from_puncture {x y q : X} {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hy : dist x y ≤ R) (hq : 2*R ≤ dist x q) (f : X → X)
    (h : R*dist y q ≤ L*(dist (f y) (f q)*max R (dist x y)*max R (dist x q))) :
    1/(2*L) ≤ dist (f y) (f q) := by
  have hRq : R ≤ dist x q := by linarith
  rw [max_eq_left hy,max_eq_right hRq] at h
  have hh : dist y q ≤ L*dist (f y) (f q)*dist x q := by
    apply (mul_le_mul_iff_right₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have ht := dist_triangle x y q
  have hdq : 0 < dist x q := lt_of_lt_of_le hR hRq
  apply (div_le_iff₀ (by positivity : 0 < 2*L)).mpr
  have hh' : dist x q ≤ (dist (f y) (f q)*(2*L))*dist x q := by nlinarith
  exact (mul_le_mul_iff_left₀ hdq).mp (by simpa only [one_mul] using hh')

lemma preimage_near_center {x y q : X} {R C e d : ℝ}
    (hR : 0 < R) (hC : 0 < C) (he : 0 < e) (hd : 0 < d)
    (hq : d ≤ dist x q) (hdiam : dist y q ≤ 1) (f : X → X)
    (hfar : e < dist (f y) (f q))
    (h : dist (f y) (f q)*max R (dist x y)*max R (dist x q) ≤ C*R*dist y q) :
    dist x y < (C/(e*d)+1)*R := by
  have hxy := dist_nonneg (x := x) (y := y)
  have hRq : 0 ≤ max R (dist x q) := hR.le.trans (le_max_left _ _)
  have hRy : 0 ≤ max R (dist x y) := hR.le.trans (le_max_left _ _)
  have h1 : e*dist x y*d ≤ dist (f y) (f q)*max R (dist x y)*max R (dist x q) :=
    mul_le_mul (mul_le_mul hfar.le (le_max_right _ _) hxy (dist_nonneg))
      (hq.trans (le_max_right _ _)) hd.le (mul_nonneg dist_nonneg hRy)
  have h2 : e*dist x y*d ≤ C*R := h1.trans (h.trans (mul_le_of_le_one_right (mul_nonneg hC.le hR.le) hdiam))
  have h3 : dist x y ≤ C/(e*d)*R := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos he hd)).mpr
    nlinarith
  nlinarith

end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_12_r693251_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_controlled_paths (φ : Boundary D ≃ₜ SphereTwo) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (x u v : Boundary D) (s : ℝ), 0 < s →
      boundaryDist D hδ x u ≤ s → boundaryDist D hδ x v ≤ s →
      JoinedIn {z | boundaryDist D hδ x z < L*s} u v := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  have hpuncture (p : Boundary D) : IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
    have hh := (CannonPaths.sphere_punctured_pathConnected (φ p)).image φ.symm.continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    constructor
    · intro hz
      refine ⟨φ z,?_,φ.symm_apply_apply z⟩
      exact fun h => hz (φ.injective h)
    · rintro ⟨w,hw,hwz⟩ heq
      apply hw
      apply φ.symm.injective
      change z = p at heq
      simpa only [φ.symm_apply_apply] using hwz.trans heq
  let p : SphereTwo := ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ),by simp⟩
  let a := φ.symm p
  let b := φ.symm (-p)
  have hab : a ≠ b := fun h => (ne_neg_of_mem_unit_sphere ℝ p) (φ.symm.injective h)
  let d := dist a b/2
  have hd : 0 < d := half_pos (dist_pos.mpr hab)
  have hfar (x : Boundary D) : ∃ q : Boundary D, d ≤ dist x q := by
    by_cases h : d ≤ dist x a
    · exact ⟨a,h⟩
    · refine ⟨b,?_⟩
      have hh := dist_triangle a x b
      rw [dist_comm a x] at hh
      dsimp [d] at *
      linarith
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := Real.exp_pos _
  obtain ⟨e,he,hpaths⟩ := CannonPaths.uniform_avoidance hpuncture
    (show 0 < 1/(2*B) by positivity)
  let t := min 1 (d/(2*A))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hd (by positivity))
  let F := (C/(e*d)+1)*A
  have hF : 0 < F := mul_pos (by positivity) hA
  let L := F+1/t+1
  have hL : 1 ≤ L := by
    have : 0 < 1/t := one_div_pos.mpr ht
    dsimp [L]
    linarith
  refine ⟨L,hL,fun x u v s hs hu hv => ?_⟩
  by_cases hsmall : s ≤ t
  · obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs (hsmall.trans (min_le_left _ _))
    obtain ⟨r,hr⟩ := Quotient.exists_rep x
    subst x
    obtain ⟨q,hq⟩ := hfar (Quotient.mk' r)
    let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
    have hp : 2*visualScale δ k ≤ boundaryDist D hδ (Quotient.mk' r) q := by
      have hh : 2*A*s ≤ d := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp (hsmall.trans (min_le_right _ _))
        nlinarith
      have hh' : visualScale δ k ≤ A*s := hk'
      nlinarith
    have hu' : 1/(2*B) ≤ dist (f u) (f q) := image_away_from_puncture (X := Boundary D)
      (visualScale_pos δ k) hB (hu.trans hk) hp f (visual_expansion_ray D hδ r k u q).2
    have hv' : 1/(2*B) ≤ dist (f v) (f q) := image_away_from_puncture (X := Boundary D)
      (visualScale_pos δ k) hB (hv.trans hk) hp f (visual_expansion_ray D hδ r k v q).2
    have hj := hpaths (f q) (f u) (f v) (by simpa only [dist_comm] using hu')
      (by simpa only [dist_comm] using hv')
    have hm := hj.map_continuousOn f.symm.continuous.continuousOn
    simp only [f.symm_apply_apply] at hm
    apply hm.mono
    rintro z ⟨w,hw,rfl⟩
    have hz : boundaryDist D hδ (Quotient.mk' r) (f.symm w) < (C/(e*d)+1)*visualScale δ k := by
      apply preimage_near_center (X := Boundary D) (visualScale_pos δ k) hC he hd hq
        (boundaryDist_le_one D hδ _ _) f _ (visual_expansion_ray D hδ r k (f.symm w) q).1
      change e < dist (f q) w at hw
      simpa only [f.apply_symm_apply,dist_comm] using hw
    have hc : 0 ≤ C/(e*d)+1 := by positivity
    have hf : F ≤ L := by
      have : 0 < 1/t := one_div_pos.mpr ht
      dsimp [L]; linarith
    calc
      _ < (C/(e*d)+1)*visualScale δ k := hz
      _ ≤ (C/(e*d)+1)*(A*s) := mul_le_mul_of_nonneg_left hk' hc
      _ = F*s := by dsimp [F]; ring
      _ ≤ L*s := mul_le_mul_of_nonneg_right hf hs.le
  · have hts : t < s := lt_of_not_ge hsmall
    have hbig : 1 < L*s := by
      have hst : 1 < s/t := (lt_div_iff₀ ht).mpr (by simpa using hts)
      have hh : s/t ≤ L*s := by
        have hle : 1/t ≤ L := by dsimp [L]; linarith
        simpa only [one_div,inv_mul_eq_div] using mul_le_mul_of_nonneg_right hle hs.le
      exact hst.trans_le hh
    exact (joinedIn_univ.mpr (PathConnectedSpace.joined u v)).mono (fun z _ =>
      (boundaryDist_le_one D hδ x z).trans_lt hbig)

end CannonRelease

namespace CannonPaths
open Set Metric

lemma expansion_endpoint_clearance {R B A s d q : ℝ}
    (hR : 0<R) (hB : 0<B) (hA : 1 ≤ A) (hs : 0 < s) (hq : 0 ≤ q)
    (hsd : s ≤ d) (hRA : R ≤ A*s)
    (hexp : R*d ≤ B*(q*R*max R d)) : 1/(B*A) ≤ q := by
  have hd : 0<d := hs.trans_le hsd
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hmax : max R d ≤ A*d := max_le
    (hRA.trans (mul_le_mul_of_nonneg_left hsd hAp.le)) (by nlinarith)
  have hc : d ≤ B*q*max R d := by
    apply (mul_le_mul_iff_left₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left hmax (mul_nonneg hB.le hq)
  have hh : 1 ≤ B*A*q := by nlinarith [hc,hm]
  apply (div_le_iff₀ (mul_pos hB hAp)).mpr
  nlinarith

lemma expansion_preimage_clearance {R C s d q e : ℝ}
    (hR : 0<R) (hC : 0<C) (hs : 0 < s) (hsR : s ≤ R)
    (he : 0<e) (heq : e<q)
    (hexp : q*R*max R d ≤ C*R*d) : (e/C)*s<d := by
  have hq : 0<q := he.trans heq
  have hc : q*max R d ≤ C*d := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left (le_max_left R d) hq.le
  have heq' := mul_lt_mul_of_pos_right heq hs
  have hsR' := mul_le_mul_of_nonneg_left hsR hq.le
  have ht : e*s<C*d := by linarith
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hC).mpr (by nlinarith)

end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_13_r693251_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_outside_paths (φ : Boundary D ≃ₜ SphereTwo) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (x u v : Boundary D) (s : ℝ), 0 < s →
      s ≤ boundaryDist D hδ x u → s ≤ boundaryDist D hδ x v →
      JoinedIn {z | c*s < boundaryDist D hδ x z} u v := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  have hpuncture (p : Boundary D) : IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
    have hh := (CannonPaths.sphere_punctured_pathConnected (φ p)).image φ.symm.continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    constructor
    · intro hz
      refine ⟨φ z,?_,φ.symm_apply_apply z⟩
      exact fun h => hz (φ.injective h)
    · rintro ⟨w,hw,hwz⟩ heq
      apply hw
      apply φ.symm.injective
      change z=p at heq
      simpa only [φ.symm_apply_apply] using hwz.trans heq
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1 ≤ A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨e,he,hpaths⟩ := CannonPaths.uniform_avoidance hpuncture
    (show 0<1/(B*A) by positivity)
  let c := min 1 (e/C)
  have hc : 0 < c := lt_min zero_lt_one (div_pos he hC)
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro x u v s hs hu hv
  have hsone : s ≤ 1 := hu.trans (boundaryDist_le_one D hδ x u)
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hsone
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r) = 0 := dist_self _
  have hund (y : Boundary D) (hy : s ≤ boundaryDist D hδ (Quotient.mk' r : Boundary D) y) :
      1/(B*A) ≤ (boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f y) := by
    apply expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs dist_nonneg hy hk'
    have h := (visual_expansion_ray D hδ r k (Quotient.mk' r : Boundary D) y).2
    change visualScale δ k*(boundaryDist D hδ) (Quotient.mk' r : Boundary D) y ≤ B*((boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f y)*
      max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (Quotient.mk' r : Boundary D))*
      max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) y)) at h
    simpa only [hself,max_eq_left (visualScale_pos δ k).le] using h
  have hj := hpaths (f (Quotient.mk' r : Boundary D)) (f u) (f v) (hund u hu) (hund v hv)
  have hm := hj.map_continuousOn f.symm.continuous.continuousOn
  simp only [f.symm_apply_apply] at hm
  apply hm.mono
  rintro z ⟨w,hw,rfl⟩
  have h := (visual_expansion_ray D hδ r k (Quotient.mk' r : Boundary D) (f.symm w)).1
  change (boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f (f.symm w))*
    max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (Quotient.mk' r : Boundary D))*
    max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (f.symm w)) ≤
    C*visualScale δ k*(boundaryDist D hδ) (Quotient.mk' r : Boundary D) (f.symm w) at h
  simp only [f.apply_symm_apply,hself,max_eq_left (visualScale_pos δ k).le] at h
  have hclear := expansion_preimage_clearance (visualScale_pos δ k) hC hs hk he hw h
  exact (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (e/C)) hs.le).trans_lt hclear

end CannonRelease

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_WordBall
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section

noncomputable section
open Set Topology

noncomputable section

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_27_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma visual_ball_expansion (r : BasedRay D) (k : ℕ) (y z : Boundary D)
    (hy : boundaryDist D hδ (Quotient.mk' r) y ≤ visualScale δ k)
    (hz : boundaryDist D hδ (Quotient.mk' r) z ≤ visualScale δ k) :
    let E := boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
      (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z)
    E*visualScale δ k ≤ (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*boundaryDist D hδ y z ∧
      boundaryDist D hδ y z ≤ (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*E*visualScale δ k := by
  have hh := visual_expansion_ray D hδ r k y z
  change _ ∧ _ at hh
  change _ ∧ _
  have hR := visualScale_pos δ k
  rw [max_eq_left hy,max_eq_left hz] at hh
  constructor
  · apply (mul_le_mul_iff_left₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.1
  · apply (mul_le_mul_iff_right₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.2

end CannonRelease

namespace CannonGraph
open SimpleGraph

variable {M : Type*} [Group M]

lemma one_mem_wordBall (S : Finset M) (n : ℕ) : 1 ∈ wordBall S n := by
  classical
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    simp only [wordBall] at *
    exact Finset.mem_biUnion.mpr ⟨1,ih,Finset.mem_image.mpr ⟨1,Finset.mem_insert_self _ _,one_mul 1⟩⟩

lemma wordBall_step (S : Finset M) {x y : M} {n : ℕ} (hx : x ∈ wordBall S n)
    (hy : y = 1 ∨ y ∈ S) : x*y ∈ wordBall S (n+1) := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hx,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩
  exact (Finset.mem_insert).mpr hy

lemma walk_end_mem_wordBall (S : Finset M) (hs : ∀ x ∈ S, x⁻¹ ∈ S)
    {x : M} (p : (mulCayley (S : Set M)).Walk 1 x) {n : ℕ} (hp : p.length ≤ n) :
    x ∈ wordBall S n := by
  classical
  induction n generalizing x with
  | zero =>
    have he := Walk.eq_of_length_eq_zero (p := p) (show p.length = 0 by omega)
    rw [← he]
    exact one_mem_wordBall S 0
  | succ n ih =>
    by_cases hz : p.length = 0
    · have he := Walk.eq_of_length_eq_zero hz
      rw [← he]
      exact one_mem_wordBall S (n+1)
    · have hp' : p.dropLast.length ≤ n := by rw [Walk.length_dropLast]; omega
      have hprev := ih p.dropLast hp'
      have hadj := p.adj_penultimate (by simpa only [← Walk.length_eq_zero_iff] using hz)
      obtain ⟨_,g,hg,he⟩ := (mulCayley_adj' (S : Set M) p.penultimate x).mp hadj
      rcases he with he | he
      · rw [← he]
        exact wordBall_step S hprev (Or.inr hg)
      · have he' : x = p.penultimate*g⁻¹ := by rw [he]; simp
        rw [he']
        exact wordBall_step S hprev (Or.inr (hs g hg))

lemma wordBall_card (S : Finset M) (n : ℕ) : (wordBall S n).card ≤ (S.card+1)^n := by
  classical
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    calc
      _ ≤ ∑ x ∈ wordBall S n, ((insert 1 S).image (x*·)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ wordBall S n, (S.card+1) := Finset.sum_le_sum (fun x _ =>
        (Finset.card_image_le).trans (Finset.card_insert_le _ _))
      _ = (wordBall S n).card*(S.card+1) := by simp
      _ ≤ (S.card+1)^n*(S.card+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_29_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma boundaryDist_le_of_prefix (r s : BasedRay D) {n : ℕ} (h : r.val n = s.val n) :
    boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) ≤ visualScale δ n := by
  apply (visualMetric_comparison D hδ r s).1.trans
  have hh : (preDist (visualExponent δ) r s : ℝ) ≤ (decay (visualExponent δ) r s n : ℝ) :=
    preDist_le_decay _ _ _ _
  apply hh.trans_eq
  rw [decay_of_agree _ r s h]
  unfold visualScale
  congr 1
  push_cast
  ring

lemma global_prefix_packing (n : ℕ) (s : Finset (Boundary D))
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → visualScale δ n < boundaryDist D hδ x y) :
    s.card ≤ (D.generators.card+1)^n := by
  classical
  choose r hr using (fun x : Boundary D => Quotient.exists_rep x)
  have hword (x : Boundary D) : (r x).val n ∈ wordBall D.generators n := by
    obtain ⟨p,hp⟩ := D.connected.exists_walk_length_eq_dist 1 ((r x).val n)
    apply walk_end_mem_wordBall D.generators D.symmetric p
    rw [hp]
    change D.graph.dist 1 ((r x).val n) ≤ n
    have hd := (r x).property.2 0 n
    dsimp only [CayleyData.graph] at hd ⊢
    simpa only [(r x).property.1,Nat.dist_zero_left] using hd.le
  let F : ↥s → ↥(wordBall D.generators n) := fun x => ⟨(r x.val).val n,hword x.val⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hn
    have hh := boundaryDist_le_of_prefix D hδ (r x.val) (r y.val) (congrArg Subtype.val hxy)
    dsimp only [Quotient.mk',CayleyData.graph,Thin] at hh
    rw [hr x.val,hr y.val] at hh
    exact not_lt_of_ge hh (hs x.val x.property y.val y.property hn)
  have hcard := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hcard
  exact hcard.trans (wordBall_card D.generators n)

end CannonRelease

namespace CannonReal
lemma power_counting_bound {A B : ℝ} (hA : 1 < A) (hB : 1 ≤ B) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∃ n : ℕ, (A⁻¹)^n < x ∧ B^n ≤ B*(1/x)^Q := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt B hA
  let Q := m+2
  have hApos : 0 < A := zero_lt_one.trans hA
  have hBQ : B ≤ A^Q := hm.le.trans (pow_le_pow_right₀ hA.le (by dsimp [Q]; omega))
  refine ⟨Q,by dsimp [Q]; omega,fun x hx hx₁ => ?_⟩
  obtain ⟨k,hk,hy⟩ := exists_nat_pow_near_of_lt_one hx hx₁ (inv_pos.mpr hApos)
    ((inv_lt_one₀ hApos).mpr hA)
  refine ⟨k+1,hk,?_⟩
  have hAk : 0 < A^k := pow_pos hApos k
  have hAx : A^k ≤ 1/x := by
    apply (le_div_iff₀ hx).mpr
    have hh := mul_le_mul_of_nonneg_right hy hAk.le
    rw [inv_pow,inv_mul_cancel₀ hAk.ne'] at hh
    simpa only [mul_comm] using hh
  have hpow : B^k ≤ (1/x)^Q := calc
    _ ≤ (A^Q)^k := pow_le_pow_left₀ (zero_le_one.trans hB) hBQ k
    _ = (A^k)^Q := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ (1/x)^Q := pow_le_pow_left₀ hAk.le hAx Q
  rw [pow_succ]
  calc
    B^k*B ≤ (1/x)^Q*B := mul_le_mul_of_nonneg_right hpow (zero_le_one.trans hB)
    _ = _ := mul_comm _ _
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

lemma global_polynomial_packing :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ s : Finset (Boundary D),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → e ≤ boundaryDist D hδ x y) →
      (s.card : ℝ) ≤ (D.generators.card+1)*(1/e)^Q := by
  let A := Real.exp (2*visualExponent δ)
  have hA : 1 < A := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  obtain ⟨Q,hQ,hbound⟩ := CannonReal.power_counting_bound hA
    (show (1:ℝ) ≤ (D.generators.card:ℝ)+1 by have h : (0:ℝ) ≤ D.generators.card := Nat.cast_nonneg _; linarith)
  refine ⟨Q,hQ,fun e he he₁ s hs => ?_⟩
  obtain ⟨n,hn,hBn⟩ := hbound e he he₁
  have hn' : visualScale δ n < e := by
    rw [visualScale_eq_pow]
    have hex : Real.exp (-(2*visualExponent δ)) = A⁻¹ := Real.exp_neg _
    rwa [hex]
  have hh := global_prefix_packing D hδ n s (fun x hx y hy hxy => hn'.trans_le (hs x hx y hy hxy))
  have hh' : (s.card:ℝ) ≤ (D.generators.card+1:ℝ)^n := by exact_mod_cast hh
  exact hh'.trans hBn

end CannonRelease

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_PolynomialPacking
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_31_r693251_1 : Setoid (BasedRay D) := raySetoid D
lemma relative_polynomial_packing :
    ∃ (Q : ℕ) (C : ℝ), 2 ≤ Q ∧ 0 < C ∧
      ∀ (x : Boundary D) (r s : ℝ), 0 < s → s ≤ r → r ≤ 1 →
      ∀ t : Finset (Boundary D),
      (∀ y ∈ t, boundaryDist D hδ x y ≤ r) →
      (∀ y ∈ t, ∀ z ∈ t, y ≠ z → s ≤ boundaryDist D hδ y z) →
      (t.card : ℝ) ≤ C*(r/s)^Q := by
  classical
  let _ := visualMetricSpace D hδ
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hL : 1 ≤ L := by
    have : 1 ≤ Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)) :=
      Real.one_le_exp (mul_nonneg (visualExponent_pos δ).le (Nat.cast_nonneg _))
    dsimp [L]; linarith
  have hA : 1 ≤ A := Real.one_le_exp (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hLA : 1 ≤ L*A := by nlinarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hApos : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨Q,hQ,hbound⟩ := global_polynomial_packing D hδ
  let B : ℝ := D.generators.card+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Q,B*(L*A)^Q,hQ,mul_pos hB (pow_pos (mul_pos hLpos hApos) Q),?_⟩
  intro x r s hs hsr hr t ht hsep
  have hrpos : 0 < r := hs.trans_le hsr
  let e := s/(r*(L*A))
  have he : 0 < e := div_pos hs (mul_pos hrpos (mul_pos hLpos hApos))
  have he₁ : e ≤ 1 := (div_le_one (by positivity)).mpr
    (hsr.trans (le_mul_of_one_le_right hrpos.le hLA))
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hrpos hr
  obtain ⟨r₀,hr₀⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryTranslate D ⟨δ,hδ⟩ (r₀.val k)⁻¹
  have hinj : Function.Injective f := (boundaryHomeomorph D ⟨δ,hδ⟩ (r₀.val k)⁻¹).injective
  have himage := hbound e he he₁ (t.image f) (by
    intro y hy z hz hyz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun heq => hyz (congrArg f heq)
    have hh := (visual_ball_expansion D hδ r₀ k u v ((ht u hu).trans hk) ((ht v hv).trans hk)).2
    change boundaryDist D hδ u v ≤ L*boundaryDist D hδ (f u) (f v)*visualScale δ k at hh
    have hn : 0 ≤ boundaryDist D hδ (f u) (f v) := dist_nonneg
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hk' (mul_nonneg hLpos.le hn))
    apply (div_le_iff₀ (mul_pos hrpos (mul_pos hLpos hApos))).mpr
    calc
      s ≤ boundaryDist D hδ u v := hsep u hu v hv huv
      _ ≤ L*boundaryDist D hδ (f u) (f v)*(A*r) := hh'
      _ = boundaryDist D hδ (f u) (f v)*(r*(L*A)) := by ring)
  rw [Finset.card_image_of_injective t hinj] at himage
  convert himage using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [e,B]
  rw [one_div_div]
  have hh : r*(L*A)/s = (L*A)*(r/s) := by ring
  rw [hh,mul_pow]
  ring

end CannonRelease

end
end
end
end
section
section
noncomputable section
open Set Metric

namespace CannonPacking

variable {X : Type*} [MetricSpace X]

lemma indexed_packing {ι : Type*} (Q : ℕ) (C : ℝ)
    (hp : PolynomialPacking (X := X) Q C) (q : ι → X) (S : Finset ι)
    (x : X) (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (hr : r ≤ 1)
    (hball : ∀ i ∈ S, dist x (q i) ≤ r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s ≤ dist (q i) (q j)) :
    (S.card : ℝ) ≤ C*(r/s)^Q := by
  classical
  have hinj : Set.InjOn q (S : Set ι) := by
    intro i hi j hj heq
    by_contra hne
    have hh := hsep i hi j hj hne
    rw [heq, dist_self] at hh
    exact (not_le_of_gt hs) hh
  have hh := hp x r s hs hsr hr (S.image q) (by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hball i hi) (by
    intro y hy z hz hyz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact hsep i hi j hj (fun heq => hyz (congrArg q heq)))
  rwa [Finset.card_image_of_injOn hinj] at hh

theorem exists_overlap_bound (Q : ℕ) (C A b : ℝ)
    (hp : PolynomialPacking (X := X) Q C) (_hC : 0 ≤ C)
    (hA : 0 < A) (hb : 0 < b) :
    ∃ B : ℕ, ∀ {ι : Type*} (q : ι → X) (S : Finset ι) (x : X) (r : ℝ),
      0 < r → max A b*r ≤ 1 →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → b*r ≤ dist (q i) (q j)) →
      (S.filter (fun i => dist x (q i) ≤ A*r)).card ≤ B := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_ge (C*(max A b/b)^Q)
  refine ⟨B, ?_⟩
  intro ι q S x r hr hscale hsep
  have hAb : 0 < max A b := hA.trans_le (le_max_left ..)
  have hh := indexed_packing Q C hp q (S.filter (fun i => dist x (q i) ≤ A*r))
    x (max A b*r) (b*r) (mul_pos hb hr)
    (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le) hscale (by
      intro i hi
      exact (Finset.mem_filter.mp hi).2 |>.trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) hr.le)) (by
      intro i hi j hj hij
      exact hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
  have heq : max A b*r/(b*r) = max A b/b := by field_simp
  rw [heq] at hh
  exact_mod_cast hh.trans hB

end CannonPacking

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_PuncturedBallConnected
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPlanarNeighborhood

theorem punctured_ball_connected (x : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConnected (ball x r\{x}) := by
  let e := OpenPartialHomeomorph.univBall x r
  have hc : IsConnected ({(0:ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  have he : e '' ({(0:ℂ)}ᶜ : Set ℂ)=ball x r\{x} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzS : z∈e.source := by simp [e]
      refine ⟨?_,?_⟩
      · simpa [e,OpenPartialHomeomorph.univBall_target x hr] using e.map_source hzS
      · intro hy
        have hz0 : z=0 := by
          calc
            z=e.symm (e z) := (e.left_inv hzS).symm
            _=0 := by simpa [e] using congrArg e.symm (mem_singleton_iff.mp hy)
        exact hz (mem_singleton_iff.mpr hz0)
    · rintro ⟨hy,hyx⟩
      have hyT : y∈e.target := by simpa [e,OpenPartialHomeomorph.univBall_target x hr] using hy
      refine ⟨e.symm y,?_,e.right_inv hyT⟩
      intro hz
      have hz0 : e.symm y=0 := mem_singleton_iff.mp hz
      apply hyx
      apply mem_singleton_iff.mpr
      calc
        y=e (e.symm y) := (e.right_inv hyT).symm
        _=x := by rw [hz0]; simp [e]
  rw [←he]
  exact hc.image e (OpenPartialHomeomorph.continuous_univBall x r).continuousOn

theorem isolated_frontier_forces_punctured_ball {R : Set ℂ} (hR : IsOpen R)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : x∈closure R) (hxR : x∉R)
    (hbound : closure R∩(ball x r\{x})⊆R) : ball x r\{x}⊆R := by
  let U := ball x r\{x}
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (punctured_ball_connected x hr).isPreconnected
  let S : Set U := Subtype.val ⁻¹' R
  have hS : IsClopen S := by
    constructor
    · have he : S=Subtype.val ⁻¹' closure R := by
        ext z
        exact ⟨fun hz => subset_closure hz,fun hz => hbound ⟨hz,z.property⟩⟩
      rw [he]
      exact isClosed_closure.preimage continuous_subtype_val
    · exact hR.preimage continuous_subtype_val
  obtain ⟨y,hyB,hyR⟩ := (mem_closure_iff_nhds.mp hx) _ (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hyx : y≠x := fun h => hxR (h ▸ hyR)
  have hn : S.Nonempty := ⟨⟨y,hyB,hyx⟩,hyR⟩
  have he := hS.eq_univ hn
  intro z hz
  exact (show (⟨z,hz⟩ : U)∈S from he.symm ▸ mem_univ _)
end CannonPlanarNeighborhood

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RegionEdges
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarNeighborhood

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma interior_dense_interval : closure (Ioo (0:I) 1)=univ := by
  rw [closure_Ioo zero_ne_one]
  ext t
  simp only [mem_Icc,mem_univ,iff_true]
  exact ⟨t.property.1,t.property.2⟩

lemma range_in_closed_of_interior {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} (hS : IsClosed S) (hI : ∀ t : I, 0<t → t<1 → a t∈S) : range a⊆S := by
  have hs : closure (Ioo (0:I) 1)⊆a ⁻¹' S :=
    closure_minimal (fun t ht => hI t ht.1 ht.2) (hS.preimage a.continuous)
  rw [interior_dense_interval] at hs
  rintro x ⟨t,rfl⟩
  exact hs (mem_univ t)

omit [Finite ι] in
lemma graph_no_isolated (F : ι → Arc ℂ) {x : ℂ} (hx : x∈⋃ i, range (F i))
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U) :
    ∃ y∈⋃ i, range (F i), y∈U ∧ y≠x := by
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hx
  obtain ⟨s,hst,hsU⟩ := (dense_compl_singleton t).exists_mem_open
    ((F i).continuous.isOpen_preimage U hU) ⟨t,hxU⟩
  exact ⟨F i s,mem_iUnion.mpr ⟨i,mem_range_self s⟩,hsU,
    fun h => hst (mem_singleton_iff.mpr ((F i).injective h))⟩

lemma region_edge_in_closure (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    {d : D} {i : ι} (hi : i∈regionEdges F π d) :
    range (F i)⊆closure (region _ π d) := by
  obtain ⟨s,hs₀,hs₁,hds⟩ := hi
  obtain ⟨labels,hlabels⟩ := tame_edge_incident_labels F hF Q hQ hπ i
  apply range_in_closed_of_interior (F i) isClosed_closure
  intro t ht₀ ht₁
  show d∈incident _ π (F i t)
  rwa [hlabels t ht₀ ht₁,←hlabels s hs₀ hs₁]

theorem tame_region_closure (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π) (d : D) :
    closure (region _ π d)=region _ π d∪⋃ i∈regionEdges F π d,range (F i) := by
  let K : Set ℂ := ⋃ i,range (F i)
  let R := region Kᶜ π d
  let S : Set ℂ := ⋃ i∈regionEdges F π d,range (F i)
  let T : Set ℂ := {x | Vertex F x}
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed)
  have hR : IsOpen R := region_isOpen hK.isOpen_compl hπ d
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun i =>
    isClosed_iUnion_of_finite (fun _ => (F i).compact_range.isClosed))
  have hT : T.Finite := finite_vertex_set F
  have hnonvert : ∀ x∈closure R, x∉R → x∉T → x∈S := by
    intro x hx hxR hxT
    have hxK : x∈K := by
      by_contra hn
      exact hxR (closure_region_inside hK.isOpen_compl hπ hx hn)
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
    have ht₀ : t≠0 := fun he => hxT ⟨i,Or.inl (congrArg (F i) he.symm)⟩
    have ht₁ : t≠1 := fun he => hxT ⟨i,Or.inr (congrArg (F i) he.symm)⟩
    exact mem_iUnion₂.mpr ⟨i,⟨t,lt_of_le_of_ne t.property.1 ht₀.symm,
      lt_of_le_of_ne t.property.2 ht₁,hx⟩,mem_range_self t⟩
  apply Subset.antisymm
  · intro x hx
    by_cases hxR : x∈R
    · exact Or.inl hxR
    right
    by_contra hxS
    have hxK : x∈K := by
      by_contra hn
      exact hxR (closure_region_inside hK.isOpen_compl hπ hx hn)
    let W := (S∪(T\{x}))ᶜ
    have hW : IsOpen W := (hS.union hT.sdiff.isClosed).isOpen_compl
    have hxW : x∈W := by
      rintro (h|h)
      · exact hxS h
      · exact h.2 rfl
    obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW x hxW
    have hall : ball x r\{x}⊆R := by
      apply isolated_frontier_forces_punctured_ball hR hr hx hxR
      rintro y ⟨hy,hyB,hyx⟩
      by_contra hyR
      have hyW := hrW hyB
      by_cases hyT : y∈T
      · exact hyW (Or.inr ⟨hyT,hyx⟩)
      · exact hyW (Or.inl (hnonvert y hy hyR hyT))
    obtain ⟨y,hyK,hyB,hyx⟩ := graph_no_isolated F hxK isOpen_ball (mem_ball_self hr)
    exact (region_subset Kᶜ π d (hall ⟨hyB,hyx⟩)) hyK
  · rintro x (hx|hx)
    · exact subset_closure hx
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
      exact region_edge_in_closure F hF Q hQ hπ hi hxi
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_TraceCard
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonIncidence
open Set Metric

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

omit [MetricSpace X] in
lemma traceCard_finite_cover (E : ι → Set X) (T : Finset X) (U : X → Set X)
    (S : Set X) (hcover : S⊆⋃ x∈T,U x) (K : ℕ)
    (hK : ∀ x∈T, traceCard E (U x)≤K) : traceCard E S≤T.card*K := by
  classical
  let IX (S : Set X) := Finset.univ.filter (fun i => (E i∩S).Nonempty)
  have hsub : IX S⊆T.biUnion (fun x => IX (U x)) := by
    intro i hi
    obtain ⟨y,hyE,hyS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcover hyS)
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hyE,hyU⟩⟩
  calc
    traceCard E S=(IX S).card := rfl
    _≤(T.biUnion (fun x => IX (U x))).card := Finset.card_le_card hsub
    _≤∑ x∈T,(IX (U x)).card := Finset.card_biUnion_le
    _≤∑ _x∈T,K := Finset.sum_le_sum (fun x hx => hK x hx)
    _=T.card*K := by simp

theorem uniform_larger_trace (Q : ℕ) (C R : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hR : 0<R) :
    ∃ B : ℕ, ∀ (r A : ℝ), 0 < r → 1≤A → (R+1)*r≤1 →
      ∀ T : Finset X, (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : X, ∃ t∈T, dist x t ≤ r) →
      ∀ {κ : Type*} [Fintype κ], ∀ E : κ → Set X, ∀ K : ℕ, (∀ x, traceCard E (ball x (2*A*r))≤K) →
      ∀ x, traceCard E (ball x (R*r))≤B*K := by
  classical
  obtain ⟨B,hB⟩ := CannonPacking.exists_overlap_bound Q C (R+1) 1 hpack hC (by linarith) zero_lt_one
  refine ⟨B,?_⟩
  intro r A hr hA hscale T hsep hcover κ _ E K hK x
  let T' := T.filter (fun t => dist x t≤(R+1)*r)
  have hTc : T'.card≤B := by
    apply hB id T x r hr
    · simpa [max_eq_left (by linarith : (1:ℝ)≤R+1)] using hscale
    · simpa using hsep
  have hcov : ball x (R*r)⊆⋃ t∈T',ball t (2*A*r) := by
    intro y hy
    obtain ⟨t,ht,hyT⟩ := hcover y
    refine mem_iUnion₂.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,?_⟩
    · have hh := dist_triangle x y t
      have hyx : dist x y<R*r := by simpa only [mem_ball,dist_comm] using hy
      linarith
    · change dist y t<2*A*r
      have hh : 2*r≤2*A*r := by nlinarith
      linarith
  exact (traceCard_finite_cover E T' (fun t => ball t (2*A*r)) _ hcov K
    (fun t _ => hK t)).trans (Nat.mul_le_mul_right K hTc)
end CannonIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ComponentRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology

variable {X : Type*} [TopologicalSpace X]

lemma component_region_eq (V : Set X) (x : V) :
    region V ConnectedComponents.mk (ConnectedComponents.mk x)=connectedComponentIn V x.val := by
  rw [connectedComponentIn_eq_image x.property]
  ext y
  constructor
  · rintro ⟨hy,hye⟩
    exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hye,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,ConnectedComponents.coe_eq_coe'.mpr hy⟩

lemma component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  rw [component_region_eq]
  exact isConnected_connectedComponentIn_iff.mpr x.property

end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RadialStable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonSegmentCones
open Set Metric Topology

lemma complex_segment_supporting_line (a b : ℂ) :
    ∃ f : ℂ →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  let x₀ := Complex.reCLM
  let x₁ := Complex.imCLM
  by_cases hd : b.re=a.re
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f 1) h
      norm_num [x₀] at hh
    · exact ((convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap).segment_subset rfl hd
  · let f := x₁-((b.im-a.im)/(b.re-a.re)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f Complex.I) h
      norm_num [f,x₀,x₁] at hh
    · have hab : f b=f a := by
        change b.im-((b.im-a.im)/(b.re-a.re))*b.re=a.im-((b.im-a.im)/(b.re-a.re))*a.re
        have hn := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      exact ((convex_singleton (f a)).linear_preimage f.toLinearMap).segment_subset rfl hab

lemma complex_finite_segments_compl_dense (Q : Finset (ℂ × ℂ)) :
    Dense ((⋃ q∈Q,segment ℝ q.1 q.2)ᶜ : Set ℂ) := by
  classical
  choose f hf hfs using fun q : Q => complex_segment_supporting_line q.val.1 q.val.2
  have hsurj (q : Q) : Function.Surjective (f q) := by
    obtain ⟨v,hv⟩ : ∃ v, f q v≠0 := by
      by_contra hn
      push Not at hn
      apply hf q
      ext v
      exact hn v
    intro y
    refine ⟨(y/f q v) • v,?_⟩
    simp only [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hopen (q : Q) : IsOpen {x | f q x≠f q q.val.1} :=
    isOpen_compl_singleton.preimage (f q).continuous
  have hdense (q : Q) : Dense {x | f q x≠f q q.val.1} :=
    (dense_compl_singleton _).preimage ((f q).isOpenMap (hsurj q))
  have hd := dense_iInter_of_isOpen hopen hdense
  apply hd.mono
  intro z hz hzQ
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzQ
  exact (mem_iInter.mp hz ⟨q,hq⟩) (hfs ⟨q,hq⟩ hzq)

end CannonSegmentCones

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexLines
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Finite ι]

lemma mem_faceVertices (F : ι → Arc ℂ) (d : Faces F) (v : ℂ) :
    v∈faceVertices F d ↔ Vertex F v ∧ v∈closure (face F d) := by
  simp [faceVertices]

omit [Finite ι] in
lemma face_nonempty (F : ι → Arc ℂ) (d : Faces F) : (face F d).Nonempty :=
  (component_region_connected _ d).nonempty
lemma face_open (F : ι → Arc ℂ) (d : Faces F) : IsOpen (face F d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  exact region_isOpen (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe d

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Spans
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma Spans.vertex_left [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F x :=
  ⟨i,h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)⟩
lemma Spans.vertex_right [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F y :=
  h.symm.vertex_left
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_PairComponentClosure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι κ : Type*}

lemma same_face_of_mem_closure [Finite ι] (F : ι → Arc ℂ) {d e : Faces F} {z : ℂ}
    (hz : z∈face F d) (he : z∈closure (face F e)) : d=e := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hh := closure_region_inside
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe he hz.1
  exact hz.2.symm.trans hh.2

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Support
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
lemma mem_vertices (F : ι → Arc ℂ) (S : Finset ι) (x : ℂ) :
    x∈vertices F S ↔ ∃ i∈S,F i 0=x ∨ F i 1=x := by
  classical
  simp [vertices,eq_comm]
end CannonPlanarEuler

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_InteriorUnion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonFacialStars
open Set Topology

variable {X D V : Type*} [TopologicalSpace X] [Finite D]

theorem interior_union_at (C : D → Set X) (hC : ∀ d,IsClosed (C d))
    (hcover : ∀ x,∃ d,x∈C d) (S : Set D) {x : X}
    (hx : ∀ d,x∈C d → d∈S) : x∈interior (⋃ d∈S,C d) := by
  let B := ⋃ d∈Sᶜ,C d
  have hB : IsClosed B := isClosed_iUnion_of_finite fun d =>
    isClosed_iUnion_of_finite fun _ => hC d
  have hxB : x∈Bᶜ := by
    intro hxB
    obtain ⟨d,hd,hxd⟩ := mem_iUnion₂.mp hxB
    exact hd (hx d hxd)
  apply mem_interior.mpr
  refine ⟨Bᶜ,?_,hB.isOpen_compl,hxB⟩
  intro y hy
  obtain ⟨d,hd⟩ := hcover y
  have hdS : d∈S := by
    by_contra hh
    exact hy (mem_iUnion₂.mpr ⟨d,hh,hd⟩)
  exact mem_iUnion₂.mpr ⟨d,hdS,hd⟩
end CannonFacialStars

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FacialStar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma facial_closures_cover (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    ∀ x : ℂ,∃ d : Faces F,x∈closure (face F d) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hd : Dense ((⋃ i,range (F i))ᶜ : Set ℂ) := (complex_finite_segments_compl_dense Q).mono (by
    intro x hx hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hx (hQ i hi))
  have hC : IsClosed (⋃ d : Faces F,closure (face F d)) :=
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hsub : (⋃ i,range (F i))ᶜ⊆⋃ d : Faces F,closure (face F d) := by
    intro x hx
    refine mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨x,hx⟩,subset_closure ?_⟩
    exact ⟨hx,rfl⟩
  intro x
  exact mem_iUnion.mp ((closure_minimal hsub hC) (hd x))

omit [DecidableEq ι] [Nonempty ι] in
theorem common_vertex_at (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (x : ℂ) :
    ∃ v∈vertices F Finset.univ,∀ d : Faces F,x∈closure (face F d) → v∈faceVertices F d := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  by_cases hxv : Vertex F x
  · refine ⟨x,?_,fun d hd=>(mem_faceVertices F d x).mpr ⟨hxv,hd⟩⟩
    obtain ⟨i,hi⟩ := hxv
    exact (mem_vertices F Finset.univ x).mpr ⟨i,Finset.mem_univ _,hi⟩
  by_cases hxK : x∈⋃ i,range (F i)
  · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
    have ht₀ : 0<t := by
      apply lt_of_le_of_ne (nonneg t)
      intro he
      exact hxv ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
    have ht₁ : t<1 := by
      apply lt_of_le_of_ne (le_one t)
      intro he
      exact hxv ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
    refine ⟨F i 0,(mem_vertices F Finset.univ (F i 0)).mpr ⟨i,Finset.mem_univ _,Or.inl rfl⟩,?_⟩
    intro d hd
    apply (mem_faceVertices F d _).mpr
    refine ⟨⟨i,Or.inl rfl⟩,?_⟩
    exact region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe
      (show i∈regionEdges F ConnectedComponents.mk d from ⟨t,ht₀,ht₁,hd⟩) (mem_range_self 0)
  · let d := ConnectedComponents.mk (⟨x,hxK⟩ : ((⋃ i,range (F i))ᶜ : Set ℂ))
    obtain ⟨v,hv⟩ := hcorner d
    have hvV := ((mem_faceVertices F d v).mp hv).1
    obtain ⟨i,hi⟩ := hvV
    refine ⟨v,(mem_vertices F Finset.univ v).mpr ⟨i,Finset.mem_univ _,hi⟩,?_⟩
    intro c hxc
    have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe c
    change closure (face F c)=face F c∪_ at hcl
    rw [hcl] at hxc
    have hxface : x∈face F c := by
      rcases hxc with h|h
      · exact h
      · obtain ⟨j,-,hj⟩ := mem_iUnion₂.mp h
        exact (hxK (mem_iUnion.mpr ⟨j,hj⟩)).elim
    have hc : c=d := hxface.2.symm
    exact hc.symm ▸ hv

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Crossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set

attribute [local instance] Classical.propDecidable

lemma crossing_neg (y z A : ℝ) : crossing z y (-A)= -crossing y z A := by
  unfold crossing
  simp only [neg_pos,neg_lt_zero]
  have hdis : ¬((y<0 ∧ 0<z ∧ 0<A) ∧ (z<0 ∧ 0<y ∧ A<0)) := by
    rintro ⟨h,k⟩
    exact lt_asymm h.1 k.2.1
  by_cases h : y<0 ∧ 0<z ∧ 0<A
  · have k : ¬(z<0 ∧ 0<y ∧ A<0) := fun k=>hdis ⟨h,k⟩
    simp only [ite_eq_left h,ite_eq_right k]
  · by_cases k : z<0 ∧ 0<y ∧ A<0 <;> simp only [h,k,and_self,ite_false,ite_true,neg_zero,neg_neg]

lemma positive_triangle_degree {y z w A B C : ℝ}
    (hy : y≠0) (hz : z≠0) (hw : w≠0) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (hp : 0<A+B+C) (hr : y*B+z*C+w*A=0) :
    crossing y z A+crossing z w B+crossing w y C=
      if 0<A ∧ 0<B ∧ 0<C then 1 else 0 := by
  rcases lt_or_gt_of_ne hy with hy|hy <;>
    rcases lt_or_gt_of_ne hz with hz|hz <;>
    rcases lt_or_gt_of_ne hw with hw|hw <;>
    rcases lt_or_gt_of_ne hA with hA|hA <;>
    rcases lt_or_gt_of_ne hB with hB|hB <;>
    rcases lt_or_gt_of_ne hC with hC|hC <;>
    (have hy' := lt_asymm hy
     have hz' := lt_asymm hz
     have hw' := lt_asymm hw
     have hA' := lt_asymm hA
     have hB' := lt_asymm hB
     have hC' := lt_asymm hC
     simp only [crossing,hy,hz,hw,hA,hB,hC,hy',hz',hw',hA',hB',hC',
       and_self,and_true,and_false,ite_true,ite_false]
     norm_num)
  all_goals
    first
    | have h1 := mul_pos hy hB
    | have h1 := mul_pos_of_neg_of_neg hy hB
    | have h1 := mul_neg_of_neg_of_pos hy hB
    | have h1 := mul_neg_of_pos_of_neg hy hB
    first
    | have h2 := mul_pos hz hC
    | have h2 := mul_pos_of_neg_of_neg hz hC
    | have h2 := mul_neg_of_neg_of_pos hz hC
    | have h2 := mul_neg_of_pos_of_neg hz hC
    first
    | have h3 := mul_pos hw hA
    | have h3 := mul_pos_of_neg_of_neg hw hA
    | have h3 := mul_neg_of_neg_of_pos hw hA
    | have h3 := mul_neg_of_pos_of_neg hw hA
    linarith

lemma area_swap (a b p : ℂ) : area b a p= -area a b p := by
  unfold area
  ring
lemma area_cyclic (a b c : ℂ) : area b c a=area a b c := by
  unfold area
  ring
lemma area_sum (a b c p : ℂ) : area a b p+area b c p+area c a p=area a b c := by
  unfold area
  ring
lemma area_relation (a b c p : ℂ) :
    (a.im-p.im)*area b c p+(b.im-p.im)*area c a p+(c.im-p.im)*area a b p=0 := by
  unfold area
  ring

lemma edgeIndex_swap (p a b : ℂ) : edgeIndex p b a= -edgeIndex p a b := by
  unfold edgeIndex
  rw [area_swap,crossing_neg]

lemma triangle_index {a b c p : ℂ} (harea : 0<area a b c) (hgen : Generic a b c p) :
    edgeIndex p a b+edgeIndex p b c+edgeIndex p c a=if Inside a b c p then 1 else 0 := by
  have ht := positive_triangle_degree (sub_ne_zero.mpr hgen.1) (sub_ne_zero.mpr hgen.2.1)
    (sub_ne_zero.mpr hgen.2.2.1) hgen.2.2.2.1 hgen.2.2.2.2.1 hgen.2.2.2.2.2
    (by rw [area_sum]; exact harea) (area_relation a b c p)
  by_cases h : Inside a b c p
  · rw [ite_eq_left h]
    change 0<area a b p ∧ 0<area b c p ∧ 0<area c a p at h
    rw [ite_eq_left h] at ht
    exact ht
  · rw [ite_eq_right h]
    change ¬(0<area a b p ∧ 0<area b c p ∧ 0<area c a p) at h
    rw [ite_eq_right h] at ht
    exact ht

lemma inside_open (a b c : ℂ) : IsOpen {p | Inside a b c p} := by
  have H (a b : ℂ) : Continuous (area a b) := by unfold area; fun_prop
  exact (isOpen_lt continuous_const (H a b)).inter
    ((isOpen_lt continuous_const (H b c)).inter (isOpen_lt continuous_const (H c a)))

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {F : ι → Arc ℂ} {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_a (C : FacialCycle F d) : C.a∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_b (C : FacialCycle F d) : C.b∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_c (C : FacialCycle F d) : C.c∈faceVertices F d := by rw [C.vertices]; simp

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_InnerFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

lemma dense_ne_of_openMap {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : IsOpenMap f) (t : ℝ) : Dense {x | f x≠t} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y,hy,ht⟩ := (dense_compl_singleton t).inter_open_nonempty (f '' U)
    (hf U hU) (hne.image f)
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨x,hx,ht⟩

lemma area_openMap {a b : ℂ} (hab : a≠b) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL (p : ℂ) : L p=(b.re-a.re)*p.im-(b.im-a.im)*p.re := rfl
  have hsurj : Function.Surjective L := by
    intro t
    by_cases h : b.re-a.re=0
    · have h' : b.im-a.im≠0 := by
        intro hh
        exact hab (Complex.ext (sub_eq_zero.mp h).symm (sub_eq_zero.mp hh).symm)
      refine ⟨⟨-t/(b.im-a.im),0⟩,?_⟩
      rw [hL]
      simp only [h,zero_mul,zero_sub]
      field_simp
    · refine ⟨⟨0,t/(b.re-a.re)⟩,?_⟩
      rw [hL]
      simp only [mul_zero,sub_zero]
      exact mul_div_cancel₀ _ h
  have ho : IsOpenMap (fun p : ℂ=>p-a) := isOpenMap_sub_right a
  exact (L.isOpenMap hsurj).comp ho

lemma generic_dense_open (a b c : ℂ) (hab : a≠b) (hbc : b≠c) (hca : c≠a) :
    Dense {p | Generic a b c p} ∧ IsOpen {p | Generic a b c p} := by
  have hd (x : ℂ) : Dense {p : ℂ | x.im≠p.im} := by
    simpa only [ne_comm] using dense_ne_of_openMap Complex.im Complex.isOpenMap_im x.im
  have he (x y : ℂ) (hxy : x≠y) : Dense {p | area x y p≠0} :=
    dense_ne_of_openMap (area x y) (area_openMap hxy) 0
  have ho (x : ℂ) : IsOpen {p : ℂ | x.im≠p.im} := isOpen_ne_fun continuous_const Complex.continuous_im
  have hp (x y : ℂ) : IsOpen {p | area x y p≠0} := by
    apply isOpen_ne_fun _ continuous_const
    unfold area
    fun_prop
  have Hr := ((he a b hab).inter_of_isOpen_right
    ((he b c hbc).inter_of_isOpen_right (he c a hca) (hp c a)) ((hp b c).inter (hp c a)))
  have HrO := (hp a b).inter ((hp b c).inter (hp c a))
  have Hq := (hd c).inter_of_isOpen_right Hr HrO
  have HqO := (ho c).inter HrO
  have HH := (hd b).inter_of_isOpen_right Hq HqO
  have HHO := (ho b).inter HqO
  exact ⟨(hd a).inter_of_isOpen_right HH HHO,(ho a).inter HHO⟩

lemma area_pos_distinct {a b c : ℂ} (h : 0<area a b c) : a≠b ∧ b≠c ∧ c≠a := by
  constructor
  · intro he; subst b; simp [area] at h
  constructor
  · intro he; subst c; have : area a b b=0 := by unfold area; ring
    rw [this] at h; exact lt_irrefl _ h
  · intro he; subst c; simp [area] at h

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_InteriorBallCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

attribute [local instance] Classical.propDecidable

lemma generic_union_iff {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w p : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hg : ∀ d,Generic (a d) (b d) (c d) p) (hgo : Generic u v w p)
    (hc : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (∃ d,Inside (a d) (b d) (c d) p) ↔ Inside u v w p := by
  classical
  have H := hc (edgeIndex p) (edgeIndex_swap p)
  simp only [triangle_index (hpos _) (hg _),triangle_index ho hgo] at H
  constructor
  · rintro ⟨d,hd⟩
    have hl : (1:ℤ)≤∑ i,if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
      have hh := Finset.single_le_sum (f:=fun i=>if Inside (a i) (b i) (c i) p then (1:ℤ) else 0)
        (fun i hi=>by split_ifs <;> norm_num) (Finset.mem_univ d)
      simpa only [ite_eq_left hd] using hh
    rw [H] at hl
    by_contra hn
    simp only [ite_eq_right hn] at hl
    norm_num at hl
  · intro hp
    by_contra hn
    push Not at hn
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_left hp] at H
    norm_num at H

lemma closure_eq_of_dense_inter_eq {X : Type*} [TopologicalSpace X]
    {G U V : Set X} (hG : Dense G) (hU : IsOpen U) (hV : IsOpen V) (hUV : G∩U=G∩V) :
    closure U=closure V := by
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hU).trans (by rw [Set.inter_comm U G,hUV]; exact closure_mono inter_subset_right)
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hV).trans (by rw [Set.inter_comm V G,←hUV]; exact closure_mono inter_subset_right)

theorem triangle_closures_fill {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (⋃ d,closure {p | Inside (a d) (b d) (c d) p})=closure {p | Inside u v w p} := by
  have hg (d : D) := generic_dense_open (a d) (b d) (c d)
    (area_pos_distinct (hpos d)).1 (area_pos_distinct (hpos d)).2.1 (area_pos_distinct (hpos d)).2.2
  have hgO := generic_dense_open u v w (area_pos_distinct ho).1
    (area_pos_distinct ho).2.1 (area_pos_distinct ho).2.2
  let G := (⋂ d : D,{p | Generic (a d) (b d) (c d) p})∩{p | Generic u v w p}
  have hG : Dense G :=
    (dense_iInter_of_isOpen (fun d=>(hg d).2) (fun d=>(hg d).1)).inter_of_isOpen_right hgO.1 hgO.2
  rw [←closure_iUnion_of_finite]
  apply closure_eq_of_dense_inter_eq hG (isOpen_iUnion fun d=>inside_open _ _ _) (inside_open _ _ _)
  ext p
  change (p∈G ∧ p∈⋃ d,{p | Inside (a d) (b d) (c d) p}) ↔ p∈G ∧ Inside u v w p
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  apply and_congr_right
  intro hp
  exact generic_union_iff a b c u v w p hpos ho (fun d=>mem_iInter.mp hp.1 d) hp.2 hchain

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_BoundaryBallCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} {d : Faces F}

lemma FacialCycle.pair_edge (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v) :
    ∃ i,Spans (F i) u v := by
  rw [C.vertices] at hu hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  all_goals first
    | exact (huv rfl).elim
    | exact ⟨C.e,C.spans_e⟩
    | exact ⟨C.e,C.spans_e.symm⟩
    | exact ⟨C.f,C.spans_f⟩
    | exact ⟨C.f,C.spans_f.symm⟩
    | exact ⟨C.g,C.spans_g⟩
    | exact ⟨C.g,C.spans_g.symm⟩

omit [Fintype ι] in
lemma Spans.developed_length {i : ι} {u v : ℂ} (h : Spans (F i) u v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  rcases h with ⟨h0,h1⟩|⟨h0,h1⟩
  · simpa only [h0,h1] using hlen
  · simpa only [h0,h1,dist_comm,add_comm] using hlen

lemma FacialCycle.developed_length (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  obtain ⟨i,hi⟩:=C.pair_edge hu hv huv
  exact hi.developed_length z r (hlen i)

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Sphere
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

lemma reflection_infty : reflection ∞=((0:ℂ):S) := by
  change CannonMobius.inv ∞=_
  exact CannonMobius.inv_infty
lemma reflection_zero : reflection ((0:ℂ):S)=∞ := by
  change CannonMobius.inv ((starRingEnd ℂ 0:ℂ):S)=_
  simpa only [map_zero] using CannonMobius.inv_zero
lemma reflection_coe {z : ℂ} (hz : z≠0) :
    reflection (z:S)=((starRingEnd ℂ z)⁻¹:ℂ) := by
  change CannonMobius.inv ((starRingEnd ℂ z:ℂ):S)=_
  exact CannonMobius.inv_coe ((map_ne_zero (starRingEnd ℂ)).mpr hz)

lemma reflection_fix {z : ℂ} (hz : z∈sphere (0:ℂ) 1) : reflection (z:S)=(z:S) := by
  have hn : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
  have hne : z≠0 := by intro hh; simp [hh] at hn
  rw [reflection_coe hne,Complex.inv_eq_conj (by simpa using hn)]
  simp

lemma reflection_involutive : Function.Involutive reflection := by
  intro p
  induction p using OnePoint.rec with
  | infty => rw [reflection_infty,reflection_zero]
  | coe z =>
    by_cases hz : z=0
    · subst z; rw [reflection_zero,reflection_infty]
    · rw [reflection_coe hz,reflection_coe (inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hz))]
      simp

lemma reflection_image_closedBall :
    reflection '' ((↑) '' closedBall (0:ℂ) 1 : Set S)=
      (((↑) '' ball (0:ℂ) 1 : Set S))ᶜ := by
  ext p
  constructor
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩ hp
    obtain ⟨w,hw,he⟩:=hp
    by_cases hz0 : z=0
    · subst z
      rw [reflection_zero] at he
      exact OnePoint.coe_ne_infty w he
    rw [reflection_coe hz0] at he
    have he' : w=(starRingEnd ℂ z)⁻¹ := OnePoint.coe_injective he
    rw [mem_ball,dist_zero_right,he',norm_inv,Complex.norm_conj] at hw
    rw [mem_closedBall,dist_zero_right] at hz
    have hn : 0<‖z‖ := norm_pos_iff.mpr hz0
    have hi : 1≤‖z‖⁻¹ := (one_le_inv₀ hn).mpr hz
    exact (not_lt_of_ge hi) hw
  · intro hp
    have hq : reflection p∈((↑) '' closedBall (0:ℂ) 1 : Set S) := by
      induction p using OnePoint.rec with
      | infty => rw [reflection_infty]; exact ⟨0,by simp,rfl⟩
      | coe z =>
        have hz : 1≤‖z‖ := by
          by_contra hh
          exact hp ⟨z,by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hh,rfl⟩
        have hz0 : z≠0 := by intro he; norm_num [he] at hz
        rw [reflection_coe hz0]
        refine ⟨(starRingEnd ℂ z)⁻¹,?_,rfl⟩
        rw [mem_closedBall,dist_zero_right,norm_inv,Complex.norm_conj]
        exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr hz
    exact ⟨reflection p,hq,reflection_involutive p⟩
end CannonSphereReflection

end
end
section
noncomputable section
namespace CannonSphereReflection
open Set Metric Topology
open scoped OnePoint

lemma onePoint_image (h : ℂ≃ₜℂ) (A : Set ℂ) :
    h.onePointCongr '' ((↑) '' A : Set S)=((↑) '' (h '' A) : Set S) := by
  rw [image_image,image_image]
  rfl

theorem exists_convex_reflection (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) :
    ∃ J : S≃ₜS,(∀ x∈frontier K,J (x:S)=(x:S)) ∧
      J '' ((↑) '' K : Set S)=(((↑) '' interior K : Set S))ᶜ := by
  obtain ⟨h,hi,hc,hf⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hint hK.isBounded
  rw [hK.isClosed.closure_eq] at hc
  let J : S≃ₜS:=h.onePointCongr.trans (reflection.trans h.symm.onePointCongr)
  have hInv : h.symm.onePointCongr '' ((↑) '' ball (0:ℂ) 1 : Set S)=((↑) '' interior K : Set S) := by
    rw [onePoint_image,←hi]
    congr 1
    rw [image_image]
    simp only [h.symm_apply_apply,image_id']
  refine ⟨J,?_,?_⟩
  · intro x hx
    have hh : h x∈sphere (0:ℂ) 1 := by rw [←hf]; exact mem_image_of_mem h hx
    change h.symm.onePointCongr (reflection ((h x:ℂ):S))=(x:S)
    rw [reflection_fix hh]
    change ((h.symm (h x):ℂ):S)=(x:S)
    rw [h.symm_apply_apply]
  · calc
      J '' ((↑) '' K : Set S) = h.symm.onePointCongr ''
          (reflection '' (h.onePointCongr '' ((↑) '' K : Set S))) := by
            simp only [image_image]
            rfl
      _ = _ := by
        rw [onePoint_image,hc,reflection_image_closedBall,
          image_compl_eq h.symm.onePointCongr.bijective,hInv]
end CannonSphereReflection

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ClosedCoverReflTrans
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonFiniteCarrier
open Set Topology Relation

lemma closed_cover_reflTransGen {Y ι : Type*} [TopologicalSpace Y] [Finite ι]
    (K : ι → Set Y) (hK : ∀ i,IsClosed (K i)) (S : Set Y)
    (hS : IsPreconnected S) (hcover : S⊆⋃i,K i)
    (i j : ι) (hi : (S∩K i).Nonempty) (hj : (S∩K j).Nonempty) :
    ReflTransGen (fun a b=> (S∩K a∩K b).Nonempty) i j := by
  classical
  by_contra hij
  let R := fun a b=> (S∩K a∩K b).Nonempty
  let T : Set ι := {k | ReflTransGen R i k}
  let U : Set Y := ⋃ k∈T,K k
  let V : Set Y := ⋃ k∈Tᶜ,K k
  have hsplit : (⋃ k,K k)=U∪V := iSup_split K (·∈T)
  have hcU : IsClosed U := isClosed_iUnion_of_finite fun k=>isClosed_iUnion_of_finite fun _=>hK k
  have hcV : IsClosed V := isClosed_iUnion_of_finite fun k=>isClosed_iUnion_of_finite fun _=>hK k
  have hiT : i∈T := ReflTransGen.refl
  obtain ⟨a,haS,hai⟩:=hi
  obtain ⟨b,hbS,hbj⟩:=hj
  have haU : (S∩U).Nonempty := ⟨a,haS,mem_iUnion₂_of_mem hiT hai⟩
  have hbV : (S∩V).Nonempty := ⟨b,hbS,mem_iUnion₂_of_mem hij hbj⟩
  obtain ⟨x,hxS,hxU,hxV⟩:=isPreconnected_closed_iff.mp hS U V hcU hcV
    (hcover.trans hsplit.le) haU hbV
  obtain ⟨k,hk,hxk⟩:=mem_iUnion₂.mp hxU
  obtain ⟨l,hl,hxl⟩:=mem_iUnion₂.mp hxV
  exact hl (hk.tail ⟨x,⟨hxS,hxk⟩,hxl⟩)

theorem connected_carrier {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Finite ι] (A : ι → Set X) (K : ι → Set Y)
    (hA : ∀ i,IsPreconnected (A i)) (hK : ∀ i,IsClosed (K i))
    (S : Set Y) (hS : IsPreconnected S) (hcover : S⊆⋃i,K i)
    (hmeet : ∀ i j,(S∩K i∩K j).Nonempty → (A i∩A j).Nonempty) :
    IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val) := by
  classical
  apply IsPreconnected.iUnion_of_reflTransGen (s:=fun i : {i : ι // (S∩K i).Nonempty}=>A i.val) (fun i=>hA i.val)
  intro i j
  have hreach := closed_cover_reflTransGen (fun i : {i : ι // (S∩K i).Nonempty}=>K i.val)
    (fun i=>hK i.val) S hS (by
      intro y hy
      obtain ⟨k,hk⟩:=mem_iUnion.mp (hcover hy)
      exact mem_iUnion.mpr ⟨⟨k,⟨y,hy,hk⟩⟩,hk⟩) i j i.property j.property
  exact ReflTransGen.mono (r:=fun a b : {i : ι // (S∩K i).Nonempty}=>(S∩K a.val∩K b.val).Nonempty)
    (fun a b hab=>hmeet a.val b.val hab) i j hreach

lemma preimage_subset_carrier {X Y ι : Type*} (A : ι → Set X) (K : ι → Set Y)
    (f : X → Y) (hcover : ∀ x,∃ i,x∈A i) (hf : ∀ i,MapsTo f (A i) (K i)) (S : Set Y) :
    f ⁻¹' S⊆⋃(i : {i : ι // (S∩K i).Nonempty}),A i.val := by
  intro x hx
  obtain ⟨i,hi⟩:=hcover x
  exact mem_iUnion.mpr ⟨⟨i,⟨f x,hx,hf i hi⟩⟩,hi⟩

end CannonFiniteCarrier

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_GraphEdgeValueCompatible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonEmbeddedArc.Arc.instFintypeRefinementIndex _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval

variable {ι : Type*} [Finite ι]

omit [Finite ι] in
lemma graph_edge_value_compatible (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ)
    {i j : ι} {s t : I} (hh : F i s=F j t) :
    Path.segment (z (F i 0)) (z (F i 1)) s =
      Path.segment (z (F j 0)) (z (F j 1)) t := by
  by_cases hij : i=j
  · subst j
    exact congrArg (Path.segment (z (F i 0)) (z (F i 1))) ((F i).injective hh)
  · obtain ⟨hs,ht⟩ := (hF hij).1 s t hh
    rcases hs with rfl|rfl <;> rcases ht with rfl|rfl
    · exact (Path.source _).trans ((congrArg z hh).trans (Path.source _).symm)
    · exact (Path.source _).trans ((congrArg z hh).trans (Path.target _).symm)
    · exact (Path.target _).trans ((congrArg z hh).trans (Path.source _).symm)
    · exact (Path.target _).trans ((congrArg z hh).trans (Path.target _).symm)

theorem compact_quotient_descent {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [CompactSpace A] [T2Space B]
    (q : A → B) (hq : Function.Surjective q) (hqc : Continuous q)
    (b : A → C) (hb : Continuous b) (he : ∀ x y,q x=q y → b x=b y) :
    ∃ g : ContinuousMap B C,∀ x,g (q x)=b x := by
  let g : B → C := fun x=>b (Function.surjInv hq x)
  have hgb (a : A) : g (q a)=b a := he _ _ (Function.surjInv_eq hq (q a))
  have hquot : IsQuotientMap q := IsQuotientMap.of_surjective_continuous hq hqc
  refine ⟨⟨g,hquot.continuous_iff.mpr ?_⟩,hgb⟩
  have heq : g ∘ q=b := funext hgb
  rw [heq]
  exact hb

theorem realize_graph (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ) :
    ∃ g : C((⋃ i,range (F i) : Set ℂ),ℂ),
      ∀ i t,g ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩=
        Path.segment (z (F i 0)) (z (F i 1)) t := by
  classical
  let S : Set ℂ := ⋃ i,range (F i)
  let q : (Σ _ : ι,I) → S := fun p=>⟨F p.1 p.2,mem_iUnion.mpr ⟨p.1,mem_range_self p.2⟩⟩
  have hq : Function.Surjective q := by
    rintro ⟨x,hx⟩
    obtain ⟨i,t,ht⟩:=mem_iUnion.mp hx
    exact ⟨⟨i,t⟩,Subtype.ext ht⟩
  have hqc : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_sigma_iff.mpr (fun i=>(F i).continuous)
  let b : (Σ _ : ι,I) → ℂ := fun p=>Path.segment (z (F p.1 0)) (z (F p.1 1)) p.2
  have hb : Continuous b := by
    apply continuous_sigma_iff.mpr
    intro i
    exact (Path.segment (z (F i 0)) (z (F i 1))).continuous
  have hbq : ∀ p r,q p=q r → b p=b r := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hh : F i s=F j t := congrArg Subtype.val he
    change Path.segment (z (F i 0)) (z (F i 1)) s =
      Path.segment (z (F j 0)) (z (F j 1)) t
    exact graph_edge_value_compatible F hF z hh
  obtain ⟨g,hg⟩:=compact_quotient_descent q hq hqc b hb hbq
  exact ⟨g,fun i t=>hg ⟨i,t⟩⟩

theorem extend_graph (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t := by
  obtain ⟨f,hf⟩:=realize_graph F hF z
  have hK : IsClosed (⋃ i,range (F i) : Set ℂ) :=
    isClosed_iUnion_of_finite (fun i=>(F i).compact_range.isClosed)
  let fr : C((⋃ i,range (F i) : Set ℂ),ℝ) := ⟨fun x=>(f x).re,Complex.continuous_re.comp f.continuous⟩
  let fi : C((⋃ i,range (F i) : Set ℂ),ℝ) := ⟨fun x=>(f x).im,Complex.continuous_im.comp f.continuous⟩
  obtain ⟨gr,hgr⟩:=fr.exists_extension' hK.isClosedEmbedding_subtypeVal
  obtain ⟨gi,hgi⟩:=fi.exists_extension' hK.isClosedEmbedding_subtypeVal
  refine ⟨⟨fun x=>⟨gr x,gi x⟩,by
    exact Complex.equivRealProdCLM.symm.continuous.comp (gr.continuous.prodMk gi.continuous)⟩,?_⟩
  intro i t
  have hr := congrFun hgr ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩
  have hi := congrFun hgi ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩
  apply Complex.ext
  · exact hr.trans (congrArg Complex.re (hf i t))
  · exact hi.trans (congrArg Complex.im (hf i t))
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_Retraction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonConvexRetraction
open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_retraction (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) :
    ∃ P : E → E,LipschitzWith 1 P ∧ (∀ x,P x∈K) ∧ ∀ x∈K,P x=x := by
  have hex (x : E) := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv x
  choose P hP hmin using hex
  have hinner (x w : E) (hw : w∈K) : ⟪x-P x,w-P x⟫_ℝ≤0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hP x)).mp (hmin x) w hw
  have hdist (x y : E) : dist (P x) (P y)≤dist x y := by
    have hx := hinner x (P y) (hP y)
    have hy := hinner y (P x) (hP x)
    have hh : ‖P x-P y‖^2≤⟪x-y,P x-P y⟫_ℝ := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [inner_sub_left,inner_sub_right] at hx hy ⊢
      have hs := real_inner_comm (P x) (P y)
      linarith
    have hcs := real_inner_le_norm (x-y) (P x-P y)
    rw [dist_eq_norm,dist_eq_norm]
    by_cases hz : ‖P x-P y‖=0
    · rw [hz]; exact norm_nonneg _
    · have hp : 0<‖P x-P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨P,LipschitzWith.of_dist_le_mul (by simpa using hdist),hP,?_⟩
  intro x hx
  have H := hinner x x hx
  rw [real_inner_self_eq_norm_sq] at H
  have hzero : ‖x-P x‖=0 := by nlinarith [norm_nonneg (x-P x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
end CannonConvexRetraction

end
end
section
noncomputable section
namespace CannonFiniteClosedGluing
open Set

variable {X Y D : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite D]

theorem exists_gluing (C : D → Set X) (hC : ∀ d,IsClosed (C d))
    (hcover : ∀ x,∃ d,x∈C d) (f : D → ContinuousMap X Y)
    (hcompat : ∀ d e x,x∈C d → x∈C e → f d x=f e x) :
    ∃ g : ContinuousMap X Y,∀ d x,x∈C d → g x=f d x := by
  choose ind hind using hcover
  let g : X → Y := fun x=>f (ind x) x
  have heq (d : D) (x : X) (hx : x∈C d) : g x=f d x :=
    hcompat (ind x) d x (hind x) hx
  have hcont : Continuous g := by
    rw [continuous_iff_isClosed]
    intro S hS
    have hpre : g ⁻¹' S=⋃ d,C d∩(f d) ⁻¹' S := by
      ext x
      simp only [mem_preimage,mem_iUnion,mem_inter_iff]
      constructor
      · intro hx
        exact ⟨ind x,hind x,hx⟩
      · rintro ⟨d,hd,hx⟩
        rwa [heq d x hd]
    rw [hpre]
    exact isClosed_iUnion_of_finite fun d=>(hC d).inter (hS.preimage (f d).continuous)
  exact ⟨⟨g,hcont⟩,heq⟩
end CannonFiniteClosedGluing

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceHull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι]

lemma graph_extension_hull [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (z : ℂ → ℂ) (g : C(ℂ,ℂ))
    (hg : ∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t)
    (d : Faces F) {x : ℂ} (hx : x∈closure (face F d)) (hgraph : x∈⋃i,range (F i)) :
    g x∈faceHull F z d := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change closure (face F d)=face F d∪_ at hcl
  rw [hcl] at hx
  have hxE : x∈⋃i∈regionEdges F ConnectedComponents.mk d,range (F i) := by
    rcases hx with hx|hx
    · exact (hx.1 hgraph).elim
    · exact hx
  obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hxE
  have ends : F i 0∈faceVertices F d ∧ F i 1∈faceVertices F d := by
    exact ⟨(mem_faceVertices F _ _).mpr ⟨⟨i,Or.inl rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨0,rfl⟩⟩,
      (mem_faceVertices F _ _).mpr ⟨⟨i,Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨1,rfl⟩⟩⟩
  rw [hg]
  have h0 : z (F i 0)∈faceHull F z d :=
    subset_convexHull ℝ (z '' (faceVertices F d : Set ℂ)) ⟨F i 0,ends.1,rfl⟩
  have h1 : z (F i 1)∈faceHull F z d :=
    subset_convexHull ℝ (z '' (faceVertices F d : Set ℂ)) ⟨F i 1,ends.2,rfl⟩
  exact (convex_convexHull ℝ (z '' (faceVertices F d : Set ℂ))).segment_subset h0 h1
    (by rw [←Path.range_segment]; exact mem_range_self t)

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_LocalCompactSurjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonLocalRealization
open Set Metric Topology

theorem exists_local_compact_surjection (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hn : U.Nonempty) (g : C(ℂ,ℂ)) :
    ∃ f : C(ℂ,ℂ),EqOn f g Uᶜ ∧
      ∃ W : Set ℂ,IsCompact W ∧ W⊆U ∧ K⊆f '' W := by
  obtain ⟨x₀,hx₀⟩:=hn
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨R,hR,hbound⟩:=hK.isBounded.exists_pos_norm_le
  let s : ℝ := r/(2*R)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : s*R=r/2 := by dsimp [s]; field_simp
  let E : ℂ → ℂ := fun y=>x₀+s • y
  have he : Continuous E := continuous_const.add (continuous_id.const_smul s)
  have hEU : E '' K⊆U := by
    rintro _ ⟨y,hy,rfl⟩
    apply hball
    rw [mem_ball,dist_eq_norm]
    change ‖x₀+s • y-x₀‖ < r
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (hbound y hy) hs.le).trans_lt (by rw [hsR]; linarith)
  obtain ⟨ψ,hψ,_,hψU,_⟩:=exists_continuousMap_one_of_isCompact_subset_isOpen (hK.image he) hU hEU
  let A : ℂ → ℂ := fun x=>(s⁻¹:ℝ) • (x-x₀)
  have hA : Continuous A := (continuous_id.sub continuous_const).const_smul (s⁻¹ : ℝ)
  let f : C(ℂ,ℂ) := ⟨fun x=>(ψ x) • A x + (1-ψ x) • g x,
    (ψ.continuous.smul hA).add ((continuous_const.sub ψ.continuous).smul g.continuous)⟩
  refine ⟨f,?_,?_⟩
  · intro x hx
    have hz : ψ x=0 := by
      by_contra hn
      exact hx (hψU (subset_closure hn))
    change (ψ x) • A x + (1-ψ x) • g x=g x
    simp [hz]
  · refine ⟨E '' K,hK.image he,hEU,?_⟩
    intro y hy
    refine ⟨E y,mem_image_of_mem E hy,?_⟩
    have h1 : ψ (E y)=1 := hψ (mem_image_of_mem E hy)
    change (ψ (E y)) • A (E y) + (1-ψ (E y)) • g (E y)=y
    simp only [h1,one_smul,sub_self,zero_smul,add_zero]
    change (s⁻¹:ℝ) • (x₀+s • y-x₀)=y
    rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

end CannonLocalRealization

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FacewiseCompactSurjectiveRealization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_facewise_compact_surjective_realization (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) ∧
        ∃ W : Set ℂ,IsCompact W ∧ W⊆face F d ∧ faceHull F z d⊆g '' W := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨g,hg⟩:=extend_graph F hF z
  have hnon (d : Faces F) : (faceHull F z d).Nonempty :=
    ((hcorner d).to_set.image z).mono (subset_convexHull ℝ _)
  have hclosed (d : Faces F) : IsClosed (faceHull F z d) :=
    (((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ).isClosed
  have hproj (d : Faces F) := CannonConvexRetraction.exists_retraction
    (faceHull F z d) (hnon d) (hclosed d) (convex_convexHull ℝ _)
  choose P hLip hP hfix using hproj
  have hlocal (d : Faces F) := CannonLocalRealization.exists_local_compact_surjection
    (faceHull F z d) (face F d) (((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ)
    (face_open F d) (face_nonempty F d) g
  choose gd hgd W hW hWU honto using hlocal
  let f (d : Faces F) : C(ℂ,ℂ) := ⟨fun x=>P d (gd d x),(hLip d).continuous.comp (gd d).continuous⟩
  have hf (d : Faces F) (x : ℂ) (hx : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
      f d x=g x := by
    have hnot : x∈(face F d)ᶜ := fun H=>H.1 hxK
    change P d (gd d x)=g x
    rw [hgd d hnot]
    exact hfix d (g x) (graph_extension_hull F hF Q hQ z g hg d hx hxK)
  obtain ⟨f₀,hf₀⟩:=CannonFiniteClosedGluing.exists_gluing
    (fun d : Faces F=>closure (face F d)) (fun _=>isClosed_closure)
    (facial_closures_cover F hF Q hQ) f (by
      intro d e x hxd hxe
      by_cases hde : d=e
      · rw [hde]
      have hxK : x∈⋃i,range (F i) := by
        by_contra hxK
        let c : Faces F := ConnectedComponents.mk ⟨x,hxK⟩
        have hc : x∈face F c := ⟨hxK,rfl⟩
        exact hde ((same_face_of_mem_closure F hc hxd).symm.trans (same_face_of_mem_closure F hc hxe))
      exact (hf d x hxd hxK).trans (hf e x hxe hxK).symm)
  refine ⟨f₀,?_,?_⟩
  · intro i t
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ (F i t)
    exact (hf₀ d _ hd).trans ((hf d _ hd (mem_iUnion.mpr ⟨i,mem_range_self t⟩)).trans (hg i t))
  · intro d
    constructor
    · intro x hx
      rw [hf₀ d x hx]
      exact hP d (gd d x)
    · refine ⟨W d,hW d,hWU d,?_⟩
      intro y hy
      obtain ⟨x,hx,hxy⟩:=honto d hy
      refine ⟨x,hx,?_⟩
      rw [hf₀ d x (subset_closure (hWU d hx))]
      change P d (gd d x)=y
      rw [hxy]
      exact hfix d y hy
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_ExteriorConnected
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonPlaneExterior
open Set Metric Topology

lemma exterior_connected {R : ℝ} (hR : 0≤R) :
    IsConnected {z : ℂ | R<‖z‖} := by
  have hs := isConnected_sphere (E:=ℂ) (by rw [Complex.rank_real_complex]; norm_num) (0:ℂ)
    (by norm_num : 0≤(1:ℝ))
  have ht : IsConnected (Ioi R) := isConnected_Ioi
  have hc := (hs.prod ht).image (fun p : ℂ×ℝ => p.2 • p.1) (by fun_prop)
  have he : (fun p : ℂ×ℝ => p.2 • p.1) '' (sphere (0:ℂ) 1 ×ˢ Ioi R)=
      {z : ℂ | R<‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
      have hu' : ‖u‖=1 := by simpa [mem_sphere,dist_zero_right] using hu
      change R<‖t • u‖
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hR.trans ht.le),hu',mul_one]
      exact ht
    · intro hz
      have hn : 0<‖z‖ := hR.trans_lt hz
      refine ⟨(‖z‖⁻¹ • z,‖z‖),⟨?_,hz⟩,?_⟩
      · simp [hn.ne']
      · simp [hn.ne']
  rwa [he] at hc
end CannonPlaneExterior

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_CompactifiedFace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem outer_face_compact_others (F : ι → Arc ℂ) :
    ∃ out : Faces F,∀ d : Faces F,d≠out → IsCompact (closure (face F d)) := by
  have hK : IsCompact (⋃ i,range (F i)) := isCompact_iUnion fun i=>(F i).compact_range
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0:ℂ)
  let E := {z : ℂ | R<‖z‖}
  have hE := CannonPlaneExterior.exterior_connected hR.le
  have hEK : E⊆(⋃ i,range (F i))ᶜ := by
    intro z hz hKz
    have hb := hKR hKz
    rw [mem_ball,dist_zero_right] at hb
    exact (lt_asymm hz hb)
  obtain ⟨x,hx⟩ := hE.nonempty
  let out : Faces F := ConnectedComponents.mk ⟨x,hEK hx⟩
  have hEf : E⊆face F out := by
    change E⊆region _ ConnectedComponents.mk _
    rw [component_region_eq]
    exact hE.isPreconnected.subset_connectedComponentIn hx hEK
  refine ⟨out,?_⟩
  intro d hd
  have hsub : face F d⊆closedBall (0:ℂ) R := by
    intro z hz
    rw [mem_closedBall,dist_zero_right]
    by_contra hh
    have ho := hEf (lt_of_not_ge hh)
    exact hd (hz.2.symm.trans ho.2)
  exact (isCompact_closedBall (0:ℂ) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsub isClosed_closedBall)

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem compactified_face_interiors_cover [DecidableEq ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty)
    (e : ℂ → X) (he : IsOpenEmbedding e) (p : X) (heR : range e={p}ᶜ)
    (hdense : DenseRange e) :
    (∀ x : X,∃ d : Faces F,x∈compactifiedFace F e d) ∧
    ∀ x : X,∃ v∈vertices F Finset.univ,
      x∈interior (⋃ d : Faces F,⋃ (_ : v∈faceVertices F d),compactifiedFace F e d) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hcover : ∀ x : X,∃ d : Faces F,x∈compactifiedFace F e d := by
    have hclosed : IsClosed (⋃ d : Faces F,compactifiedFace F e d) :=
      isClosed_iUnion_of_finite fun _=>isClosed_closure
    have hsub : range e⊆⋃d : Faces F,compactifiedFace F e d := by
      rintro _ ⟨z,rfl⟩
      obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
      exact mem_iUnion.mpr ⟨d,image_closure_subset_closure_image he.continuous ⟨z,hd,rfl⟩⟩
    intro x
    exact mem_iUnion.mp ((closure_minimal hsub hclosed) (hdense x))
  refine ⟨hcover,?_⟩
  obtain ⟨out,hout⟩ := outer_face_compact_others F
  have hp (d : Faces F) (hd : p∈compactifiedFace F e d) : d=out := by
    by_contra hn
    have hsub : compactifiedFace F e d⊆e '' closure (face F d) :=
      closure_minimal (image_mono subset_closure) (((hout d hn).image he.continuous).isClosed)
    have hpr : p∈range e := image_subset_range e _ (hsub hd)
    rw [heR] at hpr
    exact hpr (mem_singleton p)
  intro x
  by_cases hxp : x=p
  · subst x
    obtain ⟨v,hv⟩ := hcorner out
    have hvV := ((mem_faceVertices F out v).mp hv).1
    obtain ⟨i,hi⟩ := hvV
    refine ⟨v,(mem_vertices F Finset.univ v).mpr ⟨i,Finset.mem_univ _,hi⟩,?_⟩
    apply CannonFacialStars.interior_union_at _ (fun _=>isClosed_closure) hcover
    intro d hd
    exact (hp d hd).symm ▸ hv
  · have hxr : x∈range e := by rw [heR]; exact hxp
    obtain ⟨z,rfl⟩ := hxr
    obtain ⟨v,hv,hvd⟩ := common_vertex_at F hF Q hQ hcorner z
    refine ⟨v,hv,?_⟩
    apply CannonFacialStars.interior_union_at _ (fun _=>isClosed_closure) hcover
    intro d hd
    apply hvd d
    rw [he.isEmbedding.closure_eq_preimage_closure_image]
    exact hd
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_eventually_constant_facewise_realization (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ)
    (out : Faces F) (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d)))
    (q : ℂ) (hq : q∈faceHull F z out) :
    ∃ g : C(ℂ,ℂ),∃ K : Set ℂ,IsCompact K ∧
      (∀ x,x∉K → g x=q) ∧
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) ∧ faceHull F z d⊆g '' face F d := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨g,hg,hgD⟩:=exists_facewise_compact_surjective_realization F hF Q hQ hcorner z
  choose W hW hWU honto using fun d=>(hgD d).2
  let A : Set ℂ := (⋃ i,range (F i)) ∪ (⋃ d : Faces F,W d) ∪
    (⋃ d : {d : Faces F // d≠out},closure (face F d.val))
  have hA : IsCompact A := ((isCompact_iUnion fun i=>(F i).compact_range).union
    (isCompact_iUnion hW)).union (isCompact_iUnion fun d=>hout d.val d.property)
  obtain ⟨ψ,hψ,hψK,_,hψV⟩:=exists_continuousMap_one_of_isCompact_subset_isOpen hA isOpen_univ (subset_univ _)
  let f : C(ℂ,ℂ) := ⟨fun x=>(ψ x) • g x+(1-ψ x) • q,
    (ψ.continuous.smul g.continuous).add ((continuous_const.sub ψ.continuous).smul continuous_const)⟩
  have hfA {x : ℂ} (hx : x∈A) : f x=g x := by
    change (ψ x) • g x+(1-ψ x) • q=g x
    simp [hψ hx]
  refine ⟨f,tsupport ψ,hψK,?_,?_,?_⟩
  · intro x hx
    have hz : ψ x=0 := by
      by_contra hn
      exact hx (subset_closure hn)
    change (ψ x) • g x+(1-ψ x) • q=q
    simp [hz]
  · intro i t
    exact (hfA (Or.inl (Or.inl (mem_iUnion.mpr ⟨i,mem_range_self t⟩)))).trans (hg i t)
  · intro d
    constructor
    · intro x hx
      by_cases hd : d=out
      · subst d
        exact (convex_convexHull ℝ _) ((hgD out).1 hx) hq (hψV x).1
          (sub_nonneg.mpr (hψV x).2) (by ring)
      · rw [hfA (Or.inr (mem_iUnion.mpr ⟨⟨d,hd⟩,hx⟩))]
        exact (hgD d).1 hx
    · intro y hy
      obtain ⟨x,hx,hxy⟩:=honto d hy
      exact ⟨x,hWU d hx,(hfA (Or.inl (Or.inr (mem_iUnion.mpr ⟨d,hx⟩)))).trans hxy⟩
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_ClosedInside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

lemma area_combo (a b x y : ℂ) (s t : ℝ) (hst : s+t=1) :
    area a b (s • x+t • y)=s*area a b x+t*area a b y := by
  have ht : t=1-s := by linarith
  subst t
  simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

lemma closedInside_convex (a b c : ℂ) : Convex ℝ {p | ClosedInside a b c p} := by
  intro x hx y hy s t hs ht hst
  change 0≤area a b (s • x+t • y) ∧ 0≤area b c (s • x+t • y) ∧ 0≤area c a (s • x+t • y)
  rw [area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst]
  exact ⟨add_nonneg (mul_nonneg hs hx.1) (mul_nonneg ht hy.1),
    add_nonneg (mul_nonneg hs hx.2.1) (mul_nonneg ht hy.2.1),
    add_nonneg (mul_nonneg hs hx.2.2) (mul_nonneg ht hy.2.2)⟩
lemma area_barycentric (a b c p : ℂ) (h : area a b c≠0) :
    (area b c p/area a b c) • a+(area c a p/area a b c) • b+(area a b p/area a b c) • c=p := by
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  · field_simp
    simp only [area]
    ring
  · field_simp
    simp only [area]
    ring

lemma convexHull_eq_closedInside {a b c : ℂ} (h : 0<area a b c) :
    convexHull ℝ ({a,b,c}:Set ℂ)={p | ClosedInside a b c p} := by
  apply Subset.antisymm
  · apply convexHull_min _ (closedInside_convex a b c)
    have az (x y : ℂ) : area x y x=0 := by simp [area]
    have bz (x y : ℂ) : area x y y=0 := by unfold area; ring
    have ha : ClosedInside a b c a := ⟨by rw [az],by rw [area_cyclic]; exact h.le,by rw [bz]⟩
    have hb : ClosedInside a b c b := ⟨by rw [bz],by rw [az],by rw [area_cyclic,area_cyclic]; exact h.le⟩
    have hc : ClosedInside a b c c := ⟨h.le,by rw [bz],by rw [az]⟩
    rintro p (rfl|rfl|rfl) <;> assumption
  · intro p hp
    let w : Fin 3 → ℝ := ![area b c p/area a b c,area c a p/area a b c,area a b p/area a b c]
    let v : Fin 3 → ℂ := ![a,b,c]
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · exact div_nonneg hp.2.1 h.le
      · exact div_nonneg hp.2.2 h.le
      · exact div_nonneg hp.1 h.le
    · simp only [w,Fin.sum_univ_three]
      change area b c p/area a b c+area c a p/area a b c+area a b p/area a b c=1
      rw [←add_div,←add_div]
      have hs := area_sum a b c p
      convert div_self h.ne' using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      linarith
    · intro i
      fin_cases i <;> simp [v]
    · simp only [w,v,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      exact area_barycentric a b c p h.ne'

lemma convexHull_interior_nonempty {a b c : ℂ} (h : 0<area a b c) :
    (interior (convexHull ℝ ({a,b,c}:Set ℂ))).Nonempty := by
  have hsub : {p | Inside a b c p}⊆convexHull ℝ ({a,b,c}:Set ℂ) := by
    rw [convexHull_eq_closedInside h]
    exact fun p hp=>⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have hmean (x y z : ℂ) : area x y ((3:ℝ)⁻¹ • (x+y+z))=area x y z/3 := by
    simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    ring
  have hcent : Inside a b c ((3:ℝ)⁻¹ • (a+b+c)) := by
    constructor
    · rw [hmean]; positivity
    constructor
    · have he : a+b+c=b+c+a := by ring
      rw [he,hmean,area_cyclic]
      positivity
    · have he : a+b+c=c+a+b := by ring
      rw [he,hmean,area_cyclic,area_cyclic]
      positivity
  exact ⟨_,(interior_mono hsub) (by rw [(inside_open a b c).interior_eq]; exact hcent)⟩

lemma area_isOpenMap {a b c : ℂ} (h : 0<area a b c) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL : Function.Surjective L := by
    intro y
    refine ⟨(y / area a b c) • (c-a),?_⟩
    rw [map_smul]
    have he : L (c-a)=area a b c := by simp [L,area]
    rw [he,smul_eq_mul,div_mul_cancel₀ _ h.ne']
  have he : area a b=fun p=>L (p-a) := by
    funext p
    simp [L,area]
  rw [he]
  exact (L.isOpenMap hL).comp (Homeomorph.subRight a).isOpenMap

lemma area_continuous (a b : ℂ) : Continuous (area a b) := by
  unfold area
  fun_prop

lemma convexHull_interior {a b c : ℂ} (h : 0<area a b c) :
    interior (convexHull ℝ ({a,b,c}:Set ℂ))={p | Inside a b c p} := by
  have h1 := (area_isOpenMap h).preimage_interior_eq_interior_preimage (area_continuous a b) (Ici 0)
  have hb : 0<area b c a := by simpa only [area_cyclic] using h
  have hc : 0<area c a b := by simpa only [area_cyclic] using h
  have h2 := (area_isOpenMap hb).preimage_interior_eq_interior_preimage (area_continuous b c) (Ici 0)
  have h3 := (area_isOpenMap hc).preimage_interior_eq_interior_preimage (area_continuous c a) (Ici 0)
  rw [interior_Ici] at h1 h2 h3
  rw [convexHull_eq_closedInside h]
  change interior ((area a b ⁻¹' Ici 0)∩((area b c ⁻¹' Ici 0)∩(area c a ⁻¹' Ici 0)))=_
  rw [interior_inter,interior_inter,←h1,←h2,←h3]
  ext p
  simp only [mem_inter_iff,mem_preimage,mem_Ioi,mem_ofPred_eq,Inside]

lemma convexHull_closure_inside {a b c : ℂ} (h : 0<area a b c) :
    closure {p | Inside a b c p}=convexHull ℝ ({a,b,c}:Set ℂ) := by
  rw [←convexHull_interior h]
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior (convexHull_interior_nonempty h)]
  have hc : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) := by
    rw [convexHull_eq_closedInside h]
    exact (isClosed_le continuous_const (area_continuous a b)).inter
      ((isClosed_le continuous_const (area_continuous b c)).inter
        (isClosed_le continuous_const (area_continuous c a)))
  exact hc.closure_eq

lemma vertices_segment_frontier {a b c x y : ℂ} (h : 0<area a b c)
    (hx : x∈({a,b,c}:Set ℂ)) (hy : y∈({a,b,c}:Set ℂ)) :
    segment ℝ x y⊆frontier (convexHull ℝ ({a,b,c}:Set ℂ)) := by
  intro p hp
  change p∈closure (convexHull ℝ ({a,b,c}:Set ℂ)) ∧ p∉interior (convexHull ℝ ({a,b,c}:Set ℂ))
  refine ⟨subset_closure ((convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy) hp),?_⟩
  rw [convexHull_interior h]
  obtain ⟨s,t,hs,ht,hst,rfl⟩:=hp
  have hz : area a b (s • x+t • y)=0 ∨ area b c (s • x+t • y)=0 ∨ area c a (s • x+t • y)=0 := by
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      simp only [area_combo _ _ _ _ _ _ hst] <;> unfold area <;> ring_nf <;> tauto
  intro hh
  rcases hz with hz|hz|hz
  · have := hh.1; rw [hz] at this; linarith
  · have := hh.2.1; rw [hz] at this; linarith
  · have := hh.2.2; rw [hz] at this; linarith

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.hull_eq (C : FacialCycle F d) (z : ℂ → ℂ) :
    faceHull F z d=convexHull ℝ ({z C.a,z C.b,z C.c}:Set ℂ) := by
  unfold faceHull
  rw [C.vertices]
  simp only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton]

omit [DecidableEq ι] [Nonempty ι] in
lemma graph_extension_frontier (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (z : ℂ → ℂ) (g : C(ℂ,ℂ))
    (hg : ∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t)
    (d : Faces F) (C : FacialCycle F d) (hp : 0<area (z C.a) (z C.b) (z C.c))
    {x : ℂ} (hx : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
    g x∈frontier (faceHull F z d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change closure (face F d)=face F d∪_ at hcl
  rw [hcl] at hx
  have hxE : x∈⋃i∈regionEdges F ConnectedComponents.mk d,range (F i) := by
    rcases hx with hx|hx
    · exact (hx.1 hxK).elim
    · exact hx
  obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hxE
  have hend (e : I) (he : e=0 ∨ e=1) : F i e∈faceVertices F d := by
    apply (mem_faceVertices F _ _).mpr
    exact ⟨⟨i,by rcases he with rfl|rfl; exact Or.inl rfl; exact Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨e,rfl⟩⟩
  have h0 : z (F i 0)∈({z C.a,z C.b,z C.c}:Set ℂ) := by
    have := hend 0 (Or.inl rfl)
    rw [C.vertices] at this
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with h|h|h <;> simp [h]
  have h1 : z (F i 1)∈({z C.a,z C.b,z C.c}:Set ℂ) := by
    have := hend 1 (Or.inr rfl)
    rw [C.vertices] at this
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with h|h|h <;> simp [h]
  rw [hg,C.hull_eq]
  exact vertices_segment_frontier hp h0 h1 (by rw [←Path.range_segment]; exact mem_range_self t)

theorem exists_spherical_facewise_realization (F : ι → Arc ℂ) [Fintype (Faces F)]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ)
    (out : Faces F) (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d)))
    (O : FacialCycle F out) (ho : 0<area (z O.a) (z O.b) (z O.c))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
      (∀ x∈frontier (faceHull F z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
      J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))=
        (((↑) '' interior (faceHull F z out) : Set (OnePoint ℂ)))ᶜ ∧
      ∃ f : C(OnePoint ℂ,OnePoint ℂ),Function.Surjective f ∧
        (∀ d : Faces F,d≠out → MapsTo (fun x : ℂ=>f (x:OnePoint ℂ))
          (closure (face F d)) ((↑) '' faceHull F z d)) ∧
        MapsTo (fun x : ℂ=>f (x:OnePoint ℂ)) (closure (face F out))
          (J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))) ∧
        (∀ i t,f ((F i t:ℂ):OnePoint ℂ)=((Path.segment (z (F i 0)) (z (F i 1)) t:ℂ):OnePoint ℂ)) := by
  classical
  let S := OnePoint ℂ
  have hK : IsCompact (faceHull F z out) := ((faceVertices F out).finite_toSet.image z).isCompact_convexHull ℝ
  have hi : (interior (faceHull F z out)).Nonempty := by rw [O.hull_eq]; exact convexHull_interior_nonempty ho
  obtain ⟨J,hfix,hreflect⟩ := CannonSphereReflection.exists_convex_reflection (faceHull F z out) hK
    (convex_convexHull ℝ _) hi
  let q := z O.a
  have hq : q∈faceHull F z out := subset_convexHull ℝ _ ⟨O.a,O.mem_a,rfl⟩
  obtain ⟨g,K,hKc,hgK,hg,hgD⟩:=exists_eventually_constant_facewise_realization F hF Q hQ hcorner z out hout q hq
  let fD (d : Faces F) : C(ℂ,S) := if d=out then
    ⟨fun x=>J ((g x:ℂ):S),J.continuous.comp (OnePoint.continuous_coe.comp g.continuous)⟩ else
    ⟨fun x=>(g x:ℂ),OnePoint.continuous_coe.comp g.continuous⟩
  have hgraph (d : Faces F) (x : ℂ) (hxd : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
      fD d x=((g x:ℂ):S) := by
    dsimp [fD]
    split_ifs with hd
    · subst d
      exact hfix _ (graph_extension_frontier F hF Q hQ z g hg out O ho hxd hxK)
    · rfl
  obtain ⟨f,hf⟩ := CannonFiniteClosedGluing.exists_gluing
    (fun d : Faces F=>closure (face F d)) (fun _=>isClosed_closure)
    (facial_closures_cover F hF Q hQ) fD (by
      intro d e x hxd hxe
      by_cases hde : d=e
      · rw [hde]
      have hxK : x∈⋃i,range (F i) := by
        by_contra hxK
        let c : Faces F := ConnectedComponents.mk ⟨x,hxK⟩
        have hc : x∈face F c := ⟨hxK,rfl⟩
        exact hde ((same_face_of_mem_closure F hc hxd).symm.trans (same_face_of_mem_closure F hc hxe))
      exact (hgraph d x hxd hxK).trans (hgraph e x hxe hxK).symm)
  let L : Set ℂ := K∪⋃ d : {d : Faces F // d≠out},closure (face F d.val)
  have hL : IsCompact L := hKc.union (isCompact_iUnion fun d=>hout d.val d.property)
  have hfL (x : ℂ) (hx : x∉L) : f x=J (q:S) := by
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ x
    have he : d=out := by
      by_contra hn
      exact hx (Or.inr (mem_iUnion.mpr ⟨⟨d,hn⟩,hd⟩))
    subst d
    rw [hf out x hd]
    simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk,hgK x (fun h=>hx (Or.inl h))]
  let fS : S → S := OnePoint.rec (J (q:S)) f
  have hfS : Continuous fS := by
    rw [OnePoint.continuous_iff]
    constructor
    · apply Filter.Tendsto.congr' (f₁:=fun _ : ℂ=>J (q:S)) ?_ tendsto_const_nhds
      exact Filter.hasBasis_coclosedCompact.mem_iff.mpr ⟨L,⟨hL.isClosed,hL⟩,fun x hx=>(hfL x hx).symm⟩
    · exact f.continuous
  refine ⟨J,hfix,hreflect,⟨fS,hfS⟩,?_,?_,?_,?_⟩
  · intro y
    by_cases hy : y∈((↑) '' interior (faceHull F z out) : Set S)
    · obtain ⟨v,hv,rfl⟩:=hy
      have hvK := interior_subset hv
      rw [←hfill] at hvK
      obtain ⟨d,hd⟩:=mem_iUnion.mp hvK
      obtain ⟨x,hx,hgx⟩:=(hgD d.val).2 hd
      refine ⟨(x:S),?_⟩
      change f x=(v:S)
      rw [hf d.val x (subset_closure hx)]
      simp only [fD,ite_eq_right d.property,ContinuousMap.coe_mk,hgx]
    · have hyJ : y∈J '' ((↑) '' faceHull F z out : Set S) := by rw [hreflect]; exact hy
      obtain ⟨_,⟨v,hv,rfl⟩,rfl⟩:=hyJ
      obtain ⟨x,hx,hgx⟩:=(hgD out).2 hv
      refine ⟨(x:S),?_⟩
      change f x=J (v:S)
      rw [hf out x (subset_closure hx)]
      simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk,hgx]
  · intro d hd x hx
    change f x∈_
    rw [hf d x hx]
    simp only [fD,ite_eq_right hd,ContinuousMap.coe_mk]
    exact mem_image_of_mem _ ((hgD d).1 hx)
  · intro x hx
    change f x∈_
    rw [hf out x hx]
    simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk]
    exact mem_image_of_mem J (mem_image_of_mem _ ((hgD out).1 hx))
  · intro i t
    obtain ⟨d,hd⟩:=facial_closures_cover F hF Q hQ (F i t)
    change f (F i t)=_
    rw [hf d _ hd,hgraph d _ hd (mem_iUnion.mpr ⟨i,mem_range_self t⟩),hg]
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

theorem DevelopedFaces.spherical_realization (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3)
    (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d))) :
    ∃ z : ℂ → ℂ,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      (∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → B.radius u+B.radius v≤dist (z u) (z v)) ∧
      ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
        (∀ x∈frontier (faceHull F z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
        J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))=
          (((↑) '' interior (faceHull F z out) : Set (OnePoint ℂ)))ᶜ ∧
        ∃ f : C(OnePoint ℂ,OnePoint ℂ),Function.Surjective f ∧
          (∀ d : Faces F,d≠out → MapsTo (fun x : ℂ=>f (x:OnePoint ℂ))
            (closure (face F d)) ((↑) '' faceHull F z d)) ∧
          MapsTo (fun x : ℂ=>f (x:OnePoint ℂ)) (closure (face F out))
            (J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))) ∧
          (∀ i t,f ((F i t:ℂ):OnePoint ℂ)=((Path.segment (z (F i 0)) (z (F i 1)) t:ℂ):OnePoint ℂ)) := by
  classical
  obtain ⟨z,C,O,hz,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  have hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out := by
    have H:=triangle_closures_fill (fun d=>z (C d).a) (fun d=>z (C d).b) (fun d=>z (C d).c)
      (z O.a) (z O.b) (z O.c) hpos ho (hchain ℤ)
    simp only [convexHull_closure_inside (hpos _),convexHull_closure_inside ho] at H
    simp_rw [(C _).hull_eq,O.hull_eq]
    exact H
  have hcorner (d : Faces F) : (faceVertices F d).Nonempty := Finset.card_pos.mp (by rw [hthree]; norm_num)
  refine ⟨z,hz,hlen,?_,exists_spherical_facewise_realization F hF Q hQ hcorner z out hout O ho hfill⟩
  intro q hq v hv hqv
  by_cases hqo : q∈faceVertices F out
  · by_cases hvo : v∈faceVertices F out
    · exact (O.developed_length hqo hvo hqv z B.radius hlen).ge
    · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
        (hchain ℤ) hdis hv hq hvo hqv.symm
      have HH:=(disjoint_ball_ball_iff (B.radius_pos v) (B.radius_pos q)).mp H
      simpa only [add_comm,dist_comm] using HH
  · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
      (hchain ℤ) hdis hq hv hqo hqv
    exact (disjoint_ball_ball_iff (B.radius_pos q) (B.radius_pos v)).mp H
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.hull_radius_bound (C : FacialCycle F d) (z : ℂ → ℂ) (ρ : ℂ → ℝ)
    (hρ : ∀ v,0<ρ v) (c : ℝ) (hc : 0 < c)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hring : ∀ i u v,Spans (F i) u v → c*ρ u≤ρ v ∧ c*ρ v≤ρ u)
    {v : ℂ} (hv : v∈faceVertices F d) :
    faceHull F z d⊆closedBall (z v) ((1+c⁻¹)*ρ v) := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨w,hw,rfl⟩
  rw [mem_closedBall]
  by_cases hwv : w=v
  · subst w
    simp only [dist_self]
    exact mul_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hc.le)) (hρ v).le
  · obtain ⟨i,hi⟩:=C.pair_edge hw hv hwv
    rw [hi.developed_length z ρ (hlen i)]
    have hr : ρ w ≤ c⁻¹*ρ v := by
      have hh := (hring i w v hi).1
      exact (le_div_iff₀ hc).mpr (by nlinarith) |>.trans_eq (by rw [div_eq_mul_inv,mul_comm])
    nlinarith

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_NoTripleClosedBalls
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTangentSegments
open Set Metric

theorem no_triple_closedBalls {u v w x : ℂ} {a b c : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0 < c)
    (huv : a+b≤dist u v) (huw : a+c≤dist u w) (hvw : b+c≤dist v w)
    (hxu : dist u x≤a) (hxv : dist v x≤b) (hxw : dist w x ≤ c) : False := by
  have hvu:=dist_triangle u x v
  have hwu:=dist_triangle u x w
  have hwv:=dist_triangle v x w
  rw [dist_comm x v] at hvu
  rw [dist_comm x w] at hwu hwv
  have exu : dist u x=a := by linarith
  have exv : dist v x=b := by linarith
  have exw : dist w x=c := by linarith
  have Huv : x∈segment ℝ u v := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x v]; linarith))
  have Huw : x∈segment ℝ u w := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x w]; linarith))
  have Hvw : x∈segment ℝ v w := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x w]; linarith))
  have hxu0 : x-u≠0 := sub_ne_zero.mpr (by intro h; subst x; simp at exu; linarith)
  have hxw0 : w-x≠0 := sub_ne_zero.mpr (by intro h; subst w; simp at exw; linarith)
  have hxv0 : v-x≠0 := sub_ne_zero.mpr (by intro h; subst v; simp at exv; linarith)
  have hr := (sameRay_of_mem_segment Huv).symm.trans (sameRay_of_mem_segment Huw)
    (fun h=>(hxu0 h).elim)
  have hn := hr.trans (sameRay_of_mem_segment Hvw).symm (fun h=>(hxw0 h).elim)
  have hn' : SameRay ℝ (v-x) (-(v-x)) := by simpa only [neg_sub] using hn
  exact hxv0 (eq_zero_of_sameRay_self_neg hn')

theorem disjoint_edges {u v w z : ℂ} {a b c d : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hd : 0<d)
    (huv : dist u v=a+b) (hwz : dist w z=c+d)
    (huw : a+c≤dist u w) (huz : a+d≤dist u z)
    (hvw : b+c≤dist v w) (hvz : b+d≤dist v z) :
    Disjoint (segment ℝ u v) (segment ℝ w z) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have H : dist u x+dist x v=dist u v := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx)
  have K : dist w x+dist x z=dist w z := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hy)
  rw [huv,dist_comm x v] at H
  rw [hwz,dist_comm x z] at K
  have het (p q s : ℂ) (r t : ℝ) (hp : dist p s ≤ r) (hq : dist q s≤t)
      (hpq : r+t≤dist p q) : dist p s=r := by
    have hh:=dist_triangle p s q
    rw [dist_comm s q] at hh
    linarith
  by_cases hxu : dist u x≤a
  · by_cases hxw : dist w x ≤ c
    · have exu:=het u w x a c hxu hxw huw
      have hxv : dist v x≤b := by linarith
      exact no_triple_closedBalls ha hb hc huv.ge huw hvw hxu hxv hxw
    · have hxz : dist z x≤d := by linarith
      have exu:=het u z x a d hxu hxz huz
      have hxv : dist v x≤b := by linarith
      exact no_triple_closedBalls ha hb hd huv.ge huz hvz hxu hxv hxz
  · have hxv : dist v x≤b := by linarith
    by_cases hxw : dist w x ≤ c
    · have exv:=het v w x b c hxv hxw hvw
      have hxu : dist u x≤a := by linarith
      exact no_triple_closedBalls ha hb hc huv.ge huw hvw hxu hxv hxw
    · have hxz : dist z x≤d := by linarith
      have exv:=het v z x b d hxv hxz hvz
      have hxu : dist u x≤a := by linarith
      exact no_triple_closedBalls ha hb hd huv.ge huz hvz hxu hxv hxz

end CannonTangentSegments

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_ClosedInsideSegment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

lemma closedInside_zero_segment {a b c p : ℂ} (h : 0<area a b c)
    (hp : ClosedInside a b c p) (hz : area a b p=0) : p∈segment ℝ a b := by
  refine ⟨area b c p/area a b c,area c a p/area a b c,
    div_nonneg hp.2.1 h.le,div_nonneg hp.2.2 h.le,?_,?_⟩
  · rw [←add_div]
    have hs:=area_sum a b c p
    have he : area b c p+area c a p=area a b c := by linarith
    rw [he,div_self h.ne']
  · have H:=area_barycentric a b c p h.ne'
    simpa only [hz,zero_div,zero_smul,add_zero] using H

lemma frontier_hull_segments {a b c : ℂ} (h : 0<area a b c) :
    frontier (convexHull ℝ ({a,b,c}:Set ℂ))⊆
      segment ℝ a b∪segment ℝ b c∪segment ℝ c a := by
  intro p hp
  have hclosed : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) :=
    (Set.toFinite ({a,b,c}:Set ℂ)).isCompact_convexHull ℝ |>.isClosed
  have hin : ClosedInside a b c p := by
    have H:=hclosed.closure_eq ▸ hp.1
    rw [convexHull_eq_closedInside h] at H
    exact H
  have hout : ¬ Inside a b c p := by
    simpa only [convexHull_interior h,mem_ofPred_eq] using hp.2
  have hz : area a b p=0 ∨ area b c p=0 ∨ area c a p=0 := by
    by_contra H
    push Not at H
    exact hout ⟨lt_of_le_of_ne hin.1 (Ne.symm H.1),
      lt_of_le_of_ne hin.2.1 (Ne.symm H.2.1),lt_of_le_of_ne hin.2.2 (Ne.symm H.2.2)⟩
  rcases hz with hz|hz|hz
  · exact Or.inl (Or.inl (closedInside_zero_segment h hin hz))
  · exact Or.inl (Or.inr (closedInside_zero_segment (by rwa [area_cyclic])
      ⟨hin.2.1,hin.2.2,hin.1⟩ hz))
  · exact Or.inr (closedInside_zero_segment (by rwa [area_cyclic,area_cyclic])
      ⟨hin.2.2,hin.1,hin.2.1⟩ hz)

lemma hull_inter_frontier {a b c u v w p : ℂ}
    (h : 0<area a b c) (hk : 0<area u v w)
    (hdis : Disjoint (interior (convexHull ℝ ({a,b,c}:Set ℂ)))
      (interior (convexHull ℝ ({u,v,w}:Set ℂ))))
    (hp : p∈convexHull ℝ ({a,b,c}:Set ℂ))
    (hq : p∈convexHull ℝ ({u,v,w}:Set ℂ)) :
    p∈frontier (convexHull ℝ ({a,b,c}:Set ℂ)) ∧
      p∈frontier (convexHull ℝ ({u,v,w}:Set ℂ)) := by
  have hc1 : closure (interior (convexHull ℝ ({a,b,c}:Set ℂ)))=convexHull ℝ ({a,b,c}:Set ℂ) := by
    rw [convexHull_interior h,convexHull_closure_inside h]
  have hc2 : closure (interior (convexHull ℝ ({u,v,w}:Set ℂ)))=convexHull ℝ ({u,v,w}:Set ℂ) := by
    rw [convexHull_interior hk,convexHull_closure_inside hk]
  have ha : p∉interior (convexHull ℝ ({a,b,c}:Set ℂ)) := by
    have H:=hdis.symm.closure_left isOpen_interior
    rw [hc2] at H
    exact fun hh=>Set.disjoint_left.mp H hq hh
  have hb : p∉interior (convexHull ℝ ({u,v,w}:Set ℂ)) := by
    have H:=hdis.closure_left isOpen_interior
    rw [hc1] at H
    exact fun hh=>Set.disjoint_left.mp H hp hh
  exact ⟨⟨subset_closure hp,ha⟩,⟨subset_closure hq,hb⟩⟩
end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {d e : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.frontier_edges (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<area (z C.a) (z C.b) (z C.c)) {p : ℂ}
    (hp : p∈frontier (faceHull F z d)) :
    ∃ u∈faceVertices F d,∃ v∈faceVertices F d,u≠v ∧ p∈segment ℝ (z u) (z v) := by
  rw [C.hull_eq] at hp
  rcases frontier_hull_segments hpos hp with (hp|hp)|hp
  · exact ⟨C.a,C.mem_a,C.b,C.mem_b,C.ab,hp⟩
  · exact ⟨C.b,C.mem_b,C.c,C.mem_c,C.bc,hp⟩
  · exact ⟨C.c,C.mem_c,C.a,C.mem_a,C.ac.symm,hp⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.common_vertex_of_frontier_inter (C : FacialCycle F d) (E : FacialCycle F e)
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0 < r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hC : 0<area (z C.a) (z C.b) (z C.c))
    (hE : 0<area (z E.a) (z E.b) (z E.c))
    (hp : (frontier (faceHull F z d)∩frontier (faceHull F z e)).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  classical
  by_contra hn
  have hne (u : ℂ) (hu : u∈faceVertices F d) (v : ℂ) (hv : v∈faceVertices F e) : u≠v := by
    intro H
    subst v
    exact hn ⟨u,hu,hv⟩
  obtain ⟨p,hpd,hpe⟩:=hp
  obtain ⟨u,hu,v,hv,huv,hp⟩:=C.frontier_edges z hC hpd
  obtain ⟨w,hw,t,ht,hwt,hq⟩:=E.frontier_edges z hE hpe
  have hvV {d : Faces F} {v : ℂ} (hv : v∈faceVertices F d) : Vertex F v :=
    ((mem_faceVertices F d v).mp hv).1
  have H:=CannonTangentSegments.disjoint_edges (hr u) (hr v) (hr w) (hr t)
    (C.developed_length hu hv huv z r hlen) (E.developed_length hw ht hwt z r hlen)
    (hdis u (hvV hu) w (hvV hw) (hne u hu w hw))
    (hdis u (hvV hu) t (hvV ht) (hne u hu t ht))
    (hdis v (hvV hv) w (hvV hw) (hne v hv w hw))
    (hdis v (hvV hv) t (hvV ht) (hne v hv t ht))
  exact Set.disjoint_left.mp H hp hq

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.common_vertex_of_hull_inter (C : FacialCycle F d) (E : FacialCycle F e)
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0 < r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hC : 0<area (z C.a) (z C.b) (z C.c))
    (hE : 0<area (z E.a) (z E.b) (z E.c))
    (hI : Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hp : (faceHull F z d∩faceHull F z e).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  apply C.common_vertex_of_frontier_inter E z r hr hlen hdis hC hE
  obtain ⟨p,hpd,hpe⟩:=hp
  refine ⟨p,?_⟩
  simp only [C.hull_eq,E.hull_eq] at hI hpd hpe ⊢
  exact hull_inter_frontier hC hE hI hpd hpe
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence

variable {ι X Y : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [TopologicalSpace X] [TopologicalSpace Y]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma compactifiedFace_mapsTo (F : ι → Arc ℂ) (e : ℂ → X) (f : C(X,Y))
    (d : Faces F) (U : Set Y) (hU : IsClosed U)
    (hf : MapsTo (f ∘ e) (closure (face F d)) U) :
    MapsTo f (compactifiedFace F e d) U := by
  apply Set.MapsTo.closure_left (hc:=f.continuous) (ht:=hU)
  rintro _ ⟨x,hx,rfl⟩
  exact hf (subset_closure hx)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma compactifiedFace_dist_bound {X : Type*} [PseudoMetricSpace X]
    (F : ι → Arc ℂ) (e : ℂ → X) (d : Faces F) (R : ℝ)
    (hR : ∀ z∈closure (face F d),∀ w∈closure (face F d),dist (e z) (e w)≤R) :
    ∀ x∈compactifiedFace F e d,∀ y∈compactifiedFace F e d,dist x y≤R := by
  intro x hx y hy
  have H : dist x y∈closure (Iic R) :=
    map_mem_closure₂ continuous_dist hx hy (by
      rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩
      exact hR z (subset_closure hz) w (subset_closure hw))
  simpa only [closure_Iic,mem_Iic] using H
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_closed (z : ℂ → ℂ) (out d : Faces F) : IsClosed (sphereTile F z out d) := by
  classical
  unfold sphereTile
  split_ifs
  · exact (OnePoint.isOpenMap_coe _ isOpen_interior).isClosed_compl
  · exact ((((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ).image OnePoint.continuous_coe).isClosed

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_cover (z : ℂ → ℂ)
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    ∀ p : OnePoint ℂ,∃ d : Faces F,p∈sphereTile F z out d := by
  classical
  intro p
  by_cases hp : p∈((↑) '' interior (faceHull F z out):Set (OnePoint ℂ))
  · obtain ⟨q,hq,rfl⟩:=hp
    have hq':=interior_subset hq
    rw [←hfill] at hq'
    obtain ⟨d,hd⟩:=mem_iUnion.mp hq'
    exact ⟨d.val,by simp only [sphereTile,ite_eq_right d.property]; exact ⟨q,hd,rfl⟩⟩
  · exact ⟨out,by simpa [sphereTile] using hp⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
theorem sphereTile_inter_common_vertex (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (d e : Faces F) (hmeet : (sphereTile F z out d∩sphereTile F z out e).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  classical
  by_cases hde : d=e
  · subst e
    obtain ⟨C,hC⟩:=hcycles d
    exact ⟨C.a,C.mem_a,C.mem_a⟩
  have outer (d : Faces F) (hd : d≠out)
      (hm : (sphereTile F z out d∩sphereTile F z out out).Nonempty) :
      ∃ v,v∈faceVertices F d ∧ v∈faceVertices F out := by
    obtain ⟨p,hpd,hpo⟩:=hm
    simp only [sphereTile,ite_eq_right hd] at hpd
    obtain ⟨q,hq,rfl⟩:=hpd
    simp only [sphereTile] at hpo
    have hqo : q∉interior (faceHull F z out) := by
      intro h
      apply hpo
      exact ⟨q,h,rfl⟩
    have hsub : faceHull F z d⊆faceHull F z out := by
      rw [←hfill]
      exact subset_iUnion (fun d : {d : Faces F // d≠out}=>faceHull F z d.val) ⟨d,hd⟩
    obtain ⟨C,hC⟩:=hcycles d
    obtain ⟨O,hO⟩:=hcycles out
    apply C.common_vertex_of_frontier_inter O z ρ hρ hlen hdis hC hO
    refine ⟨q,⟨subset_closure hq,fun hi=>hqo (interior_mono hsub hi)⟩,
      subset_closure (hsub hq),hqo⟩
  by_cases hd : d=out
  · subst d
    obtain ⟨v,hve,hvo⟩:=outer e (Ne.symm hde) (by simpa only [inter_comm] using hmeet)
    exact ⟨v,hvo,hve⟩
  by_cases he : e=out
  · subst e
    exact outer d hd hmeet
  obtain ⟨C,hC⟩:=hcycles d
  obtain ⟨E,hE⟩:=hcycles e
  apply C.common_vertex_of_hull_inter E z ρ hρ hlen hdis hC hE (hI d e hd he hde)
  obtain ⟨p,hpd,hpe⟩:=hmeet
  simp only [sphereTile,ite_eq_right hd,ite_eq_right he] at hpd hpe
  obtain ⟨q,hq,rfl⟩:=hpd
  obtain ⟨w,hw,hew⟩:=hpe
  have hew' : w=q:=OnePoint.coe_injective hew
  subst w
  exact ⟨q,hq,hw⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X]
omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] [T2Space X] in
lemma compactifiedFace_vertex (e : ℂ → X) (he : Continuous e)
    {d : Faces F} {v : ℂ} (hv : v∈faceVertices F d) : e v∈compactifiedFace F e d :=
  image_closure_subset_closure_image he ⟨v,((mem_faceVertices F d v).mp hv).2,rfl⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] [T2Space X] in
lemma compactifiedFace_preconnected (e : ℂ → X) (he : Continuous e) (d : Faces F) :
    IsPreconnected (compactifiedFace F e d) :=
  ((component_region_connected _ d).isPreconnected.image e he.continuousOn).closure

omit [DecidableEq ι] [Nonempty ι] [T2Space X] in
theorem sphere_carrier_preconnected (e : ℂ → X) (he : Continuous e)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (S : Set (OnePoint ℂ)) (hS : IsPreconnected S) :
    IsPreconnected (⋃ (d : {d : Faces F // (S∩sphereTile F z out d).Nonempty}),
      compactifiedFace F e d.val) := by
  apply CannonFiniteCarrier.connected_carrier _ _ (compactifiedFace_preconnected e he)
    (sphereTile_closed z out) S hS
  · intro y hy
    exact mem_iUnion.mpr (sphereTile_cover z hfill y)
  · intro d k hdk
    obtain ⟨v,hvd,hvk⟩:=sphereTile_inter_common_vertex z ρ hρ hlen hdis hcycles hI hfill d k
      (by obtain ⟨x,⟨_,hx⟩,hk⟩:=hdk; exact ⟨x,hx,hk⟩)
    exact ⟨e v,compactifiedFace_vertex e he hvd,compactifiedFace_vertex e he hvk⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
theorem sphere_realization_fiber_bound {X : Type*} [PseudoMetricSpace X]
    (e : ℂ → X) (he : Continuous e) (f : X → OnePoint ℂ)
    (hcover : ∀ x,∃ d : Faces F,x∈compactifiedFace F e d)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (hf : ∀ d,MapsTo f (compactifiedFace F e d) (sphereTile F z out d))
    (R : ℝ) (hR : ∀ d,∀ x∈compactifiedFace F e d,∀ y∈compactifiedFace F e d,dist x y≤R)
    (x y : X) (hxy : f x=f y) : dist x y≤2*R := by
  obtain ⟨d,hd⟩:=hcover x
  obtain ⟨k,hk⟩:=hcover y
  obtain ⟨v,hvd,hvk⟩:=sphereTile_inter_common_vertex z ρ hρ hlen hdis hcycles hI hfill d k
    ⟨f x,hf d hd,hxy.symm ▸ hf k hk⟩
  have hvd' := image_closure_subset_closure_image he ⟨v,((mem_faceVertices F d v).mp hvd).2,rfl⟩
  have hvk' := image_closure_subset_closure_image he ⟨v,((mem_faceVertices F k v).mp hvk).2,rfl⟩
  calc dist x y ≤ dist x (e v)+dist (e v) y := dist_triangle _ _ _
       _ ≤ R+R := add_le_add (hR d x hd (e v) hvd') (hR k (e v) hvk' y hk)
       _ = 2*R := by ring
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

theorem normalize_finite_realization {X : Type*} [PseudoMetricSpace X]
    (f : C(X,Sphere)) (hf : Function.Surjective f) (R : ℝ)
    (hsmall : ∀ x y,f x=f y → dist x y≤R)
    (a : Fin 3 → X) (ha : ∀ i j,i≠j → R<dist (a i) (a j)) :
    ∃ N : Sphere ≃ₜ Sphere,N∈biholomorphic ∧
      ∃ g : C(X,Sphere),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
        (∀ i,g (a i)=std i) ∧ (∀ x y,g x=g y → dist x y≤R) := by
  have hinj : Function.Injective (fun i=>f (a i)) := by
    intro i j hij
    by_contra hn
    exact (not_le_of_gt (ha i j hn)) (hsmall _ _ hij)
  let t : Triple := ⟨fun i=>f (a i),hinj⟩
  obtain ⟨M,hM,hMt⟩ := exists_triple_normalizer t
  let g : C(X,Sphere) := ⟨M.symm ∘ f,M.symm.continuous.comp f.continuous⟩
  refine ⟨M.symm,biholomorphic.inv_mem hM,g,(fun _=>rfl),M.symm.surjective.comp hf,?_,?_⟩
  · intro i
    have H : M (std i)=f (a i) := congrArg (fun t : Triple=>t.val i) hMt
    change M.symm (f (a i))=std i
    rw [←H,M.symm_apply_apply]
  · intro x y hxy
    exact hsmall x y (M.symm.injective hxy)

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexNearCard
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric unitInterval

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [Fintype ι]

lemma vertex_near_card_le (H : ι → Arc ℂ) (e : ℂ → X) (x : X) (R : ℝ) :
    Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<R} ≤
      2*Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<R} := by
  classical
  let J := {i : ι // ∃ t:I,dist (e (H i t)) x<R}
  let f : J × Bool → ℂ:=fun j=>if j.2 then H j.1.val 0 else H j.1.val 1
  have hsub : {v : ℂ | Vertex H v ∧ dist (e v) x<R}⊆range f := by
    rintro v ⟨⟨i,hi|hi⟩,hv⟩
    · refine ⟨(⟨i,⟨0,hi.symm ▸ hv⟩⟩,true),?_⟩
      simpa only [f,ite_true] using hi
    · refine ⟨(⟨i,⟨1,hi.symm ▸ hv⟩⟩,false),?_⟩
      simpa only [f,Bool.false_eq_true,ite_false] using hi
  have h1:=Nat.card_mono (finite_range f) hsub
  have h2 : Nat.card (range f)≤Nat.card (J × Bool) :=
    Nat.card_le_card_of_surjective (fun j=>(⟨f j,mem_range_self j⟩:range f)) (by
      rintro ⟨w,⟨j,rfl⟩⟩; exact ⟨j,rfl⟩)
  calc
    _ ≤ Nat.card (range f) := h1
    _ ≤ Nat.card (J × Bool) := h2
    _ = _ := by
      rw [Nat.card_prod]
      change Nat.card J*Nat.card Bool=2*Nat.card J
      have hb : Nat.card Bool=2 := by norm_num
      rw [hb,Nat.mul_comm]
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_UniformOriginalChargingCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonCarrierCharging
open Set Metric unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonIncidence

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

theorem uniform_original_charging_counts (Q : ℕ) (C L : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hL : 1≤L)
    (N : ℕ) :
    ∃ kr kc : ℕ, ∀ (r M : ℝ),0 < r → 1≤M → (L+4)*r≤1 →
      ∀ T : Finset X,(∀ x∈T,∀ y∈T,x≠y → r≤dist x y) →
      (∀ x : X,∃ y∈T,dist x y ≤ r) →
      ∀ {ι : Type*} [Fintype ι],∀ H : ι → Arc ℂ,∀ e : ℂ → X,
      (∀ x : X,Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) →
      (∀ x : X,(T.filter (fun y=>dist x y<(L+3)*r)).card≤kr) ∧
      (∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*r}≤kc) := by
  classical
  obtain ⟨kr,hkr⟩:=CannonPacking.exists_overlap_bound Q C (L+3) 1 hpack hC (by linarith) zero_lt_one
  obtain ⟨B,hB⟩:=CannonIncidence.uniform_larger_trace Q C (L+3) hpack hC (by linarith)
  refine ⟨kr,2*(B*N),?_⟩
  intro r M hr hM hscale T hsep hcov ι _ H e hN
  constructor
  · intro x
    apply (Finset.card_le_card (show T.filter (fun y=>dist x y<(L+3)*r)⊆
      T.filter (fun y=>dist x y≤(L+3)*r) from fun y hy=>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2.le⟩)).trans
    apply hkr id T x r hr
    · rw [max_eq_left (by linarith : (1:ℝ)≤L+3)]
      nlinarith
    · simpa only [id_eq,one_mul] using hsep
  · intro x
    have htrace (center : X) (radius : ℝ) :
        traceCard (fun i=>range (fun t:I=>e (H i t))) (ball center radius)=
          Nat.card {i : ι | ∃ t:I,dist (e (H i t)) center < radius} := by
      have heq : {i : ι | (range (fun t:I=>e (H i t))∩ball center radius).Nonempty}=
          {i : ι | ∃ t:I,dist (e (H i t)) center < radius} := by
        ext index
        constructor
        · rintro ⟨point,⟨parameter,rfl⟩,hpoint⟩
          exact ⟨parameter,hpoint⟩
        · rintro ⟨parameter,hparameter⟩
          exact ⟨e (H index parameter),mem_range_self parameter,hparameter⟩
      simp only [traceCard,←heq,Nat.card_eq_fintype_card,Fintype.card_subtype,Set.mem_ofPred_eq]
    have hb:=hB r M hr hM (by linarith) T hsep hcov (fun i=>range (fun t:I=>e (H i t))) N
      (by
        intro center
        rw [htrace]
        exact hN center) x
    have hb' : Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<(L+3)*r}≤B*N := by
      simpa only [htrace] using hb
    exact (vertex_near_card_le H e x ((L+3)*r)).trans (Nat.mul_le_mul_left 2 hb')
end CannonCarrierCharging

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_BoundaryFiniteSphereRealizations
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence
open scoped OnePoint

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
attribute [local instance] Classical.propDecidable
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_finite_sphere_realizations (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ,1≤M ∧ 1≤L ∧ 0 < r₀ ∧ ∃ N : ℕ, ∃ c : ℝ,0 < c ∧ c≤1 ∧ ∃ kr kc : ℕ,
    ∀ r : ℝ,0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T,∀ y∈T,x≠y → r≤dist x y) →
      (∀ x : Boundary D,∃ y∈T,dist x y ≤ r) →
      ∀ p : Boundary D,p∉T →
      ∃ e : ℂ → Boundary D,IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (_ : Nonempty κ) (H : κ → Arc ℂ),
        Pairwise (fun i j=>Compatible (H i) (H j)) ∧
        ∃ Q : Finset (ℂ × ℂ),(∀ i,range (H i)⊆⋃q∈Q,segment ℝ q.1 q.2) ∧
        (T:Set (Boundary D))⊆e '' (⋃ i,range (H i)) ∧
        (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
        (∀ i,∀ t s : I,dist (e (H i t)) (e (H i s))≤M*r) ∧
        (∀ d,∀ z∈closure (face H d),∀ w∈closure (face H d),dist (e z) (e w)≤L*r) ∧
        (∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y≤L*r) ∧
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ x : Boundary D,(T.filter (fun y=>dist x y<(L+3)*r)).card≤kr) ∧
        (∀ x : Boundary D,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*r}≤kc) ∧
        (∀ v : ℂ,Nat.card {i : κ | v∈range (H i)}≤N) ∧
        (∀ d : Faces H,(faceVertices H d).card=3) ∧
        ∃ _ : Fintype (Faces H),∃ out : Faces H,
          (∀ d,d≠out → IsCompact (closure (face H d))) ∧
          ∃ B : DevelopedFaces H out, ∃ z : ℂ → ℂ,
            (∀ d,d≠out → ∀ q∈faceVertices H d,z q=B.chart d q) ∧
            (∀ i,dist (z (H i 0)) (z (H i 1))=B.radius (H i 0)+B.radius (H i 1)) ∧
            (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → B.radius u+B.radius v≤dist (z u) (z v)) ∧
            (∀ j,∀ u v,Spans (H j) u v → c*B.radius u≤B.radius v ∧ c*B.radius v≤B.radius u) ∧
            (∀ d,∀ v∈faceVertices H d,faceHull H z d⊆closedBall (z v) ((1+c⁻¹)*B.radius v)) ∧
            ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
              (∀ x∈frontier (faceHull H z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
              J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))=
                (((↑) '' interior (faceHull H z out) : Set (OnePoint ℂ)))ᶜ ∧
              ∃ f : C(Boundary D,OnePoint ℂ),Function.Surjective f ∧
                (∀ d : Faces H,d≠out → MapsTo f (compactifiedFace H e d) ((↑) '' faceHull H z d)) ∧
                MapsTo f (compactifiedFace H e out)
                  (J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))) ∧
                (∀ i t,f (e (H i t))=((Path.segment (z (H i 0)) (z (H i 1)) t:ℂ):OnePoint ℂ)) ∧
                (∀ x y : Boundary D,f x=f y → dist x y≤2*(L*r)) ∧
                (∀ S : Set (OnePoint ℂ),IsPreconnected S →
                  IsPreconnected (⋃ (d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),
                    compactifiedFace H e d.val)) ∧
                (∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
                  ⋃ (d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),
                    compactifiedFace H e d.val) ∧
                (∀ a : Fin 3 → Boundary D,(∀ i j,i≠j → 2*(L*r)<dist (a i) (a j)) →
                  ∃ N : OnePoint ℂ≃ₜOnePoint ℂ,N∈CannonMobius.biholomorphic ∧
                    ∃ g : C(Boundary D,OnePoint ℂ),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
                      (∀ i,g (a i)=CannonMobius.std i) ∧
                      (∀ x y,g x=g y → dist x y≤2*(L*r))) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,hgraph⟩ := boundary_uniform_circle_packing D hδ φ
  obtain ⟨c,hc,hc1,hcgraph⟩ := exists_global_radius_constant N
  obtain ⟨Q₀,C,_hQ₀,hC,hpoly⟩:=relative_polynomial_packing D hδ
  have hpolypack : CannonPacking.PolynomialPacking (X:=Boundary D) Q₀ C:=hpoly
  obtain ⟨kr,kc,hcharge⟩:=CannonCarrierCharging.uniform_original_charging_counts Q₀ C L hpolypack hC.le hL N
  have hL4 : 0<L+4 := by linarith
  refine ⟨M,L,min r₀ ((L+4)⁻¹),hM,hL,lt_min hr₀ (inv_pos.mpr hL4),N,c,hc,hc1,kr,kc,?_⟩
  intro r hr hrs T hsep hcover p hp
  have hrs₀ : r ≤ r₀:=hrs.trans (min_le_left _ _)
  have hscale : (L+4)*r≤1 := by
    have hh:=mul_le_mul_of_nonneg_left (hrs.trans (min_le_right _ _)) hL4.le
    simpa only [mul_inv_cancel₀ hL4.ne'] using hh
  obtain ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,hdeg,htri,hfaces,hpack⟩ :=
    hgraph r hr hrs₀ T hsep hcover p hp
  let _ : Fintype κ := hκ
  let _ : DecidableEq κ := hκd
  let _ : Nonempty κ := hκn
  let _ : Fintype (Faces H) := hfaces
  obtain ⟨hrow,hcol⟩:=hcharge r M hr hM hscale T hsep hcover H e hN
  obtain ⟨out,hout⟩:=outer_face_compact_others H
  obtain ⟨B,-⟩:=hpack out
  obtain ⟨z,hz,hlen,hdis,J,hJ,hJI,f,hf,hfin,hfout,hfedge⟩:=B.spherical_realization hH Q hQ hK htri hout
  obtain ⟨O⟩:=facialCycle_exists H hH Q hQ hK out (htri out)
  have hring : ∀ j u v,Spans (H j) u v → c*B.radius u≤B.radius v ∧ c*B.radius v≤B.radius u := by
    intro j u v huv
    exact ⟨hcgraph H out B hH Q hQ hK z hz hlen hdis O u v j huv.vertex_left (hdeg u) huv,
      hcgraph H out B hH Q hQ hK z hz hlen hdis O v u j huv.vertex_right (hdeg v) huv.symm⟩
  let E : OnePoint ℂ≃ₜBoundary D:=OnePoint.equivOfIsEmbeddingOfRangeEq p e he.isEmbedding heR
  let g : C(Boundary D,OnePoint ℂ):=f.comp ⟨E.symm,E.symm.continuous⟩
  have hge (x : ℂ) : g (e x)=f (x:OnePoint ℂ) := by
    change f (E.symm (E (x:OnePoint ℂ)))=f (x:OnePoint ℂ)
    rw [E.symm_apply_apply]
  have hfin' (d : Faces H) (hd : d≠out) :
      MapsTo g (compactifiedFace H e d) ((↑) '' faceHull H z d) := by
    apply compactifiedFace_mapsTo H e g d _
    · exact ((((faceVertices H d).finite_toSet.image z).isCompact_convexHull ℝ).image
        OnePoint.continuous_coe).isClosed
    · intro x hx
      simpa only [Function.comp_apply,hge] using hfin d hd hx
  have hfout' : MapsTo g (compactifiedFace H e out)
      (J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))) := by
    apply compactifiedFace_mapsTo H e g out _
    · exact (((((faceVertices H out).finite_toSet.image z).isCompact_convexHull ℝ).image
        OnePoint.continuous_coe).image J.continuous).isClosed
    · intro x hx
      simpa only [Function.comp_apply,hge] using hfout hx
  have hmaps (d : Faces H) : MapsTo g (compactifiedFace H e d) (sphereTile H z out d) := by
    by_cases hd : d=out
    · subst d
      simpa [sphereTile,hJI] using hfout'
    · simpa only [sphereTile,ite_eq_right hd] using hfin' d hd
  have hdiam := fun d=>compactifiedFace_dist_bound H e d (L*r) (hD d)
  obtain ⟨hcycles,hinter,hfill⟩:=B.hull_geometry hH Q hQ hK htri z hz
  have hdense : DenseRange e := by
    have hd : DenseRange (E ∘ ((↑):ℂ → OnePoint ℂ)) :=
      E.surjective.denseRange.comp OnePoint.denseRange_coe E.continuous
    exact hd
  have hcorner (d : Faces H) : (faceVertices H d).Nonempty := by
    rw [←Finset.card_pos,htri d]
    norm_num
  have hsourcecover := (compactified_face_interiors_cover H hH Q hQ hcorner e he p heR hdense).1
  have hfiber := sphere_realization_fiber_bound e he.continuous g hsourcecover z B.radius B.radius_pos
      hlen hdis hcycles hinter hfill hmaps (L*r) hdiam
  refine ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hdiam,hN,hrow,hcol,hdeg,htri,hfaces,out,hout,
    B,z,hz,hlen,hdis,hring,?_,J,hJ,hJI,g,hf.comp E.symm.surjective,hfin',hfout',?_,hfiber,?_,?_,?_⟩
  · intro d v hv
    obtain ⟨C⟩:=facialCycle_exists H hH Q hQ hK d (htri d)
    exact C.hull_radius_bound z B.radius B.radius_pos c hc hlen hring hv
  · intro i t
    rw [hge,hfedge]
  · intro S hS
    exact sphere_carrier_preconnected e he.continuous z B.radius B.radius_pos hlen hdis
      hcycles hinter hfill S hS
  · exact CannonFiniteCarrier.preimage_subset_carrier _ _ g hsourcecover hmaps
  · intro a ha
    exact CannonMobius.normalize_finite_realization g (hf.comp E.symm.surjective) (2*(L*r)) hfiber a ha
end CannonRelease

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_NormalizePackingCenters
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

theorem normalize_packing_centers {ν : Type*}
    (z : ν → ℂ) (r : ν → ℝ) (hr : ∀ v,0 < r v)
    (hsep : ∀ u v,u≠v → r u+r v≤dist (z u) (z v))
    (b : Fin 3 → ν) (hb : Function.Injective b) :
    ∃ N : Sphere ≃ₜ Sphere,N∈biholomorphic ∧
      (∀ i,N ((z (b i):ℂ):Sphere)=std i) ∧
      (∀ v,IsOpen (N '' ((↑) '' ball (z v) (r v) : Set Sphere))) ∧
      Pairwise (fun u v=>Disjoint (N '' ((↑) '' ball (z u) (r u) : Set Sphere))
        (N '' ((↑) '' ball (z v) (r v) : Set Sphere))) ∧
      (∀ v,∃ i j : Fin 3,i≠j ∧
        std i∉N '' ((↑) '' ball (z v) (r v) : Set Sphere) ∧
        std j∉N '' ((↑) '' ball (z v) (r v) : Set Sphere)) := by
  have hz : Function.Injective z := by
    intro u v huv
    by_contra hne
    have hh:=hsep u v hne
    rw [huv,dist_self] at hh
    linarith [hr u,hr v]
  let t : Triple:=⟨fun i=>(z (b i):Sphere),OnePoint.coe_injective.comp (hz.comp hb)⟩
  obtain ⟨M,hM,hMt⟩:=exists_triple_normalizer t
  let N : Sphere ≃ₜ Sphere:=M.symm
  have hN (i : Fin 3) : N (z (b i):Sphere)=std i := by
    have H : M (std i)=(z (b i):Sphere):=congrArg (fun t : Triple=>t.val i) hMt
    dsimp only [N]
    rw [←H,M.symm_apply_apply]
  have hout {v : ν} {i : Fin 3} (hi : b i≠v) :
      std i∉N '' ((↑) '' ball (z v) (r v) : Set Sphere) := by
    rintro ⟨_,⟨w,hw,rfl⟩,hew⟩
    have hcoe : (w:Sphere)=(z (b i):Sphere):=N.injective (hew.trans (hN i).symm)
    have hew : w=z (b i):=OnePoint.coe_injective hcoe
    rw [hew] at hw
    have hh:=hsep (b i) v hi
    have hh':=mem_ball.mp hw
    linarith [hr (b i)]
  refine ⟨N,biholomorphic.inv_mem hM,hN,?_,?_,?_⟩
  · intro v
    exact N.isOpenMap _ (OnePoint.isOpenMap_coe _ isOpen_ball)
  · intro u v huv
    apply disjoint_left.mpr
    rintro q ⟨_,⟨w,hwu,rfl⟩,hwq⟩ ⟨_,⟨w',hwv,rfl⟩,hwq'⟩
    have heq : w=w' := OnePoint.coe_injective (N.injective (hwq.trans hwq'.symm))
    subst w'
    have h1:=mem_ball.mp hwu
    have h2:=mem_ball.mp hwv
    have ht:=dist_triangle (z u) w (z v)
    rw [dist_comm (z u) w] at ht
    have hh:=hsep u v huv
    linarith
  · intro v
    have hx : ∃ i j : Fin 3,i≠j ∧ b i≠v ∧ b j≠v := by
      by_cases h0 : b 0=v
      · refine ⟨1,2,by decide,?_,?_⟩ <;> intro h
        · have hh:=hb (h.trans h0.symm)
          exact (by decide : (1:Fin 3)≠0) hh
        · have hh:=hb (h.trans h0.symm)
          exact (by decide : (2:Fin 3)≠0) hh
      · by_cases h1 : b 1=v
        · refine ⟨0,2,by decide,h0,?_⟩
          intro h
          have hh:=hb (h.trans h1.symm)
          exact (by decide : (2:Fin 3)≠1) hh
        · exact ⟨0,1,by decide,h0,h1⟩
    obtain ⟨i,j,hij,hi,hj⟩:=hx
    exact ⟨i,j,hij,hout hi,hout hj⟩
end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_GraphVerticesDenseOriginal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval

variable {X ι : Type*} [MetricSpace X] [Fintype ι]
omit [Fintype ι] in
lemma graph_vertices_dense_from_original_net (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (r M : ℝ)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y ≤ r)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*r) :
    ∀ x : X,∃ v : GraphVertices H,dist x (e v.val)≤(1+M)*r := by
  intro x
  obtain ⟨y,hy,hxy⟩:=hcover x
  obtain ⟨z,hz,hez⟩:=hT hy
  obtain ⟨i,t,rfl⟩:=mem_iUnion.mp hz
  refine ⟨⟨H i 0,⟨i,Or.inl rfl⟩⟩,?_⟩
  have hh:=dist_triangle x (e (H i t)) (e (H i 0))
  have ht:=hE i t 0
  rw [hez] at hh ht
  change dist x (e (H i 0)) ≤ (1+M)*r
  nlinarith

omit [Fintype ι] in
lemma separated_graph_marks (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (r M s0 : ℝ) (a : Fin 3 → X)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y ≤ r)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*r)
    (ha : ∀ i j,i≠j → s0≤dist (a i) (a j)) (hs0 : 2*((1+M)*r) < s0) :
    ∃ b : Fin 3 → GraphVertices H,Function.Injective b ∧
      ∀ i,dist (a i) (e (b i).val)≤(1+M)*r := by
  choose b hb using fun i=>graph_vertices_dense_from_original_net H e T r M hT hcover hE (a i)
  refine ⟨b,?_,hb⟩
  intro i j hij
  by_contra hne
  have hd:=dist_triangle (a i) (e (b i).val) (a j)
  have hj:=hb j
  rw [←hij,dist_comm (a j) (e (b i).val)] at hj
  have hi:=hb i
  have hs:=ha i j hne
  linarith
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RealizationVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval
open scoped OnePoint

variable {X ι : Type*} [MetricSpace X] [Fintype ι]
omit [MetricSpace X] [Fintype ι] in
lemma realization_at_vertex (H : ι → Arc ℂ) (e : ℂ → X)
    (z : ℂ → ℂ) (f : X → OnePoint ℂ)
    (hfedge : ∀ i t,f (e (H i t))=((Path.segment (z (H i 0))
      (z (H i 1)) t:ℂ):OnePoint ℂ)) (v : GraphVertices H) :
    f (e v.val)=(z v.val:OnePoint ℂ) := by
  obtain ⟨i,hi|hi⟩:=v.property
  · rw [←hi,hfedge]
    simp
  · rw [←hi,hfedge]
    simp

omit [Fintype ι] in
theorem packing_center_normalized_realization (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (mesh M sep : ℝ) (a : Fin 3 → X)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y≤ mesh)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*mesh)
    (ha : ∀ i j,i≠j → sep≤dist (a i) (a j)) (hsep : 2*((1+M)*mesh) < sep)
    (z : ℂ → ℂ) (rad : ℂ → ℝ) (hr : ∀ v,Vertex H v → 0 < rad v)
    (hdis : ∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → rad u+rad v≤dist (z u) (z v))
    (f : C(X,OnePoint ℂ)) (hfs : Function.Surjective f)
    (hfedge : ∀ i t,f (e (H i t))=((Path.segment (z (H i 0))
      (z (H i 1)) t:ℂ):OnePoint ℂ)) :
    ∃ b : Fin 3 → GraphVertices H,Function.Injective b ∧
      (∀ i,dist (a i) (e (b i).val)≤(1+M)*mesh) ∧
      ∃ N : OnePoint ℂ≃ₜOnePoint ℂ,N∈CannonMobius.biholomorphic ∧
        ∃ g : C(X,OnePoint ℂ),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
          (∀ i,g (e (b i).val)=CannonMobius.std i) ∧
          (∀ v : GraphVertices H,IsOpen
            (N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)))) ∧
          Pairwise (fun u v : GraphVertices H=>Disjoint
            (N '' ((↑) '' ball (z u.val) (rad u.val) : Set (OnePoint ℂ)))
            (N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)))) ∧
          (∀ v : GraphVertices H,∃ i j : Fin 3,i≠j ∧
            CannonMobius.std i∉N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)) ∧
            CannonMobius.std j∉N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ))) := by
  obtain ⟨b,hb,hba⟩:=separated_graph_marks H e T mesh M sep a hT hcover hE ha hsep
  obtain ⟨N,hN,hNb,hNo,hNd,hNmarks⟩:=CannonMobius.normalize_packing_centers
    (fun v : GraphVertices H=>z v.val) (fun v=>rad v.val) (fun v=>hr v.val v.property)
    (fun u v huv=>hdis u.val u.property v.val v.property (fun h=>huv (Subtype.ext h))) b hb
  let g : C(X,OnePoint ℂ):=⟨fun x=>N (f x),N.continuous.comp f.continuous⟩
  refine ⟨b,hb,hba,N,hN,g,fun x=>rfl,N.surjective.comp hfs,?_,hNo,hNd,hNmarks⟩
  intro i
  change N (f (e (b i).val))=CannonMobius.std i
  rw [realization_at_vertex H e z f hfedge]
  exact hNb i
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_ThreeSeparation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonFiniteNormalization
open Set Metric Topology CannonMobius
open scoped OnePoint

lemma three_separation {X : Type*} [MetricSpace X] (v : Fin 3 → X)
    (hv : Function.Injective v) :
    ∃ s : ℝ,0 < s ∧ ∀ i j,i≠j → s≤dist (v i) (v j) := by
  let s:=min (dist (v 0) (v 1)) (min (dist (v 0) (v 2)) (dist (v 1) (v 2)))
  have hpos (i j : Fin 3) (hij : i≠j) : 0<dist (v i) (v j):=dist_pos.mpr (hv.ne hij)
  refine ⟨s,lt_min (hpos 0 1 (by decide)) (lt_min (hpos 0 2 (by decide)) (hpos 1 2 (by decide))),?_⟩
  have h01 : s≤dist (v 0) (v 1):=min_le_left _ _
  have h02 : s≤dist (v 0) (v 2):=(min_le_right _ _).trans (min_le_left _ _)
  have h12 : s≤dist (v 1) (v 2):=(min_le_right _ _).trans (min_le_right _ _)
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact h01
  · exact h02
  · rwa [dist_comm]
  · exact h12
  · rwa [dist_comm]
  · rwa [dist_comm]

end CannonFiniteNormalization

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_PreimageCarrierPostcompose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonCarrierCharging
open Set Metric Topology CannonMobius CannonUniformization
open scoped OnePoint

lemma preimage_carrier_postcompose {X Y Z κ : Type*}
    (A : κ → Set X) (K : κ → Set Y) (f : X → Y) (N : Y → Z)
    (hpre : ∀ S : Set Y,f ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) :
    ∀ S : Set Z,(N ∘ f) ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩N '' K d).Nonempty}),A d.val := by
  intro S x hx
  obtain ⟨d,hd⟩:=mem_iUnion.mp (hpre (N ⁻¹' S) hx)
  obtain ⟨y,hy,hyk⟩:=d.property
  exact mem_iUnion.mpr ⟨⟨d.val,⟨N y,hy,⟨y,hyk,rfl⟩⟩⟩,hd⟩

end CannonCarrierCharging

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryPackingRelativeTests
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Topology CannonGraph CannonVisual CannonMobius CannonCells CannonUniformization
open CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence CannonFiniteNormalization
open CannonCarrierCharging
open scoped OnePoint

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_packing_relative_tests_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L LI σ s r₀ Z : ℝ,1 ≤ L ∧ 1 ≤ LI ∧ 0<σ ∧ σ ≤ 1 ∧ 0 < s ∧ 0 < r₀ ∧ 0 ≤ Z ∧
    ∃ V : ℝ → ℝ,(∀ ε,0<ε → 0<V ε) ∧
    ∀ mesh : ℝ,0 < mesh → mesh ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T,∀ y∈T,x≠y → mesh ≤ dist x y) →
      (∀ x : Boundary D,∃ y∈T,dist x y ≤ mesh) →
    ∃ g : C(Boundary D,Sphere),Function.Surjective g ∧
      (∀ x y,g x=g y → dist x y ≤ 2*(L*mesh)) ∧
      ∀ (o a b : Boundary D) (r R ε : ℝ),0 < r → 0<R → R ≤ s →
        dist o a ≤ r → R ≤ dist o b → 0<dist (g o) (g b) → 0<ε →
        ε*dist (g o) (g b)<dist (g o) (g a) →
      V ε ≤ Z*modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R)) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo:=CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D):=φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,c,hc,hc1,kr,kc,hprod⟩:=boundary_finite_sphere_realizations D hδ φ
  obtain ⟨LI,hLI,hi⟩:=boundary_controlled_paths D hδ φ
  obtain ⟨σ,hσ,hσ1,ho⟩:=boundary_outside_paths D hδ φ
  have hinner : ∀ o u v : Boundary D,∀ r : ℝ,0 < r → dist o u ≤ r → dist o v ≤ r →
      JoinedIn (closedBall o (LI*r)) u v := by
    intro o u v r hr hu hv
    exact (hi o u v r hr hu hv).mono (fun x hx=>by
      change dist o x<LI*r at hx
      rw [mem_closedBall,dist_comm]
      exact hx.le)
  have houter : ∀ o u v : Boundary D,∀ r : ℝ,0 < r → r ≤ dist o u → r ≤ dist o v →
      JoinedIn (ball o (σ*r))ᶜ u v := by
    intro o u v r hr hu hv
    exact (ho o u v r hr hu hv).mono (fun x hx=>by
      change σ*r<dist o x at hx
      rw [mem_compl_iff,mem_ball,dist_comm]
      exact not_lt.mpr hx.le)
  obtain ⟨V,hV,hcost⟩:=packing_relative_modulus_cost LI σ hinner houter
  let marks : Fin 3 → Boundary D:=fun i=>φ.symm (roundChart (std i))
  have hmarks : Function.Injective marks:=φ.symm.injective.comp (roundChart.injective.comp std_injective)
  obtain ⟨sep,hsep,hsepmarks⟩:=three_separation marks hmarks
  have hMp : 0<1+M:=by linarith
  let small:=min r₀ (sep/(8*(1+M)))
  have hsmall : 0 < small:=lt_min hr₀ (div_pos hsep (by positivity))
  let Z : ℝ:=324*(26*(N:ℝ)+1)*(kr:ℝ)*(N*kc:ℕ)
  refine ⟨L,LI,σ,sep/4,small,Z,hL,hLI,hσ,hσ1,by positivity,hsmall,by dsimp [Z]; positivity,V,hV,?_⟩
  intro mesh hm hms T hTsep hcover
  have hmesh₀ : mesh ≤ r₀:=hms.trans (min_le_left _ _)
  have hsmallmesh : (1+M)*mesh ≤ sep/8 := by
    have hh:=(le_div_iff₀ (show 0<8*(1+M) by positivity)).mp (hms.trans (min_le_right _ _))
    nlinarith
  let : Infinite (Boundary D):=Infinite.of_injective
    (fun z : ℂ=>φ.symm (roundChart (z:Sphere)))
    (φ.symm.injective.comp (roundChart.injective.comp OnePoint.coe_injective))
  obtain ⟨p,hp⟩:=T.exists_notMem
  obtain ⟨e,he,heR,ι,hι,hιd,hιn,H,hH,Q,hQ,hT,hK,hE,hD,hdiam,hN,hrow,hcol,hdeg,htri,hfaces,
    out,hout,B,z,hz,hlen,hdis,hring,hull,J,hJ,hJI,f,hfs,hfin,hfout,hfedge,hfiber,hconn,hpre,hnorm⟩:=
    hprod mesh hm hmesh₀ T hTsep hcover p hp
  let _ : Fintype ι:=hι
  let _ : DecidableEq ι:=hιd
  let _ : Nonempty ι:=hιn
  let _ : Fintype (Faces H):=hfaces
  obtain ⟨v,hv,hva,Norm,hNorm,g,hg,hgs,hmark,rest⟩:=packing_center_normalized_realization
    H e T mesh M sep marks hT hcover hE hsepmarks (by linarith) z B.radius
    (fun v _=>B.radius_pos v) hdis f hfs hfedge
  have hmarksep : ∀ i j,i≠j → sep/2 ≤ dist (e (v i).val) (e (v j).val) := by
    intro i j hij
    have hs:=hsepmarks i j hij
    have h1:=hva i
    have h2:=hva j
    have ht:=dist_triangle (marks i) (e (v i).val) (marks j)
    have ht':=dist_triangle (e (v i).val) (e (v j).val) (marks j)
    rw [dist_comm (e (v j).val) (marks j)] at ht'
    linarith
  have hNm (i : Fin 3) : Norm (z (v i).val)=std i := by
    rw [←realization_at_vertex H e z f hfedge (v i),←hg]
    exact hmark i
  have hpre' : ∀ S : Set Sphere,g ⁻¹' S ⊆
      ⋃(d : {d : Faces H // (S∩Norm '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val := by
    intro S x hx
    have hh:=preimage_carrier_postcompose (compactifiedFace H e) (sphereTile H z out) f Norm hpre S
    apply hh
    change Norm (f x)∈S
    rw [←hg]
    exact hx
  obtain ⟨hcycles,hinter,hfill⟩:=B.hull_geometry hH Q hQ hK htri z hz
  refine ⟨g,hgs,?_,?_⟩
  · intro x y hxy
    exact hfiber x y (Norm.injective (by simpa only [hg] using hxy))
  · intro o a b r R ε hr hR hRs ha hb hgb hε hdiff
    exact hcost H hH Q hQ hK N hdeg e he.continuous z B.radius B.radius_pos hlen hdis hcycles
      out hinter hfill Norm hNorm T mesh L hm hcover hdiam kr kc hrow hcol hconn g hpre'
      (fun i=>(v i).val) (sep/2) (by positivity) (fun i=>(v i).property) hmarksep hmark hNm
      o a b r R ε hr hR (by linarith) ha hb hgb hε hdiff
end CannonRelease

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.CannonRelease.boundary_packing_relative_tests_oai.{u} := @OAI.CannonRelease.boundary_packing_relative_tests_oai.{u}
