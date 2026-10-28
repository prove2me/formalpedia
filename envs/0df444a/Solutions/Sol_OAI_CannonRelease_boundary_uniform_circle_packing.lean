-- Prove2me | solution 1 for OAI.CannonRelease.boundary_uniform_circle_packing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:12:47.514023+00:00
-- url     : https://prove2.me/submissions/e1ed0af1-8cb8-4f36-a3c1-b72176f2b4db

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_circle_packing
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_intrinsic_developed_faces
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_proper_facial_bound
import Theorems.Thm_OAI_CannonPlanarEuler_triangular_counts
import Theorems.Thm_OAI_CannonRelease_boundary_uniform_controlled_faces

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

local instance instSetoidBasedRay_2_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FiniteSupport
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
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonEmbeddedArc
namespace Arc
variable {X : Type*} [TopologicalSpace X]
lemma trans_injective {x y z : X} (a : Path x y) (b : Path y z)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmeet : ∀ s t, a s=b t → s=1 ∧ t=0) : Function.Injective (a.trans b) := by
  intro s t he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have h := congrArg Subtype.val (ha he)
    apply Subtype.ext
    dsimp at h
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he.symm
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · have h := congrArg Subtype.val (hb he)
    apply Subtype.ext
    dsimp at h
    linarith

theorem extend_arc [T2Space X] (a b : Arc X) (hab : a 1=b 0)
    (hy : b 1∉range a) :
    ∃ c : Arc X, c 0=a 0 ∧ c 1=b 1 ∧ range c⊆range a∪range b := by
  have hc : IsCompact (b ⁻¹' range a) :=
    (a.compact_range.isClosed.preimage b.continuous).isCompact
  have hn : (b ⁻¹' range a).Nonempty := ⟨0,⟨1,hab⟩⟩
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hn
  obtain ⟨u,hu⟩ := hv.1
  have hv₁ : v≠1 := fun h => hy (h ▸ hv.1)
  let d := b.subarc v 1 hv₁
  have hd₀ : d 0=a u := (subarc_zero ..).trans hu.symm
  have hd₁ : d 1=b 1 := subarc_one ..
  have hds : range d⊆range b := subarc_range_subset ..
  have hmeet : ∀ s t, a s=d t → s=u ∧ t=0 := by
    intro s t he
    have hin : Icc.convexComb v 1 t∈b ⁻¹' range a := ⟨s,he⟩
    have hle := hv.2 hin
    have hvlt : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun h => hv₁ (Subtype.ext h))
    have hle' : (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v := by
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v at hle
      exact hle
    have ht : t=0 := by
      apply Subtype.ext
      dsimp
      nlinarith [t.property.1]
    refine ⟨?_,ht⟩
    apply a.injective
    simpa only [ht,hd₀] using he
  by_cases hu₀ : u=0
  · refine ⟨d,by simpa only [hu₀] using hd₀,hd₁,hds.trans subset_union_right⟩
  · let c := a.subarc 0 u (Ne.symm hu₀)
    let p : Path (a 0) (a u) := ⟨c.map,subarc_zero ..,subarc_one ..⟩
    let q : Path (a u) (b 1) := ⟨d.map,hd₀,hd₁⟩
    have hpq : ∀ s t, p s=q t → s=1 ∧ t=0 := by
      intro s t he
      obtain ⟨hs,ht⟩ := hmeet (Icc.convexComb 0 u s) t he
      refine ⟨?_,ht⟩
      have huc : (u:ℝ)≠0 := fun h => hu₀ (Subtype.ext h)
      have hh := congrArg Subtype.val hs
      simp only [Icc.coe_convexComb] at hh
      apply Subtype.ext
      dsimp at hh ⊢
      have heq : ((s:ℝ)-1)*(u:ℝ)=0 := by nlinarith [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right huc)
    refine ⟨⟨(p.trans q).toContinuousMap,trans_injective p q c.injective d.injective hpq⟩,
      (p.trans q).source,(p.trans q).target,?_⟩
    change range (p.trans q)⊆range a∪range b
    rw [Path.trans_range]
    exact union_subset_union (subarc_range_subset a 0 u (Ne.symm hu₀)) hds
end Arc
end CannonEmbeddedArc

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma FiniteSupport.mono {S T : Set E} (hT : FiniteSupport T) (hST : S⊆T) :
    FiniteSupport S := by
  obtain ⟨P,hP⟩ := hT
  exact ⟨P,hST.trans hP⟩
lemma FiniteSupport.segment (x y : E) : FiniteSupport (segment ℝ x y) := by
  classical
  exact ⟨{(x,y)},by simp⟩
lemma FiniteSupport.union {S T : Set E} (hS : FiniteSupport S) (hT : FiniteSupport T) :
    FiniteSupport (S∪T) := by
  classical
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P∪Q,?_⟩
  intro x hx
  rcases hx with hx|hx
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hP hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_left Q hp,hx⟩
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hQ hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_right P hp,hx⟩

lemma polyJoined_of_open_preconnected {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y : E} (hx : x∈U) (hy : y∈U) : PolyJoined U x y := by
  let V := {z | z∈U ∧ PolyJoined U x z}
  let W := {z | z∈U ∧ ¬PolyJoined U x z}
  have hstep (z : E) (hz : z∈U) :
      ∃ ε : ℝ, 0<ε ∧ ∀ w∈ball z ε, segment ℝ z w⊆U := by
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨ε,hε,fun w hw => ((convex_ball z ε).segment_subset (mem_ball_self hε) hw).trans hεU⟩
  have hV : IsOpen V := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),hz.2.tail (hs w hw)⟩⟩
  have hW : IsOpen W := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),?_⟩⟩
    intro hj
    apply hz.2 (hj.tail ?_)
    simpa only [segment_symm] using hs w hw
  have hs : U⊆V∪W := by intro z hz; by_cases hj : PolyJoined U x z <;> simp_all [V,W]
  have hd : Disjoint V W := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz'.2 hz.2
  have hv : x∈U∩V := ⟨hx,hx,.refl⟩
  exact (hc.subset_left_of_subset_union hV hW hd hs ⟨x,hv⟩ hy).2

theorem polyJoined_arc {U : Set E} {x y : E} (h : PolyJoined U x y) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
  have hh : x=y ∨ ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
    clear hne
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      by_cases hxz : x=z
      · exact Or.inl hxz
      · apply Or.inr
        rcases ih with rfl|⟨a,ha₀,ha₁,haU,haS⟩
        · let b : Arc E := ⟨(Path.segment x z).toContinuousMap,Path.segment_injective_of_ne hxz⟩
          refine ⟨b,(Path.segment x z).source,(Path.segment x z).target,?_,?_⟩
          · change range (Path.segment x z)⊆U
            rwa [Path.range_segment]
          · change FiniteSupport (range (Path.segment x z))
            rw [Path.range_segment]
            exact FiniteSupport.segment x z
        · by_cases hz : z∈range a
          · obtain ⟨t,ht⟩ := hz
            have ht₀ : (0:I)≠t := fun h => hxz (ha₀.symm.trans ((congrArg a h).trans ht))
            refine ⟨a.subarc 0 t ht₀,(subarc_zero ..).trans ha₀,(subarc_one ..).trans ht,
              (subarc_range_subset ..).trans haU,haS.mono (subarc_range_subset ..)⟩
          · have hyz' : y≠z := fun h => hz ⟨1,ha₁.trans h⟩
            let b : Arc E := ⟨(Path.segment y z).toContinuousMap,Path.segment_injective_of_ne hyz'⟩
            have hb₀ : b 0=y := (Path.segment y z).source
            have hb₁ : b 1=z := (Path.segment y z).target
            have hbR : range b=segment ℝ y z := Path.range_segment y z
            obtain ⟨c,hc₀,hc₁,hcs⟩ := extend_arc a b (ha₁.trans hb₀.symm) (by simpa only [hb₁] using hz)
            refine ⟨c,hc₀.trans ha₀,hc₁.trans hb₁,hcs.trans (union_subset haU ?_),
              (haS.union ?_).mono hcs⟩
            · rwa [hbR]
            · rw [hbR]
              exact FiniteSupport.segment y z
  exact hh.resolve_left hne

end CannonPolygonal

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

local instance instSetoidBasedRay_27_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_29_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Consecutive
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

namespace CannonEmbeddedArc
open Set unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma intersectionCount_eq_card {ι : Type*} [Fintype ι] (E : ι → Arc X) (S : Set X) :
    intersectionCount E S = by classical exact (Finset.univ.filter
      (fun i => (range (E i) ∩ S).Nonempty)).card := by
  classical
  simp only [intersectionCount,Finset.sum_boole,Nat.cast_id]

end Arc
end CannonEmbeddedArc

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

local instance instSetoidBasedRay_31_r368cec_1 : Setoid (BasedRay D) := raySetoid D
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Lift
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

namespace CannonWinding

lemma lift_exp (f : C(I,Circle)) (t : I) : Circle.exp (lift f t)=f t :=
  congr_fun (Circle.isCoveringMap_exp.liftPath_lifts f _ _) t

lemma turn_eq_of_lift (f : C(I,Circle)) (g : C(I,ℝ))
    (hg : ∀ t, Circle.exp (g t)=f t) : turn f=g 1-g 0 := by
  have hconst : ∀ t t', g t-lift f t=g t'-lift f t' := by
    apply Circle.isCoveringMap_exp.const_of_comp (g.continuous.sub (lift f).continuous)
    intro t t'
    change Circle.exp (g t-lift f t)=Circle.exp (g t'-lift f t')
    simp only [Circle.exp_sub,hg,lift_exp,div_self']
  have h := hconst 1 0
  dsimp only [turn]
  linarith

lemma turn_homotopy (H : C(I×I,Circle)) (hH : ∀ s, H (s,0)=H (s,1)) :
    turn (H.comp ⟨fun t => (0,t),by fun_prop⟩)=
      turn (H.comp ⟨fun t => (1,t),by fun_prop⟩) := by
  let f := H.comp (⟨fun t => (0,t),by fun_prop⟩ : C(I,I×I))
  let g := lift f
  have h₀ (t : I) : H (0,t)=Circle.exp (g t) := (lift_exp f t).symm
  let L := Circle.isCoveringMap_exp.liftHomotopy H g h₀
  have hL (s t : I) : Circle.exp (L (s,t))=H (s,t) :=
    congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H g h₀) (s,t)
  have heq : ∀ s s', L (s,1)-L (s,0)=L (s',1)-L (s',0) := by
    apply Circle.isCoveringMap_exp.const_of_comp (by fun_prop)
    intro s s'
    simp only [Circle.exp_sub,hL,←hH,div_self']
  rw [turn_eq_of_lift (H.comp ⟨fun t => (0,t),by fun_prop⟩) (L.comp ⟨fun t => (0,t),by fun_prop⟩) (fun t => hL 0 t),
    turn_eq_of_lift (H.comp ⟨fun t => (1,t),by fun_prop⟩) (L.comp ⟨fun t => (1,t),by fun_prop⟩) (fun t => hL 1 t)]
  exact heq 0 1

end CannonWinding

namespace CannonWinding
variable {A : Type*} [TopologicalSpace A]

lemma winding_homotopy (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (z : ℂ) (hz : z∉range H) :
    winding (H.comp ⟨fun t => (0,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(0,t),ht⟩)=
    winding (H.comp ⟨fun t => (1,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(1,t),ht⟩) := by
  let K := direction (H-.const (I×I) z) (fun p hp => hz ⟨p,sub_eq_zero.mp hp⟩)
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,hclosed]
  exact turn_homotopy K hc

lemma winding_moving_point (f : C(I,ℂ)) (hf : f 0=f 1) (p : C(I,ℂ))
    (hp : ∀ s, p s∉range f) : winding f (p 0) (hp 0)=winding f (p 1) (hp 1) := by
  let H : C(I×I,ℂ) := ⟨fun z => f z.2-p z.1,by fun_prop⟩
  have hH (z : I×I) : H z≠0 := fun h => hp z.1 ⟨z.2,sub_eq_zero.mp h⟩
  let K := direction H hH
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,H,ContinuousMap.coe_mk,hf]
  exact turn_homotopy K hc

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_eq_of_homotopy (f g : C(I,ℂ)) (z : ℂ) (hf : z∉range f) (hg : z∉range g)
    (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (h₀ : ∀ t, H (0,t)=f t) (h₁ : ∀ t, H (1,t)=g t) (hz : z∉range H) :
    winding f z hf=winding g z hg := by
  have h₀' : H.comp ⟨fun t => (0,t),by fun_prop⟩=f := ContinuousMap.ext h₀
  have h₁' : H.comp ⟨fun t => (1,t),by fun_prop⟩=g := ContinuousMap.ext h₁
  simpa only [h₀',h₁'] using winding_homotopy H hclosed z hz

theorem winding_locally_constant (f : C(I,ℂ)) (hf : f 0=f 1) :
    IsLocallyConstant (fun z : ↥((range f)ᶜ) => winding f z.val z.property) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds z.property)
  refine ⟨Subtype.val ⁻¹' ball z.val ε,isOpen_ball.preimage continuous_subtype_val,
    mem_ball_self hε,?_⟩
  intro w hw
  have hp (s : I) : Path.segment z.val w.val s∉range f := by
    apply hball
    apply (convex_ball z.val ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]
    exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z.val w.val).toContinuousMap hp
  change winding f (Path.segment z.val w.val 0) _ =
    winding f (Path.segment z.val w.val 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

end CannonWinding

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

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma map_pullChart (e : X → Y) (he : IsEmbedding e) (a : Arc Y)
    (ha : range a⊆range e) (t : I) : e (pullChart e he a ha t)=a t := by
  exact congrArg Subtype.val (he.toHomeomorph.apply_symm_apply ⟨a t,ha (mem_range_self t)⟩)

lemma pullChart_range (e : X → Y) (he : IsEmbedding e) (a : Arc Y)
    (ha : range a⊆range e) : range (pullChart e he a ha)=e ⁻¹' range a := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,(map_pullChart e he a ha t).symm⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,he.injective ((map_pullChart e he a ha t).trans ht)⟩

lemma pullChart_compatible (e : X → Y) (he : IsEmbedding e) (a b : Arc Y)
    (ha : range a⊆range e) (hb : range b⊆range e) (hab : Compatible a b) :
    Compatible (pullChart e he a ha) (pullChart e he b hb) := by
  constructor
  · intro s t h
    apply hab.1 s t
    simpa only [map_pullChart] using congrArg e h
  · intro x hx y hy
    apply he.injective
    simp only [mem_inter_iff,pullChart_range,mem_preimage] at hx hy
    exact hab.2 hx hy

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_UnitCircle
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
namespace CannonCircleBoundary
open Set Topology Metric
open scoped OnePoint

lemma real_interval_bounded {S : Set ℝ} (hS : IsPreconnected S)
    {b c : ℝ} (hbc : b < c) (hb : b∈closure S\S) (hc : c∈closure S\S) :
    S⊆Icc b c := by
  intro z hz
  constructor
  · by_contra h
    have hzb : z<b := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hc.1) (Ioi b) (isOpen_Ioi.mem_nhds hbc)
    exact hb.2 (hS.ordConnected.out hz hwS ⟨hzb.le,hw.le⟩)
  · by_contra h
    have hcz : c<z := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hb.1) (Iio c) (isOpen_Iio.mem_nhds hbc)
    exact hc.2 (hS.ordConnected.out hwS hz ⟨hw.le,hcz.le⟩)

lemma onePoint_boundary_unique {S : Set (OnePoint ℝ)} (hS : IsPreconnected S)
    (hinf : (∞ : OnePoint ℝ)∈closure S\S) {b c : ℝ}
    (hb : (b : OnePoint ℝ)∈closure S\S) (hc : (c : OnePoint ℝ)∈closure S\S) : b=c := by
  let T : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' S
  have he : ((↑) : ℝ → OnePoint ℝ) '' T=S := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    obtain ⟨w,rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinf.2 (h ▸ hz))
    exact ⟨w,hz,rfl⟩
  have hT : IsPreconnected T := OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.mp (he ▸ hS)
  have hcl : closure T=((↑) : ℝ → OnePoint ℝ) ⁻¹' closure S := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image,he]
  have hbT : b∈closure T\T := ⟨by rw [hcl]; exact hb.1,hb.2⟩
  have hcT : c∈closure T\T := ⟨by rw [hcl]; exact hc.1,hc.2⟩
  by_contra hbc
  have hbounded : ∃ l u : ℝ,T⊆Icc l u := by
    rcases lt_or_gt_of_ne hbc with h|h
    · exact ⟨b,c,real_interval_bounded hT h hbT hcT⟩
    · exact ⟨c,b,real_interval_bounded hT h hcT hbT⟩
  obtain ⟨l,u,hlu⟩ := hbounded
  have hcompact := (isCompact_Icc (a:=l) (b:=u)).image OnePoint.continuous_coe
  have hsub : S⊆((↑) : ℝ → OnePoint ℝ) '' Icc l u := by
    rw [←he]
    exact image_mono hlu
  have hinfmem := (closure_minimal hsub hcompact.isClosed) hinf.1
  exact OnePoint.infty_notMem_image_coe hinfmem

theorem circle_boundary_no_three {S : Set UnitCircle} (hS : IsPreconnected S)
    {a b c : UnitCircle} (ha : a∈closure S\S) (hb : b∈closure S\S)
    (hc : c∈closure S\S) (hab : a≠b) (hac : a≠c) : b=c := by
  let H := circleChart a
  let T : Set (OnePoint ℝ) := H.symm '' S
  have hT : IsPreconnected T := hS.image H.symm H.symm.continuous.continuousOn
  have hcl : closure T=H.symm '' closure S := H.symm.isClosedEmbedding.closure_image_eq S
  have hboundary {z : UnitCircle} (hz : z∈closure S\S) : H.symm z∈closure T\T := by
    refine ⟨?_,?_⟩
    · rw [hcl]; exact mem_image_of_mem _ hz.1
    · rintro ⟨w,hw,he⟩
      exact hz.2 (H.symm.injective he ▸ hw)
  have hH : H ∞=a := circleChart_infty a
  have hainf : H.symm a=∞ := H.symm_apply_eq.mpr hH.symm
  have hinf : (∞ : OnePoint ℝ)∈closure T\T := hainf ▸ hboundary ha
  have hbinf : H.symm b≠∞ := fun h => hab (H.symm.injective (hainf.trans h.symm))
  have hcinf : H.symm c≠∞ := fun h => hac (H.symm.injective (hainf.trans h.symm))
  obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp hbinf
  obtain ⟨y,hy⟩ := OnePoint.ne_infty_iff_exists.mp hcinf
  have he := onePoint_boundary_unique hT hinf (hx.symm ▸ hboundary hb) (hy.symm ▸ hboundary hc)
  apply H.symm.injective
  rw [←hx,←hy,he]

end CannonCircleBoundary

namespace CannonCircleBoundary
open Set Topology Metric

lemma radialDirection_continuous (q : ℂ) : Continuous (radialDirection q) := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Punctured q => (z:ℂ)-q) :=
    continuous_subtype_val.sub continuous_const
  exact (h.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property))).smul h

lemma radialDirection_reconstruct (q : ℂ) (z : Punctured q) :
    (z:ℂ)=q+‖(z:ℂ)-q‖ • (radialDirection q z:ℂ) := by
  have hn : ‖(z:ℂ)-q‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)
  simp only [radialDirection,smul_smul,mul_inv_cancel₀ hn,one_smul]
  abel

lemma radialDirection_radial (q : ℂ) (u : UnitCircle) {s : ℝ} (hs : 0 < s) :
    radialDirection q ⟨q+s•(u:ℂ),radial_ne q u hs⟩=u := by
  apply Subtype.ext
  have hu : ‖(u:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [radialDirection,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs,
    hu,mul_one,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

theorem radial_face_degree_two {q : ℂ} {r : ℝ} {U : Set ℂ}
    (hU : IsPreconnected U) (hUball : U⊆ball q r\{q})
    (u : Fin 3 → UnitCircle)
    (hnot : ∀ i,∀ s : ℝ,0 < s → s < r → q+s•(u i:ℂ)∉U)
    (hcl : ∀ i,∃ s : ℝ,0 < s ∧ q+s•(u i:ℂ)∈closure U) :
    ¬Function.Injective u := by
  let V : Set (Punctured q) := Subtype.val ⁻¹' U
  have he : Subtype.val '' V=U := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    exact ⟨⟨z,(hUball hz).2⟩,hz,rfl⟩
  have hV : IsPreconnected V := IsInducing.subtypeVal.isPreconnected_image.mp (he ▸ hU)
  let S := radialDirection q '' V
  have hS : IsPreconnected S := hV.image _ (radialDirection_continuous q).continuousOn
  have hb (i : Fin 3) : u i∈closure S\S := by
    constructor
    · obtain ⟨s,hs,hsi⟩ := hcl i
      let z : Punctured q := ⟨q+s•(u i:ℂ),radial_ne q (u i) hs⟩
      have hz : z∈closure V := by
        rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,he]
        exact hsi
      have hh := mem_closure_image (radialDirection_continuous q).continuousAt hz
      rwa [radialDirection_radial q (u i) hs] at hh
    · rintro ⟨z,hz,heq⟩
      have hs : 0<‖(z:ℂ)-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr z.property)
      have hsr : ‖(z:ℂ)-q‖ < r := by simpa only [mem_ball,dist_eq_norm] using (hUball hz).1
      have hz' : q+‖(z:ℂ)-q‖•(u i:ℂ)∈U := by
        rw [←heq,←radialDirection_reconstruct q z]
        exact hz
      exact hnot i _ hs hsr hz'
  intro hu
  have hh := circle_boundary_no_three hS (hb 0) (hb 1) (hb 2)
    (hu.ne (by decide)) (hu.ne (by decide))
  exact (by decide : (1:Fin 3)≠2) (hu hh)
end CannonCircleBoundary

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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_RegionBoundaryHitsOpen
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

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

lemma region_boundary_hits_in_open {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V⊆U) (hconn : IsPreconnected U) (hne : (U\V).Nonempty)
    {π : V → D} (hπ : Continuous π) (d : D) (hd : (region V π d).Nonempty) :
    ∃ x∈U\V, d∈incident V π x := by
  by_contra hn
  have hbound : closure (region V π d)⊆region V π d∪Uᶜ := by
    intro x hx
    by_cases hxU : x∈U
    · left
      have hxV : x∈V := by by_contra hxV; exact hn ⟨x,⟨hxU,hxV⟩,hx⟩
      exact closure_region_inside hV hπ hx hxV
    · exact Or.inr hxU
  have hclosed : IsClosed (region V π d∪Uᶜ) := by
    apply isClosed_of_closure_subset
    rw [closure_union,hU.isClosed_compl.closure_eq]
    exact union_subset hbound subset_union_right
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set U := Subtype.val ⁻¹' region V π d
  have hC : IsClopen C := by
    constructor
    · have he : C=Subtype.val ⁻¹' (region V π d∪Uᶜ) := by
        ext x
        simp only [C,mem_preimage,mem_union,mem_compl_iff]
        exact or_iff_left (not_not.mpr x.property) |>.symm
      rw [he]
      exact hclosed.preimage continuous_subtype_val
    · exact (region_isOpen hV hπ d).preimage continuous_subtype_val
  obtain ⟨x,hx⟩ := hd
  have hxU : x∈U := hVU (region_subset _ _ _ hx)
  have hCe : C=univ := hC.eq_univ ⟨⟨x,hxU⟩,hx⟩
  obtain ⟨y,hyU,hyV⟩ := hne
  have hyC : (⟨y,hyU⟩ : U)∈C := hCe.symm ▸ mem_univ _
  exact hyV (region_subset _ _ _ hyC)
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Reverse
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

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

lemma local_arc_flat {K : Set ℂ} {x : ℂ} (a : Arc ℂ)
    (Q : Finset (ℂ × ℂ)) (hQ : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : a t=x)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U)
    (hUK : ∀ z∈U, z∈K ↔ z∈range a) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
  obtain ⟨H,W,hW,htW,h₀,hW'⟩ := tame_graph_flat_chart (fun _ : Unit => a)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) Q (fun _ => hQ) () ht₀ ht₁
  refine ⟨H,W∩U,hW.inter hU,⟨ht ▸ htW,hxU⟩,h₀.trans ht,?_⟩
  intro z hz
  exact (hUK z hz.2).trans (by simpa only [iUnion_const] using hW' z hz.1)

lemma pair_start_local_arc (a b : Arc ℂ) (hab : a 0=b 0)
    (hc : ∀ s t, a s=b t → (s=0∨s=1) ∧ (t=0∨t=1)) :
    ∃ (c : Arc ℂ) (t : I) (U : Set ℂ), 0<t ∧ t<1 ∧ c t=a 0 ∧
      IsOpen U ∧ a 0∈U ∧ range c⊆range a∪range b ∧
      ∀ z∈U, (z∈range a∪range b ↔ z∈range c) := by
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm₀ : 0 < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < 1 := by change (1/2:ℝ)<1; norm_num
  let A := a.subarc 0 m hm₀.ne
  let B := b.subarc 0 m hm₀.ne
  let p : Path (a m) (a 0) := A.path.symm.cast (by simp [A]) (by simp [A])
  let q : Path (a 0) (b m) := B.path.cast (by simpa [B] using hab) (by simp [B])
  have hp (s : I) : p s=a (Icc.convexComb 0 m (unitInterval.symm s)) := rfl
  have hq (s : I) : q s=b (Icc.convexComb 0 m s) := rfl
  have hpq (s t : I) (he : p s=q t) : s=1 ∧ t=0 := by
    obtain ⟨hs,ht⟩ := hc _ _ he
    have hsₘ : Icc.convexComb 0 m (unitInterval.symm s) ≤ m := Icc.convexComb_le hm₀.le _
    have htₘ : Icc.convexComb 0 m t ≤ m := Icc.convexComb_le hm₀.le _
    have hs₀ : Icc.convexComb 0 m (unitInterval.symm s)=0 := hs.resolve_right (fun h => hm₁.not_ge (h ▸ hsₘ))
    have ht₀ : Icc.convexComb 0 m t=0 := ht.resolve_right (fun h => hm₁.not_ge (h ▸ htₘ))
    have hsval := congrArg Subtype.val hs₀
    have htval := congrArg Subtype.val ht₀
    constructor <;> apply Subtype.ext
    · simp only [Icc.coe_convexComb,unitInterval.coe_symm_eq] at hsval
      change (s:ℝ)=1
      dsimp [m] at hsval
      linarith
    · simp only [Icc.coe_convexComb] at htval
      change (t:ℝ)=0
      dsimp [m] at htval
      linarith
  have hpi : Function.Injective p := fun s t he =>
    unitInterval.symm_bijective.injective (A.injective he)
  have hqi : Function.Injective q := B.injective
  let c : Arc ℂ := ⟨(p.trans q).toContinuousMap,trans_injective p q hpi hqi hpq⟩
  have hcrange : range c=a '' Icc 0 m ∪ b '' Icc 0 m := by
    change range (p.trans q)=_
    rw [Path.trans_range]
    have hpR : range p=range A := by exact Path.symm_range A.path
    rw [hpR]
    change range A∪range B=_
    rw [subarc_range_eq a hm₀,subarc_range_eq b hm₀]
  let T : Set ℂ := a '' Ici m ∪ b '' Ici m
  have hT : IsClosed T :=
    (isClosed_Ici.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image b.continuous).isClosed
  have hxT : a 0∉T := by
    rintro (⟨s,hs,he⟩|⟨s,hs,he⟩)
    · have he₀ := a.injective he
      subst s
      exact hm₀.not_ge hs
    · have he₀ := b.injective (he.trans hab)
      subst s
      exact hm₀.not_ge hs
  refine ⟨c,m,Tᶜ,hm₀,hm₁,?_,hT.isOpen_compl,hxT,?_,?_⟩
  · change (p.trans q) m=a 0
    rw [Path.trans_apply]
    split_ifs with h
    · have hr : (⟨2*(m:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨m.2.1,h⟩⟩:I)=1 := by apply Subtype.ext; dsimp [m]; norm_num
      rw [hr,Path.target]
    · exact (h (by change (1/2:ℝ)≤1/2; rfl)).elim
  · rw [hcrange]
    exact union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  · intro z hz
    rw [hcrange]
    constructor
    · rintro (⟨s,rfl⟩|⟨s,rfl⟩)
      · exact Or.inl ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inl ⟨s,hm,rfl⟩))⟩,rfl⟩
      · exact Or.inr ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inr ⟨s,hm,rfl⟩))⟩,rfl⟩
    · intro hh
      exact union_subset_union (image_subset_range _ _) (image_subset_range _ _) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner CannonFaceIncidence

lemma pair_start_flat (a b : Arc ℂ) (hab : a 0 = b 0)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0 ∈ W ∧
      H (0,0)=a 0 ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  obtain ⟨c,t,U,ht₀,ht₁,ht,hU,hxU,hsub,hUK⟩ := pair_start_local_arc a b hab hc
  exact local_arc_flat c Q (fun z hz => (hsub hz).elim (fun h => ha h) (fun h => hb h)) ht₀ ht₁ ht hU hxU hUK

theorem pair_flat_at_left (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) (t : I) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a t ∈ W ∧
      H (0,0)=a t ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  by_cases ht₀ : t=0
  · subst t
    exact pair_start_flat a b hab₀ hc Q ha hb
  by_cases ht₁ : t=1
  · subst t
    have hc' : ∀ s t, a.reverse s = b.reverse t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
      intro s t he
      obtain ⟨hs,ht⟩ := hc _ _ he
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using And.intro hs ht
    have hh := pair_start_flat a.reverse b.reverse (by simpa) hc' Q
      (by simpa using ha) (by simpa using hb)
    simpa using hh
  have ht₀' : 0<t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  have ht₁' : t<1 := lt_of_le_of_ne (unitInterval.le_one t) ht₁
  have htB : a t ∉ range b := by
    rintro ⟨s,hs⟩
    exact ((hc t s hs.symm).1).elim ht₀ ht₁
  exact local_arc_flat a Q ha ht₀' ht₁' rfl
    b.compact_range.isClosed.isOpen_compl htB (fun z hz => or_iff_left hz)

theorem pair_incident_labels (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π) :
    ∃ labels : Bool → D, ∀ x∈range a ∪ range b,
      incident _ π x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsPreconnected K :=
    IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,hab₀.symm⟩⟩
      (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)
  have hflat : ∀ x∈K, ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
    rintro x (⟨t,rfl⟩|⟨t,rfl⟩)
    · exact pair_flat_at_left a b hab₀ hab₁ hc Q ha hb t
    · have hh := pair_flat_at_left b a hab₀.symm hab₁.symm
        (fun s t he => (hc t s he.symm).symm) Q hb ha t
      simpa only [K,union_comm] using hh
  have hloc₀ : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∃ labels : Bool → D, ∀ y∈U∩K, incident _ π y=range labels := by
    intro x hx
    obtain ⟨H,W,hW,hxW,h₀,hW'⟩ := hflat x hx
    have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
      rw [H.image_eq_preimage_symm]
      rfl
    obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ hxW)
      (fun z hz => not_congr ((hW' z hz).trans (he z)))
    exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩
  have hloc : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈K∩U, incident _ π y=incident _ π x := by
    intro x hx
    obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ x hx
    exact ⟨U,hU,hxU,fun y hy => (hl y hy.symm).trans (hl x ⟨hxU,hx⟩).symm⟩
  have hxK : a 0∈K := Or.inl (mem_range_self 0)
  obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ (a 0) hxK
  refine ⟨l,fun x hx => ?_⟩
  exact (incident_constant_on_preconnected hK hloc x hx (a 0) hxK).trans (hl (a 0) ⟨hxU,hxK⟩)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem pair_labels_surjective (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hπs : Function.Surjective π) :
    ∃ labels : Bool → D, Function.Surjective labels ∧
      ∀ x∈range a ∪ range b, incident _ π x=range labels := by
  obtain ⟨l,hl⟩ := pair_incident_labels a b hab₀ hab₁ hc Q ha hb hπ
  refine ⟨l,?_,hl⟩
  intro d
  obtain ⟨z,hz⟩ := hπs d
  have hd : (region _ π d).Nonempty := ⟨z.val,z.property,hz⟩
  have hK : IsClosed (range a ∪ range b) := a.compact_range.isClosed.union b.compact_range.isClosed
  obtain ⟨x,hx,_,hxd⟩ := region_boundary_hits hK (T:=∅) isClosed_empty (empty_subset _)
    (by simpa using (isPreconnected_univ : IsPreconnected (univ : Set ℂ)))
    ⟨a 0,Or.inl (mem_range_self 0),notMem_empty _⟩ hπ d hd
  change d∈range l
  rw [←hl x hx]
  exact hxd
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma centered_chord_endpoints (A B : ℂ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1/2) :
    let x := A+(1/2:ℝ)•(B-A)
    let c := ε•(B-A)
    x-c∈segment ℝ A B ∧ x+c∈segment ℝ A B := by
  dsimp
  rw [segment_eq_image']
  constructor
  · refine ⟨1/2-ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [sub_smul]
    abel
  · refine ⟨1/2+ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [add_smul]
    abel

lemma centered_chord_ball (A B : ℂ) (hAB : A≠B) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z∈segment ℝ A B)
    (hb : z∈ball (A+(1/2:ℝ)•(B-A)) ‖ε•(B-A)‖) :
    z∈segment ℝ (A+(1/2:ℝ)•(B-A)-ε•(B-A))
      (A+(1/2:ℝ)•(B-A)+ε•(B-A)) := by
  rw [segment_eq_image'] at hz ⊢
  obtain ⟨s,hs,rfl⟩ := hz
  have hD : 0 < ‖B-A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have he : A+s•(B-A)-(A+(1/2:ℝ)•(B-A))=(s-1/2)•(B-A) := by rw [sub_smul]; abel
  have habs : |s-1/2| < ε := by
    rw [mem_ball,dist_eq_norm,he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hε] at hb
    exact (mul_lt_mul_iff_left₀ hD).mp hb
  have hlo := (abs_lt.mp habs).1
  have hhi := (abs_lt.mp habs).2
  refine ⟨(s-1/2+ε)/(2*ε),⟨div_nonneg (by linarith) (by positivity),
    (div_le_one (by positivity : 0 < 2*ε)).mpr (by linarith)⟩,?_⟩
  have hd : (A+(1/2:ℝ)•(B-A)+ε•(B-A))-
      (A+(1/2:ℝ)•(B-A)-ε•(B-A))=(2*ε)•(B-A) := by
    rw [mul_smul,two_smul]; abel
  dsimp only
  rw [hd,smul_smul,div_mul_cancel₀ _ (by positivity : 2*ε≠0)]
  simp only [add_smul,sub_smul]
  abel

theorem pair_isolated_chord (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ (u v : I) (x c : ℂ), u < v ∧ c≠0 ∧ a u=x-c ∧ a v=x+c ∧
      a '' Icc u v=segment ℝ (a u) (a v) ∧
      (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v := by
  let m : I := ⟨1/2,by constructor  <;> norm_num⟩
  obtain ⟨p,q,hpm,hmq,hleft,_,_⟩ := tame_interior_corner Q a ha
    (t:=m) (by change (0:ℝ) < 1/2; norm_num) (by change (1/2:ℝ) < 1; norm_num)
  let D := a m-a p
  have hD : D≠0 := sub_ne_zero.mpr (a.injective.ne hpm.ne.symm)
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  let x := a p+(1/2:ℝ)•D
  have hxseg : x∈segment ℝ (a p) (a m) := by
    rw [segment_eq_image']
    exact ⟨1/2,by constructor  <;> norm_num,rfl⟩
  obtain ⟨w,hw,hwx⟩ := hleft.symm ▸ hxseg
  have hxp : x≠a p := by
    intro he
    have hh : (1/2:ℝ)•D=0 := by
      change a p+(1/2:ℝ)•D=a p at he
      exact add_left_cancel (he.trans (add_zero (a p)).symm)
    exact hD ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hxm : x≠a m := by
    intro he
    have hh : (1/2:ℝ)•D=D := by
      change a p+(1/2:ℝ)•D=a m at he
      exact eq_sub_of_add_eq (by rwa [add_comm])
    have hh' : ((1/2:ℝ)-1)•D=0 := by rw [sub_smul,one_smul,hh,sub_self]
    exact hD ((smul_eq_zero.mp hh').resolve_left (by norm_num))
  have hpw : p < w := lt_of_le_of_ne hw.1 (fun he => hxp (he ▸ hwx).symm)
  have hwm : w  <  m := lt_of_le_of_ne hw.2 (fun he => hxm (he ▸ hwx).symm)
  let T : Set ℂ := a '' Iic p ∪ a '' Ici m ∪ range b
  have hT : IsClosed T :=
    ((isClosed_Iic.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image a.continuous).isClosed).union b.compact_range.isClosed
  have hxT : x∉T := by
    rintro ((⟨s,hs,he⟩|⟨s,hs,he⟩)|⟨s,hs⟩)
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hpw.not_ge hs
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hwm.not_ge hs
    · rcases (hc w s (hwx.trans hs.symm)).2 with rfl | rfl
      · have hwzero := a.injective ((hwx.trans hs.symm).trans hab₀.symm)
        exact (not_lt_of_ge (show (0:I) ≤ p from p.2.1)) (hwzero ▸ hpw)
      · have hwone := a.injective ((hwx.trans hs.symm).trans hab₁.symm)
        exact (not_lt_of_ge (show m ≤ (1:I) from m.2.2)) (hwone ▸ hwm)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hxT)
  let ε := min (1/4) (δ/(2*‖D‖))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε₁ : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  let c : ℂ := ε•D
  have hcn : ‖c‖=ε*‖D‖ := by simp [c,Real.norm_eq_abs,abs_of_pos hε]
  have hc₀ : c≠0 := smul_ne_zero hε.ne' hD
  have hcδ : ‖c‖ < δ := by
    rw [hcn]
    have hh : ε*(2*‖D‖) ≤ δ := (le_div_iff₀ (by positivity)).mp (min_le_right (1/4) (δ/(2*‖D‖)))
    nlinarith
  have hend := centered_chord_endpoints (a p) (a m) hε hε₁
  change x-c∈segment ℝ (a p) (a m) ∧ x+c∈segment ℝ (a p) (a m) at hend
  obtain ⟨u,hu,hu'⟩ := hleft.symm ▸ hend.1
  obtain ⟨v,hv,hv'⟩ := hleft.symm ▸ hend.2
  have huv : u≠v := by
    intro he
    have hh : x-c=x+c := hu'.symm.trans (he ▸ hv')
    have hh' : c+c=0 := by linear_combination -hh
    exact hc₀ (by linear_combination (1/2:ℂ)*hh')
  have hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ segment ℝ (x-c) (x+c) := by
    rintro z ⟨hz,hzb⟩
    have hzT : z∉T := hball (ball_subset_ball hcδ.le hzb)
    rcases hz with ⟨s,rfl⟩|hz
    · have hsp : p ≤ s := le_of_not_ge (fun hh => hzT (Or.inl (Or.inl ⟨s,hh,rfl⟩)))
      have hsm : s  ≤  m := le_of_not_ge (fun hh => hzT (Or.inl (Or.inr ⟨s,hh,rfl⟩)))
      exact centered_chord_ball (a p) (a m) (a.injective.ne hpm.ne) hε
        (hleft ▸ ⟨s,⟨hsp,hsm⟩,rfl⟩) hzb
    · exact (hzT (Or.inr hz)).elim
  rcases lt_or_gt_of_ne huv with huv|hvu
  · have he := segment_subarc_image a hpm huv hleft
      (fun s hs => ⟨hu.1.trans hs.1,hs.2.trans hv.2⟩)
    refine ⟨u,v,x,c,huv,hc₀,hu',hv',he,?_⟩
    rw [he,hu',hv']
    exact hsmall
  · have he := segment_subarc_image a hpm hvu hleft
      (fun s hs => ⟨hv.1.trans hs.1,hs.2.trans hu.2⟩)
    refine ⟨v,u,x,-c,hvu,neg_ne_zero.mpr hc₀,?_,?_,he,?_⟩
    · simpa using hv'
    · simpa only [sub_eq_add_neg] using hu'
    · rw [norm_neg,he,hv',hu',segment_symm]
      exact hsmall
end CannonEmbeddedArc.Arc

noncomputable section
open Set Topology unitInterval

namespace CannonWinding
open Set Topology unitInterval

lemma turn_path_trans {a b c : Circle} (p : Path a b) (q : Path b c) :
    turn (p.trans q).toContinuousMap=turn p.toContinuousMap+turn q.toContinuousMap := by
  let f := lift p.toContinuousMap
  let g := lift q.toContinuousMap
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1+f 1-g 0) :=
    ⟨⟨fun t => g t+f 1-g 0,by fun_prop⟩,by ring,rfl⟩
  have hP (t : I) : Circle.exp (P t)=p t := lift_exp _ t
  have hQ (t : I) : Circle.exp (Q t)=q t := by
    change Circle.exp (g t+f 1-g 0)=q t
    simp only [Circle.exp_sub,Circle.exp_add,f,g,lift_exp]
    simp
  have hL (t : I) : Circle.exp ((P.trans Q) t)=(p.trans q) t := by
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> simp only [hP,hQ]
  rw [turn_eq_of_lift _ (P.trans Q).toContinuousMap hL]
  change (P.trans Q) 1-(P.trans Q) 0=_
  rw [Path.target,Path.source]
  dsimp only [turn,f,g]
  ring

lemma winding_path_trans {a b c : ℂ} (p : Path a b) (q : Path b c)
    (z : ℂ) (hp : z∉range p) (hq : z∉range q) :
    winding (p.trans q).toContinuousMap z (by change z∉range (p.trans q); rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)=
      winding p.toContinuousMap z hp+winding q.toContinuousMap z hq := by
  let f := direction (p.toContinuousMap-.const I z) (fun t ht => hp ⟨t,sub_eq_zero.mp ht⟩)
  let g := direction (q.toContinuousMap-.const I z) (fun t ht => hq ⟨t,sub_eq_zero.mp ht⟩)
  have hfg : f 1=g 0 := by
    apply Circle.ext
    simp [f,g,direction_coe]
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1) := ⟨g,hfg.symm,rfl⟩
  have he : direction ((p.trans q).toContinuousMap-.const I z)
      (fun t ht => (show z∉range (p.trans q) by rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)
        ⟨t,sub_eq_zero.mp ht⟩)=(P.trans Q).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change ((p.trans q) t-z)/(‖(p.trans q) t-z‖:ℂ)=((P.trans Q) t:ℂ)
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> rfl
  change turn (direction _ _)=turn f+turn g
  rw [he]
  exact turn_path_trans P Q

lemma winding_path_homotopy {a : ℂ} {p q : Path a a} (H : p.Homotopy q)
    (z : ℂ) (hz : z∉range H) :
    winding p.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(0,t),by simpa using ht⟩)=
      winding q.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(1,t),by simpa using ht⟩) := by
  exact winding_eq_of_homotopy _ _ _ _ _ H.toHomotopy.toContinuousMap
    (fun s => (H.source s).trans (H.target s).symm)
    (fun t => H.map_zero_left t) (fun t => H.map_one_left t) hz

lemma upperSemi_im (t : I) : 0≤(upperSemi t).im := by
  change 0≤(Circle.exp (Real.pi*(1-(t:ℝ))):ℂ).im
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le (sub_nonneg.mpr t.property.2),
    by nlinarith [t.property.1,Real.pi_pos]⟩
lemma lowerSemi_im (t : I) : (lowerSemi t).im≤0 := by
  change (Circle.exp (Real.pi*(1+(t:ℝ))):ℂ).im≤0
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im,
    show Real.pi*(1+(t:ℝ))=(Real.pi*(t:ℝ))+Real.pi by ring,Real.sin_add_pi]
  exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le t.property.1,mul_le_of_le_one_right Real.pi_pos.le t.property.2⟩)

lemma winding_upperSemi :
    winding upperSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change upperSemi t=0 at ht; have := upperSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = -Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1-(t:ℝ)),by fun_prop⟩
  have he : direction (upperSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := upperSemi_norm t
      change upperSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (upperSemi t-0)/(‖upperSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,upperSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]

lemma winding_lowerSemi :
    winding lowerSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change lowerSemi t=0 at ht; have := lowerSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1+(t:ℝ)),by fun_prop⟩
  have he : direction (lowerSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := lowerSemi_norm t
      change lowerSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (lowerSemi t-0)/(‖lowerSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,lowerSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval Metric

lemma winding_outside_move {a : ℂ} (p : Path a a) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) :
    winding p.toContinuousMap z (path_outside_avoids p hp hz)=
      winding p.toContinuousMap 0 (path_outside_avoids p hp (by simp)) := by
  have hw (s : I) : ‖Path.segment z 0 s‖<1 := by
    have hs : Path.segment z 0 s∈ball (0:ℂ) 1 := by
      apply (convex_ball (0:ℂ) 1).segment_subset
        (by simpa [mem_ball,dist_zero_right] using hz) (show (0:ℂ)∈ball (0:ℂ) 1 by simp)
      rw [←Path.range_segment]
      exact mem_range_self s
    simpa [mem_ball,dist_zero_right] using hs
  have he := winding_moving_point p.toContinuousMap (by change p 0=p 1; simp)
    (Path.segment z 0).toContinuousMap (fun s => path_outside_avoids p hp (hw s))
  change winding _ (Path.segment z 0 0) _=winding _ (Path.segment z 0 1) _ at he
  simpa only [Path.source,Path.target] using he

lemma segment_diameter_im (t : I) : (Path.segment (-1:ℂ) 1 t).im=0 := by
  simp [Path.segment,AffineMap.lineMap_apply]

theorem winding_chord_replace (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (q : Path (-1:ℂ) 1) (hq : ∀ t, ‖q t‖=1)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn= -1) (hside : ∀ t, sgn*(q t).im≤0)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ hz : ((sgn*η:ℝ):ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ),
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap
        (((sgn*η:ℝ):ℂ)*Complex.I) hz =
      winding (q.trans γ).toContinuousMap 0 (by
        apply path_outside_avoids (q.trans γ) _ (by simp)
        intro t
        rw [Path.trans_apply]
        split_ifs
        · exact (hq _).ge
        · exact hγ _) := by
  let z : ℂ := ((sgn*η:ℝ):ℂ)*Complex.I
  have hnz : ‖z‖<1 := by
    rcases hsgn with rfl|rfl <;> simpa [z,norm_mul,Complex.norm_I,abs_of_pos hη] using hη₁
  have himz : sgn*z.im=η := by
    rcases hsgn with rfl|rfl <;> simp [z]
  have him (s t : I) : sgn*(blendPaths (Path.segment (-1:ℂ) 1) q (s,t)).im≤0 := by
    change sgn*(((1-(s:ℝ)) • Path.segment (-1:ℂ) 1 t+(s:ℝ) • q t).im)≤0
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,segment_diameter_im,mul_zero,zero_add]
    nlinarith [hside t,s.property.1]
  let H := (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ)
  have hzH : z∉range H := by
    rintro ⟨⟨s,t⟩,he⟩
    change (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ) (s,t)=z at he
    rw [Path.Homotopy.hcomp_apply] at he
    split_ifs at he with h
    · change blendPaths (Path.segment (-1:ℂ) 1) q (s,_) = z at he
      have hh := him s ⟨2*(t:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,h⟩⟩
      rw [he,himz] at hh
      exact hη.not_ge hh
    · exact path_outside_avoids γ hγ hnz ⟨_,he⟩
  have hp : z∉range ((Path.segment (-1:ℂ) 1).trans γ) := by
    rintro ⟨t,ht⟩
    exact hzH ⟨(0,t),by simpa [H] using ht⟩
  refine ⟨hp,?_⟩
  have he := winding_path_homotopy H z hzH
  change winding _ z hp=_
  rw [he]
  apply winding_outside_move (q.trans γ) _ hnz
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact (hq _).ge
  · exact hγ _

theorem chord_winding_jump (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ (hplus : (η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ))
      (hminus : -(η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ)),
    winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap ((η:ℂ)*Complex.I) hplus -
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap (-(η:ℂ)*Complex.I) hminus
      =2*Real.pi := by
  obtain ⟨hp,hp'⟩ := winding_chord_replace γ hγ lowerSemi lowerSemi_norm 1 (Or.inl rfl)
    (fun t => by simpa using lowerSemi_im t) η hη hη₁
  obtain ⟨hm,hm'⟩ := winding_chord_replace γ hγ upperSemi upperSemi_norm (-1) (Or.inr rfl)
    (fun t => by simpa using upperSemi_im t) η hη hη₁
  simp only [one_mul,neg_one_mul,Complex.ofReal_neg] at hp hm hp' hm'
  refine ⟨hp,hm,?_⟩
  have hγ₀ := path_outside_avoids γ hγ (z:=0) (by simp)
  have hl₀ := path_outside_avoids lowerSemi (fun t => (lowerSemi_norm t).ge) (z:=0) (by simp)
  have hu₀ := path_outside_avoids upperSemi (fun t => (upperSemi_norm t).ge) (z:=0) (by simp)
  rw [hp',hm',winding_path_trans lowerSemi γ 0 hl₀ hγ₀,
    winding_path_trans upperSemi γ 0 hu₀ hγ₀,winding_lowerSemi,winding_upperSemi]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval

lemma winding_on_component (f : C(I,ℂ)) (hf : f 0=f 1) {z w : ℂ}
    (hz : z∉range f) (hw : w∈connectedComponentIn (range f)ᶜ z) :
    winding f z hz=winding f w (connectedComponentIn_subset _ _ hw) := by
  let V : Set ℂ := (range f)ᶜ
  let z' : V := ⟨z,hz⟩
  let w' : V := ⟨w,connectedComponentIn_subset _ _ hw⟩
  have hwc : w'∈connectedComponent z' := by
    have hwi : w∈Subtype.val '' connectedComponent z' :=
      (connectedComponentIn_eq_image (F:=V) (x:=z) hz) ▸ hw
    obtain ⟨v,hv,hve⟩ := hwi
    have he : v=w' := Subtype.ext hve
    exact he ▸ hv
  exact (winding_locally_constant f hf).apply_eq_of_isPreconnected
    (s:=connectedComponent z') isPreconnected_connectedComponent
    (x:=z') (y:=w') (mem_connectedComponent (x:=z')) hwc

theorem chord_separates (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    -(η:ℂ)*Complex.I∉connectedComponentIn
      (range ((Path.segment (-1:ℂ) 1).trans γ))ᶜ ((η:ℂ)*Complex.I) := by
  obtain ⟨hp,hm,he⟩ := chord_winding_jump γ hγ η hη hη₁
  intro hh
  have hc : ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 0=
      ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 1 := by
    change ((Path.segment (-1:ℂ) 1).trans γ) 0=((Path.segment (-1:ℂ) 1).trans γ) 1
    simp
  have heq := winding_on_component _ hc hp hh
  rw [heq,sub_self] at he
  linarith [Real.pi_pos]
end CannonWinding

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Portion
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
open Set Topology Metric unitInterval

lemma portion_range (a : Arc ℂ) {u v : I} (huv : u ≤ v) :
    range (a.portion u v)=a '' Icc u v := by
  rcases huv.eq_or_lt with he|hl
  · subst v
    simp [portion,Icc.convexComb_eq]
  · exact subarc_range_eq a hl

lemma pair_closing_path (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (u v : I) :
    ∃ γ : Path (a v) (a u), range γ=
      a '' Icc v 1 ∪ range b ∪ a '' Icc 0 u := by
  let p : Path (a 1) (a 0) := b.path.symm.cast hab₁ hab₀
  refine ⟨((a.portion v 1).trans p).trans (a.portion 0 u),?_⟩
  rw [Path.trans_range,Path.trans_range,portion_range a (unitInterval.le_one v),
    portion_range a (unitInterval.nonneg u)]
  have hp : range p=range b := Path.symm_range b.path
  rw [hp]

lemma isolated_chord_closer (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ∃ γ : Path (a v) (a u),
      range (Path.segment (a u) (a v))∪range γ=range a∪range b ∧
      ∀ t, ‖c‖ ≤ dist (γ t) x := by
  obtain ⟨γ,hγ⟩ := pair_closing_path a b hab₀ hab₁ u v
  have hball : ∀ z∈(range a∪range b)∩ball x ‖c‖,
      ∃ s∈Ioo u v, a s=z := by
    intro z hz
    obtain ⟨s,hs,hsz⟩ := hsmall hz
    have hsu : s≠u := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hu,mem_ball,dist_eq_norm] at hh
      have hd : x-c-x=-c := by abel
      rw [hd,norm_neg] at hh
      exact lt_irrefl _ hh
    have hsv : s≠v := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hv,mem_ball,dist_eq_norm,add_sub_cancel_left] at hh
      exact lt_irrefl _ hh
    exact ⟨s,⟨lt_of_le_of_ne hs.1 hsu.symm,lt_of_le_of_ne hs.2 hsv⟩,hsz⟩
  refine ⟨γ,?_,?_⟩
  · rw [Path.range_segment,hγ,←he]
    apply Subset.antisymm
    · exact union_subset (fun _ h => Or.inl (image_subset_range _ _ h))
        (union_subset (union_subset (fun _ h => Or.inl (image_subset_range _ _ h)) subset_union_right)
          (fun _ h => Or.inl (image_subset_range _ _ h)))
    · rintro z (⟨s,rfl⟩|hz)
      · rcases lt_trichotomy s u with hsu | rfl | hus
        · exact Or.inr (Or.inr ⟨s,⟨unitInterval.nonneg s,hsu.le⟩,rfl⟩)
        · exact Or.inl ⟨s,⟨le_rfl,huv.le⟩,rfl⟩
        · by_cases hvs : v < s
          · exact Or.inr (Or.inl (Or.inl ⟨s,⟨hvs.le,unitInterval.le_one s⟩,rfl⟩))
          · exact Or.inl ⟨s,⟨hus.le,le_of_not_gt hvs⟩,rfl⟩
      · exact Or.inr (Or.inl (Or.inr hz))
  · intro t
    apply le_of_not_gt
    intro ht
    have htγ := mem_range_self (f:=γ) t
    rw [hγ] at htγ
    have htK : γ t∈range a∪range b := by
      rcases htγ with ((⟨s,_,he'⟩|hh)|⟨s,_,he'⟩)
      · exact Or.inl ⟨s,he'⟩
      · exact Or.inr hh
      · exact Or.inl ⟨s,he'⟩
    obtain ⟨s,hs,hse⟩ := hball (γ t) ⟨htK,ht⟩
    rcases htγ with ((⟨r,hr,he'⟩|⟨r,he'⟩)|⟨r,hr,he'⟩)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.2.not_ge hr.1
    · have hh := (hc s r (hse.trans he'.symm)).1
      rcases hh with hh|hh
      · exact (not_lt_of_ge (show (0:I) ≤ u from u.2.1)) (hh ▸ hs.1)
      · exact (not_lt_of_ge (show v ≤ (1:I) from v.2.2)) (hh ▸ hs.2)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.1.not_ge hr.2
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma isolated_chord_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hc₀ : c≠0) (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨γ,hγK,hγ⟩ := isolated_chord_closer a b hab₀ hab₁ hc huv hu hv he hsmall
  let L : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-x)).trans
    (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc₀))
  have hL (z : ℂ) : L z=(z-x)/c := by rfl
  have hLu : L (a u)=-1 := by rw [hL,hu]; simp [sub_sub_cancel_left,hc₀]
  have hLv : L (a v)=1 := by rw [hL,hv]; simp [hc₀]
  let Γ : Path (1:ℂ) (-1) := (γ.map L.continuous).cast hLv.symm hLu.symm
  have hΓ (t : I) : 1 ≤ ‖Γ t‖ := by
    change 1 ≤ ‖L (γ t)‖
    rw [hL,norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr hc₀)).mpr
    simpa only [one_mul,dist_eq_norm] using hγ t
  let N : ℂ →ᵃ[ℝ] ℂ := {
    toFun := fun z => (z-x)/c
    linear := {
      toFun := fun z => z/c
      map_add' := fun z w => add_div z w c
      map_smul' := fun r z => by simp only [Complex.real_smul, RingHom.id_apply]; ring }
    map_vadd' := fun z w => by change (w+z-x)/c=w/c+(z-x)/c; ring }
  have hseg : L '' segment ℝ (a u) (a v)=segment ℝ (-1:ℂ) 1 := by
    change N '' segment ℝ (a u) (a v)=_
    rw [image_segment ℝ N]
    change segment ℝ (L (a u)) (L (a v))=_
    rw [hLu,hLv]
  have hΓR : range Γ=L '' range γ := by
    change range (L ∘ γ)=_
    exact range_comp L γ
  let f := (Path.segment (-1:ℂ) 1).trans Γ
  have hfR : range f=L '' (range a∪range b) := by
    rw [show f=(Path.segment (-1:ℂ) 1).trans Γ from rfl,Path.trans_range,
      Path.range_segment,←hseg,hΓR,←image_union,←Path.range_segment,hγK]
  intro hconn
  have hconn' : IsPreconnected (range f)ᶜ := by
    rw [hfR,←L.image_compl]
    exact hconn.image L L.continuous.continuousOn
  obtain ⟨hp,hm,_⟩ := CannonWinding.chord_winding_jump Γ hΓ (1/2)
    (by norm_num) (by norm_num)
  exact CannonWinding.chord_separates Γ hΓ (1/2) (by norm_num) (by norm_num)
    (hconn'.subset_connectedComponentIn hp subset_rfl hm)

theorem pair_complement_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨u,v,x,c,huv,hc₀,hu,hv,he,hs⟩ := pair_isolated_chord a b hab₀ hab₁ hc Q ha
  exact isolated_chord_not_preconnected a b hab₀ hab₁ hc huv hc₀ hu hv he hs
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ labels : Bool ≃ ConnectedComponents ((range a ∪ range b)ᶜ : Set ℂ),
      ∀ x∈range a ∪ range b,
        incident _ ConnectedComponents.mk x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hls,hl⟩ := pair_labels_surjective a b hab₀ hab₁ hc Q ha hb
    (π:=ConnectedComponents.mk) ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  have hne : l false ≠ l true := by
    intro he
    have hconst (s t : Bool) : l s=l t := by
      cases s <;> cases t
      · rfl
      · exact he
      · exact he.symm
      · rfl
    have hsub (d e : ConnectedComponents (Kᶜ : Set ℂ)) : d=e := by
      obtain ⟨s,rfl⟩ := hls d
      obtain ⟨t,rfl⟩ := hls e
      exact hconst s t
    have hconn : PreconnectedSpace (Kᶜ : Set ℂ) := by
      rw [preconnectedSpace_iff_connectedComponent]
      intro x
      apply eq_univ_of_forall
      intro y
      exact ConnectedComponents.coe_eq_coe'.mp (hsub _ _)
    exact pair_complement_not_preconnected a b hab₀ hab₁ hc Q ha
      (isPreconnected_iff_preconnectedSpace.mpr hconn)
  have hli : Function.Injective l := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective l ⟨hli,hls⟩,hl⟩
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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_PositiveHalfAxis
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

namespace CannonPlanarCorner
open Set Topology Metric

lemma slit_box_connected {r : ℝ} (hr : 0 < r) :
    IsConnected (CannonFaceIncidence.openBox r\positiveHalfAxis) := by
  let L : Set (ℝ × ℝ) := Ioo (-r) 0 ×ˢ Ioo (-r) r
  have hL : IsConnected L := (isConnected_Ioo (neg_neg_of_pos hr)).prod
    (isConnected_Ioo (by linarith : -r < r))
  have hm (b : Bool) : (L∩CannonFaceIncidence.halfBox r b).Nonempty := by
    cases b
    · refine ⟨(-r/2,-r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r< -r/2 ∧ -r/2 < r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2 < r) ∧ (-r< -r/2 ∧ -r/2<0)
        constructor <;> constructor <;> linarith
    · refine ⟨(-r/2,r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r < r/2 ∧ r/2 < r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2 < r) ∧ (0 < r/2 ∧ r/2 < r)
        constructor <;> constructor <;> linarith
  have he : CannonFaceIncidence.openBox r\positiveHalfAxis=
      (L∪CannonFaceIncidence.halfBox r false)∪CannonFaceIncidence.halfBox r true := by
    ext p
    simp only [CannonFaceIncidence.openBox,CannonFaceIncidence.halfBox,L,positiveHalfAxis,
      Bool.false_eq_true,↓reduceIte,mem_sdiff,mem_ofPred_eq,mem_prod,mem_Ioo,mem_union]
    constructor
    · rintro ⟨⟨hx,hy⟩,hn⟩
      by_cases hpx : p.1<0
      · exact Or.inl (Or.inl ⟨⟨hx.1,hpx⟩,hy⟩)
      · have hpy : p.2≠0 := fun h => hn ⟨le_of_not_gt hpx,h⟩
        rcases lt_or_gt_of_ne hpy with hp|hp
        · exact Or.inl (Or.inr ⟨hx,hy.1,hp⟩)
        · exact Or.inr ⟨hx,hp,hy.2⟩
    · rintro ((⟨hx,hy⟩|⟨hx,hy⟩)|⟨hx,hy⟩)
      · exact ⟨⟨⟨hx.1,hx.2.trans hr⟩,hy⟩,fun h => hx.2.not_ge h.1⟩
      · exact ⟨⟨hx,hy.1,hy.2.trans hr⟩,fun h => hy.2.ne h.2⟩
      · exact ⟨⟨hx,(neg_neg_of_pos hr).trans hy.1,hy.2⟩,fun h => hy.1.ne' h.2⟩
  rw [he]
  apply IsConnected.union _ (IsConnected.union (hm false) hL (CannonFaceIncidence.halfBox_connected hr false))
    (CannonFaceIncidence.halfBox_connected hr true)
  obtain ⟨p,hpL,hpT⟩ := hm true
  exact ⟨p,Or.inl hpL,hpT⟩

lemma straight_ray_chart (x u : ℂ) (hu : u≠0) :
    ∃ H : (ℝ × ℝ) ≃ₜ ℂ, H (0,0)=x ∧
      H '' positiveHalfAxis={z | ∃ s : ℝ, 0 ≤ s ∧ z=x+s•u} := by
  let H := (Complex.equivRealProdCLM.toHomeomorph.symm.trans (Homeomorph.mulLeft₀ u hu)).trans
    (Homeomorph.addLeft x)
  have ht (t : ℝ) : H (t,0)=x+t•u := by
    change x+u*Complex.equivRealProdCLM.symm (t,0)=x+t•u
    congr 1
    rw [Complex.real_smul]
    have he : Complex.equivRealProdCLM.symm (t,0)=(t:ℂ) := by apply Complex.ext <;> rfl
    rw [he,mul_comm]
  refine ⟨H,by simpa using ht 0,?_⟩
  ext z
  constructor
  · rintro ⟨⟨s,t⟩,⟨hs,ht₀⟩,rfl⟩
    change t=0 at ht₀
    subst t
    exact ⟨s,hs,ht s⟩
  · rintro ⟨s,hs,hz⟩
    exact ⟨(s,0),⟨hs,rfl⟩,(ht s).trans hz.symm⟩
end CannonPlanarCorner

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameInitialInterval
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
open Set Topology Metric unitInterval CannonPlanarCorner

lemma tame_initial_interval (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ q : I, 0<q ∧ a '' Icc 0 q=segment ℝ (a 0) (a q) := by
  classical
  obtain ⟨P,h₀,h₁,hP⟩ := finite_segment_arc_subdivision Q a ha
  let R := P.filter (0<·)
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,zero_lt_one⟩⟩
  let q := R.min' hR
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hcon : Consecutive P 0 q := by
    refine ⟨h₀,hq.1,hq.2,?_⟩
    intro z hz hz₀ hzq
    exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,hz₀⟩))
  have hh := hP ⟨(0,q),(mem_segments P 0 q).mpr hcon⟩
  rw [subdivArc_range_eq] at hh
  exact ⟨q,hq.2,hh⟩

theorem tame_tip_chart (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0∈W ∧ H (0,0)=a 0 ∧
      ∀ z∈W, (z∈range a ↔ z∈H '' positiveHalfAxis) := by
  obtain ⟨q,hq,hseg⟩ := tame_initial_interval a Q ha
  let u := a q-a 0
  have hu : u≠0 := sub_ne_zero.mpr (a.injective.ne hq.ne')
  obtain ⟨H,hH₀,hH⟩ := straight_ray_chart (a 0) u hu
  let T := a '' Ici q
  have hT : IsClosed T := (isClosed_Ici.isCompact.image a.continuous).isClosed
  have hxT : a 0∉T := by
    rintro ⟨s,hs,he⟩
    have he' := a.injective he
    subst s
    exact hq.not_ge hs
  refine ⟨H,Tᶜ∩ball (a 0) ‖u‖,hT.isOpen_compl.inter isOpen_ball,
    ⟨hxT,mem_ball_self (norm_pos_iff.mpr hu)⟩,hH₀,?_⟩
  intro z hz
  rw [hH]
  change (z∈range a ↔ ∃ s : ℝ, 0 ≤ s ∧ z=a 0+s•u)
  rw [local_ray_segment le_rfl hz.2]
  have he : a 0+u=a q := by dsimp [u]; abel
  rw [he,←hseg]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hs => hz.1 ⟨s,hs,rfl⟩)⟩,rfl⟩
  · intro hz
    exact image_subset_range _ _ hz

theorem tame_tip_connected_neighborhood (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) {U : Set ℂ} (hU : IsOpen U) (hxU : a 0∈U) :
    ∃ W : Set ℂ, IsOpen W ∧ a 0∈W ∧ W⊆U ∧ IsConnected (W\range a) := by
  obtain ⟨H,W,hW,hxW,h₀,hflat⟩ := tame_tip_chart a Q ha
  have h₀WU : H (0,0)∈W∩U := h₀.symm ▸ ⟨hxW,hxU⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (((hW.inter hU).preimage H.continuous).mem_nhds h₀WU)
  let C := CannonFaceIncidence.openBox r
  let W' := H '' C
  have hsub : C⊆H ⁻¹' (W∩U) := by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact hball
  have hW'U : W'⊆W∩U := by rintro _ ⟨p,hp,rfl⟩; exact hsub hp
  refine ⟨W',H.isOpenMap C (by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact isOpen_ball),
    ⟨(0,0),by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact mem_ball_self hr,h₀⟩,
    fun z hz => (hW'U hz).2,?_⟩
  have he : W'\range a=H '' (C\positiveHalfAxis) := by
    ext z
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpA⟩
      refine ⟨p,⟨hp,?_⟩,rfl⟩
      intro hpR
      exact hpA ((hflat (H p) (hsub hp).1).mpr ⟨p,hpR,rfl⟩)
    · rintro ⟨p,⟨hp,hpR⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      intro hpA
      obtain ⟨q,hq,heq⟩ := (hflat (H p) (hsub hp).1).mp hpA
      exact hpR (H.injective heq ▸ hq)
  rw [he]
  exact (slit_box_connected hr).image H H.continuous.continuousOn
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RadialStable
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

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyJoined_of_preconnected_finite_segments (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) :
    PolyJoined (⋃ q∈Q,segment ℝ q.1 q.2) x y := by
  classical
  let K := ⋃ q∈Q,segment ℝ q.1 q.2
  let V := ⋃ q∈Q.filter (fun q => PolyJoined K x q.1),segment ℝ q.1 q.2
  let W := ⋃ q∈Q.filter (fun q => ¬PolyJoined K x q.1),segment ℝ q.1 q.2
  have hseg (q : E×E) (hq : q∈Q) : segment ℝ q.1 q.2⊆K :=
    subset_iUnion₂_of_subset q hq Subset.rfl
  have hreach (q : E×E) (hq : q∈Q) {z : E} (hz : z∈segment ℝ q.1 q.2) :
      PolyJoined K x z ↔ PolyJoined K x q.1 := by
    constructor
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset hz (left_mem_segment ..)).trans (hseg q hq))
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset (left_mem_segment ..) hz).trans (hseg q hq))
  have hV (z : E) : z∈V ↔ z∈K ∧ PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,(hreach q hq hzq).mpr hqr⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,(hreach q hq hzq).mp hr⟩,hzq⟩
  have hW (z : E) : z∈W ↔ z∈K ∧ ¬PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,fun h => hqr ((hreach q hq hzq).mp h)⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,fun h => hr ((hreach q hq hzq).mpr h)⟩,hzq⟩
  have hcV : IsClosed V := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  have hcW : IsClosed W := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  by_contra hn
  have hcover : K⊆V∪W := by
    intro z hz
    by_cases hr : PolyJoined K x z
    · exact Or.inl ((hV z).mpr ⟨hz,hr⟩)
    · exact Or.inr ((hW z).mpr ⟨hz,hr⟩)
  obtain ⟨z,hzK,hzV,hzW⟩ := isPreconnected_closed_iff.mp hK V W hcV hcW hcover
    ⟨x,hx,(hV x).mpr ⟨hx,.refl⟩⟩ ⟨y,hy,(hW y).mpr ⟨hy,hn⟩⟩
  exact ((hW z).mp hzW).2 ((hV z).mp hzV).2

theorem preconnected_finite_segments_arc (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) (hne : x≠y) :
    ∃ a : CannonEmbeddedArc.Arc E, a 0=x ∧ a 1=y ∧
      range a⊆⋃ q∈Q,segment ℝ q.1 q.2 ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_preconnected_finite_segments Q hK hx hy) hne
end CannonPolygonal

namespace CannonSegmentCones
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma radial_dist (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    dist (x+t • (y-x)) x=t*dist y x := by
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]

lemma radial_mem_ball {x y : E} {ε t : ℝ} (hy : dist y x < ε)
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) : dist (x+t • (y-x)) x < ε := by
  rw [radial_dist x y ht]
  exact (mul_le_of_le_one_left dist_nonneg ht₁).trans_lt hy

lemma segment_split {a b x : E} (hx : x ∈ segment ℝ a b) :
    segment ℝ a b=segment ℝ x a ∪ segment ℝ x b := by
  apply Subset.antisymm
  · intro z hz
    by_cases hza : z=a
    · exact Or.inl (hza ▸ right_mem_segment ℝ x a)
    by_cases hzb : z=b
    · exact Or.inr (hzb ▸ right_mem_segment ℝ x b)
    have hzo := mem_openSegment_of_ne_left_right (Ne.symm hza) (Ne.symm hzb) hz
    have hxr : x ∈ range (AffineMap.lineMap a b : ℝ → E) := by
      rw [segment_eq_image_lineMap] at hx
      exact image_subset_range _ _ hx
    rcases openSegment_subset_union a b hxr hzo with he|ha|hb
    · exact Or.inl (he ▸ left_mem_segment ℝ x a)
    · exact Or.inl (segment_symm ℝ a x ▸ openSegment_subset_segment ℝ _ _ ha)
    · exact Or.inr (openSegment_subset_segment ℝ _ _ hb)
  · exact union_subset
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (left_mem_segment ℝ a b))
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (right_mem_segment ℝ a b))

lemma anchored_radial_stable (x a : E) :
    ∃ ε>0, RadialStable (segment ℝ x a) x ε := by
  by_cases ha : a=x
  · subst a
    refine ⟨1,zero_lt_one,?_⟩
    intro y hy t ht ht₁
    simp only [segment_same,mem_singleton_iff,add_eq_left]
    rw [smul_eq_zero]
    simp [ht.ne',sub_eq_zero]
  · refine ⟨‖a-x‖,norm_pos_iff.mpr (sub_ne_zero.mpr ha),?_⟩
    intro y hy t ht ht₁
    constructor
    · intro hz
      rw [segment_eq_image'] at hz ⊢
      obtain ⟨s,hs,he⟩ := hz
      have he' : s • (a-x)=t • (y-x) := by
        simpa only [add_right_inj] using he
      have hv : y-x=(s/t) • (a-x) := by
        calc
          y-x=t⁻¹ • (t • (y-x)) := by simp [smul_smul,ht.ne']
          _=t⁻¹ • (s • (a-x)) := by rw [he']
          _=(s/t) • (a-x) := by rw [smul_smul,div_eq_inv_mul]
      have hst₀ : 0 ≤ s/t := div_nonneg hs.1 ht.le
      have hst₁ : s/t ≤ 1 := by
        have hn := congrArg norm hv
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hst₀] at hn
        rw [dist_eq_norm] at hy
        have han : 0 < ‖a-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
        nlinarith
      refine ⟨s/t,⟨hst₀,hst₁⟩,?_⟩
      change x+(s/t) • (a-x)=y
      rw [←hv,add_sub_cancel]
    · intro hyseg
      have hz := (convex_segment (𝕜:=ℝ) x a) (left_mem_segment ℝ x a) hyseg
        (sub_nonneg.mpr ht₁) ht.le (sub_add_cancel 1 t)
      convert hz using 1; module

lemma RadialStable.mono_radius {K : Set E} {x : E} {ε δ : ℝ}
    (h : RadialStable K x ε) (hδε : δ ≤ ε) : RadialStable K x δ :=
  fun y hy t ht ht₁ => h y (hy.trans_le hδε) t ht ht₁

lemma RadialStable.union {K L : Set E} {x : E} {ε δ : ℝ}
    (hK : RadialStable K x ε) (hL : RadialStable L x δ) :
    RadialStable (K∪L) x (min ε δ) := by
  intro y hy t ht ht₁
  simp only [mem_union]
  rw [hK y (hy.trans_le (min_le_left _ _)) t ht ht₁,
    hL y (hy.trans_le (min_le_right _ _)) t ht ht₁]

lemma segment_closed (a b : E) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))).isClosed

lemma segment_radial_stable (a b x : E) :
    ∃ ε>0, RadialStable (segment ℝ a b) x ε := by
  by_cases hx : x∈segment ℝ a b
  · obtain ⟨ε,hε,hεK⟩ := anchored_radial_stable x a
    obtain ⟨δ,hδ,hδK⟩ := anchored_radial_stable x b
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    rw [segment_split hx]
    exact hεK.union hδK
  · obtain ⟨ε,hε,hεK⟩ := Metric.isOpen_iff.mp (segment_closed a b).isOpen_compl x hx
    refine ⟨ε,hε,?_⟩
    intro y hy t ht ht₁
    have hyK := hεK hy
    have hzK := hεK (radial_mem_ball hy ht.le ht₁)
    exact iff_of_false hzK hyK

theorem finite_segments_radial_stable (Q : Finset (E×E)) (x : E) :
    ∃ ε>0, RadialStable (⋃ q∈Q,segment ℝ q.1 q.2) x ε := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp [RadialStable]⟩
  | @insert q Q hq ih =>
    obtain ⟨ε,hε,hεK⟩ := segment_radial_stable q.1 q.2 x
    obtain ⟨δ,hδ,hδK⟩ := ih
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hεK.union hδK

theorem component_radial_access (Q : Finset (E×E)) {x a : E}
    (hxK : x ∈ ⋃ q∈Q,segment ℝ q.1 q.2)
    (hx : x∈closure (connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a)) :
    ∃ y : E, y≠x ∧ ∀ t : ℝ, 0<t → t≤1 →
      x+t • (y-x)∈connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a := by
  let K : Set E := ⋃ q∈Q,segment ℝ q.1 q.2
  obtain ⟨ε,hε,hstable⟩ := finite_segments_radial_stable Q x
  obtain ⟨y,hyball,hy⟩ := (mem_closure_iff_nhds.mp hx)
    (Metric.ball x ε) (Metric.ball_mem_nhds x hε)
  have hyK : y∉K := connectedComponentIn_subset _ _ hy
  have hyx : y≠x := fun h => hyK (h ▸ hxK)
  let S : Set E := (fun t : ℝ => x+t • (y-x)) '' Ioc 0 1
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hyS : y∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSK : S⊆Kᶜ := by
    rintro z ⟨t,ht,rfl⟩ hz
    exact hyK ((hstable y hyball t ht.1 ht.2).mp hz)
  have hsub := hS.subset_connectedComponentIn hyS hSK
  rw [←connectedComponentIn_eq hy] at hsub
  refine ⟨y,hyx,fun t ht ht₁ => hsub ⟨t,⟨ht,ht₁⟩,rfl⟩⟩

end CannonSegmentCones
namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Finite ι]

theorem finite_graph_exact_segments (F : ι → Arc E)
    (Q : Finset (E×E)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2) :
    ∃ P : Finset (E×E), (⋃ i,range (F i))=⋃ p∈P,segment ℝ p.1 p.2 := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP₀ hP₁ hPs using fun i => finite_segment_arc_subdivision Q (F i) (hQ i)
  let R : Finset (E×E) := Finset.univ.biUnion fun i =>
    (segments (P i)).image (fun z => (F i z.1,F i z.2))
  refine ⟨R,?_⟩
  have he (i : ι) : range (F i)=⋃ z : segments (P i),
      segment ℝ (F i z.val.1) (F i z.val.2) := by
    rw [subdivision_cover (F i) (P i) (hP₀ i) (hP₁ i)]
    exact iUnion_congr fun z => hPs i z
  simp only [he]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxi
    apply mem_iUnion₂.mpr
    refine ⟨(F i z.val.1,F i z.val.2),?_,hz⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
      Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩⟩
  · intro hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨z,hz⟩,hxp⟩⟩

lemma halfopen_radial_segment {U : Set E} {x y : E}
    (h : ∀ t : ℝ, 0<t → t≤1 → x+t • (y-x)∈U) :
    segment ℝ x y⊆insert x U := by
  rw [segment_eq_image']
  rintro z ⟨t,ht,rfl⟩
  rcases eq_or_lt_of_le ht.1 with he|he
  · simp [←he]
  · exact Or.inr (h t he ht.2)

end CannonEmbeddedArc.Arc
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

theorem refined_component_at_boundary (P Q : Finset (ℂ × ℂ))
    (hPQ : (⋃ p∈P,segment ℝ p.1 p.2)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {a x : ℂ} (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)) :
    ∃ z∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a,
      z∉⋃ q∈Q,segment ℝ q.1 q.2 ∧
      x∈closure (connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ z) ∧
      connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ z⊆
        connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a := by
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let L := ⋃ q∈Q,segment ℝ q.1 q.2
  let U := connectedComponentIn Kᶜ a
  have hK : IsClosed K := isClosed_biUnion_finset (fun p _ => segment_closed p.1 p.2)
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  obtain ⟨ε,hε,hstable⟩ := finite_segments_radial_stable Q x
  have hne : (ball x ε∩U).Nonempty := mem_closure_iff_nhds.mp hx _ (ball_mem_nhds x hε)
  obtain ⟨z,⟨hzball,hzU⟩,hzL⟩ := (complex_finite_segments_compl_dense Q).inter_open_nonempty
    _ (isOpen_ball.inter hU) hne
  let S : Set ℂ := (fun t : ℝ => x+t • (z-x)) '' Ioc 0 1
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hzS : z∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSL : S⊆Lᶜ := by
    rintro w ⟨t,ht,rfl⟩ hw
    exact hzL ((hstable z hzball t ht.1 ht.2).mp hw)
  have hSR : S⊆connectedComponentIn Lᶜ z := hS.subset_connectedComponentIn hzS hSL
  have hxS : x∈closure S := by
    have h₀ : (0:ℝ)∈closure (Ioc (0:ℝ) 1) := by rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl,zero_le_one⟩
    have hh := image_closure_subset_closure_image (s:=Ioc (0:ℝ) 1) (show Continuous (fun t : ℝ => x+t • (z-x)) by fun_prop)
    exact hh ⟨0,h₀,by simp⟩
  have hsub : connectedComponentIn Lᶜ z⊆U := by
    have hLK : Lᶜ⊆Kᶜ := compl_subset_compl.mpr hPQ
    have hconn : IsPreconnected (U ∪ connectedComponentIn Lᶜ z) :=
      IsPreconnected.union z hzU (mem_connectedComponentIn hzL)
        isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
    exact subset_union_right.trans (hconn.subset_connectedComponentIn
      (Or.inl (mem_connectedComponentIn ha))
      (union_subset (connectedComponentIn_subset _ _)
        ((connectedComponentIn_subset _ _).trans hLK)))
  exact ⟨z,hzU,hzL,closure_mono hSR hxS,hsub⟩
end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_between_accessible_points {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y a b : E} (hxy : x≠y)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (a-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (b-y)∈U) :
    ∃ c : Arc E, c 0=x ∧ c 1=y ∧ (∀ t : I, t≠0 → t≠1 → c t∈U) ∧
      FiniteSupport (range c) := by
  let V := insert x (insert y U)
  have ha : a∈U := by simpa using hax 1 zero_lt_one le_rfl
  have hb : b∈U := by simpa using hby 1 zero_lt_one le_rfl
  have hUV : U⊆V := (subset_insert y U).trans (subset_insert x _)
  have hxa : PolyJoined V x a := Relation.ReflTransGen.single
    ((halfopen_radial_segment hax).trans (insert_subset (mem_insert _ _) hUV))
  have hab : PolyJoined V a b := Relation.ReflTransGen.mono
    (r:=fun a b => segment ℝ a b⊆U) (p:=fun a b => segment ℝ a b⊆V)
    (fun _ _ h => h.trans hUV) a b (polyJoined_of_open_preconnected hU hc ha hb)
  have hby' : PolyJoined V b y := Relation.ReflTransGen.single (by
    rw [segment_symm]
    exact (halfopen_radial_segment hby).trans (insert_subset (by simp [V]) hUV))
  obtain ⟨c,hc₀,hc₁,hcV,hcS⟩ := polyJoined_arc (hxa.trans (hab.trans hby')) hxy
  refine ⟨c,hc₀,hc₁,?_,hcS⟩
  intro t ht₀ ht₁
  rcases hcV (mem_range_self t) with h|h|h
  · exact (ht₀ (c.injective (h.trans hc₀.symm))).elim
  · exact (ht₁ (c.injective (h.trans hc₁.symm))).elim
  · exact h

theorem finite_segment_component_crosscut (P : Finset (E×E))
    {x y z : E} (hx : x∈⋃ p∈P,segment ℝ p.1 p.2)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2) (hxy : x≠y)
    (hxcl : x∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z))
    (hycl : y∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z)) :
    ∃ c : Arc E, c 0=x ∧ c 1=y ∧
      (∀ t : I, t≠0 → t≠1 → c t∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z) ∧
      FiniteSupport (range c) := by
  obtain ⟨a,_,ha⟩ := component_radial_access P hx hxcl
  obtain ⟨b,_,hb⟩ := component_radial_access P hy hycl
  have hK : IsClosed (⋃ p∈P,segment ℝ p.1 p.2) :=
    isClosed_biUnion_finset (fun p _ => segment_closed p.1 p.2)
  exact arc_between_accessible_points hK.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxy ha hb
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameEdgeIncidenceOpen
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
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_in_open (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ F i t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩(⋃ j,range (F j)), incident (U\(⋃ j,range (F j))) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart F hF Q hQ i ht₀ ht₁
  have htU : F i t∈U := hiU ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\(⋃ j,range (F j)) ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈(⋃ j,range (F j)) ↔ (H.symm z).2=0 := by
      rw [hflat z hz.1,H.image_eq_preimage_symm]
      rfl
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  exact ⟨W',hW',h₀ ▸ h₀W',l,fun x hx => hl x ⟨hx.1,fun h => h.2 hx.2⟩⟩

theorem tame_edge_labels_in_open (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\(⋃ j,range (F j))) π (F i t)=range l := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := tame_edge_incidence_in_open F hF Q hQ hU hπ i hiU ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩⟩).trans
      (hl (F i t) ⟨htW,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := tame_edge_incidence_in_open F hF Q hQ hU hπ i hiU hm.1 hm.2
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (F i m) ⟨m,hm,rfl⟩).trans (hl (F i m) ⟨hmW,mem_iUnion.mpr ⟨i,mem_range_self m⟩⟩)

theorem tame_star_center_incident [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (x : ℂ) (hx : x∈U) (h₀ : ∀ i, F i 0=x) (h₁ : ∀ i, F i 1∉U)
    (hFU : ∀ i, F i '' Ioo (0:I) 1⊆U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region (U\(⋃ j,range (F j))) π d).Nonempty) :
    d∈incident (U\(⋃ j,range (F j))) π x := by
  let K := ⋃ j,range (F j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  have hxK : x∈K := by obtain ⟨i⟩ := ‹Nonempty ι›; exact mem_iUnion.mpr ⟨i,⟨0,h₀ i⟩⟩
  have hne : (U\(U\K)).Nonempty := ⟨x,hx,fun hxV => hxV.2 hxK⟩
  obtain ⟨y,⟨hyU,hyV⟩,hyd⟩ := region_boundary_hits_in_open
    hU (hU.sdiff hK) sdiff_subset hconn hne hπ d hd
  by_cases hyx : y=x
  · subst y
    exact hyd
  have hyK : y∈K := by by_contra hn; exact hyV ⟨hyU,hn⟩
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hyK
  have ht₀ : t≠0 := fun ht => hyx (ht ▸ h₀ i)
  have ht₁ : t≠1 := fun h => h₁ i (h ▸ hyU)
  obtain ⟨l,hl⟩ := tame_edge_labels_in_open F hF Q hQ hU hπ i (hFU i)
  have hdR : d∈range l := by
    rw [←hl t (lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) ht₀.symm)
      (lt_of_le_of_ne (le_one t) ht₁)]
    exact hyd
  have hclosed : IsClosed ((F i) ⁻¹' closure (region (U\K) π d)) :=
    isClosed_closure.preimage (F i).continuous
  have hs : Ioo (0:I) 1⊆(F i) ⁻¹' closure (region (U\K) π d) := by
    intro t ht
    show d∈incident (U\K) π (F i t)
    rw [hl t ht.1 ht.2]
    exact hdR
  have hz : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  have he := closure_minimal hs hclosed hz
  change x∈closure (region (U\K) π d)
  simpa only [mem_preimage,h₀ i] using he
end CannonEmbeddedArc.Arc

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma FiniteSupport.iUnion {ι : Type*} [Finite ι] {S : ι → Set E}
    (hS : ∀ i, FiniteSupport (S i)) : FiniteSupport (⋃ i,S i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP using hS
  refine ⟨Finset.univ.biUnion P,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hP i hi)
  exact mem_iUnion₂.mpr ⟨p,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩,hxp⟩
end CannonPolygonal

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

lemma finite_segment_union (P Q : Finset (ℂ × ℂ)) :
    (⋃ p∈P∪Q,segment ℝ p.1 p.2)=(⋃ p∈P,segment ℝ p.1 p.2)∪(⋃ p∈Q,segment ℝ p.1 p.2) := by
  ext x
  simp only [mem_iUnion,Finset.mem_union,mem_union]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact hp.elim (fun h => Or.inl ⟨p,h,hx⟩) (fun h => Or.inr ⟨p,h,hx⟩)
  · rintro (⟨p,hp,hx⟩|⟨p,hp,hx⟩)
    · exact ⟨p,Or.inl hp,hx⟩
    · exact ⟨p,Or.inr hp,hx⟩

theorem extend_tame_star {ι : Type*} [Finite ι] [Nonempty ι]
    (P : Finset (ℂ × ℂ)) {a x y : ℂ}
    (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2)
    (hycl : y∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a))
    (F : ι → Arc ℂ) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hS : ∀ i,FiniteSupport (range (F i)))
    (h₀ : ∀ i,F i 0=x)
    (h₁ : ∀ i,F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hny : ∀ i,F i 1≠y)
    (hFU : ∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (c '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,Compatible c (F i) := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  let G := ⋃ i,range (F i)
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hyU : y∉U := fun hh => hUK hh hy
  have hxy : x≠y := fun he => hyU (he ▸ hx)
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  have hQi (i : ι) : range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    fun z hz => hQ (mem_iUnion.mpr ⟨i,hz⟩)
  obtain ⟨R,hR⟩ := finite_graph_exact_segments F Q hQi
  let L := K∪G
  have hL : L=⋃ p∈P∪R,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hR]
  have hKL : (⋃ p∈P,segment ℝ p.1 p.2)⊆⋃ p∈P∪R,segment ℝ p.1 p.2 := by
    rw [←hL]
    exact subset_union_left
  obtain ⟨z,hzU,hzL,hycl',hsubU⟩ := refined_component_at_boundary P (P∪R) hKL ha hycl
  rw [←hL] at hzL hycl' hsubU
  have hzG : z∉G := fun hh => hzL (Or.inr hh)
  let V := U\G
  have hV : IsOpen V := hU.sdiff (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
  have hzV : z∈V := ⟨hzU,hzG⟩
  have hVL : V⊆Lᶜ := by
    rintro w ⟨hwU,hwG⟩ (hwK|hwG')
    · exact hUK hwU hwK
    · exact hwG hwG'
  have hcomp : connectedComponentIn V z=connectedComponentIn Lᶜ z := by
    apply subset_antisymm (connectedComponentIn_mono z hVL)
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL)
    intro w hw
    exact ⟨hsubU hw,fun hwG => connectedComponentIn_subset _ _ hw (Or.inr hwG)⟩
  let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents V) := inferInstance
  have hxcl' := tame_star_center_incident F hF Q hQi hU isPreconnected_connectedComponentIn
    x hx h₀ h₁ hFU ConnectedComponents.continuous_coe
    (ConnectedComponents.mk (⟨z,hzV⟩ : V)) ⟨z,hzV,rfl⟩
  change x∈closure (region V ConnectedComponents.mk (ConnectedComponents.mk (⟨z,hzV⟩ : V))) at hxcl'
  rw [component_region_eq,hcomp] at hxcl'
  have hxG : x∈G := by
    let i : ι := Classical.choice inferInstance
    exact mem_iUnion.mpr ⟨i,0,h₀ i⟩
  have hxL : x∈L := Or.inr hxG
  have hyL : y∈L := Or.inl hy
  rw [hL] at hxL hyL hxcl' hycl'
  obtain ⟨c,hc₀,hc₁,hcU,hcS⟩ := finite_segment_component_crosscut (P∪R) hxL hyL hxy hxcl' hycl'
  have hcV (t : I) (ht₀ : t≠0) (ht₁ : t≠1) : c t∈V := by
    have hh := hcU t ht₀ ht₁
    rw [←hL,←hcomp] at hh
    exact connectedComponentIn_subset _ _ hh
  have hyG : y∉G := by
    intro hyG
    obtain ⟨i,t,he⟩ := mem_iUnion.mp hyG
    by_cases ht₀ : t=0
    · exact hxy ((h₀ i).symm.trans (ht₀ ▸ he))
    by_cases ht₁ : t=1
    · exact hny i (ht₁ ▸ he)
    exact hyU (he ▸ hFU i ⟨t,⟨lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) (Ne.symm ht₀),
      lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩)
  have hinter (i : ι) (s t : I) (he : c s=F i t) : s=0 ∧ t=0 := by
    have hs : s=0 := by
      by_contra hs
      by_cases hs₁ : s=1
      · exact hyG (mem_iUnion.mpr ⟨i,t,he.symm.trans (hs₁ ▸ hc₁)⟩)
      · exact (hcV s hs hs₁).2 (mem_iUnion.mpr ⟨i,t,he.symm⟩)
    refine ⟨hs,(F i).injective ?_⟩
    exact he.symm.trans ((hs ▸ hc₀).trans (h₀ i).symm)
  refine ⟨c,hc₀,hc₁,hcS,?_,fun i => ?_⟩
  · rintro w ⟨t,ht,rfl⟩
    exact (hcV t ht.1.ne' ht.2.ne).1
  · refine ⟨fun s t he => ⟨Or.inl (hinter i s t he).1,Or.inl (hinter i s t he).2⟩,?_⟩
    rintro w ⟨⟨s,rfl⟩,t,he⟩ w' ⟨⟨s',rfl⟩,t',he'⟩
    rw [(hinter i s t he.symm).1,(hinter i s' t' he'.symm).1]
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem finite_tame_star (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (B : Finset ℂ) (hB : ∀ y∈B,y∈(⋃ p∈P,segment ℝ p.1 p.2) ∩
      closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)) :
    ∃ F : B → Arc ℂ, Pairwise (fun i j => Compatible (F i) (F j)) ∧
      (∀ i,F i 0=x) ∧ (∀ i,F i 1=i.val) ∧
      (∀ i,FiniteSupport (range (F i))) ∧
      (∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  induction B using Finset.induction_on with
  | empty =>
    refine ⟨fun i => False.elim ((Finset.notMem_empty i.val) i.property),?_,?_,?_,?_,?_⟩ <;>
      intro i <;> exact ((Finset.notMem_empty i.val) i.property).elim
  | @insert y B hy ih =>
    obtain ⟨F,hF,h₀,h₁,hS,hFU⟩ := ih (fun z hz => hB z (Finset.mem_insert_of_mem hz))
    have hyK := (hB y (Finset.mem_insert_self _ _)).1
    have hycl := (hB y (Finset.mem_insert_self _ _)).2
    have hyU : y∉U := fun h => hUK h hyK
    have hF₁ (i : B) : F i 1∉U := by
      rw [h₁]
      exact fun h => hUK h (hB i.val (Finset.mem_insert_of_mem i.property)).1
    have hny (i : B) : F i 1≠y := by
      rw [h₁]
      exact fun h => hy (h ▸ i.property)
    obtain ⟨c,hc₀,hc₁,hcS,hcU,hcF⟩ : ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧
        FiniteSupport (range c) ∧ (c '' Ioo (0:I) 1⊆U) ∧ ∀ i,Compatible c (F i) := by
      by_cases hn : Nonempty B
      · let _ : Nonempty B := hn
        exact extend_tame_star P ha hx hyK hycl F hF hS h₀ hF₁ hny hFU
      · have hxy : x≠y := fun he => hyU (he ▸ hx)
        obtain ⟨b,_,hb⟩ := component_radial_access P hyK hycl
        obtain ⟨c,hc₀,hc₁,hcU,hcS⟩ := arc_between_accessible_points hU
          isPreconnected_connectedComponentIn hxy (a:=x)
          (fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using (show x∈U from hx)) hb
        refine ⟨c,hc₀,hc₁,hcS,?_,fun i => (hn ⟨i⟩).elim⟩
        rintro z ⟨t,ht,rfl⟩
        exact hcU t ht.1.ne' ht.2.ne
    let F' : ↥(insert y B : Finset ℂ) → Arc ℂ := fun i =>
      if h : i.val=y then c else F ⟨i.val,(Finset.mem_insert.mp i.property).resolve_left h⟩
    have hiold (i : (insert y B : Finset ℂ)) (h : i.val≠y) : i.val∈B :=
      (Finset.mem_insert.mp i.property).resolve_left h
    have hnew (i : (insert y B : Finset ℂ)) (h : i.val=y) : F' i=c := by simp [F',h]
    have hold (i : (insert y B : Finset ℂ)) (h : i.val≠y) : F' i=F ⟨i.val,hiold i h⟩ := by simp [F',h]
    refine ⟨F',?_,?_,?_,?_,?_⟩
    · intro i j hij
      by_cases hi : i.val=y
      · rw [hnew i hi]
        by_cases hj : j.val=y
        · exact (hij (Subtype.ext (hi.trans hj.symm))).elim
        · rw [hold j hj]
          exact hcF _
      · rw [hold i hi]
        by_cases hj : j.val=y
        · rw [hnew j hj]
          exact (hcF _).symm
        · rw [hold j hj]
          exact hF (fun h => hij (Subtype.ext (congrArg (fun b : B => b.val) h)))
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hc₀
      · rw [hold i hi]; exact h₀ _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hc₁.trans hi.symm
      · rw [hold i hi]; exact h₁ _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hcS
      · rw [hold i hi]; exact hS _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hcU
      · rw [hold i hi]; exact hFU _
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {X : Type*} [TopologicalSpace X] [T2Space X]
theorem isolate_edge_interior_weak {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (i : ι) {p t q : I} (hpt : p<t) (htq : t<q) :
    ∃ W : Set X, IsOpen W ∧ F i t∈W ∧
      ∀ z∈W, (z∈⋃ j, range (F j) ↔ z∈F i '' Icc p q) := by
  classical
  let A : Set X := ⋃ j : {j // j≠i}, range (F j.val)
  let B : Set X := F i '' (Iic p∪Ici q)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => (F j.val).compact_range.isClosed)
  have hB : IsClosed B :=
    ((isClosed_Iic.union isClosed_Ici).isCompact.image (F i).continuous).isClosed
  let W := (A∪B)ᶜ
  have ht₀ : t≠0 := ne_of_gt ((unitInterval.nonneg p).trans_lt hpt)
  have ht₁ : t≠1 := ne_of_lt (htq.trans_le (unitInterval.le_one q))
  have htA : F i t∉A := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    obtain ⟨s,hs⟩ := hj
    have hh := (hF j.property.symm) t s hs.symm
    exact hh.1.elim ht₀ ht₁
  have htB : F i t∉B := by
    rintro ⟨s,hs,hst⟩
    have he := (F i).injective hst
    subst s
    exact hs.elim hpt.not_ge htq.not_ge
  refine ⟨W,(hA.union hB).isOpen_compl,fun h => h.elim htA htB,?_⟩
  intro z hz
  constructor
  · intro hzF
    obtain ⟨j,s,hs⟩ := mem_iUnion.mp hzF
    by_cases hji : j=i
    · subst j
      refine ⟨s,?_,hs⟩
      have hsB : s∉Iic p∪Ici q := fun hsB => hz (Or.inr ⟨s,hsB,hs⟩)
      constructor
      · exact (lt_of_not_ge (fun h => hsB (Or.inl h))).le
      · exact (lt_of_not_ge (fun h => hsB (Or.inr h))).le
    · exact (hz (Or.inl (mem_iUnion.mpr ⟨⟨j,hji⟩,⟨s,hs⟩⟩))).elim
  · rintro ⟨s,_,rfl⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self s⟩
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

theorem tame_graph_flat_chart_weak {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ F i t∈W ∧
      H (0,0)=F i t ∧ ∀ z∈W,
        (z∈⋃ j, range (F j) ↔ z∈H '' horizontal) := by
  obtain ⟨p,q,hpt,htq,hleft,hright,hcorner⟩ := tame_interior_corner Q (F i) (hQ i) ht₀ ht₁
  obtain ⟨W,hW,htW,hiso⟩ := isolate_edge_interior_weak F hF i hpt htq
  let x := F i t
  let u := F i p-x
  let v := F i q-x
  have hu : u≠0 := sub_ne_zero.mpr ((F i).injective.ne hpt.ne)
  have hv : v≠0 := sub_ne_zero.mpr ((F i).injective.ne htq.ne.symm)
  let r := min ‖u‖ ‖v‖
  have hr : 0 < r := lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  obtain ⟨H₀,hH₀,hHr⟩ := straighten_corner hcorner
  let H := H₀.trans (Homeomorph.addLeft x)
  refine ⟨H,W∩ball x r,hW.inter isOpen_ball,⟨htW,mem_ball_self hr⟩,?_,?_⟩
  · simp [H,hH₀,x]
  · intro z hz
    rw [hiso z hz.1]
    have he : Icc p q=Icc p t∪Icc t q := by
      ext s
      constructor
      · intro hs
        rcases le_total s t with hst|hts
        · exact Or.inl ⟨hs.1,hst⟩
        · exact Or.inr ⟨hts,hs.2⟩
      · rintro (hs|hs)
        · exact ⟨hs.1,hs.2.trans htq.le⟩
        · exact ⟨hpt.le.trans hs.1,hs.2⟩
    rw [he,image_union,hleft,hright]
    have hHimage : H '' horizontal=(fun w : ℂ => x+w) '' (ray u∪ray v) := by
      change ((fun w : ℂ => x+w) ∘ H₀) '' horizontal=_
      rw [image_comp,hHr]
    rw [hHimage,image_union,mem_union,mem_union]
    have hxU : x+u=F i p := by dsimp [u,x]; abel
    have hxV : x+v=F i q := by dsimp [v,x]; abel
    have hmem (w : ℂ) : z∈(fun b : ℂ => x+b) '' ray w ↔
        ∃ s : ℝ, 0 ≤ s ∧ z = x+s•w := by
      constructor
      · rintro ⟨b,⟨s,hs,hb⟩,hbe⟩
        exact ⟨s,hs,by rw [hb] at hbe; exact hbe.symm⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨s•w,⟨s,hs,rfl⟩,rfl⟩
    rw [hmem u,hmem v,local_ray_segment (min_le_left _ _) hz.2,
      local_ray_segment (min_le_right _ _) hz.2,hxU,hxV]
    rw [segment_symm (𝕜:=ℝ) (x:=F i p) (y:=x)]
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ F i t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩(⋃ j,range (F j)), incident (U\(⋃ j,range (F j))) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart_weak F hF Q hQ i ht₀ ht₁
  have htU : F i t∈U := hiU ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\(⋃ j,range (F j)) ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈(⋃ j,range (F j)) ↔ (H.symm z).2=0 := by
      rw [hflat z hz.1,H.image_eq_preimage_symm]
      rfl
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  exact ⟨W',hW',h₀ ▸ h₀W',l,fun x hx => hl x ⟨hx.1,fun h => h.2 hx.2⟩⟩

theorem tame_edge_labels_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\(⋃ j,range (F j))) π (F i t)=range l := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩⟩).trans
      (hl (F i t) ⟨htW,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU hm.1 hm.2
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (F i m) ⟨m,hm,rfl⟩).trans (hl (F i m) ⟨hmW,mem_iUnion.mpr ⟨i,mem_range_self m⟩⟩)

theorem tame_star_center_incident_weak [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (x : ℂ) (hx : x∈U) (h₀ : ∀ i, F i 0=x) (h₁ : ∀ i, F i 1∉U)
    (hFU : ∀ i, F i '' Ioo (0:I) 1⊆U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region (U\(⋃ j,range (F j))) π d).Nonempty) :
    d∈incident (U\(⋃ j,range (F j))) π x := by
  let K := ⋃ j,range (F j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  have hxK : x∈K := by obtain ⟨i⟩ := ‹Nonempty ι›; exact mem_iUnion.mpr ⟨i,⟨0,h₀ i⟩⟩
  have hne : (U\(U\K)).Nonempty := ⟨x,hx,fun hxV => hxV.2 hxK⟩
  obtain ⟨y,⟨hyU,hyV⟩,hyd⟩ := region_boundary_hits_in_open
    hU (hU.sdiff hK) sdiff_subset hconn hne hπ d hd
  by_cases hyx : y=x
  · subst y
    exact hyd
  have hyK : y∈K := by by_contra hn; exact hyV ⟨hyU,hn⟩
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hyK
  have ht₀ : t≠0 := fun ht => hyx (ht ▸ h₀ i)
  have ht₁ : t≠1 := fun h => h₁ i (h ▸ hyU)
  obtain ⟨l,hl⟩ := tame_edge_labels_in_open_weak F hF Q hQ hU hπ i (hFU i)
  have hdR : d∈range l := by
    rw [←hl t (lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) ht₀.symm)
      (lt_of_le_of_ne (le_one t) ht₁)]
    exact hyd
  have hclosed : IsClosed ((F i) ⁻¹' closure (region (U\K) π d)) :=
    isClosed_closure.preimage (F i).continuous
  have hs : Ioo (0:I) 1⊆(F i) ⁻¹' closure (region (U\K) π d) := by
    intro t ht
    show d∈incident (U\K) π (F i t)
    rw [hl t ht.1 ht.2]
    exact hdR
  have hz : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  have he := closure_minimal hs hclosed hz
  change x∈closure (region (U\K) π d)
  simpa only [mem_preimage,h₀ i] using he
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem arc_with_terminal_germ {U C : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y w z : ℂ} (hxy : x≠y) (hy : y∉U)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (w-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (z-y)∈U∩C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (∀ t : I,t≠0 → t≠1 → c t∈U) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
  have hz : z∈U := by simpa using (hby 1 zero_lt_one le_rfl).1
  have hzy : z≠y := fun h => hy (h ▸ hz)
  have hseg : segment ℝ y z⊆insert y (U∩C) := halfopen_radial_segment hby
  by_cases hxz : x=z
  · subst x
    let c := lineArc z y hzy
    refine ⟨c,by simp [c],by simp [c],?_,?_,1,zero_lt_one,?_⟩
    · rw [show range c=segment ℝ z y by exact lineArc_range ..]
      exact FiniteSupport.segment z y
    · intro t ht₀ ht₁
      have hm : c t∈segment ℝ y z := by rw [segment_symm,←lineArc_range z y hzy]; exact mem_range_self t
      rcases hseg hm with hm|hm
      · exact (ht₁ (c.injective (hm.trans (show c 1=y by simp [c]).symm))).elim
      · exact hm.1
    · intro q hq
      have hm : q∈segment ℝ y z := by
        have hh := hq.1
        rwa [show range c=segment ℝ z y by exact lineArc_range ..,segment_symm] at hh
      exact (hseg hm).imp id And.right
  obtain ⟨b,hb₀,hb₁,hbU,hbS⟩ := arc_between_accessible_points hU hc hxz hax
    (a:=w) (b:=z) (fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hz)
  have hyb : y∉range b := by
    rintro ⟨t,ht⟩
    by_cases ht₀ : t=0
    · exact hxy (hb₀.symm.trans (ht₀ ▸ ht))
    by_cases ht₁ : t=1
    · exact hy ((ht₁ ▸ ht) ▸ hb₁.symm ▸ hz)
    exact hy (ht ▸ hbU t ht₀ ht₁)
  let d := lineArc z y hzy
  obtain ⟨c,hc₀,hc₁,hcr⟩ := extend_arc b d (by simpa [d] using hb₁) (by simpa [d] using hyb)
  have hc₀' : c 0=x := hc₀.trans hb₀
  have hc₁' : c 1=y := by simpa [d] using hc₁
  have hdr : range d=segment ℝ y z := by rw [lineArc_range,segment_symm]
  have hr : range b⊆insert x U := by
    rintro q ⟨t,rfl⟩
    by_cases ht₀ : t=0
    · exact Or.inl (ht₀ ▸ hb₀)
    by_cases ht₁ : t=1
    · exact Or.inr (ht₁ ▸ hb₁.symm ▸ hz)
    exact Or.inr (hbU t ht₀ ht₁)
  obtain ⟨ε,hε,havoid⟩ := Metric.isOpen_iff.mp b.compact_range.isClosed.isOpen_compl y hyb
  refine ⟨c,hc₀',hc₁',?_,?_,ε,hε,?_⟩
  · apply (hbS.union (FiniteSupport.segment y z)).mono
    simpa only [hdr] using hcr
  · intro t ht₀ ht₁
    rcases hcr (mem_range_self t) with hh|hh
    · rcases hr hh with hh|hh
      · exact (ht₀ (c.injective (hh.trans hc₀'.symm))).elim
      · exact hh
    · rw [hdr] at hh
      rcases hseg hh with hh|hh
      · exact (ht₁ (c.injective (hh.trans hc₁'.symm))).elim
      · exact hh.1
  · rintro q ⟨hq,hqball⟩
    rcases hcr hq with hh|hh
    · exact (havoid hqball hh).elim
    · rw [hdr] at hh
      exact (hseg hh).imp id And.right
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_HalfParam
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
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem extend_star_in_sector {ι : Type*} [Finite ι]
    (P : Finset (ℂ × ℂ)) {a x y : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2)
    (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (hS : ∀ i,FiniteSupport (range (F i))) (h₀ : ∀ i,F i 0=x)
    (h₁ : ∀ i,F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hFU : ∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Set ℂ) (hC : IsOpen C) (hyC : y∈closure C)
    (hCU : C⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → y+t • (z-y)∈C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (c '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      (∀ i,∀ s t : I,c s=F i t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  let G := ⋃ i,range (F i)
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hyU : y∉U := fun hh => hUK hh hy
  have hxy : x≠y := fun he => hyU (he ▸ hx)
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  have hQi (i : ι) : range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    fun z hz => hQ (mem_iUnion.mpr ⟨i,hz⟩)
  obtain ⟨R,hR⟩ := finite_graph_exact_segments F Q hQi
  let L := K∪G
  have hL : L=⋃ p∈P∪R,segment ℝ p.1 p.2 := by rw [finite_segment_union,←hR]
  have hLc : IsClosed L := by rw [hL]; exact isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable (P∪R) y
  have hne : (ball y r∩C).Nonempty := mem_closure_iff_nhds.mp hyC _ (ball_mem_nhds y hr)
  obtain ⟨z,⟨hzball,hzC⟩,hzL⟩ := (complex_finite_segments_compl_dense (P∪R)).inter_open_nonempty
    _ (isOpen_ball.inter hC) hne
  rw [←hL] at hzL
  have hzU : z∈U := hCU hzC
  let Z := connectedComponentIn Lᶜ z
  have hZU : Z⊆U := by
    have hs := connectedComponentIn_mono z (show Lᶜ⊆Kᶜ from compl_subset_compl.mpr subset_union_left)
    rwa [←connectedComponentIn_eq hzU] at hs
  have hzrad (t : ℝ) (ht : 0<t) (ht₁ : t≤1) : y+t • (z-y)∈Z∩C := by
    let T : Set ℂ := (fun t : ℝ => y+t • (z-y)) '' Ioc 0 1
    have hT : IsPreconnected T := isPreconnected_Ioc.image _ (by fun_prop)
    have hzT : z∈T := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
    have hTL : T⊆Lᶜ := by
      rintro b ⟨s,hs,rfl⟩ hb
      rw [hL] at hb
      exact hzL (hL ▸ (hstable z hzball s hs.1 hs.2).mp hb)
    exact ⟨hT.subset_connectedComponentIn hzT hTL ⟨t,⟨ht,ht₁⟩,rfl⟩,hrad z hzC t ht ht₁⟩
  let V := U\G
  have hV : IsOpen V := hU.sdiff (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
  have hzV : z∈V := ⟨hzU,fun h => hzL (Or.inr h)⟩
  have hVL : V⊆Lᶜ := by
    rintro b ⟨hbU,hbG⟩ (hbK|hbG')
    · exact hUK hbU hbK
    · exact hbG hbG'
  have hcomp : connectedComponentIn V z=Z := by
    apply subset_antisymm (connectedComponentIn_mono z hVL)
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL)
    intro b hb
    exact ⟨hZU hb,fun hbG => connectedComponentIn_subset _ _ hb (Or.inr hbG)⟩
  have haccess : ∃ w : ℂ, ∀ t : ℝ,0<t → t≤1 → x+t • (w-x)∈Z := by
    by_cases hn : Nonempty ι
    · let _ : Nonempty ι := hn
      let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
      let _ : DiscreteTopology (ConnectedComponents V) := inferInstance
      have hxcl := tame_star_center_incident_weak F hF Q hQi hU isPreconnected_connectedComponentIn
        x hx h₀ h₁ hFU ConnectedComponents.continuous_coe
        (ConnectedComponents.mk (⟨z,hzV⟩ : V)) ⟨z,hzV,rfl⟩
      change x∈closure (region V ConnectedComponents.mk (ConnectedComponents.mk (⟨z,hzV⟩ : V))) at hxcl
      rw [component_region_eq,hcomp] at hxcl
      have hxG : x∈G := by
        obtain ⟨i⟩ := hn
        exact mem_iUnion.mpr ⟨i,0,h₀ i⟩
      have hxL : x∈⋃ p∈P∪R,segment ℝ p.1 p.2 := hL ▸ Or.inr hxG
      change x∈closure (connectedComponentIn Lᶜ z) at hxcl
      rw [hL] at hxcl
      obtain ⟨w,_,hw⟩ := component_radial_access (P∪R) hxL hxcl
      exact ⟨w,fun t ht ht₁ => by simpa only [←hL] using hw t ht ht₁⟩
    · have hGe : G=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨i,_⟩ := mem_iUnion.mp hb
        exact hn ⟨i⟩
      have hUL : U⊆Lᶜ := by simpa only [L,hGe,union_empty] using hUK
      have hxZ : x∈Z := isPreconnected_connectedComponentIn.subset_connectedComponentIn hzU hUL hx
      exact ⟨x,fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hxZ⟩
  obtain ⟨w,hw⟩ := haccess
  obtain ⟨c,hc₀,hc₁,hcS,hcZ,hce⟩ := arc_with_terminal_germ hLc.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxy (fun h => hyU (hZU h)) hw hzrad
  have hcV (t : I) (ht₀ : t≠0) (ht₁ : t≠1) : c t∈V := by
    have hh : c t∈Z := hcZ t ht₀ ht₁
    rw [←hcomp] at hh
    exact connectedComponentIn_subset _ _ hh
  refine ⟨c,hc₀,hc₁,hcS,?_,?_,hce⟩
  · rintro b ⟨t,ht,rfl⟩
    exact (hcV t ht.1.ne' ht.2.ne).1
  · intro i s t he
    have hs : s=0 ∨ s=1 := by
      by_contra hn
      exact (hcV s (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))).2
        (mem_iUnion.mpr ⟨i,t,he.symm⟩)
    refine ⟨hs,?_⟩
    rcases hs with rfl|rfl
    · exact Or.inl ((F i).injective (he.symm.trans (hc₀.trans (h₀ i).symm)))
    · by_contra hn
      have htU := hFU i ⟨t,⟨lt_of_le_of_ne (show (0:I) ≤ t from t.property.1)
        (fun h => hn (Or.inl h.symm)),lt_of_le_of_ne (le_one t) (fun h => hn (Or.inr h))⟩,rfl⟩
      exact hyU ((he.symm.trans hc₁) ▸ htU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal

theorem finite_prescribed_star (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (n : ℕ) (y : Fin n → ℂ) (C : Fin n → Set ℂ)
    (hy : ∀ i,y i∈⋃ p∈P,segment ℝ p.1 p.2)
    (hC : ∀ i,IsOpen (C i)) (hyC : ∀ i,y i∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → y i+t • (z-y i)∈C i) :
    ∃ F : Fin n → Arc ℂ,
      Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,F i 0=x) ∧ (∀ i,F i 1=y i) ∧ (∀ i,FiniteSupport (range (F i))) ∧
      (∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (F i)∩ball (y i) ε⊆insert (y i) (C i) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := ih (fun i => y i.succ) (fun i => C i.succ)
      (fun i => hy i.succ) (fun i => hC i.succ) (fun i => hyC i.succ)
      (fun i => hCU i.succ) (fun i => hrad i.succ)
    have h₁' (i : Fin n) : F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a := by
      intro h
      exact connectedComponentIn_subset _ _ h (h₁ i ▸ hy i.succ)
    obtain ⟨c,hc₀,hc₁,hcS,hcU,hcF,hce⟩ := extend_star_in_sector P hx (hy 0) F hF hS h₀ h₁'
      hFU (C 0) (hC 0) (hyC 0) (hCU 0) (hrad 0)
    let F' : Fin (n+1) → Arc ℂ := Fin.cases c F
    refine ⟨F',?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact fun h => (h rfl).elim
        · intro _ s t he
          exact hcF j s t he
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ s t he
          exact (hcF i t s he.symm).symm
        · intro h s t he
          exact hF (fun h' => h (congrArg Fin.succ h')) s t he
    · exact Fin.cases hc₀ h₀
    · exact Fin.cases hc₁ h₁
    · exact Fin.cases hcS hS
    · exact Fin.cases hcU hFU
    · exact Fin.cases hce hgerm
end CannonEmbeddedArc.Arc

namespace CannonSectors
open Set Metric Topology CannonPolygonal CannonSegmentCones

variable {ι : Type*}

lemma radial_vertex_closure {C : Set ℂ} {x : ℂ} (hne : C.Nonempty)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → x+t • (z-x)∈C) : x∈closure C := by
  obtain ⟨z,hz⟩ := hne
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min (1/2:ℝ) (ε/(2*(dist z x+1)))
  have hd : 0<2*(dist z x+1) := by positivity
  have ht : 0<t := lt_min (by norm_num) (div_pos hε hd)
  have ht₁ : t≤1 := (min_le_left ..).trans (by norm_num)
  have htd : t*(2*(dist z x+1))≤ε := (le_div_iff₀ hd).mp (min_le_right ..)
  refine ⟨x+t • (z-x),hrad z hz t ht ht₁,?_⟩
  rw [dist_comm,radial_dist x z ht.le]
  nlinarith [dist_nonneg (x:=z) (y:=x)]

end CannonSectors

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

omit [Finite ι] in
lemma vertex_mem_support (F : ι → Arc ℂ) {v : ℂ} (hv : Vertex F v) :
    v∈⋃ i,range (F i) := by
  obtain ⟨i,hi⟩ := hv
  exact mem_iUnion.mpr ⟨i,hi.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)⟩

omit [Finite ι] in
lemma vertex_parameter (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι) {t : I}
    (ht : Vertex F (F i t)) : t=0 ∨ t=1 := by
  by_contra hn
  push Not at hn
  exact interior_not_vertex F hF i (lt_of_le_of_ne (nonneg t) hn.1.symm)
    (lt_of_le_of_ne (le_one t) hn.2) ht

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

theorem face_vertex_fan (F : ι → Arc ℂ) (P : Finset (ℂ × ℂ))
    (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) {x : ℂ} (hx : x∈face F d) :
    ∃ A : faceVertices F d → Arc ℂ,
      Pairwise (fun u v => Compatible (A u) (A v)) ∧
      (∀ v,A v 0=x) ∧ (∀ v,A v 1=v.val) ∧
      (∀ v,FiniteSupport (range (A v))) ∧
      (∀ v,A v '' Ioo (0:I) 1⊆face F d) := by
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  obtain ⟨a,ha⟩ := ConnectedComponents.surjective_coe d
  have hface : face F d=connectedComponentIn (⋃ p∈Q,segment ℝ p.1 p.2)ᶜ a.val := by
    unfold face
    rw [←ha,component_region_eq]
    exact congrArg (fun K : Set ℂ => connectedComponentIn Kᶜ a.val) hQ
  obtain ⟨A,hA,h₀,h₁,hS,hU⟩ := finite_tame_star Q
    (hQ ▸ (show a.val∉⋃ i,range (F i) from a.property)) (hface ▸ hx) (faceVertices F d) (by
      intro v hv
      obtain ⟨hv,hcl⟩ := (mem_faceVertices F d v).mp hv
      exact ⟨hQ ▸ vertex_mem_support F hv,hface ▸ hcl⟩)
  exact ⟨A,hA,h₀,h₁,hS,fun v => by simpa only [←hface] using hU v⟩

omit [Finite ι] in
lemma fan_parameter_in_face {F : ι → Arc ℂ} {d : Faces F} {a : Arc ℂ}
    (h₀ : a 0∈face F d) (hU : a '' Ioo (0:I) 1⊆face F d) {t : I} (ht : t≠1) :
    a t∈face F d := by
  by_cases h : t=0
  · simpa only [h] using h₀
  · exact hU ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm h),lt_of_le_of_ne (le_one t) ht⟩,rfl⟩

omit [Finite ι] in
lemma old_fan_compatible (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι)
    {d : Faces F} {a : Arc ℂ} (h₀ : a 0∈face F d)
    (h₁ : Vertex F (a 1)) (hU : a '' Ioo (0:I) 1⊆face F d) : Compatible (F i) a := by
  have hend {s t : I} (h : F i s=a t) : t=1 := by
    by_contra ht
    exact (fan_parameter_in_face h₀ hU ht).1 (mem_iUnion.mpr ⟨i,s,h⟩)
  constructor
  · intro s t h
    have ht := hend h
    refine ⟨vertex_parameter F hF i ?_,Or.inr ht⟩
    simpa only [h,ht] using h₁
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    rw [←ht,←hv,hend ht.symm,hend hv.symm]

omit [Finite ι] in
lemma different_face_fans_compatible {F : ι → Arc ℂ} {d e : Faces F} (hde : d≠e)
    {a b : Arc ℂ} (ha₀ : a 0∈face F d) (hb₀ : b 0∈face F e)
    (ha₁ : a 1∈⋃ i,range (F i)) (hb₁ : b 1∈⋃ i,range (F i))
    (haU : a '' Ioo (0:I) 1⊆face F d) (hbU : b '' Ioo (0:I) 1⊆face F e) :
    Compatible a b := by
  have hend {s t : I} (h : a s=b t) : s=1 ∧ t=1 := by
    by_cases hs : s=1
    · refine ⟨hs,?_⟩
      by_contra ht
      exact (fan_parameter_in_face hb₀ hbU ht).1 (by simpa only [←h,hs] using ha₁)
    · have has := fan_parameter_in_face ha₀ haU hs
      by_cases ht : t=1
      · exact (has.1 (by simpa only [h,ht] using hb₁)).elim
      · have hbt := fan_parameter_in_face hb₀ hbU ht
        exact (hde (has.2.symm.trans (by simpa only [h] using hbt.2))).elim
  constructor
  · intro s t h
    exact ⟨Or.inr (hend h).1,Or.inr (hend h).2⟩
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    rw [(hend ht.symm).1,(hend hv.symm).1]

theorem global_vertex_stellation (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) := by
  classical
  choose c hc using face_nonempty F
  choose A hA h₀ h₁ hS hU using fun d => face_vertex_fan F P hP d (hc d)
  refine ⟨c,(fun i => A i.1 i.2),hc,?_,(fun i => h₀ i.1 i.2),
    (fun i => h₁ i.1 i.2),(fun i => hS i.1 i.2),(fun i => hU i.1 i.2)⟩
  intro i j hij
  rcases i with i|⟨d,v⟩ <;> rcases j with j|⟨e,w⟩
  · exact hF (fun h => hij (congrArg Sum.inl h))
  · exact old_fan_compatible F hF i (h₀ e w ▸ hc e)
      (h₁ e w ▸ ((mem_faceVertices F e w.val).mp w.property).1) (hU e w)
  · exact (old_fan_compatible F hF j (h₀ d v ▸ hc d)
      (h₁ d v ▸ ((mem_faceVertices F d v.val).mp v.property).1) (hU d v)).symm
  · by_cases hde : d=e
    · subst e
      exact hA d (fun he => hij (by cases he; rfl))
    · exact different_face_fans_compatible hde (h₀ d v ▸ hc d) (h₀ e w ▸ hc e)
        (h₁ d v ▸ vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1)
        (h₁ e w ▸ vertex_mem_support F ((mem_faceVertices F e w.val).mp w.property).1)
        (hU d v) (hU e w)
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
-- module Solutions.OAIQ046_CN.Cannon_Topology_LabelsConstant
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

namespace CannonClosedCover
open Set

variable {X D J : Type*} [TopologicalSpace X] [Finite J]

theorem labels_constant {S : Set X} (hS : IsPreconnected S) (C : J → Set X)
    (hC : ∀ j,IsClosed (C j)) (hcover : S⊆⋃ j,C j) (hne : ∀ j,(S∩C j).Nonempty)
    (l : J → D) (hcompat : ∀ x∈S,∀ i,x∈C i → ∀ j,x∈C j → l i=l j) :
    ∀ i j,l i=l j := by
  classical
  intro i j
  by_contra hij
  let A := ⋃ k∈{k | l k=l i},C k
  let B := ⋃ k∈{k | l k≠l i},C k
  have hA : IsClosed A := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hB : IsClosed B := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hAB : S⊆A∪B := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases h : l k=l i
    · exact Or.inl (mem_iUnion₂.mpr ⟨k,h,hk⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨k,h,hk⟩)
  obtain ⟨u,hu,huC⟩ := hne i
  obtain ⟨v,hv,hvC⟩ := hne j
  obtain ⟨x,hx,hxa,hxb⟩ := isPreconnected_closed_iff.mp hS A B hA hB hAB
    ⟨u,hu,mem_iUnion₂.mpr ⟨i,rfl,huC⟩⟩
    ⟨v,hv,mem_iUnion₂.mpr ⟨j,Ne.symm hij,hvC⟩⟩
  obtain ⟨k,hk,hkx⟩ := mem_iUnion₂.mp hxa
  obtain ⟨m,hm,hmx⟩ := mem_iUnion₂.mp hxb
  exact hm ((hcompat x hx m hmx k hkx).trans hk)
end CannonClosedCover

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceClosuresCover
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
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*}

lemma face_closures_cover [Finite ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    (⋃ d : Faces F,closure (face F d))=univ := by
  let _ : Finite (Faces F) := faces_finite F hF P hP
  have hd : Dense ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (complex_finite_segments_compl_dense P).mono (compl_subset_compl.mpr (iUnion_subset hP))
  have hh : closure ((⋃ i,range (F i))ᶜ : Set ℂ)⊆⋃ d : Faces F,closure (face F d) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun _ => isClosed_closure)
    intro x hx
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨x,hx⟩,subset_closure ⟨hx,rfl⟩⟩
  rw [hd.closure_eq] at hh
  exact eq_univ_of_univ_subset hh

lemma face_boundary_edges [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) {z : ℂ} (hz : z∈closure (face F d)) (hzK : z∈⋃ i,range (F i)) :
    ∃ i,z∈range (F i) ∧ range (F i)⊆closure (face F d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hh := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  change z∈closure (region _ ConnectedComponents.mk d) at hz
  rw [hh] at hz
  rcases hz with hz|hz
  · exact (hz.1 hzK).elim
  · obtain ⟨i,hi,hiz⟩ := mem_iUnion₂.mp hz
    exact ⟨i,hiz,region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe hi⟩

lemma faceVertices_nontrivial [Finite ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) : (faceVertices F d : Set ℂ).Nontrivial := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
  have hcl := region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe ⟨t,ht₀,ht₁,ht⟩
  exact ⟨F i 0,(mem_faceVertices F d _).mpr ⟨⟨i,Or.inl rfl⟩,hcl (mem_range_self 0)⟩,
    F i 1,(mem_faceVertices F d _).mpr ⟨⟨i,Or.inr rfl⟩,hcl (mem_range_self 1)⟩,(F i).endpoints_ne⟩

lemma arc_label_interval {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} {f : X → Bool} (hf : ContinuousOn f S) {u v : I}
    (huv : u≤v) (hS : ∀ t∈Icc u v,a t∈S) : f (a u)=f (a v) := by
  exact isPreconnected_Icc.constant (hf.comp a.continuous.continuousOn hS)
    (left_mem_Icc.mpr huv) (right_mem_Icc.mpr huv)

lemma arc_punctured_endpoint_label {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} (hS : range a⊆S) {q : X} {f : X → Bool} (hf : ContinuousOn f (S\{q}))
    {t : I} (ht : a t≠q) :
    ∃ e : I,(e=0 ∨ e=1) ∧ a e≠q ∧ f (a t)=f (a e) := by
  classical
  by_cases h : ∀ s∈Icc (0:I) t,a s≠q
  · exact ⟨0,Or.inl rfl,h _ ⟨le_rfl,nonneg t⟩,
      (arc_label_interval a hf (nonneg t) (fun s hs => ⟨hS (mem_range_self s),h s hs⟩)).symm⟩
  · push Not at h
    obtain ⟨s,hs,hsq⟩ := h
    have hst : s<t := lt_of_le_of_ne hs.2 (fun he => ht (he ▸ hsq))
    have hn : ∀ u∈Icc t (1:I),a u≠q := by
      intro u hu he
      have hus := a.injective (he.trans hsq.symm)
      exact (not_lt_of_ge hu.1) (hus.symm ▸ hst)
    exact ⟨1,Or.inr rfl,hn _ ⟨le_one t,le_rfl⟩,
      arc_label_interval a hf (le_one t) (fun s hs => ⟨hS (mem_range_self s),hn s hs⟩)⟩

lemma fan_to_center_label [Finite ι] {F : ι → Arc ℂ} {d : Faces F} {a : Arc ℂ}
    (h₀ : a 0∈face F d) (hU : a '' Ioo (0:I) 1⊆face F d)
    {S : Set ℂ} (hS : range a⊆S) {q : ℂ} (hq : q∈⋃ i,range (F i))
    {f : ℂ → Bool} (hf : ContinuousOn f (S\{q})) {t : I} (ht : a t≠q) :
    f (a t)=f (a 0) := by
  apply (arc_label_interval a hf (nonneg t) ?_).symm
  intro s hs
  refine ⟨hS (mem_range_self s),?_⟩
  intro hsq
  have hs₁ : s=1 := by
    by_contra hn
    exact (fan_parameter_in_face h₀ hU hn).1 (hsq ▸ hq)
  have ht₁ : t=1 := le_antisymm (le_one t) (hs₁ ▸ hs.2)
  exact ht (ht₁.symm ▸ hs₁ ▸ hsq)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem stellar_old_point_no_cut (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (hc : ∀ d,c d∈face F d)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    {q : ℂ} (hq : q∈⋃ i,range (F i)) :
    IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let K := ⋃ i,range (F i)
  let S := K∪⋃ i,range (A i)
  have hAS (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆S :=
    fun z hz => Or.inr (mem_iUnion.mpr ⟨i,hz⟩)
  have hFS (i : ι) : range (F i)⊆S := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hnew (i : Σ d : Faces F,faceVertices F d) {t : I} (ht : A i t≠q) :
      f (A i t)=f (c i.1) := by
    have hh := fan_to_center_label (h₀ i ▸ hc i.1) (hU i) (hAS i) hq hf ht
    rwa [h₀ i] at hh
  have hold (d : Faces F) {z : ℂ} (hz : z∈closure (face F d)) (hzK : z∈K) (hzq : z≠q) :
      f z=f (c d) := by
    obtain ⟨i,⟨t,rfl⟩,hi⟩ := face_boundary_edges F hF P hP d hz hzK
    obtain ⟨e,he,heq,hlabel⟩ := arc_punctured_endpoint_label (F i) (hFS i) hf hzq
    have hv : F i e∈faceVertices F d := by
      apply (mem_faceVertices F d _).mpr
      refine ⟨⟨i,?_⟩,hi (mem_range_self e)⟩
      rcases he with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    let v : faceVertices F d := ⟨F i e,hv⟩
    have hh := hnew ⟨d,v⟩ (t:=1) (by simpa only [h₁] using heq)
    rw [h₁] at hh
    exact hlabel.trans hh
  have hcover : ∀ z : ℂ,∃ d : Faces F,z∈closure (face F d) := by
    intro z
    apply mem_iUnion.mp
    rw [face_closures_cover F hF P hP]
    exact mem_univ z
  have hlabels : ∀ d e : Faces F,f (c d)=f (c e) := by
    apply CannonClosedCover.labels_constant
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) q).isPreconnected
      (fun d => closure (face F d)) (fun _ => isClosed_closure)
      (fun z _ => mem_iUnion.mpr (hcover z))
      (fun d => ⟨c d,(fun he => (hc d).1 (he ▸ hq)),subset_closure (hc d)⟩) (fun d => f (c d))
    intro z hz d hzd e hze
    by_cases hzK : z∈K
    · exact (hold d hzd hzK hz).symm.trans (hold e hze hzK hz)
    · have hzd' := closure_region_inside
        (isClosed_iUnion_of_finite fun j => (F j).compact_range.isClosed).isOpen_compl
        ConnectedComponents.continuous_coe hzd hzK
      have hze' := closure_region_inside
        (isClosed_iUnion_of_finite fun j => (F j).compact_range.isClosed).isOpen_compl
        ConnectedComponents.continuous_coe hze hzK
      have hde : d=e := hzd'.2.symm.trans hze'.2
      rw [hde]
  have hpoint {z : ℂ} (hz : z∈S\{q}) : ∃ d : Faces F,f z=f (c d) := by
    rcases hz.1 with hzK|hzA
    · obtain ⟨d,hd⟩ := hcover z
      exact ⟨d,hold d hd hzK hz.2⟩
    · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzA
      exact ⟨i.1,hnew i hz.2⟩
  obtain ⟨d,hd⟩ := hpoint hx
  obtain ⟨e,he⟩ := hpoint hy
  exact hd.trans ((hlabels d e).trans he.symm)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

lemma face_spoke_avoiding (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : Pairwise (fun i j => Compatible (A i) (A j)))
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    (d : Faces F) {q : ℂ} (hq : q∉⋃ i,range (F i)) (hqc : c d≠q) :
    ∃ v : faceVertices F d,q∉range (A ⟨d,v⟩) := by
  classical
  obtain ⟨x,hx,y,hy,hxy⟩ := faceVertices_nontrivial F hF P hP d
  let v : faceVertices F d := ⟨x,hx⟩
  let w : faceVertices F d := ⟨y,hy⟩
  by_cases hv : q∈range (A ⟨d,v⟩)
  swap
  · exact ⟨v,hv⟩
  refine ⟨w,?_⟩
  rintro ⟨t,ht⟩
  obtain ⟨s,hs⟩ := hv
  have hvw : (⟨d,v⟩ : Σ d : Faces F,faceVertices F d)≠⟨d,w⟩ := by
    intro h
    have hh := Sigma.mk.inj_iff.mp h
    have : v=w := eq_of_heq hh.2
    exact hxy (congrArg Subtype.val this)
  obtain ⟨he,_⟩ := (hA hvw).1 s t (hs.trans ht.symm)
  rcases he with rfl|rfl
  · exact hqc ((h₀ _).symm.trans hs)
  · apply hq
    rw [←hs,h₁]
    exact vertex_mem_support F ((mem_faceVertices F d x).mp hx).1

theorem stellar_new_point_no_cut (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsPreconnected (⋃ i,range (F i)))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : Pairwise (fun i j => Compatible (A i) (A j)))
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    {q : ℂ} (hq : q∉⋃ i,range (F i)) :
    IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  classical
  let K := ⋃ i,range (F i)
  let S := K∪⋃ i,range (A i)
  have hKS : K⊆S\{q} := fun z hz => ⟨Or.inl hz,fun he => hq (he ▸ hz)⟩
  have hAS (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆S :=
    fun z hz => Or.inr (mem_iUnion.mpr ⟨i,hz⟩)
  let i₀ : ι := Classical.choice inferInstance
  let b := F i₀ 0
  have hb : b∈K := mem_iUnion.mpr ⟨i₀,mem_range_self 0⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hold {z : ℂ} (hz : z∈K) : f z=f b := hK.constant (hf.mono hKS) hz hb
  have hcenter {d : Faces F} (hdq : c d≠q) : f (c d)=f b := by
    obtain ⟨v,hv⟩ := face_spoke_avoiding F hF P hP c A hA h₀ h₁ d hq hdq
    have hsub : range (A ⟨d,v⟩)⊆S\{q} := fun z hz =>
      ⟨hAS _ hz,fun he => hv (he ▸ hz)⟩
    have hh := (isPreconnected_range (A ⟨d,v⟩).continuous).constant (hf.mono hsub)
      (mem_range_self (0:I)) (mem_range_self (1:I))
    rw [h₀,h₁] at hh
    exact hh.trans (hold (vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1))
  have hpoint {z : ℂ} (hz : z∈S\{q}) : f z=f b := by
    rcases hz.1 with hzK|hzA
    · exact hold hzK
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzA
    obtain ⟨e,he,heq,hlabel⟩ := arc_punctured_endpoint_label (A i) (hAS i) hf hz.2
    rcases he with rfl|rfl
    · rw [h₀] at heq hlabel
      exact hlabel.trans (hcenter heq)
    · rw [h₁] at hlabel
      exact hlabel.trans (hold (vertex_mem_support F ((mem_faceVertices F i.1 i.2.val).mp i.2.property).1))
  exact (hpoint hx).trans (hpoint hy).symm

theorem global_stellation_no_cut_points (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsPreconnected (⋃ i,range (F i))) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) ∧
      ∀ q : ℂ,IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  obtain ⟨c,A,hc,hA,h₀,h₁,hS,hU⟩ := global_vertex_stellation F hF P hP
  refine ⟨c,A,hc,hA,h₀,h₁,hS,hU,?_⟩
  intro q
  by_cases hq : q∈⋃ i,range (F i)
  · exact stellar_old_point_no_cut F hF P hP c hc A h₀ h₁ hU hq
  · exact stellar_new_point_no_cut F hF P hP hK c A
      (fun _ _ hne => hA (fun h => hne (Sum.inr_injective h))) h₀ h₁ hq
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_interior_complement_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (e : ι)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    IsPreconnected ((⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  let m : I := ⟨1/2,by norm_num,by norm_num⟩
  have hm₀ : (0:I) < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < (1:I) := by change (1/2:ℝ)<1; norm_num
  let q := F e m
  let S : Set ℂ := (⋃ i,range (F i))\{q}
  have hR₀ : F e 0∈R := Or.inr (by simp)
  have hR₁ : F e 1∈R := Or.inr (by simp)
  have hRi (i : {i : ι // i≠e}) : range (F i.val)⊆R := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  have hnot (i : {i : ι // i≠e}) : q∉range (F i.val) := by
    rintro ⟨t,ht⟩
    rcases ((hF i.property).1 t m ht).2 with h|h
    · exact hm₀.ne' h
    · exact hm₁.ne h
  have hRS : R⊆S := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i.val,hzi⟩,fun he => hnot i (he ▸ hzi)⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 0⟩,fun he => hm₀.ne ((F e).injective he)⟩
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 1⟩,fun he => hm₁.ne ((F e).injective he).symm⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  let C : ({i : ι // i≠e}⊕Bool) → Set ℂ := Sum.elim (fun i => range (F i.val))
    (fun b => if b then F e '' Icc m (1:I) else F e '' Icc (0:I) m)
  let l : ({i : ι // i≠e}⊕Bool) → Bool := Sum.elim (fun i => f (F i.val 0))
    (fun b => if b then f (F e 1) else f (F e 0))
  have hclosed : ∀ j,IsClosed (C j) := by
    rintro (i|b)
    · exact (F i.val).compact_range.isClosed
    · cases b <;> exact (isCompact_Icc.image (F e).continuous).isClosed
  have hcover : S⊆⋃ j,C j := by
    rintro z ⟨hz,hzq⟩
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
    by_cases hi : i=e
    · subst i
      rcases le_total t m with ht|ht
      · exact mem_iUnion.mpr ⟨Sum.inr false,⟨t,⟨nonneg t,ht⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨Sum.inr true,⟨t,⟨ht,le_one t⟩,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨i,hi⟩,mem_range_self t⟩
  have hne : ∀ j,(S∩C j).Nonempty := by
    rintro (i|b)
    · exact ⟨F i.val 0,hRS (hRi i (mem_range_self 0)),mem_range_self 0⟩
    · cases b
      · exact ⟨F e 0,hRS hR₀,⟨0,⟨le_rfl,hm₀.le⟩,rfl⟩⟩
      · exact ⟨F e 1,hRS hR₁,⟨1,⟨hm₁.le,le_rfl⟩,rfl⟩⟩
  have hlabel (i : {i : ι // i≠e}) {z : ℂ} (hz : z∈C (Sum.inl i)) :
      f z=l (Sum.inl i) :=
    (isPreconnected_range (F i.val).continuous).constant (hf.mono (hRi i)) hz (mem_range_self 0)
  have holdnew (i : {i : ι // i≠e}) (b : Bool) {z : ℂ}
      (hzi : z∈C (Sum.inl i)) (hzb : z∈C (Sum.inr b)) :
      l (Sum.inl i)=l (Sum.inr b) := by
    obtain ⟨s,rfl⟩ := hzi
    cases b
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₀ : t=0 := ((hF i.property).1 s t he.symm).2.resolve_right
        (fun h => hm₁.not_ge (h ▸ ht.2))
      have hz : F i.val s=F e 0 := ht₀ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₁ : t=1 := ((hF i.property).1 s t he.symm).2.resolve_left
        (fun h => hm₀.not_ge (h ▸ ht.1))
      have hz : F i.val s=F e 1 := ht₁ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
  have hall : ∀ i j,l i=l j := by
    apply CannonClosedCover.labels_constant (hK q) C hclosed hcover hne l
    intro z hz i hzi j hzj
    rcases i with i|b <;> rcases j with j|c
    · exact (hlabel i hzi).symm.trans (hlabel j hzj)
    · exact holdnew i c hzi hzj
    · exact (holdnew j b hzj hzi).symm
    · cases b <;> cases c
      · rfl
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm hs.2 (hts ▸ ht.1)
        exact (hz.2 (congrArg (F e) hsm)).elim
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm (hts ▸ ht.2) hs.1
        exact (hz.2 (congrArg (F e) hsm)).elim
      · rfl
  have hvalue {z : ℂ} (hz : z∈R) : f z=l (Sum.inr false) := by
    rcases hz with hz|hz
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact (hlabel i hzi).trans (hall _ _)
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · rfl
      · exact hall (Sum.inr true) _
  exact (hvalue hx).trans (hvalue hy).symm
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_on_tame_cycle (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ b : Arc ℂ,b 0=F e 0 ∧ b 1=F e 1 ∧
      range b⊆⋃ i,range (F i) ∧ FiniteSupport (range b) ∧
      ∀ s t,F e s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  have hR : IsPreconnected R := edge_interior_complement_preconnected F hF e hK
  obtain ⟨P,hP⟩ := finite_graph_exact_segments (fun i : {i : ι // i≠e} => F i.val) Q (fun i => hQ i.val)
  let T := P∪{(F e 0,F e 0),(F e 1,F e 1)}
  have hT : R=⋃ p∈T,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hP]
    apply congrArg (fun S : Set ℂ => (⋃ i : {i : ι // i≠e},range (F i.val))∪S)
    ext z
    constructor
    · intro hz
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion₂.mpr ⟨(F e 0,F e 0),Finset.mem_insert_self ..,left_mem_segment ..⟩
      · exact mem_iUnion₂.mpr ⟨(F e 1,F e 1),Finset.mem_insert_of_mem (Finset.mem_singleton_self _),left_mem_segment ..⟩
    · intro hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      rcases Finset.mem_insert.mp hp with rfl|hp
      · exact Or.inl (by simpa only [segment_same,mem_singleton_iff] using hz)
      · have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (by simpa only [segment_same,mem_singleton_iff] using hz)
  obtain ⟨b,hb₀,hb₁,hbT,hbS⟩ := preconnected_finite_segments_arc T (hT ▸ hR)
    (hT ▸ (show F e 0∈R from Or.inr (by simp)))
    (hT ▸ (show F e 1∈R from Or.inr (by simp))) (F e).endpoints_ne
  have hbR : range b⊆R := by rwa [←hT] at hbT
  have hRK : R⊆⋃ i,range (F i) := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i.val,hzi⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion.mpr ⟨e,mem_range_self 0⟩
      · exact mem_iUnion.mpr ⟨e,mem_range_self 1⟩
  refine ⟨b,hb₀,hb₁,hbR.trans hRK,hbS,?_⟩
  intro s t he
  have hs : s=0 ∨ s=1 := by
    have hbs : F e s∈R := he.symm ▸ hbR (mem_range_self t)
    rcases hbs with hbs|hbs
    · obtain ⟨i,u,hu⟩ := mem_iUnion.mp hbs
      exact ((hF i.property).1 u s hu).2
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hbs : F e s=F e 0 ∨ F e s=F e 1) with h|h
      · exact Or.inl ((F e).injective h)
      · exact Or.inr ((F e).injective h)
  refine ⟨hs,?_⟩
  rcases hs with rfl|rfl
  · exact Or.inl (b.injective (he.symm.trans hb₀.symm))
  · exact Or.inr (b.injective (he.symm.trans hb₁.symm))
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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_FlatChartBoundaryPatch
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
open Set Topology Metric

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
theorem flat_chart_boundary_patch {V W : Set X} {π : V → D} (hπ : Continuous π)
    (H : (ℝ × ℝ) ≃ₜ X) (hW : IsOpen W) (h₀ : H (0,0)∈W)
    (hflat : ∀ z∈W, z∈V ↔ (H.symm z).2≠0)
    {d : D} (hd : d∈incident V π (H (0,0))) :
    ∃ U B : Set X, IsOpen U ∧ H (0,0)∈U ∧ U⊆W ∧
      IsConnected B ∧ B⊆W∩region V π d ∧ U∩Vᶜ⊆closure B := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage H.continuous).mem_nhds h₀)
  let C := openBox r
  let U := H '' C
  have hCU : C⊆H ⁻¹' W := by rw [show C=openBox r from rfl,openBox_eq_ball]; exact hball
  have hUW : U⊆W := by rintro _ ⟨p,hp,rfl⟩; exact hCU hp
  have hU : IsOpen U := H.isOpenMap C (by rw [show C=openBox r from rfl,openBox_eq_ball]; exact isOpen_ball)
  have h₀U : H (0,0)∈U := ⟨(0,0),by rw [show C=openBox r from rfl,openBox_eq_ball]; exact mem_ball_self hr,rfl⟩
  let S : Bool → Set X := fun b => H '' halfBox r b
  have hSc (b : Bool) : IsConnected (S b) :=
    (halfBox_connected hr b).image H H.continuous.continuousOn
  have hcover : U∩V=⋃ b, S b := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpV⟩
      have hp₂ : p.2≠0 := by simpa using (hflat (H p) (hCU hp)).mp hpV
      rcases lt_or_gt_of_ne hp₂ with hl|hr'
      · exact mem_iUnion.mpr ⟨false,⟨p,⟨hp.1,hp.2.1,hl⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨true,⟨p,⟨hp.1,hr',hp.2.2⟩,rfl⟩⟩
    · intro hx
      obtain ⟨b,p,hp,rfl⟩ := mem_iUnion.mp hx
      have hpC : p∈C := by
        cases b
        · exact ⟨hp.1,hp.2.1,hp.2.2.trans hr⟩
        · exact ⟨hp.1,(neg_neg_of_pos hr).trans hp.2.1,hp.2.2⟩
      refine ⟨⟨p,hpC,rfl⟩,(hflat (H p) (hCU hpC)).mpr ?_⟩
      simp only [H.symm_apply_apply]
      cases b
      · exact hp.2.2.ne
      · exact hp.2.1.ne'
  have hclose (b : Bool) : U∩Vᶜ⊆closure (S b) := by
    rintro x ⟨⟨p,hp,hpx⟩,hxV⟩
    subst x
    have hp₂ : p.2=0 := by
      by_contra h
      apply hxV
      apply (hflat (H p) (hCU hp)).mpr
      simpa using h
    rw [show S b=H '' halfBox r b from rfl,←H.image_closure]
    exact ⟨p,halfBox_closure hr hp hp₂ b,rfl⟩
  obtain ⟨labels,hsub,hlabels⟩ := sector_incidence hU inter_subset_left hπ S hSc hcover hclose
  have hnv : H (0,0)∉V := by
    intro h
    have hh := (hflat _ h₀).mp h
    simp at hh
  have hh := hlabels (H (0,0)) ⟨h₀U,hnv⟩
  obtain ⟨b,hb⟩ := hh ▸ hd
  refine ⟨U,S b,hU,h₀U,hUW,hSc b,?_,hclose b⟩
  intro z hz
  refine ⟨hUW ?_,hb ▸ hsub b hz⟩
  exact (hcover.symm ▸ mem_iUnion_of_mem b hz).1
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoncutCycleFreeRegion
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
open Set Topology Metric unitInterval CannonFaceIncidence

theorem noncut_cycle_free_region {K : Set ℂ}
    (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hb : range b⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : IsConnected (K\{a 1}))
    (hCK : (range a∪range b)\{a 1}⊆Kᶜ) :
    ∃ d : ConnectedComponents ((range a∪range b)ᶜ : Set ℂ),
      (∀ z∈range a∪range b,d∈incident _ ConnectedComponents.mk z) ∧
      closure (region _ ConnectedComponents.mk d)\{a 1}⊆connectedComponentIn Kᶜ (a 0) := by
  let C : Set ℂ := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  have hqC : a 1∈C := Or.inl (mem_range_self 1)
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  have hKC : K\{a 1}⊆Cᶜ := by
    intro z hz hzC
    exact hCK ⟨hzC,hz.2⟩ hz.1
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe hK hKC
  let i := l.symm d
  let e := l (!i)
  let R := region Cᶜ ConnectedComponents.mk e
  have hRconn : IsConnected R := component_region_connected _ _
  have hRi : R⊆Kᶜ := by
    intro z hz hzK
    have hzq : z≠a 1 := fun h => (region_subset _ _ _ hz) (h.symm ▸ hqC)
    obtain ⟨_,he⟩ := hd ⟨hzK,hzq⟩
    obtain ⟨_,he'⟩ := hz
    have hh : (!i)=i := l.injective (he'.symm.trans (he.trans (l.apply_symm_apply d).symm))
    cases i <;> simp at hh
  have hRcl : closure R=R∪C := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzC : z∈C
      · exact Or.inr hzC
      · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hz hzC)
    · apply union_subset subset_closure
      intro z hz
      change e∈incident _ ConnectedComponents.mk z
      rw [hl z hz]
      exact mem_range_self (!i)
  have hRnoq : R⊆closure R\{a 1} := by
    intro z hz
    exact ⟨subset_closure hz,fun he => (region_subset _ _ _ hz) (he.symm ▸ hqC)⟩
  have hpre : IsPreconnected (closure R\{a 1}) :=
    hRconn.isPreconnected.subset_closure hRnoq sdiff_subset
  have hsub : closure R\{a 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rw [hRcl] at hz
    exact hz.elim (fun h => hRi h) (fun h => hCK ⟨h,hzq⟩)
  have hxcl : a 0∈closure R\{a 1} := by
    rw [hRcl]
    exact ⟨Or.inr (Or.inl (mem_range_self 0)),a.endpoints_ne⟩
  refine ⟨e,?_,hpre.subset_connectedComponentIn hxcl hsub⟩
  intro z hz
  rw [hl z hz]
  exact mem_range_self (!i)
end CannonEmbeddedArc.Arc

namespace CannonSegmentCones
open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_component_radial {K : Set E} {q : E} {r : ℝ}
    (hstable : RadialStable K q r) {a z : E}
    (hz : z∈connectedComponentIn (ball q r\K) a) {t : ℝ} (ht : 0<t) (ht₁ : t≤1) :
    q+t • (z-q)∈connectedComponentIn (ball q r\K) a := by
  let S : Set E := (fun u : ℝ => q+u • (z-q)) '' Ioc 0 1
  have hzV := connectedComponentIn_subset (ball q r\K) a hz
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hSV : S⊆ball q r\K := by
    rintro w ⟨u,hu,rfl⟩
    exact ⟨radial_mem_ball hzV.1 hu.1.le hu.2,fun h => hzV.2 ((hstable z hzV.1 u hu.1 hu.2).mp h)⟩
  have hzS : z∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSC := hS.subset_connectedComponentIn hzS hSV
  have he := connectedComponentIn_eq hz
  rw [←he] at hSC
  exact hSC ⟨t,⟨ht,ht₁⟩,rfl⟩
end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_radial_germs_join (P : Finset (ℂ × ℂ)) {q a x : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Fin 2 → Set ℂ) (hC : ∀ i,IsOpen (C i)) (hqC : ∀ i,q∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i)
    {r : ℝ} (hr : 0 < r) :
    ∃ B : Set ℂ,IsConnected B ∧
      B⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r ∧
      ∀ i,(B∩C i).Nonempty := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := finite_prescribed_star P hx 2 (fun _ => q) C
    (fun _ => hqK) hC hqC hCU hrad
  let b := F 0
  let c := F 1
  have hbc₀ : b 0=c 0 := (h₀ 0).trans (h₀ 1).symm
  have hbc₁ : b 1=c 1 := (h₁ 0).trans (h₁ 1).symm
  have hbc : ∀ s t,b s=c t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := hF (by decide : (0:Fin 2)≠1)
  obtain ⟨Q,hQ⟩ := (hS 0).union (hS 1)
  have hbQ : range b⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inl hz)
  have hcQ : range c⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inr hz)
  have hFnot (i : Fin 2) {t : I} (ht : t≠1) : F i t∈U := by
    by_cases ht₀ : t=0
    · simpa only [ht₀,h₀] using hx
    · exact hFU i ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
        lt_of_le_of_ne (le_one t) ht⟩,rfl⟩
  have hCK : (range b∪range c)\{b 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rcases hz with ⟨t,rfl⟩|⟨t,rfl⟩
    · exact connectedComponentIn_subset Kᶜ a (hFnot 0 (fun he => hzq (congrArg b he)))
    · exact connectedComponentIn_subset Kᶜ a (hFnot 1 (fun he => hzq ((congrArg c he).trans hbc₁.symm)))
  have hconn : IsConnected (K\{b 1}) := by simpa only [b,h₁] using hK
  obtain ⟨d,hd,hfree⟩ := noncut_cycle_free_region b c hbc₀ hbc₁ hbc Q hbQ hcQ hconn hCK
  have hBU : closure (region _ ConnectedComponents.mk d)\{q}⊆U := by
    have he : connectedComponentIn Kᶜ (b 0)=U := by
      rw [show b 0=x from h₀ 0]
      exact (connectedComponentIn_eq hx).symm
    simpa only [show b 1=q from h₁ 0,he] using hfree
  let L : Set ℂ := range b∪range c
  have hL : IsClosed L := b.compact_range.isClosed.union c.compact_range.isClosed
  let _ : LocallyConnectedSpace (Lᶜ : Set ℂ) := hL.isOpen_compl.locallyConnectedSpace
  obtain ⟨H,W,hW,hqW,hH,hflat⟩ := pair_flat_at_left b c hbc₀ hbc₁ hbc Q hbQ hcQ 1
  have hHq : H (0,0)=q := hH.trans (h₁ 0)
  have hqW' : q∈W∩ball q r := ⟨(h₁ 0) ▸ hqW,mem_ball_self hr⟩
  have hflat' : ∀ z∈W∩ball q r,z∈Lᶜ ↔ (H.symm z).2≠0 := by
    intro z hz
    rw [mem_compl_iff,hflat z hz.1]
    have hh : z∈H '' CannonPlanarCorner.horizontal ↔ (H.symm z).2=0 := by
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [H.symm_apply_apply,CannonPlanarCorner.horizontal,mem_ofPred_eq] using hy
      · intro hy
        exact ⟨H.symm z,hy,H.apply_symm_apply z⟩
    rw [hh]
  obtain ⟨V,B,hV,hqV,hVW,hB,hBW,hBcl⟩ := flat_chart_boundary_patch
    ConnectedComponents.continuous_coe H (hW.inter isOpen_ball) (hHq.symm ▸ hqW') hflat'
    (d:=d) (by rw [hHq]; exact hd q (Or.inl ⟨1,h₁ 0⟩))
  have hqV' : q∈V := hHq ▸ hqV
  have hBV : B⊆U∩ball q r := by
    intro z hz
    have hh := hBW hz
    refine ⟨hBU ⟨subset_closure hh.2,?_⟩,hh.1.2⟩
    intro he
    exact (region_subset _ _ _ hh.2) (he.symm ▸ Or.inl ⟨1,h₁ 0⟩)
  refine ⟨B,hB,hBV,?_⟩
  intro i
  obtain ⟨ε,hε,hεg⟩ := hgerm i
  let N := V∩ball q ε
  have hN : IsOpen N := hV.inter isOpen_ball
  have hqN : q∈N := ⟨hqV',mem_ball_self hε⟩
  obtain ⟨t,ht,htN⟩ := (dense_compl_singleton (1:I)).exists_mem_open
    ((F i).continuous.isOpen_preimage N hN) ⟨1,by change F i 1∈N; rw [h₁]; exact hqN⟩
  have htq : F i t≠q := fun he => ht ((F i).injective (he.trans (h₁ i).symm))
  have htC : F i t∈C i := (hεg ⟨mem_range_self t,htN.2⟩).resolve_left htq
  have htL : F i t∈L := by
    fin_cases i
    · exact Or.inl (mem_range_self t)
    · exact Or.inr (mem_range_self t)
  have htcl : F i t∈closure B := hBcl ⟨htN.1,by simpa only [compl_compl] using htL⟩
  obtain ⟨z,hzC,hzB⟩ := (mem_closure_iff_nhds.mp htcl) (C i) ((hC i).mem_nhds htC)
  exact ⟨z,hzB,hzC⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_face_ball_preconnected (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    {r : ℝ} (hr : 0 < r) (hstable : RadialStable (⋃ p∈P,segment ℝ p.1 p.2) q r) :
    ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r) := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  have hKclosed : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  let V := ball q r\K
  have hV : IsOpen V := isOpen_ball.sdiff hKclosed
  intro a
  let U := connectedComponentIn Kᶜ a
  by_cases hne : (U∩ball q r).Nonempty
  · obtain ⟨x,hxU,hxr⟩ := hne
    have hxV : x∈V := ⟨hxr,connectedComponentIn_subset Kᶜ a hxU⟩
    have hsub {z : ℂ} (hz : z∈U∩ball q r) : connectedComponentIn V z⊆U∩ball q r := by
      have hzV : z∈V := ⟨hz.2,connectedComponentIn_subset Kᶜ a hz.1⟩
      have h := (isPreconnected_connectedComponentIn (F:=V) (x:=z)).subset_connectedComponentIn
        (mem_connectedComponentIn hzV) (fun w hw => (connectedComponentIn_subset V z hw).2)
      have he : U=connectedComponentIn Kᶜ z := connectedComponentIn_eq hz.1
      change connectedComponentIn V z⊆connectedComponentIn Kᶜ z at h
      rw [←he] at h
      exact fun w hw => ⟨h hw,(connectedComponentIn_subset V z hw).1⟩
    have heq : U∩ball q r=connectedComponentIn V x := by
      apply Subset.antisymm ?_ (hsub ⟨hxU,hxr⟩)
      intro y hy
      let Z : Fin 2 → ℂ := ![x,y]
      have hZ : ∀ i,Z i∈U∩ball q r := by
        intro i
        fin_cases i
        · exact ⟨hxU,hxr⟩
        · exact hy
      let C : Fin 2 → Set ℂ := fun i => connectedComponentIn V (Z i)
      have hZV (i : Fin 2) : Z i∈V := ⟨(hZ i).2,connectedComponentIn_subset Kᶜ a (hZ i).1⟩
      have hCopen (i : Fin 2) : IsOpen (C i) := hV.connectedComponentIn
      have hCrad (i : Fin 2) : ∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i :=
        fun _ hz _ ht ht₁ => local_component_radial hstable hz ht ht₁
      have hCcl (i : Fin 2) : q∈closure (C i) := CannonSectors.radial_vertex_closure
        ⟨Z i,mem_connectedComponentIn (hZV i)⟩ (hCrad i)
      have hCU (i : Fin 2) : C i⊆U := (hsub (hZ i)).trans inter_subset_left
      obtain ⟨B,hB,hBV,hBC⟩ := noncut_radial_germs_join P hqK hK hxU C hCopen hCcl hCU hCrad hr
      obtain ⟨z,hzB,hzC⟩ := hBC 0
      have hBV' : B⊆V := fun w hw => ⟨(hBV hw).2,connectedComponentIn_subset Kᶜ a (hBV hw).1⟩
      have hBC₀ := hB.isPreconnected.subset_connectedComponentIn hzB hBV'
      have he₀ : C 0=connectedComponentIn V z := connectedComponentIn_eq hzC
      rw [←he₀] at hBC₀
      obtain ⟨w,hwB,hwC⟩ := hBC 1
      have he₁ : C 1=connectedComponentIn V w := connectedComponentIn_eq hwC
      have he₂ : C 0=connectedComponentIn V w := connectedComponentIn_eq (hBC₀ hwB)
      have hyC : y∈C 1 := mem_connectedComponentIn (hZV 1)
      rw [he₁,←he₂] at hyC
      exact hyC
    rw [heq]
    exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty
theorem noncut_locally_connected_faces (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q})) :
    ∃ r>0,∀ s : ℝ,0 < s → s ≤ r → ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q s) := by
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable P q
  exact ⟨r,hr,fun _ hs hsr => noncut_face_ball_preconnected P hqK hK hs (hstable.mono_radius hsr)⟩
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
open Set unitInterval Topology Metric CannonFaceIncidence CannonCircleBoundary

variable {ι : Type*} [Finite ι]

lemma tame_incident_segment (a : Arc ℂ) (P : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) {q : ℂ} (hq : q=a 0 ∨ q=a 1) :
    ∃ p : ℂ,p≠q ∧ segment ℝ q p⊆range a := by
  have first (a : Arc ℂ) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) :
      ∃ p : ℂ,p≠a 0 ∧ segment ℝ (a 0) p⊆range a := by
    obtain ⟨t,ht,he⟩ := tame_initial_interval a P ha
    exact ⟨a t,a.injective.ne ht.ne',he ▸ image_subset_range _ _⟩
  rcases hq with rfl|rfl
  · exact first a ha
  · simpa only [reverse_zero,reverse_range] using first a.reverse (by simpa only [reverse_range] using ha)

lemma radial_mem_segment {q p : ℂ} (hp : p≠q) {s : ℝ}
    (hs : 0 ≤ s) (hsp : s ≤ ‖p-q‖) :
    q+s • (radialDirection q ⟨p,hp⟩:ℂ)∈segment ℝ q p := by
  have hn : 0<‖p-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  rw [segment_eq_image']
  refine ⟨s/‖p-q‖,⟨div_nonneg hs hn.le,(div_le_one hn).mpr hsp⟩,?_⟩
  simp only [radialDirection,smul_smul,div_eq_mul_inv]

theorem noncut_face_degree_two (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    (e : Fin 3 → ι) (he : Function.Injective e)
    (heq : ∀ k,q∈range (F (e k)))
    (heface : ∀ k,e k∈regionEdges F ConnectedComponents.mk d) : False := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hqK : q∈K := vertex_mem_support F hq
  have hep (k : Fin 3) : q=F (e k) 0 ∨ q=F (e k) 1 := by
    obtain ⟨t,ht⟩ := heq k
    have hh := vertex_parameter F hF (e k) (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  choose p hp hps using fun k => tame_incident_segment (F (e k)) P (hP (e k)) (hep k)
  let u : Fin 3 → UnitCircle := fun k => radialDirection q ⟨p k,hp k⟩
  have hn (k : Fin 3) : 0<‖p k-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hp k))
  have hui : Function.Injective u := by
    intro i j hij
    by_contra hne
    let s := min ‖p i-q‖ ‖p j-q‖/2
    have hs : 0 < s := half_pos (lt_min (hn i) (hn j))
    have hsi : s≤‖p i-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_left _ _)
    have hsj : s≤‖p j-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_right _ _)
    have hz₁ : q+s • (u i:ℂ)∈range (F (e i)) := hps i (radial_mem_segment (hp i) hs.le hsi)
    have hz₂ : q+s • (u i:ℂ)∈range (F (e j)) := by
      rw [hij]
      exact hps j (radial_mem_segment (hp j) hs.le hsj)
    exact radial_ne q (u i) hs ((hF (he.ne hne)).2 ⟨hz₁,hz₂⟩ ⟨heq i,heq j⟩)
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  have hKc : IsConnected (K\{q}) := by
    obtain ⟨z,hz,-,hzq⟩ := graph_no_isolated F hqK isOpen_univ (mem_univ _)
    exact ⟨⟨z,hz,hzq⟩,hK⟩
  have hqQ : q∈⋃ p∈Q,segment ℝ p.1 p.2 := by rw [←hQ]; exact hqK
  have hKQ : IsConnected ((⋃ p∈Q,segment ℝ p.1 p.2)\{q}) := by rw [←hQ]; exact hKc
  obtain ⟨R,hR,hlocal⟩ := noncut_locally_connected_faces Q hqQ hKQ
  let r := min R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
  have hr : 0 < r := lt_min hR (lt_min (hn 0) (lt_min (hn 1) (hn 2)))
  have hrR : r≤R := min_le_left _ _
  have hrp (k : Fin 3) : r≤‖p k-q‖ := by
    have hh := min_le_right R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
    fin_cases k
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  let U := face F d∩ball q r
  have hU : IsPreconnected U := by
    obtain ⟨a,ha⟩ := ConnectedComponents.surjective_coe d
    have hh := hlocal r hr hrR a.val
    rw [←hQ] at hh
    simpa only [U,face,←ha,component_region_eq] using hh
  have hUball : U⊆ball q r\{q} := by
    intro z hz
    exact ⟨hz.2,fun heq => hz.1.1 (heq ▸ hqK)⟩
  apply radial_face_degree_two hU hUball u ?_ ?_ hui
  · intro k s hs hsr hz
    exact hz.1.1 (mem_iUnion.mpr ⟨e k,hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k)))⟩)
  · intro k
    have hs : 0 < r/2 := half_pos hr
    have hsr : r/2 < r := half_lt_self hr
    let z := q+(r/2) • (u k:ℂ)
    have hzr : z∈ball q r := by
      have hu : ‖(u k:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp (u k).property
      simpa only [z,mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_pos hs,hu,mul_one] using hsr
    have hzcl : z∈closure (face F d) :=
      region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe (heface k)
        (hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k))))
    refine ⟨r/2,hs,?_⟩
    change z∈closure (face F d∩ball q r)
    rw [inter_comm]
    exact isOpen_ball.inter_closure ⟨hzr,hzcl⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma cycle_edge_otherpoint (a b : Arc ℂ) (h₀ : b 0=a 0) (h₁ : b 1=a 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {q : ℂ} (hq : q=a 0 ∨ q=a 1) {W : Set ℂ} (hW : IsOpen W) (hqW : q∈W) :
    ∃ z∈range b,z∈W ∧ z∉range a := by
  have first (t : I) (ht : q=b t) (hqt : t∈closure (Ioo (0:I) 1)) :
      ∃ z∈range b,z∈W ∧ z∉range a := by
    obtain ⟨s,hsW,hs⟩ := (mem_closure_iff_nhds.mp hqt) (b ⁻¹' W)
      ((hW.preimage b.continuous).mem_nhds (show b t∈W from ht ▸ hqW))
    refine ⟨b s,mem_range_self s,hsW,?_⟩
    rintro ⟨u,hu⟩
    exact ((hc u s hu).2).elim hs.1.ne' hs.2.ne
  rcases hq with h|h
  · apply first 0 (h.trans h₀.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl,zero_le_one⟩
  · apply first 1 (h.trans h₁.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one,le_rfl⟩

theorem noncut_face_second_edge (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (d : Faces F) {q : ℂ} (hq : Vertex F q) {e : ι}
    (he : e∈regionEdges F ConnectedComponents.mk d) (heq : q∈range (F e)) :
    ∃ j : ι,j≠e ∧ j∈regionEdges F ConnectedComponents.mk d ∧ q∈range (F j) := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let B : Set ℂ := ⋃ i∈E,range (F i)
  let T : Set ℂ := ⋃ i∈E\{e},range (F i)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  by_contra hn
  push Not at hn
  have hqT : q∉T := by
    intro hh
    obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp hh
    exact hn j hj.2 hj.1 hqj
  have hep : q=F e 0 ∨ q=F e 1 := by
    obtain ⟨t,ht⟩ := heq
    have hh := vertex_parameter F hF e (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  have hw : ∃ W : Set ℂ,IsOpen W ∧ q∈W ∧ W⊆Tᶜ ∧ IsConnected (W\range (F e)) := by
    rcases hep with h|h
    · exact h.symm ▸ tame_tip_connected_neighborhood (F e) P (hP e) hT.isOpen_compl (h ▸ hqT)
    · have hh := tame_tip_connected_neighborhood (F e).reverse P
        (by simpa only [reverse_range] using hP e) hT.isOpen_compl
        (by simpa only [reverse_zero] using h ▸ hqT)
      simpa only [reverse_range,reverse_zero,←h] using hh
  obtain ⟨W,hW,hqW,hWT,hconn⟩ := hw
  have hB (z : ℂ) (hz : z∈W\range (F e)) : z∉B := by
    intro hh
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hh
    by_cases hie : i=e
    · exact hz.2 (hie ▸ hzi)
    · exact hWT hz.1 (mem_iUnion₂.mpr ⟨i,⟨hi,hie⟩,hzi⟩)
  have hcl : closure (face F d)=face F d∪B :=
    tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  have hcover : W\range (F e)⊆face F d∪(closure (face F d))ᶜ := by
    intro z hz
    by_cases hzu : z∈face F d
    · exact Or.inl hzu
    · refine Or.inr ?_
      rw [hcl]
      exact fun h => h.elim hzu (hB z hz)
  have hdis : Disjoint (face F d) (closure (face F d))ᶜ :=
    disjoint_left.mpr (fun _ hu hcl => hcl (subset_closure hu))
  have hh := hconn.isPreconnected.subset_or_subset (face_open F d) isClosed_closure.isOpen_compl hdis hcover
  have hqcl : q∈closure (face F d) := region_edge_in_closure F hF P hP
    ConnectedComponents.continuous_coe he heq
  obtain ⟨x,hxW,hxU⟩ := (mem_closure_iff_nhds.mp hqcl) W (hW.mem_nhds hqW)
  have hx : x∈W\range (F e) := ⟨hxW,fun h => hxU.1 (mem_iUnion.mpr ⟨e,h⟩)⟩
  obtain ⟨b,hb₀,hb₁,hbK,-,hbc⟩ := edge_on_tame_cycle F hF P hP hK e
  obtain ⟨z,hzb,hzW,hza⟩ := cycle_edge_otherpoint (F e) b hb₀ hb₁ hbc hep hW hqW
  rcases hh with hh|hh
  · exact (hh ⟨hzW,hza⟩).1 (hbK hzb)
  · exact hh hx (subset_closure hxU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma Spans.mem_left {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : x∈range a := by
  rcases h with h|h
  · exact ⟨0,h.1⟩
  · exact ⟨1,h.1⟩
lemma Spans.mem_right {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : y∈range a := h.symm.mem_left
lemma Spans.vertex_left [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F x :=
  ⟨i,h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)⟩
lemma Spans.vertex_right [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F y :=
  h.symm.vertex_left
lemma Spans.other_unique {a : Arc ℂ} {x y z : ℂ} (h : Spans a x y) (h' : Spans a x z) : y=z := by
  rcases h with h|h <;> rcases h' with h'|h'
  · exact h.2.symm.trans h'.2
  · exact (a.endpoints_ne (h.1.trans h'.1.symm)).elim
  · exact (a.endpoints_ne (h'.1.trans h.1.symm)).elim
  · exact h.2.symm.trans h'.2
lemma spans_edge_unique [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i j : ι} {x y : ℂ}
    (hi : Spans (F i) x y) (hj : Spans (F j) x y) : i=j := by
  by_contra hn
  exact hi.ne ((hF hn).2 ⟨hi.mem_left,hj.mem_left⟩ ⟨hi.mem_right,hj.mem_right⟩)
lemma vertex_spans [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {q : ℂ}
    (hq : Vertex F q) {i : ι} (hi : q∈range (F i)) : ∃ z,Spans (F i) q z := by
  obtain ⟨t,ht⟩ := hi
  rcases vertex_parameter F hF i (ht.symm ▸ hq) with h|h
  · exact ⟨F i 1,Or.inl ⟨h ▸ ht,rfl⟩⟩
  · exact ⟨F i 0,Or.inr ⟨h ▸ ht,rfl⟩⟩

lemma face_edge_eq [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    {i j k : ι} (hij : i≠j)
    (hi : i∈regionEdges F ConnectedComponents.mk d) (hj : j∈regionEdges F ConnectedComponents.mk d)
    (hk : k∈regionEdges F ConnectedComponents.mk d)
    (hqi : q∈range (F i)) (hqj : q∈range (F j)) (hqk : q∈range (F k)) : k=i ∨ k=j := by
  by_contra hn
  push Not at hn
  let es : Fin 3 → ι := ![i,j,k]
  have hes : Function.Injective es := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [es]
  exact noncut_face_degree_two F hF P hP hq hK d es hes
    (by intro a; fin_cases a <;> assumption)
    (by intro a; fin_cases a <;> assumption)

theorem facial_graph_isCycles [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (edgeGraph F (regionEdges F ConnectedComponents.mk d)).IsCycles := by
  intro x ⟨y,i,hi,hiy⟩
  obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF P hP hK d x.property hi hiy.mem_left
  obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hqj
  let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
  have hyz : y≠z' := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from (congrArg Subtype.val h).symm ▸ hjz) hiy)
  apply Set.ncard_eq_two.mpr
  refine ⟨y,z',hyz,?_⟩
  ext w
  constructor
  · rintro ⟨k,hk,hkw⟩
    rcases face_edge_eq F hF P hP x.property (hK x.val) d hji.symm hi hj hk
      hiy.mem_left hqj hkw.mem_left with h|h
    · subst k
      exact Or.inl (Subtype.ext (hkw.other_unique hiy))
    · subst k
      exact Or.inr (Subtype.ext (hkw.other_unique hjz))
  · rintro (rfl|rfl)
    · exact ⟨i,hi,hiy⟩
    · exact ⟨j,hj,hjz⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma edgeKey_eq [Finite ι] (F : ι → Arc ℂ) (i : ι) (x y : GraphVertices F) :
    edgeKey F i=s(x,y) ↔ Spans (F i) x.val y.val := by
  simp only [edgeKey,Sym2.eq_iff,Subtype.ext_iff,edgeStart,edgeEnd,Spans]
  tauto

lemma edgeKey_injective [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) : Function.Injective (edgeKey F) := by
  intro i j hij
  exact spans_edge_unique F hF (show Spans (F i) (F i 0) (F i 1) from Or.inl ⟨rfl,rfl⟩)
    ((edgeKey_eq F j (edgeStart F i) (edgeEnd F i)).mp hij.symm)

lemma walkCarrier_cons [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y z : GraphVertices F} (h : (edgeGraph F E).Adj x y) (w : (edgeGraph F E).Walk y z)
    {i : ι} (hi : Spans (F i) x.val y.val) : walkCarrier F (w.cons h)=range (F i)∪walkCarrier F w := by
  have hk := (edgeKey_eq F i x y).mpr hi
  ext p
  simp only [walkCarrier,mem_ofPred_eq,SimpleGraph.Walk.edges_cons,List.mem_cons,mem_union]
  constructor
  · rintro ⟨j,(hj|hj),hp⟩
    · have he := edgeKey_injective F hF (hj.trans hk.symm)
      exact Or.inl (he ▸ hp)
    · exact Or.inr ⟨j,hj,hp⟩
  · rintro (hp|⟨j,hj,hp⟩)
    · exact ⟨i,Or.inl hk,hp⟩
    · exact ⟨j,Or.inr hj,hp⟩

lemma walkCarrier_vertex [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y q : GraphVertices F} {w : (edgeGraph F E).Walk x y} (hq : q.val∈walkCarrier F w) : q∈w.support := by
  obtain ⟨i,hi,t,ht⟩ := hq
  rcases vertex_parameter F hF i (ht.symm ▸ q.property) with h|h
  · have he : edgeStart F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.fst_mem_support_of_mem_edges hi
  · have he : edgeEnd F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.snd_mem_support_of_mem_edges hi

lemma oriented_arc {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) :
    ∃ b : Arc ℂ,b 0=x ∧ b 1=y ∧ range b=range a := by
  rcases h with h|h
  · exact ⟨a,h.1,h.2,rfl⟩
  · exact ⟨a.reverse,by simpa using h.1,by simpa using h.2,a.reverse_range⟩

theorem simple_walk_arc [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) (hw : w.IsPath) (hne : x≠y) :
    ∃ a : Arc ℂ,a 0=x.val ∧ a 1=y.val ∧ range a=walkCarrier F w := by
  induction w with
  | nil => exact (hne rfl).elim
  | @cons x v y h w ih =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hw' := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hw
    by_cases hvy : v=y
    · subst y
      have hn : w.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hw'.1
      cases hn
      refine ⟨a,ha₀,ha₁,?_⟩
      rw [walkCarrier_cons F hF _ _ hix,ha]
      simp [walkCarrier]
    · obtain ⟨b,hb₀,hb₁,hb⟩ := ih hw'.1 hvy
      have hmeet : ∀ s t,a s=b t → s=1 ∧ t=0 := by
        intro s t he
        have hbs : b t∈walkCarrier F w := hb ▸ mem_range_self t
        obtain ⟨j,hj,u,hju⟩ := hbs
        have hji : j≠i := by
          intro hji
          subst j
          have hk := (edgeKey_eq F i x v).mpr hix
          exact hw'.2 (w.fst_mem_support_of_mem_edges (hk ▸ hj))
        obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
        have hrj : F i r=F j u := hr.trans (he.trans hju.symm)
        have hre := ((hF hji.symm).1 r u hrj).1
        have hax : a s=x.val ∨ a s=v.val := by
          rcases hre with rfl|rfl <;> rcases hix with hix|hix
          · exact Or.inl (hr.symm.trans hix.1)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inl (hr.symm.trans hix.1)
        have hav : a s=v.val := hax.resolve_left (by
          intro hx
          apply hw'.2
          apply walkCarrier_vertex F hF (q:=x)
          exact (he.symm.trans hx) ▸ (hb ▸ mem_range_self t))
        exact ⟨a.injective (hav.trans ha₁.symm),b.injective (he.symm.trans (hav.trans hb₀.symm))⟩
      let pa : Path x.val v.val := a.path.cast ha₀.symm ha₁.symm
      let pb : Path v.val y.val := b.path.cast hb₀.symm hb₁.symm
      let c : Arc ℂ := ⟨(pa.trans pb).toContinuousMap,
        trans_injective pa pb a.injective b.injective hmeet⟩
      refine ⟨c,(pa.trans pb).source,(pa.trans pb).target,?_⟩
      change range (pa.trans pb)=_
      rw [Path.trans_range,walkCarrier_cons F hF _ _ hix]
      exact congrArg₂ (·∪·) ha hb
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma walkCarrier_subset [Finite ι] (F : ι → Arc ℂ) {E : Set ι} {x y : GraphVertices F}
    (w : (edgeGraph F E).Walk x y) : walkCarrier F w⊆⋃ i,range (F i) := by
  rintro z ⟨i,-,hi⟩
  exact mem_iUnion.mpr ⟨i,hi⟩

lemma cycle_saturated {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsCycles)
    {x : V} (p : G.Walk x x) (hp : p.IsCycle) {v w : V}
    (hv : v∈p.support) (hvw : G.Adj v w) : s(v,w)∈p.edges := by
  have hn : (G.neighborSet v).Nonempty := ⟨w,hvw⟩
  have he : G.neighborSet v=p.toSubgraph.neighborSet v := by
    apply (Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset v) ?_ (Set.toFinite _)).symm
    rw [hG hn,hp.ncard_neighborSet_toSubgraph_eq_two hv]
  apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
  exact (show w∈p.toSubgraph.neighborSet v from he ▸ hvw)

theorem simple_cycle_arcs [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x : GraphVertices F} (p : (edgeGraph F E).Walk x x) (hp : p.IsCycle) :
    ∃ a b : Arc ℂ,a 0=b 0 ∧ a 1=b 1 ∧
      (∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      range a∪range b=walkCarrier F p := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | @cons x v x h p =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hp' := (p.cons_isCycle_iff h).mp hp
    obtain ⟨c,hc₀,hc₁,hc⟩ := simple_walk_arc F hF p hp'.1 h.ne.symm
    let b := c.reverse
    have hb₀ : b 0=x.val := by simpa only [b,reverse_zero] using hc₁
    have hb₁ : b 1=v.val := by simpa only [b,reverse_one] using hc₀
    have hb : range b=walkCarrier F p := c.reverse_range.trans hc
    refine ⟨a,b,ha₀.trans hb₀.symm,ha₁.trans hb₁.symm,?_,?_⟩
    · intro s t he
      obtain ⟨j,hj,u,hju⟩ := (show b t∈walkCarrier F p from hb ▸ mem_range_self t)
      have hji : j≠i := by
        intro hji
        subst j
        exact hp'.2 ((edgeKey_eq F i x v).mpr hix ▸ hj)
      obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
      have hre := ((hF hji.symm).1 r u (hr.trans (he.trans hju.symm))).1
      have hav : a s=x.val ∨ a s=v.val := by
        rcases hre with rfl|rfl <;> rcases hix with hix|hix
        · exact Or.inl (hr.symm.trans hix.1)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inl (hr.symm.trans hix.1)
      rcases hav with hx|hv
      · exact ⟨Or.inl (a.injective (hx.trans ha₀.symm)),Or.inl (b.injective (he.symm.trans (hx.trans hb₀.symm)))⟩
      · exact ⟨Or.inr (a.injective (hv.trans ha₁.symm)),Or.inr (b.injective (he.symm.trans (hv.trans hb₁.symm)))⟩
    · rw [ha,hb,walkCarrier_cons F hF h p hix]

theorem cycle_edges_isolated [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    (hG : (edgeGraph F E).IsCycles) {x : GraphVertices F}
    (p : (edgeGraph F E).Walk x x) (hp : p.IsCycle) :
    Disjoint (walkCarrier F p) (⋃ i∈{i∈E | edgeKey F i∉p.edges},range (F i)) := by
  apply disjoint_left.mpr
  intro z hz hzi
  obtain ⟨i,⟨hi,hip⟩,s,his⟩ := mem_iUnion₂.mp hzi
  obtain ⟨j,hjp,t,hjt⟩ := hz
  have hij : i≠j := by intro h; exact hip (h ▸ hjp)
  have hends := ((hF hij).1 s t (his.trans hjt.symm)).1
  have hv : Vertex F z := by
    refine ⟨i,?_⟩
    rcases hends with rfl|rfl
    · exact Or.inl his
    · exact Or.inr his
  let v : GraphVertices F := ⟨z,hv⟩
  have hvp : v∈p.support := walkCarrier_vertex F hF ⟨j,hjp,t,hjt⟩
  obtain ⟨w,hw⟩ := vertex_spans F hF hv ⟨s,his⟩
  let w' : GraphVertices F := ⟨w,hw.vertex_right⟩
  have hed : (edgeGraph F E).Adj v w' := ⟨i,hi,hw⟩
  have hk := cycle_saturated hG p hp hvp hed
  exact hip ((edgeKey_eq F i v w').mpr hw ▸ hk)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem pair_no_cut (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) (q : ℂ) :
    IsConnected ((range a∪range b)\{q}) := by
  refine ⟨?_,?_⟩
  · by_cases h : a 0=q
    · exact ⟨a 1,Or.inl (mem_range_self 1),fun he => a.endpoints_ne (h.trans he.symm)⟩
    · exact ⟨a 0,Or.inl (mem_range_self 0),h⟩
  · apply isPreconnected_of_forall_constant
    intro f hf x hx y hy
    have hends (hs : a 0≠q) (ht : a 1≠q) : f (a 0)=f (a 1) := by
      by_cases hqa : q∈range a
      · have hqb : q∉range b := by
          obtain ⟨s,hsq⟩ := hqa
          rintro ⟨t,htq⟩
          rcases (hc s t (hsq.trans htq.symm)).1 with rfl|rfl
          · exact hs hsq
          · exact ht hsq
        rw [h₀,h₁]
        apply arc_label_interval b hf zero_le_one
        intro t ht
        exact ⟨Or.inr (mem_range_self t),fun h => hqb ⟨t,h⟩⟩
      · apply arc_label_interval a hf zero_le_one
        intro t ht
        exact ⟨Or.inl (mem_range_self t),fun h => hqa ⟨t,h⟩⟩
    have endpoint {z : ℂ} (hz : z∈(range a∪range b)\{q}) :
        ∃ w,w∈({a 0,a 1} : Set ℂ) ∧ w≠q ∧ f z=f w := by
      rcases hz.1 with ⟨t,rfl⟩|⟨t,rfl⟩
      · obtain ⟨e,he,heq,hf⟩ := arc_punctured_endpoint_label a (S:=range a∪range b) subset_union_left hf hz.2
        refine ⟨a e,?_,heq,hf⟩
        rcases he with rfl|rfl <;> simp
      · obtain ⟨e,he,heq,hf⟩ := arc_punctured_endpoint_label b (S:=range a∪range b) subset_union_right hf hz.2
        refine ⟨b e,?_,heq,hf⟩
        rcases he with rfl|rfl
        · simp [←h₀]
        · simp [←h₁]
    obtain ⟨u,hu,huq,hxu⟩ := endpoint hx
    obtain ⟨v,hv,hvq,hyv⟩ := endpoint hy
    rw [hxu,hyv]
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    · rfl
    · rw [mem_singleton_iff] at hv
      subst v
      exact hends huq hvq
    · rw [mem_singleton_iff] at hu
      subst u
      exact (hends hvq huq).symm
    · exact congrArg f (hu.trans hv.symm)

theorem pair_component_local_access (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : q∈range a∪range b) :
    ∃ r>0,∀ s : ℝ,0 < s → s ≤ r → ∀ x : ℂ,
      IsPreconnected (connectedComponentIn (range a∪range b)ᶜ x∩ball q s) := by
  obtain ⟨A,hA⟩ := finite_graph_exact_segments (fun _ : Unit => a) P (fun _ => ha)
  obtain ⟨B,hB⟩ := finite_graph_exact_segments (fun _ : Unit => b) P (fun _ => hb)
  simp only [iUnion_const] at hA hB
  have he : range a∪range b=⋃ p∈A∪B,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hA,←hB]
  rw [he]
  exact noncut_locally_connected_faces (A∪B) (he ▸ hq) (he ▸ pair_no_cut a b h₀ h₁ hc q)
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
open Set unitInterval Topology Metric CannonFaceIncidence

lemma pair_component_closure (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    {x : ℂ} (hx : x∉range a∪range b) :
    closure (connectedComponentIn (range a∪range b)ᶜ x)=
      connectedComponentIn (range a∪range b)ᶜ x∪(range a∪range b) := by
  let C := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  let d : ConnectedComponents (Cᶜ : Set ℂ) := ConnectedComponents.mk ⟨x,hx⟩
  have he : region Cᶜ ConnectedComponents.mk d=connectedComponentIn Cᶜ x := component_region_eq _ ⟨x,hx⟩
  rw [←he]
  obtain ⟨l,hl⟩ := tame_pair_jordan a b h₀ h₁ hc P ha hb
  apply Subset.antisymm
  · intro z hz
    by_cases hzC : z∈C
    · exact Or.inr hzC
    · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hz hzC)
  · apply union_subset subset_closure
    intro z hz
    show d∈incident Cᶜ ConnectedComponents.mk z
    rw [hl z hz]
    exact l.surjective d

theorem isolated_jordan_face {K T : Set ℂ} (hKclosed : IsClosed K) (hK : IsPreconnected K)
    (hT : IsClosed T) (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hCK : range a∪range b⊆K) (hCT : Disjoint (range a∪range b) T)
    {x : ℂ} (hx : x∉K)
    (hcl : closure (connectedComponentIn Kᶜ x)=connectedComponentIn Kᶜ x∪((range a∪range b)∪T)) :
    frontier (connectedComponentIn Kᶜ x)=range a∪range b ∧
      closure (connectedComponentIn Kᶜ x)=connectedComponentIn Kᶜ x∪(range a∪range b) := by
  let C := range a∪range b
  let U := connectedComponentIn Kᶜ x
  let R := connectedComponentIn Cᶜ x
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  have hxC : x∉C := fun h => hx (hCK h)
  have hUopen : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
  have hRopen : IsOpen R := hC.isOpen_compl.connectedComponentIn
  have hRconn : IsConnected R := isConnected_connectedComponentIn_iff.mpr hxC
  have hUsub : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hRsub : R⊆Cᶜ := connectedComponentIn_subset _ _
  have hUR : U⊆R := isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx) (fun z hz => fun h => hUsub hz (hCK h))
  have hRcl : closure R=R∪C := pair_component_closure a b h₀ h₁ hc P ha hb hxC
  have hCcl : C⊆closure U := by intro q hq; rw [hcl]; exact Or.inr (Or.inl hq)
  have hfree (q : ℂ) (hq : q∈C) : q∉closure (K∩R) := by
    obtain ⟨r,hr,hloc⟩ := pair_component_local_access a b h₀ h₁ hc P ha hb hq
    have hqT : q∉T := disjoint_left.mp hCT hq
    obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hqT)
    let s := min r δ
    have hs : 0 < s := lt_min hr hδ
    have hconn : IsPreconnected (R∩ball q s) := hloc s hs (min_le_left ..) x
    have hball : ball q s⊆Tᶜ := (ball_subset_ball (min_le_right ..)).trans hδT
    have hcover : R∩ball q s⊆U∪(closure U)ᶜ := by
      intro z hz
      by_cases hzU : z∈U
      · exact Or.inl hzU
      · refine Or.inr ?_
        rw [hcl]
        exact fun h => h.elim hzU (fun h => h.elim (hRsub hz.1) (hball hz.2))
    have hdis : Disjoint U (closure U)ᶜ := disjoint_left.mpr (fun z hz hn => hn (subset_closure hz))
    obtain ⟨z,hzB,hzU⟩ := (mem_closure_iff_nhds.mp (hCcl hq)) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
    have hsub : R∩ball q s⊆U := hconn.subset_left_of_subset_union hUopen isClosed_closure.isOpen_compl
      hdis hcover ⟨z,⟨hUR hzU,hzB⟩,hzU⟩
    intro hqKR
    obtain ⟨z,hzB,hzK,hzR⟩ := (mem_closure_iff_nhds.mp hqKR) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
    exact hUsub (hsub ⟨hzR,hzB⟩) hzK
  have hKRclosed : IsClosed (K∩R) := by
    apply isClosed_of_closure_subset
    intro z hz
    have hzK : z∈K := hKclosed.closure_subset_iff.mpr inter_subset_left hz
    have hzclR : z∈closure R := closure_mono inter_subset_right hz
    rw [hRcl] at hzclR
    exact ⟨hzK,hzclR.resolve_right (fun hzC => hfree z hzC hz)⟩
  have hRfree : R⊆Kᶜ := by
    intro z hzR hzK
    have haC : a 0∈C := Or.inl (mem_range_self 0)
    obtain ⟨w,-,hwKR,hwR⟩ := (isPreconnected_closed_iff.mp hK) (K∩R) Rᶜ hKRclosed hRopen.isClosed_compl
      (by intro y hy; by_cases hyR : y∈R; exact Or.inl ⟨hy,hyR⟩; exact Or.inr hyR)
      ⟨z,hzK,hzK,hzR⟩ ⟨a 0,hCK haC,fun h => hRsub h haC⟩
    exact hwR hwKR.2
  have hRU : R⊆U := hRconn.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hxC) hRfree
  have hUR' : U=R := Subset.antisymm hUR hRU
  have hcl' : closure U=U∪C := by rw [hUR',hRcl]
  refine ⟨?_,hcl'⟩
  rw [frontier,hUopen.interior_eq,hcl']
  ext z
  constructor
  · rintro ⟨h,hn⟩
    exact h.resolve_left hn
  · intro hz
    exact ⟨Or.inr hz,fun h => hUsub h (hCK hz)⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma walk_edge_mem (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) {i : ι} (hi : edgeKey F i∈w.edges) : i∈E := by
  have h := w.edges_subset_edgeSet hi
  change (edgeGraph F E).Adj (edgeStart F i) (edgeEnd F i) at h
  obtain ⟨j,hj,hji⟩ := h
  have he : j=i := spans_edge_unique F hF hji (Or.inl ⟨rfl,rfl⟩)
  exact he ▸ hj

lemma walkCarrier_edgeUnion (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) :
    walkCarrier F w⊆⋃ i∈E,range (F i) := by
  rintro z ⟨i,hi,hzi⟩
  exact mem_iUnion₂.mpr ⟨i,walk_edge_mem F hF w hi,hzi⟩

theorem facial_jordan_cycle [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    ∃ (v : GraphVertices F) (p : (edgeGraph F (regionEdges F ConnectedComponents.mk d)).Walk v v)
      (a b : Arc ℂ),p.IsCycle ∧ a 0=b 0 ∧ a 1=b 1 ∧
      (∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      range a∪range b=walkCarrier F p ∧
      frontier (face F d)=range a∪range b ∧
      closure (face F d)=face F d∪(range a∪range b) := by
  classical
  let K := ⋃ i,range (F i)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hKclosed.isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let G := edgeGraph F E
  have hG : G.IsCycles := facial_graph_isCycles F hF P hP hK d
  obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
  have hi : i∈E := ⟨t,ht₀,ht₁,ht⟩
  have hne : (G.neighborSet (edgeStart F i)).Nonempty := ⟨edgeEnd F i,i,hi,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨p,hp,-⟩ := hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c:=G.connectedComponentMk (edgeStart F i)) (show edgeStart F i∈(G.connectedComponentMk (edgeStart F i)).supp from rfl) hne
  obtain ⟨a,b,h₀,h₁,hc,hC⟩ := simple_cycle_arcs F hF p hp
  let T := ⋃ j∈{j∈E | edgeKey F j∉p.edges},range (F j)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (F j).compact_range.isClosed
  have hB : (⋃ j∈E,range (F j))=(range a∪range b)∪T := by
    rw [hC]
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      by_cases hjp : edgeKey F j∈p.edges
      · exact Or.inl ⟨j,hjp,hzj⟩
      · exact Or.inr (mem_iUnion₂.mpr ⟨j,⟨hj,hjp⟩,hzj⟩)
    · apply union_subset (walkCarrier_edgeUnion F hF p)
      intro z hz
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨j,hj.1,hzj⟩
  have hCT : Disjoint (range a∪range b) T := hC ▸ cycle_edges_isolated F hF hG p hp
  have hCK : range a∪range b⊆K := hC ▸ walkCarrier_subset F p
  have hseg : (range a∪range b)⊆⋃ p∈P,segment ℝ p.1 p.2 := by
    intro z hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hCK hz)
    exact hP j hj
  obtain ⟨x,hxd⟩ := ConnectedComponents.surjective_coe d
  have hface : face F d=connectedComponentIn Kᶜ x.val := by
    change region Kᶜ ConnectedComponents.mk d=_
    rw [←hxd,component_region_eq]
  have hconn : IsPreconnected K := by
    have he : K\{x.val}=K := sdiff_singleton_eq_self x.property
    exact he ▸ hK x.val
  have hwhole := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  rw [hB] at hwhole
  have hh := isolated_jordan_face hKclosed hconn hT a b h₀ h₁ hc P
    (subset_union_left.trans hseg) (subset_union_right.trans hseg) hCK hCT x.property (hface ▸ hwhole)
  rw [←hface] at hh
  exact ⟨edgeStart F i,p,a,b,hp,h₀,h₁,hc,hC,hh.1,hh.2⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma facial_boundary_preconnected [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    IsPreconnected (frontier (face F d)) := by
  obtain ⟨v,p,a,b,hp,h₀,h₁,hc,hC,hfront,hcl⟩ := facial_jordan_cycle F hF P hP hK d
  rw [hfront]
  exact IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,h₀.symm⟩⟩
    (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)

lemma third_facial_edge_impossible (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    {i j k : ι} (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hi : i∈regionEdges F ConnectedComponents.mk d)
    (hj : j∈regionEdges F ConnectedComponents.mk d)
    (hk : k∈regionEdges F ConnectedComponents.mk d)
    {q : ℂ} (hq : Vertex F q) (hqi : q∈range (F i))
    (hqj : q∈range (F j)) (hqk : q∈range (F k)) : False := by
  apply noncut_face_degree_two F hF P hP hq (hK q) d ![i,j,k]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro parameter; fin_cases parameter <;> assumption
  · intro parameter; fin_cases parameter <;> assumption

theorem triangle_whole_face [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    (S : Finset ι) (hS : S.Nonempty)
    (hface : ∀ i∈S,i∈regionEdges F ConnectedComponents.mk d)
    (hsecond : ∀ i∈S,∀ t:I,t=0 ∨ t=1 → ∃ j∈S,j≠i ∧ F i t∈range (F j)) :
    frontier (face F d)=⋃ i∈S,range (F i) ∧
      closure (face F d)=face F d∪⋃ i∈S,range (F i) := by
  classical
  let K := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let C := ⋃ i∈S,range (F i)
  let T := ⋃ i∈E\(S : Set ι),range (F i)
  have hCc : IsClosed C := isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  have hTc : IsClosed T := isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  have hCT : Disjoint C T := by
    apply disjoint_left.mpr
    intro q hqC hqT
    obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hqC
    obtain ⟨k,hk,u,huk⟩ := mem_iUnion₂.mp hqT
    have hki : k≠i := fun h => hk.2 (h ▸ hi)
    have ht := ((hF hki).1 u t huk).2
    obtain ⟨j,hj,hji,hqj⟩ := hsecond i hi t ht
    have hkj : k≠j := fun h => hk.2 (h ▸ hj)
    exact third_facial_edge_impossible F hF P hP hK d hji.symm hki.symm hkj.symm
      (hface i hi) (hface j hj) hk.1
      ⟨i,ht.elim (fun h => Or.inl (congrArg (F i) h).symm) (fun h => Or.inr (congrArg (F i) h).symm)⟩
      (mem_range_self t) hqj ⟨u,huk⟩
  have hcl : closure (face F d)=face F d∪(C∪T) := by
    have hh : closure (face F d)=face F d∪⋃ i∈E,range (F i) := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
    rw [hh]
    congr 1
    ext z
    constructor
    · intro h
      obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
      by_cases hiS : i∈S
      · exact Or.inl (mem_iUnion₂.mpr ⟨i,hiS,hzi⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨i,⟨hi,hiS⟩,hzi⟩)
    · rintro (h|h)
      · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
        exact mem_iUnion₂.mpr ⟨i,hface i hi,hzi⟩
      · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
        exact mem_iUnion₂.mpr ⟨i,hi.1,hzi⟩
  have hCK : C∪T⊆K := by
    rintro z (h|h) <;> obtain ⟨i,-,hzi⟩ := mem_iUnion₂.mp h <;> exact mem_iUnion.mpr ⟨i,hzi⟩
  have hfront : frontier (face F d)=C∪T := by
    rw [frontier,(face_open F d).interior_eq,hcl]
    ext z
    constructor
    · rintro ⟨h,hn⟩; exact h.resolve_left hn
    · intro h; exact ⟨Or.inr h,fun hz => hz.1 (hCK h)⟩
  have hBC : C∪T⊆C := by
    have hp := facial_boundary_preconnected F hF P hP hK d
    rw [hfront] at hp
    obtain ⟨i,hi⟩ := hS
    have hh := (isPreconnected_closed_iff.mp hp) C T hCc hTc Subset.rfl
      ⟨F i 0,Or.inl (mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩),mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩⟩
    intro z hz
    by_contra hn
    obtain ⟨y,-,hyC,hyT⟩ := hh ⟨z,hz,hz.resolve_left hn⟩
    exact disjoint_left.mp hCT hyC hyT
  have he : C∪T=C := Subset.antisymm hBC subset_union_left
  exact ⟨hfront.trans he,by simpa only [he] using hcl⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι κ : Type*} [Finite ι] [Finite κ]

theorem refined_face_new_edge (G : κ → Arc ℂ)
    (hG : Pairwise (fun i j => Compatible (G i) (G j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (G i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces G) {K U : Set ℂ} (hUK : U⊆Kᶜ) (hVU : face G d⊆U)
    {q : ℂ} (hq : q∈closure (face G d))
    (hloc : ∃ r : ℝ,0 < r ∧ ∀ s,0 < s → s ≤ r → IsPreconnected (U∩ball q s))
    (hacc : q∈closure (U∩(⋃ i,range (G i)))) :
    ∃ j,j∈regionEdges G ConnectedComponents.mk d ∧ q∈range (G j) ∧ ¬range (G j)⊆K := by
  classical
  let L := ⋃ i,range (G i)
  let _ : LocallyConnectedSpace (Lᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let V := face G d
  let E := regionEdges G ConnectedComponents.mk d
  let T := ⋃ j∈{j∈E | q∉range (G j)},range (G j)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (G j).compact_range.isClosed
  have hqT : q∉T := by
    intro h
    obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp h
    exact hj.2 hqj
  by_contra hn
  have hjK (j : κ) (hj : j∈E) (hqj : q∈range (G j)) : range (G j)⊆K := by
    by_contra hn'
    exact hn ⟨j,hj,hqj,hn'⟩
  obtain ⟨r,hr,hloc⟩ := hloc
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hqT)
  let s := min r δ
  have hs : 0 < s := lt_min hr hδ
  have hball : ball q s⊆Tᶜ := (ball_subset_ball (min_le_right ..)).trans hδT
  have hcl : closure V=V∪⋃ j∈E,range (G j) := tame_region_closure G hG P hP ConnectedComponents.continuous_coe d
  have hcover : U∩ball q s⊆V∪(closure V)ᶜ := by
    intro z hz
    by_cases hzV : z∈V
    · exact Or.inl hzV
    · refine Or.inr ?_
      rw [hcl]
      rintro (h|h)
      · exact hzV h
      · obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp h
        by_cases hqj : q∈range (G j)
        · exact hUK hz.1 (hjK j hj hqj hzj)
        · exact hball hz.2 (mem_iUnion₂.mpr ⟨j,⟨hj,hqj⟩,hzj⟩)
  obtain ⟨z,hzB,hzV⟩ := (mem_closure_iff_nhds.mp hq) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
  have hUV : U∩ball q s⊆V := (hloc s hs (min_le_left ..)).subset_left_of_subset_union
    (face_open G d) isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun _ h hn => hn (subset_closure h)) hcover ⟨z,⟨hVU hzV,hzB⟩,hzV⟩
  obtain ⟨z,hzB,hzU,hzL⟩ := (mem_closure_iff_nhds.mp hacc) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
  exact (hUV ⟨hzU,hzB⟩).1 hzL

lemma face_local_access (F : ι → Arc ℂ)
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : q∈⋃ i,range (F i))
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    ∃ r : ℝ,0 < r ∧ ∀ s,0 < s → s ≤ r → IsPreconnected (face F d∩ball q s) := by
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  have hconn : IsConnected ((⋃ i,range (F i))\{q}) := by
    obtain ⟨z,hz,-,hzq⟩ := graph_no_isolated F hq isOpen_univ (mem_univ _)
    exact ⟨⟨z,hz,hzq⟩,hK⟩
  rw [hQ] at hq hconn
  obtain ⟨r,hr,hloc⟩ := noncut_locally_connected_faces Q hq hconn
  refine ⟨r,hr,fun s hs hsr => ?_⟩
  obtain ⟨x,hx⟩ := ConnectedComponents.surjective_coe d
  have hh := hloc s hs hsr x.val
  rw [←hQ] at hh
  simpa only [face,←hx,component_region_eq] using hh

lemma arc_endpoint_closure_interior {X : Type*} [TopologicalSpace X] (a : Arc X) :
    a 1∈closure (a '' Ioo (0:I) 1) := by
  have h : (1:I)∈closure (Ioo (0:I) 1) := by rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one,le_rfl⟩
  exact image_closure_subset_closure_image a.continuous ⟨1,h,rfl⟩

theorem spoke_forces_new_facial_edge (F : ι → Arc ℂ)
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (G : κ → Arc ℂ) (hG : Pairwise (fun i j => Compatible (G i) (G j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (G i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (d : Faces F) (e : Faces G) (hsub : face G e⊆face F d)
    (a : Arc ℂ) (ha : a '' Ioo (0:I) 1⊆face F d) (haG : range a⊆⋃ i,range (G i))
    (haK : a 1∈⋃ i,range (F i)) (hK : IsPreconnected ((⋃ i,range (F i))\{a 1}))
    (hq : a 1∈closure (face G e)) :
    ∃ j,j∈regionEdges G ConnectedComponents.mk e ∧ a 1∈range (G j) ∧
      ¬range (G j)⊆⋃ i,range (F i) := by
  apply refined_face_new_edge G hG Q hQ e (fun _ h => h.1) hsub hq (face_local_access F P hP haK hK d)
  apply closure_mono _ (arc_endpoint_closure_interior a)
  intro z hz
  exact ⟨ha hz,haG (image_subset_range _ _ hz)⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι κ : Type*}

lemma face_parent [Finite ι] [Finite κ] (F : ι → Arc ℂ) (G : κ → Arc ℂ)
    (hFG : (⋃ i,range (F i))⊆⋃ i,range (G i)) (e : Faces G) :
    ∃ d : Faces F,face G e⊆face F d := by
  obtain ⟨x,hx⟩ := face_nonempty G e
  have hxF : x∉⋃ i,range (F i) := fun h => hx.1 (hFG h)
  let d : Faces F := ConnectedComponents.mk ⟨x,hxF⟩
  refine ⟨d,?_⟩
  have hconn := (component_region_connected (⋃ i,range (G i))ᶜ e).isPreconnected
  have hsub : face G e⊆(⋃ i,range (F i))ᶜ := fun z hz h => hz.1 (hFG h)
  have hh := hconn.subset_connectedComponentIn hx hsub
  simpa only [face,d,component_region_eq] using hh

lemma same_face_of_mem_closure [Finite ι] (F : ι → Arc ℂ) {d e : Faces F} {z : ℂ}
    (hz : z∈face F d) (he : z∈closure (face F e)) : d=e := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hh := closure_region_inside
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe he hz.1
  exact hz.2.symm.trans hh.2

lemma stellar_spoke_parent [Finite ι] (F : ι → Arc ℂ) [Finite (Faces F)]
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    {i : Σ d : Faces F,faceVertices F d}
    (hi : Sum.inr i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e) : i.1=d := by
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ j,range (G j))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun j => (G j).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hcl := region_edge_in_closure G hG Q hQ ConnectedComponents.continuous_coe hi
  obtain ⟨parameter,_,hlt,_⟩ := hi
  have hpoint : A i parameter∈closure (face F d) :=
    closure_mono hsub (hcl (mem_range_self parameter))
  exact same_face_of_mem_closure F
    (fan_parameter_in_face (h₀ i ▸ hc i.1) (hU i) (ne_of_lt hlt)) hpoint

lemma stellar_old_endpoint [Finite ι] (F : ι → Arc ℂ)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    {q : ℂ} (hq : q∈⋃ j,range (F j)) {i : Σ d : Faces F,faceVertices F d}
    (hi : q∈range (A i)) : q=i.2.val := by
  obtain ⟨t,ht⟩ := hi
  have ht1 : t=1 := by
    by_contra hn
    exact (fan_parameter_in_face (h₀ i ▸ hc i.1) (hU i) hn).1 (ht ▸ hq)
  exact ht.symm.trans (ht1 ▸ h₁ i)

theorem stellar_old_vertex_spoke_facial [Finite ι] (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    (v : faceVertices F d) (hv : v.val∈closure (face (Sum.elim F A) e)) :
    Sum.inr ⟨d,v⟩∈regionEdges (Sum.elim F A) ConnectedComponents.mk e := by
  have hvK := vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1
  obtain ⟨j,hj,hvj,hjK⟩ := spoke_forces_new_facial_edge F P hP (Sum.elim F A) hG Q hQ d e hsub
    (A ⟨d,v⟩) (hU ⟨d,v⟩) (subset_iUnion (fun i => range (Sum.elim F A i : Arc ℂ)) (Sum.inr ⟨d,v⟩))
    (h₁ ⟨d,v⟩ ▸ hvK) (hK _) (h₁ ⟨d,v⟩ ▸ hv)
  rcases j with j|⟨d',v'⟩
  · exact (hjK (subset_iUnion (fun i => range (F i)) j)).elim
  · have hd' : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hj
    subst d'
    have hv' : v'=v := Subtype.ext (by
      have hh := stellar_old_endpoint F c A hc h₀ h₁ hU hvK (show v.val∈range (A ⟨d,v'⟩) by simpa only [h₁,Sum.elim_inr] using hvj)
      exact hh.symm)
    simpa only [hv'] using hj

lemma stellar_face_old_edge [Finite ι] (F : ι → Arc ℂ) [Nonempty ι] [Finite (Faces F)]
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}))
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d) :
    ∃ i : ι,Sum.inl i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e := by
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ i,range (G i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨j,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge G hG ConnectedComponents.continuous_coe e (face_nonempty G e)
  have hj : j∈regionEdges G ConnectedComponents.mk e := ⟨t,ht₀,ht₁,ht⟩
  rcases j with i|⟨d',v⟩
  · exact ⟨i,hj⟩
  · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hj
    subst d'
    have hvK := vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1
    have hvG : Vertex G v.val := ⟨Sum.inr ⟨d,v⟩,Or.inr (h₁ ⟨d,v⟩)⟩
    obtain ⟨k,hkj,hk,hvk⟩ := noncut_face_second_edge G hG Q hQ hK e hvG hj ⟨1,h₁ ⟨d,v⟩⟩
    rcases k with i|⟨d',w⟩
    · exact ⟨i,hk⟩
    · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hk
      subst d'
      have hvw : v=w := Subtype.ext (stellar_old_endpoint F c A hc h₀ h₁ hU hvK hvk)
      exact (hkj (by rw [hvw])).elim

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem stellar_face_triangle (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hGK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}))
    (e : Faces (Sum.elim F A)) :
    ∃ (d : Faces F) (i : ι) (v w : faceVertices F d),
      F i 0=v.val ∧ F i 1=w.val ∧ v≠w ∧
      face (Sum.elim F A) e⊆face F d ∧
      frontier (face (Sum.elim F A) e)=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) ∧
      closure (face (Sum.elim F A) e)=face (Sum.elim F A) e∪
        (range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩)) := by
  classical
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ i,range (G i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hFG : (⋃ i,range (F i))⊆⋃ i,range (G i) := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨Sum.inl i,hi⟩
  obtain ⟨d,hsub⟩ := face_parent F G hFG e
  obtain ⟨i,hi⟩ := stellar_face_old_edge F c A hc h₀ h₁ hU hG Q hQ hGK hsub
  have hcl : range (F i)⊆closure (face G e) := region_edge_in_closure G hG Q hQ ConnectedComponents.continuous_coe hi
  have hv : F i 0∈faceVertices F d := (mem_faceVertices F d _).mpr
    ⟨⟨i,Or.inl rfl⟩,closure_mono hsub (hcl (mem_range_self 0))⟩
  have hw : F i 1∈faceVertices F d := (mem_faceVertices F d _).mpr
    ⟨⟨i,Or.inr rfl⟩,closure_mono hsub (hcl (mem_range_self 1))⟩
  let v : faceVertices F d := ⟨F i 0,hv⟩
  let w : faceVertices F d := ⟨F i 1,hw⟩
  have hvw : v≠w := fun h => (F i).endpoints_ne (congrArg Subtype.val h)
  have hvf := stellar_old_vertex_spoke_facial F P hP hK c A hc h₀ h₁ hU hG Q hQ hsub v (hcl (mem_range_self 0))
  have hwf := stellar_old_vertex_spoke_facial F P hP hK c A hc h₀ h₁ hU hG Q hQ hsub w (hcl (mem_range_self 1))
  let k : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inl i
  let j : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inr ⟨d,v⟩
  let l : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inr ⟨d,w⟩
  have hjl : j≠l := by
    intro he
    have hh : (⟨d,v⟩ : Σ d : Faces F,faceVertices F d)=⟨d,w⟩ := Sum.inr.inj he
    exact (F i).endpoints_ne (congrArg (fun z : Σ d : Faces F,faceVertices F d => z.2.val) hh)
  let S : Finset (ι ⊕ (Σ d : Faces F,faceVertices F d)) := {k,j,l}
  have hS : S.Nonempty := ⟨k,by simp [S]⟩
  have hSf : ∀ x∈S,x∈regionEdges G ConnectedComponents.mk e := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact hi
    · exact hvf
    · exact hwf
  have hsecond : ∀ x∈S,∀ t:I,t=0 ∨ t=1 → ∃ y∈S,y≠x ∧ G x t∈range (G y) := by
    intro x hx t ht
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> rcases ht with rfl|rfl
    · exact ⟨j,by simp [S],by simp [j,k],1,h₁ ⟨d,v⟩⟩
    · exact ⟨l,by simp [S],by simp [l,k],1,h₁ ⟨d,w⟩⟩
    · exact ⟨l,by simp [S],hjl.symm,0,(h₀ ⟨d,w⟩).trans (h₀ ⟨d,v⟩).symm⟩
    · exact ⟨k,by simp [S],by simp [j,k],0,(h₁ ⟨d,v⟩).symm⟩
    · exact ⟨j,by simp [S],hjl,0,(h₀ ⟨d,v⟩).trans (h₀ ⟨d,w⟩).symm⟩
    · exact ⟨k,by simp [S],by simp [l,k],1,(h₁ ⟨d,w⟩).symm⟩
  obtain ⟨hfront,hclosure⟩ := triangle_whole_face G hG Q hQ hGK e S hS hSf hsecond
  have hC : (⋃ x∈S,range (G x))=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) := by
    simp [S,k,j,l,G,union_assoc]
  exact ⟨d,i,v,w,rfl,rfl,hvw,hsub,hfront.trans hC,by simpa only [hC] using hclosure⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem global_triangular_stellation (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) ∧
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q})) ∧
      ∀ e : Faces (Sum.elim F A),∃ (d : Faces F) (i : ι) (v w : faceVertices F d),
        F i 0=v.val ∧ F i 1=w.val ∧ v≠w ∧
        face (Sum.elim F A) e⊆face F d ∧
        frontier (face (Sum.elim F A) e)=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) ∧
        closure (face (Sum.elim F A) e)=face (Sum.elim F A) e∪
          (range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩)) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  obtain ⟨z,hz⟩ := (complex_finite_segments_compl_dense P).nonempty
  have hzK : z∉⋃ i,range (F i) := fun h => hz (iUnion_subset hP h)
  have hconn : IsPreconnected (⋃ i,range (F i)) := by
    have he : (⋃ i,range (F i))\{z}=⋃ i,range (F i) := sdiff_singleton_eq_self hzK
    exact he ▸ hK z
  obtain ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK⟩ := global_stellation_no_cut_points F hF P hP hconn
  have hGK' : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}) := by
    intro q
    simpa only [iUnion_sum,Sum.elim_inl,Sum.elim_inr] using hGK q
  have hGS : ∀ i,FiniteSupport (range (Sum.elim F A i : Arc ℂ)) := by
    rintro (i|i)
    · exact ⟨P,hP i⟩
    · exact hS i
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hGS
  have hQ' : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun i =>
    (subset_iUnion (fun i => range (Sum.elim F A i : Arc ℂ)) i).trans hQ
  exact ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK',stellar_face_triangle F P hP hK c A hc h₀ h₁ hU hG Q hQ' hGK'⟩
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceVerticesCard
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

variable {ι : Type*} [Finite ι]

theorem face_vertices_card_le (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) (d : Faces F) :
    Nat.card (faceVertices F d)≤2*Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let K := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  have hend (i : E) (b : Bool) : (if b then F i.val 1 else F i.val 0)∈faceVertices F d := by
    apply (mem_faceVertices F d _).mpr
    have hh := region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe i.property
    cases b
    · exact ⟨⟨i.val,Or.inl rfl⟩,hh (mem_range_self 0)⟩
    · exact ⟨⟨i.val,Or.inr rfl⟩,hh (mem_range_self 1)⟩
  let f : E × Bool → faceVertices F d := fun p => ⟨_,hend p.1 p.2⟩
  have hsur : Function.Surjective f := by
    intro v
    obtain ⟨hv,hvcl⟩ := (mem_faceVertices F d v.val).mp v.property
    have hK := vertex_mem_support F hv
    have hcl : closure (face F d)=face F d∪⋃ i∈E,range (F i) := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
    rw [hcl] at hvcl
    have hh := hvcl.resolve_left (fun h => h.1 hK)
    obtain ⟨i,hi,t,ht⟩ := mem_iUnion₂.mp hh
    have ht' := vertex_parameter F hF i (ht ▸ hv)
    rcases ht' with rfl|rfl
    · exact ⟨(⟨i,hi⟩,false),Subtype.ext ht⟩
    · exact ⟨(⟨i,hi⟩,true),Subtype.ext ht⟩
  have hh := Nat.card_le_card_of_surjective f hsur
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool,mul_comm] using hh

lemma stellar_old_edge_parent (F : ι → Arc ℂ)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    {i : ι} (hi : Sum.inl i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e) :
    i∈regionEdges F ConnectedComponents.mk d := by
  obtain ⟨t,ht₀,ht₁,ht⟩ := hi
  exact ⟨t,ht₀,ht₁,closure_mono hsub ht⟩

theorem stellar_face_edges_card_le (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d) :
    Nat.card (regionEdges (Sum.elim F A) ConnectedComponents.mk e)≤
      3*Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let E := regionEdges F ConnectedComponents.mk d
  let E' := regionEdges (Sum.elim F A) ConnectedComponents.mk e
  let g : E ⊕ (faceVertices F d) → ι ⊕ (Σ d : Faces F,faceVertices F d) :=
    Sum.elim (fun i => Sum.inl i.val) (fun v => Sum.inr ⟨d,v⟩)
  have hsub' : E'⊆range g := by
    rintro (i|⟨d',v⟩) hi
    · exact ⟨Sum.inl ⟨i,stellar_old_edge_parent F A hsub hi⟩,rfl⟩
    · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hi
      subst d'
      exact ⟨Sum.inr v,rfl⟩
  have h1 := Nat.card_mono (toFinite (range g)) hsub'
  have h2 : Nat.card (range g)≤Nat.card (E⊕(faceVertices F d)) :=
    Nat.card_le_card_of_surjective (fun x => (⟨g x,mem_range_self x⟩ : range g)) (by
      rintro ⟨y,⟨x,rfl⟩⟩; exact ⟨x,rfl⟩)
  have hv := face_vertices_card_le F hF P hP d
  rw [Nat.card_sum] at h2
  change Nat.card E'≤3*Nat.card E
  change Nat.card (faceVertices F d)≤2*Nat.card E at hv
  omega
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι X : Type*} [Finite ι] [Nonempty ι] [PseudoMetricSpace X]

omit [Nonempty ι] in
lemma stellar_spoke_closure (F : ι → Arc ℂ)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆closure (face F i.1) := by
  rintro z ⟨t,rfl⟩
  by_cases ht₀ : t=0
  · rw [ht₀,h₀]; exact subset_closure (hc i.1)
  by_cases ht₁ : t=1
  · rw [ht₁,h₁]; exact ((mem_faceVertices F i.1 i.2.val).mp i.2.property).2
  exact subset_closure (hU i ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
    lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩)

theorem near_faces_card_le (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}≤
      2*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  choose labels hlabels using tame_edge_incident_labels F hF P hP ConnectedComponents.continuous_coe
  let H := {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  let g : E × Bool → Faces F := fun p => labels p.1.val p.2
  have hsub : H⊆range g := by
    rintro d ⟨z,hz,hzx⟩
    obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
    have hi : i∈E := by
      refine ⟨t,?_⟩
      have hd := hdiam d (F i t) ht z hz
      have hh := dist_triangle (f (F i t)) (f z) x
      linarith
    have ht' : d∈range (labels i) := by rw [←hlabels i t ht₀ ht₁]; exact ht
    obtain ⟨b,hb⟩ := ht'
    exact ⟨(⟨i,hi⟩,b),hb⟩
  have h1 := Nat.card_mono (toFinite (range g)) hsub
  have h2 : Nat.card (range g)≤Nat.card (E × Bool) :=
    Nat.card_le_card_of_surjective (fun a => (⟨g a,mem_range_self a⟩ : range g)) (by
      rintro ⟨y,⟨a,rfl⟩⟩; exact ⟨a,rfl⟩)
  have hh := h1.trans h2
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool,mul_comm] using hh

theorem stellar_spokes_local_card (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B)
    (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R}≤
      4*B*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  classical
  let H := {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  let S := {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R}
  have hparent (i : S) : i.val.1∈H := by
    obtain ⟨t,ht⟩ := i.property
    exact ⟨A i.val t,stellar_spoke_closure F c A hc h₀ h₁ hU i.val (mem_range_self t),ht⟩
  let g : S → (Σ d : H,faceVertices F d.val) := fun i => ⟨⟨i.val.1,hparent i⟩,i.val.2⟩
  have hg : Function.Injective g := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun a : Σ d : H,faceVertices F d.val => (⟨a.1.val,a.2⟩ : Σ d : Faces F,faceVertices F d)) he
  let _ : Fintype H := Fintype.ofFinite H
  have hcount : Nat.card (Σ d : H,faceVertices F d.val)≤Nat.card H*(2*B) := by
    rw [Nat.card_sigma]
    calc
      _≤∑ _d : H,2*B := Finset.sum_le_sum (fun d _ =>
        (face_vertices_card_le F hF P hP d.val).trans (Nat.mul_le_mul_left 2 (hB d.val)))
      _=Nat.card H*(2*B) := by simp [Nat.card_eq_fintype_card]
  have hf := near_faces_card_le F hF P hP f D hdiam x R
  change Nat.card H≤2*Nat.card E at hf
  have hh := (Nat.card_le_card_of_injective g hg).trans hcount
  change Nat.card S≤4*B*Nat.card E
  exact hh.trans (by nlinarith)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι X : Type*} [Finite ι] [Nonempty ι] [PseudoMetricSpace X]

theorem stellar_graph_local_card (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B)
    (f : ℂ → X) (D : ℝ) (hD : 0≤D)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {i : ι ⊕ (Σ d : Faces F,faceVertices F d) | ∃ t:I,dist (f (Sum.elim F A i t)) x<R}≤
      (1+4*B)*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  have hOld : Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R}≤Nat.card E := by
    apply Nat.card_mono (toFinite E)
    rintro i ⟨t,ht⟩
    exact ⟨t,lt_of_lt_of_le ht (le_add_of_nonneg_right hD)⟩
  have hNew := stellar_spokes_local_card F hF P hP c A hc h₀ h₁ hU B hB f D hdiam x R
  have he : Nat.card {i : ι ⊕ (Σ d : Faces F,faceVertices F d) | ∃ t:I,dist (f (Sum.elim F A i t)) x<R}=
      Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R}+
      Nat.card {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R} :=
    (Nat.card_congr Equiv.subtypeSum).trans Nat.card_sum
  rw [he]
  change _≤(1+4*B)*Nat.card E
  change _≤4*B*Nat.card E at hNew
  nlinarith

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

universe u
variable {ι : Type u} [Finite ι] [Nonempty ι]
variable {X : Type*} [PseudoMetricSpace X]

omit [Nonempty ι] in
lemma support_subset_stellar (F : ι → Arc ℂ)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ) :
    (⋃ i,range (F i))⊆⋃ i,range (Sum.elim F A i : Arc ℂ) := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨Sum.inl i,hi⟩

omit [Nonempty ι] in
lemma stellar_support_finite (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : ∀ i,FiniteSupport (range (A i))) :
    ∃ Q : Finset (ℂ × ℂ),∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2 := by
  have hS : ∀ i,FiniteSupport (range (Sum.elim F A i : Arc ℂ)) := by
    rintro (i|i)
    · exact ⟨P,hP i⟩
    · exact hA i
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  exact ⟨Q,fun i => (subset_iUnion _ i).trans hQ⟩

omit [Nonempty ι] in
lemma stellar_faces_diam (F : ι → Arc ℂ) [Finite (Faces F)]
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ) (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D) :
    ∀ e,∀ z∈closure (face (Sum.elim F A) e),∀ w∈closure (face (Sum.elim F A) e),dist (f z) (f w)≤D := by
  intro e z hz w hw
  obtain ⟨d,hd⟩ := face_parent F (Sum.elim F A) (support_subset_stellar F A) e
  exact hdiam d z (closure_mono hd hz) w (closure_mono hd hw)

theorem quantitative_triangular_refinement (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hconn : IsPreconnected (⋃ i,range (F i)))
    (f : ℂ → X) (D E : ℝ) (hD : 0≤D)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (hEdge : ∀ i,∀ t s : I,dist (f (F i t)) (f (F i s))≤E)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B) :
    ∃ (κ : Type u) (H : κ → Arc ℂ), Finite κ ∧ Nonempty κ ∧
      Pairwise (fun i j => Compatible (H i) (H j)) ∧
      (∃ Q : Finset (ℂ × ℂ),∀ i,range (H i)⊆⋃ p∈Q,segment ℝ p.1 p.2) ∧
      (⋃ i,range (F i))⊆(⋃ i,range (H i)) ∧
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
      (∀ i,∀ t s : I,dist (f (H i t)) (f (H i s))≤ max E D) ∧
      (∀ e,∀ z∈closure (face H e),∀ w∈closure (face H e),dist (f z) (f w)≤D) ∧
      (∀ x : X,∀ R : ℝ,
        Nat.card {i : κ | ∃ t:I,dist (f (H i t)) x<R}≤
          (1+12*B)*(1+4*B)*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+2*D}) ∧
      (∀ e : Faces H,∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
        frontier (face H e)=range (H i)∪range (H j)∪range (H k) ∧
        closure (face H e)=face H e∪(range (H i)∪range (H j)∪range (H k))) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  obtain ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK⟩ := global_stellation_no_cut_points F hF P hP hconn
  let G := Sum.elim F A
  obtain ⟨Q,hQ⟩ := stellar_support_finite F P hP A hS
  have hGK' : ∀ q : ℂ,IsPreconnected ((⋃ i,range (G i))\{q}) := by
    intro q
    simpa only [G,iUnion_sum,Sum.elim_inl,Sum.elim_inr] using hGK q
  have hGdiam := stellar_faces_diam F A f D hdiam
  have hGB : ∀ d,Nat.card (regionEdges G ConnectedComponents.mk d)≤3*B := by
    intro e
    obtain ⟨d,hd⟩ := face_parent F G (support_subset_stellar F A) e
    exact (stellar_face_edges_card_le F hF P hP c A hc h₀ hU hG Q hQ hd).trans
      (Nat.mul_le_mul_left 3 (hB d))
  have hGE : ∀ i,∀ t s : I,dist (f (G i t)) (f (G i s))≤ max E D := by
    rintro (i|i) t s
    · exact (hEdge i t s).trans (le_max_left _ _)
    · exact (hdiam i.1 _ (stellar_spoke_closure F c A hc h₀ h₁ hU i (mem_range_self t))
        _ (stellar_spoke_closure F c A hc h₀ h₁ hU i (mem_range_self s))).trans (le_max_right _ _)
  let _ : Finite (Faces G) := faces_finite G hG Q hQ
  obtain ⟨c',A',hc',hH,h₀',h₁',hS',hU',hHK,hTri⟩ := global_triangular_stellation G hG Q hQ hGK'
  let H := Sum.elim G A'
  obtain ⟨Q',hQ'⟩ := stellar_support_finite G Q hQ A' hS'
  refine ⟨_,H,inferInstance,inferInstance,hH,⟨Q',hQ'⟩,
    (support_subset_stellar F A).trans (support_subset_stellar G A'),hHK,?_,
    stellar_faces_diam G A' f D hGdiam,?_,?_⟩
  · rintro (i|i) t s
    · exact hGE i t s
    · exact (hGdiam i.1 _ (stellar_spoke_closure G c' A' hc' h₀' h₁' hU' i (mem_range_self t))
        _ (stellar_spoke_closure G c' A' hc' h₀' h₁' hU' i (mem_range_self s))).trans (le_max_right _ _)
  · intro x R
    have h1 := stellar_graph_local_card G hG Q hQ c' A' hc' h₀' h₁' hU' (3*B) hGB f D hD hGdiam x R
    have h2 := stellar_graph_local_card F hF P hP c A hc h₀ h₁ hU B hB f D hD hdiam x (R+D)
    have hh := h1.trans (Nat.mul_le_mul_left (1+4*(3*B)) h2)
    have heR : R+D+D=R+2*D := by ring
    rw [heR] at hh
    have heB : 1+4*(3*B)=1+12*B := by omega
    rw [heB] at hh
    simpa only [Nat.mul_assoc] using hh
  · intro e
    obtain ⟨d,i,v,w,hiv,hiw,hvw,hsub,hfront,hcl⟩ := hTri e
    refine ⟨Sum.inl i,Sum.inr ⟨d,v⟩,Sum.inr ⟨d,w⟩,by simp,?_,by simp,hfront,hcl⟩
    intro he
    have hh := Sum.inr.inj he
    apply hvw
    apply Subtype.ext
    exact congrArg (fun a : Σ d : Faces G,faceVertices G d => a.2.val) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric

variable {X : Type*} [PseudoMetricSpace X]
lemma continuous_closure_diam (f : ℂ → X) (hf : Continuous f) (U : Set ℂ) (D : ℝ)
    (h : ∀ z∈U,∀ w∈U,dist (f z) (f w)≤D) :
    ∀ z∈closure U,∀ w∈closure U,dist (f z) (f w)≤D := by
  have hrow (z : ℂ) (hz : z∈U) : closure U⊆{w | dist (f z) (f w)≤D} :=
    closure_minimal (h z hz) (isClosed_le (continuous_const.dist hf) continuous_const)
  intro z hz w hw
  have hcol : closure U⊆{z | dist (f z) (f w)≤D} :=
    closure_minimal (fun z hz => hrow z hz hw) (isClosed_le (hf.dist continuous_const) continuous_const)
  exact hcol hz
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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryUniformTriangularGraphs
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
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

  CannonFaceIncidence CannonPlaneLinear CannonIncidence CannonPolygonal
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_triangular_graphs (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ, 1≤M ∧ 1≤L ∧ 0 < r₀ ∧ ∃ N : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ (κ : Type) (H : κ → Arc ℂ), Finite κ ∧ Nonempty κ ∧
        Pairwise (fun i j => Compatible (H i) (H j)) ∧
        (∃ Q : Finset (ℂ × ℂ),∀ i,range (H i)⊆⋃ q∈Q,segment ℝ q.1 q.2) ∧
        (T:Set (Boundary D))⊆e '' (⋃ i,range (H i)) ∧
        (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
        (∀ i,∀ t s : I,dist (e (H i t)) (e (H i s))≤M*r) ∧
        (∀ d,∀ z∈closure (face H d),∀ w∈closure (face H d),dist (e z) (e w)≤L*r) ∧
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ d : Faces H,∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
          frontier (face H d)=range (H i)∪range (H j)∪range (H k) ∧
          closure (face H d)=face H d∪(range (H i)∪range (H j)∪range (H k))) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,L,rG,hA,hL,hrG,K,J,hgraph⟩ := boundary_uniform_controlled_faces D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left _ _)
  let R := 2*M+2*L
  have hR : 0<R := by dsimp only [R]; linarith
  obtain ⟨Q₀,C,hQ₀,hC,hpoly⟩ := relative_polynomial_packing D hδ
  obtain ⟨B,hB⟩ := uniform_larger_trace Q₀ C R hpoly hC.le hR
  refine ⟨M,L,min rG (1/(R+1)),hM,hL,lt_min hrG (by positivity),
    (1+12*J)*(1+4*J)*(B*K),?_⟩
  intro r hr hrs T hsep hcover p hpT
  have hrG' : r ≤ rG := hrs.trans (min_le_left ..)
  have hrR : r≤1/(R+1) := hrs.trans (min_le_right ..)
  have hscale : (R+1)*r≤1 := by
    have hh := (le_div_iff₀ (by linarith : 0<R+1)).mp hrR
    nlinarith
  obtain ⟨e,he,heR,Q,n,hn,F,hF,hFd,hFt,hFJ,hconn,hTV,hFS,hfinite,hsmall,hstructure⟩ :=
    hgraph r hr hrG' T hsep hcover p hpT
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let V : Set (Boundary D) := ⋃ i,range (F i)
  have hrange (i : Fin n) : range (F i)⊆range e :=
    (subset_iUnion (fun j => range (F j)) i).trans (hFS.trans (image_subset_range ..))
  let Fc : Fin n → Arc ℂ := fun i => pullChart e he.isEmbedding (F i) (hrange i)
  have hmap (i : Fin n) (t : I) : e (Fc i t)=F i t := map_pullChart e he.isEmbedding (F i) (hrange i) t
  have hFc : Pairwise (fun i j => Compatible (Fc i) (Fc j)) :=
    fun _ _ hij => pullChart_compatible e he.isEmbedding _ _ _ _ (hF hij)
  have hFcQ (i : Fin n) : range (Fc i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    rintro z ⟨t,rfl⟩
    obtain ⟨w,hw,hew⟩ := hFS (mem_iUnion.mpr ⟨i,mem_range_self t⟩)
    exact he.injective (hew.trans (hmap i t).symm) ▸ hw
  have himage : e '' (⋃ i,range (Fc i))=V := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hw
      exact mem_iUnion.mpr ⟨i,t,(hmap i t).symm⟩
    · intro hz
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
      exact ⟨Fc i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,hmap i t⟩
  have hconnc : IsPreconnected (⋃ i,range (Fc i)) := by
    apply he.isEmbedding.isInducing.isPreconnected_image.mp
    rw [himage]
    exact hconn.isConnected.isPreconnected
  have hfcSmall (d : Faces Fc) :
      ∀ z∈closure (face Fc d),∀ w∈closure (face Fc d),dist (e z) (e w)≤L*r := by
    apply continuous_closure_diam e he.continuous
    have hc : IsPreconnected (e '' face Fc d) :=
      (CannonFaceIncidence.component_region_connected _ d).isPreconnected.image e he.continuous.continuousOn
    have hs : e '' face Fc d⊆Vᶜ := by
      rintro z ⟨w,hw,rfl⟩ hv
      rw [←himage] at hv
      obtain ⟨u,hu,heu⟩ := hv
      have heq := he.injective heu
      subst u
      exact (region_subset _ ConnectedComponents.mk d hw) hu
    intro z hz w hw
    exact (hsmall _ hc hs (e z) (mem_image_of_mem _ hz) (e w) (mem_image_of_mem _ hw)).le
  have hfcE (i : Fin n) (t s : I) : dist (e (Fc i t)) (e (Fc i s))≤A*r := by
    rw [hmap,hmap]
    exact (dist_le_diam_of_mem (F i).compact_range.isBounded (mem_range_self _) (mem_range_self _)).trans (hFd i)
  let _ : LocallyConnectedSpace ((⋃ i,range (Fc i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (Fc i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (Fc i))ᶜ : Set ℂ)) := inferInstance
  have hfcB (d : Faces Fc) : Nat.card (regionEdges Fc ConnectedComponents.mk d)≤J := by
    obtain ⟨x,hx⟩ := face_nonempty Fc d
    have hs : regionEdges Fc ConnectedComponents.mk d⊆
        {i | (range (F i)∩ball (e x) ((L+1)*r)).Nonempty} := by
      intro i hi
      refine ⟨F i 0,mem_range_self 0,?_⟩
      have hcl := region_edge_in_closure Fc hFc Q hFcQ ConnectedComponents.continuous_coe hi (mem_range_self (0:I))
      have hd := hfcSmall d (Fc i 0) hcl x (subset_closure hx)
      rw [hmap] at hd
      change dist (F i 0) (e x)<(L+1)*r
      nlinarith
    calc
      Nat.card (regionEdges Fc ConnectedComponents.mk d)≤
          Nat.card {i | (range (F i)∩ball (e x) ((L+1)*r)).Nonempty} :=
        Nat.card_le_card_of_injective (Set.inclusion hs) (Set.inclusion_injective hs)
      _=intersectionCount F (ball (e x) ((L+1)*r)) := by
        simp [intersectionCount_eq_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
      _≤J := hFJ (e x)
  obtain ⟨κ,H,hκ,hκn,hH,hHQ,hFH,hHK,hHE,hHD,hHC,hTri⟩ :=
    quantitative_triangular_refinement Fc hFc Q hFcQ hconnc e (L*r) (A*r)
      (mul_nonneg (by linarith) hr.le) hfcSmall hfcE J hfcB
  let _ : Finite κ := hκ
  let _ : Nonempty κ := hκn
  refine ⟨e,he,heR,κ,H,hκ,hκn,hH,hHQ,?_,hHK,?_,hHD,?_,hTri⟩
  · apply hTV.trans
    change V⊆e '' (⋃ i,range (H i))
    rw [←himage]
    exact image_mono hFH
  · intro i t s
    have hm : max (A*r) (L*r)=M*r := by
      exact (max_mul_of_nonneg A L hr.le).symm
    exact hm ▸ hHE i t s
  · intro x
    have hlarge := hB r A hr hA hscale T hsep hcover (fun i => range (F i)) K
      (fun x => by simpa only [traceCard,intersectionCount_eq_card] using hFt x) x
    have hcount : Nat.card {i : Fin n | ∃ t:I,dist (e (Fc i t)) x<2*M*r+2*(L*r)}≤B*K := by
      have heq : 2*M*r+2*(L*r)=R*r := by dsimp only [R]; ring
      simp_rw [heq,hmap]
      have hp : {i : Fin n | ∃ t:I,dist (F i t) x<R*r}=
          {i : Fin n | (range (F i)∩ball x (R*r)).Nonempty} := by
        ext i
        constructor
        · rintro ⟨t,ht⟩
          exact ⟨F i t,mem_range_self t,ht⟩
        · rintro ⟨y,⟨t,rfl⟩,hy⟩
          exact ⟨t,hy⟩
      rw [hp]
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,traceCard,Set.mem_ofPred_eq] using hlarge
    exact (hHC x (2*M*r)).trans (Nat.mul_le_mul_left _ hcount)
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
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Demand
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
namespace CannonTriangleCuts
open Finset

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

omit [Fintype V] in
lemma demand_pos (out : Finset V) (v : V) : 0<demand out v := by
  unfold demand
  split_ifs <;> omega
omit [Fintype V] in
lemma demand_sum (out T : Finset V) :
    (∑ v∈T,demand out v)+5*(T.filter fun v=>v∈out).card=6*T.card := by
  have h (v : V) : demand out v+5*(if v∈out then 1 else 0)=6 := by
    unfold demand
    split_ifs <;> omega
  calc
    _=∑ v∈T,(demand out v+5*(if v∈out then 1 else 0)) := by
      rw [sum_add_distrib,←mul_sum]
      simp [Finset.filter_mem_eq_inter]
    _=6*T.card := by simp_rw [h]; simp [mul_comm]

theorem disk_demands (corners : F → Finset V) (out : F)
    (hout : (corners out).card=3)
    (hEuler : Fintype.card F+4=2*Fintype.card V)
    (hbound : ∀ T : Finset V,T≠Finset.univ →
      (∃ f,corners f⊆T) → (Finset.univ.filter fun f=>corners f⊆T).card+5≤2*T.card) :
    (∑ v,demand (corners out) v)=3*Fintype.card {f : F // f≠out} ∧
    ∀ S : Finset V,S.Nonempty → S≠Finset.univ →
      (∑ v∈S,demand (corners out) v)<
        3*(Finset.univ.filter fun f : {f : F // f≠out}=>∃ v∈S,v∈corners f.val).card := by
  classical
  let A := {f : F // f≠out}
  have hAc : Fintype.card A+1=Fintype.card F := by
    have he : Fintype.card A=(Finset.univ.erase out : Finset F).card :=
      Fintype.card_of_subtype _ (fun _=>by simp)
    rw [he,card_erase_add_one (mem_univ out),card_univ]
  have hsum := demand_sum (corners out) (Finset.univ : Finset V)
  have hfilter : (Finset.univ.filter fun v=>v∈corners out)=corners out := by ext v; simp
  rw [hfilter,hout,card_univ] at hsum
  have htotal : (∑ v,demand (corners out) v)=3*Fintype.card A := by omega
  refine ⟨htotal,?_⟩
  intro S hS hSp
  let T := Sᶜ
  let B : Finset F := Finset.univ.filter (fun f=>corners f⊆T)
  let B' : Finset A := Finset.univ.filter (fun f=>corners f.val⊆T)
  let N : Finset A := Finset.univ.filter (fun f=>∃ v∈S,v∈corners f.val)
  have hTp : T≠Finset.univ := by
    obtain ⟨v,hv⟩ := hS
    intro he
    have ht : v∈T := he ▸ mem_univ v
    exact (mem_compl.mp ht) hv
  have hT : T.Nonempty := by
    by_contra hn
    have he : T=∅ := not_nonempty_iff_eq_empty.mp hn
    apply hSp
    ext v
    simp only [mem_univ,iff_true]
    by_contra hv
    have ht : v∈T := mem_compl.mpr hv
    simp only [he,notMem_empty] at ht
  have hBN : B'.card+N.card=Fintype.card A := by
    have he : N=Finset.univ.filter (fun f : A=>¬corners f.val⊆T) := by
      ext f
      simp only [N,mem_filter,mem_univ,true_and,not_subset]
      constructor
      · rintro ⟨v,hvS,hvf⟩
        exact ⟨v,hvf,fun hvT=>(mem_compl.mp hvT) hvS⟩
      · rintro ⟨v,hvf,hvT⟩
        exact ⟨v,by simpa only [T,mem_compl,not_not] using hvT,hvf⟩
    rw [he]
    exact (card_filter_add_card_filter_not (s:=Finset.univ) (fun f : A=>corners f.val⊆T)).trans (card_univ)
  have himage : B'.image (fun f : A=>f.val)=B.erase out := by
    ext f
    simp only [mem_image,mem_filter,mem_univ,true_and,mem_erase,B',B]
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨g.property,hg⟩
    · rintro ⟨hf,hB⟩
      exact ⟨⟨f,hf⟩,hB,rfl⟩
  have hBcard : B'.card=(B.erase out).card := by
    rw [←himage,card_image_of_injective _ Subtype.val_injective]
  have hsplit : (∑ v∈S,demand (corners out) v)+(∑ v∈T,demand (corners out) v)=
      ∑ v,demand (corners out) v := sum_add_sum_compl S _
  have hstrict : 3*B'.card<(∑ v∈T,demand (corners out) v) := by
    by_cases hb : B.Nonempty
    · obtain ⟨f,hf⟩ := hb
      have hpl := hbound T hTp ⟨f,(mem_filter.mp hf).2⟩
      change B.card+5≤2*T.card at hpl
      have hd := demand_sum (corners out) T
      by_cases ho : corners out⊆T
      · have hB : out∈B := mem_filter.mpr ⟨mem_univ _,ho⟩
        have hbc : B'.card+1=B.card := by rw [hBcard,card_erase_add_one hB]
        have hfi : T.filter (fun v=>v∈corners out)=corners out := by
          ext v
          simp only [mem_filter]
          exact ⟨fun h=>h.2,fun h=>⟨ho h,h⟩⟩
        rw [hfi,hout] at hd
        omega
      · have hB : out∉B := by simpa only [B,mem_filter,mem_univ,true_and] using ho
        have hbc : B'.card=B.card := by rw [hBcard,erase_eq_of_notMem hB]
        have hsmall : (T.filter fun v=>v∈corners out).card<3 := by
          rw [←hout]
          apply card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨fun v hv=>(mem_filter.mp hv).2,?_⟩
          intro he
          apply ho
          intro v hv
          exact (mem_filter.mp (he.symm ▸ hv)).1
        omega
    · have hz : B=∅ := not_nonempty_iff_eq_empty.mp hb
      have hz' : B'.card=0 := by rw [hBcard,hz,erase_empty,card_empty]
      rw [hz',mul_zero]
      exact sum_pos (fun v _=>demand_pos _ v) hT
  change (∑ v∈S,demand (corners out) v)<3*N.card
  omega
end CannonTriangleCuts

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_AngleGradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variational angle functional for a conformal circle packing. -/

section
section
section
section
namespace CannonPackingGeometry
open Set Filter Topology MeasureTheory

noncomputable section

lemma angleEntropy_continuous : Continuous angleEntropy := by
  have hs : Continuous (fun θ : ℝ => ∫ x in (0:ℝ)..θ, Real.log (Real.sin x)) :=
    intervalIntegral.continuous_primitive (fun _ _ => intervalIntegrable_log_sin) 0
  have hc : Continuous (fun θ : ℝ => ∫ x in (0:ℝ)..θ, Real.log (Real.cos x)) :=
    intervalIntegral.continuous_primitive (fun _ _ => intervalIntegrable_log_cos) 0
  exact continuous_const.mul ((hs.comp (by fun_prop)).sub (hc.comp (by fun_prop)))

lemma half_trig_pos {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    0 < Real.sin (θ/2) ∧ 0 < Real.cos (θ/2) := by
  rcases hθ with ⟨hθ0,hθπ⟩
  exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩⟩

lemma angleGradient_continuousAt {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    ContinuousAt angleGradient θ := by
  have hh := half_trig_pos hθ
  unfold angleGradient
  apply ContinuousAt.sub
  · apply ContinuousAt.log
    · exact (Real.continuous_sin.comp (continuous_id.div_const 2)).continuousAt
    · exact hh.1.ne'
  · apply ContinuousAt.log
    · exact (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt
    · exact hh.2.ne'

lemma angleEntropy_hasDerivAt {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    HasDerivAt angleEntropy (angleGradient θ) θ := by
  have hh := half_trig_pos hθ
  have hs := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun x => Real.log (Real.sin x)) volume 0 (θ/2) from intervalIntegrable_log_sin)
    ((Real.measurable_log.comp Real.continuous_sin.measurable).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((Real.continuousAt_log hh.1.ne').comp Real.continuous_sin.continuousAt)
  have hc := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun x => Real.log (Real.cos x)) volume 0 (θ/2) from intervalIntegrable_log_cos)
    ((Real.measurable_log.comp Real.continuous_cos.measurable).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((Real.continuousAt_log hh.2.ne').comp Real.continuous_cos.continuousAt)
  have hd := ((hs.comp θ ((hasDerivAt_id θ).div_const 2)).sub
    (hc.comp θ ((hasDerivAt_id θ).div_const 2))).const_mul 2
  have heq : 2 * (Real.log (Real.sin (θ/2))*(1/2) - Real.log (Real.cos (θ/2))*(1/2)) = angleGradient θ := by
    unfold angleGradient
    ring
  rw [heq] at hd
  exact hd

lemma angleGradient_zero_limit : Tendsto angleGradient (𝓝[>] (0:ℝ)) atBot := by
  have hs : Tendsto (fun θ : ℝ => Real.sin (θ/2)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show Continuous (fun θ : ℝ => Real.sin (θ/2)) by fun_prop).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi from Real.pi_pos)] with θ hθ
      exact (half_trig_pos hθ).1
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hs
  have hc : Tendsto (fun θ : ℝ => -Real.log (Real.cos (θ/2))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh : ContinuousAt (fun θ : ℝ => -Real.log (Real.cos (θ/2))) 0 := by
      apply ContinuousAt.neg
      apply ContinuousAt.log
      · fun_prop
      · norm_num
    simpa using hh.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  change Tendsto (fun x : ℝ => Real.log (Real.sin (x/2)) - Real.log (Real.cos (x/2))) _ _
  simpa only [sub_eq_add_neg,Function.comp_def] using hlog.atBot_add hc

lemma angleGradient_pi_sub (θ : ℝ) : angleGradient (Real.pi-θ) = -angleGradient θ := by
  unfold angleGradient
  have heq : (Real.pi-θ)/2=Real.pi/2-θ/2 := by ring
  rw [heq,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  ring

lemma angleGradient_pi_limit : Tendsto angleGradient (𝓝[<] Real.pi) atTop := by
  have ht : Tendsto (fun θ : ℝ => Real.pi-θ) (𝓝[<] Real.pi) (𝓝[>] (0:ℝ)) := by
    have hh := (show ContinuousWithinAt (fun θ : ℝ => Real.pi-θ) (Iio Real.pi) Real.pi from
      (continuous_const.sub continuous_id).continuousWithinAt).tendsto_nhdsWithin
      (show MapsTo (fun θ : ℝ => Real.pi-θ) (Iio Real.pi) (Ioi (0:ℝ)) by intro θ hθ; exact sub_pos.mpr (show θ < Real.pi from hθ))
    simpa using hh
  have hh := tendsto_neg_atBot_atTop.comp (angleGradient_zero_limit.comp ht)
  simpa only [Function.comp_def,angleGradient_pi_sub,neg_neg] using hh

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section

variable {I : Type*} [Fintype I]

lemma angleMove_interior {x s t : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi)
    (hs : s ∈ Ioo (0:ℝ) Real.pi) (ht : t ∈ Ioo (0:ℝ) 1) :
    angleMove x s t ∈ Ioo (0:ℝ) Real.pi := by
  rcases hx with ⟨hx0,hxπ⟩
  rcases hs with ⟨hs0,hsπ⟩
  rcases ht with ⟨ht0,ht1⟩
  unfold angleMove
  have h0 := mul_nonneg (sub_nonneg.mpr ht1.le) hx0
  have h1 := mul_pos ht0 hs0
  have h2 := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hxπ)
  have h3 := mul_pos ht0 (sub_pos.mpr hsπ)
  constructor <;> nlinarith

lemma angleMove_hasDerivAt (x s t : ℝ) : HasDerivAt (angleMove x s) (s-x) t := by
  unfold angleMove
  simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const (s-x)).const_add x

lemma segmentGradient_boundary {x s : ℝ} (hs : s ∈ Ioo (0:ℝ) Real.pi)
    (hx : x=0 ∨ x=Real.pi) :
    Tendsto (segmentGradient x s) (𝓝[>] (0:ℝ)) atBot := by
  rcases hx with rfl | rfl
  · have ht : Tendsto (angleMove 0 s) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [angleMove] using (angleMove_hasDerivAt 0 s 0).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
        exact (angleMove_interior ⟨le_rfl,Real.pi_pos.le⟩ hs ht).1
    change Tendsto (fun t => (s-0)*angleGradient (angleMove 0 s t)) _ _
    simpa only [Function.comp_def] using
      (angleGradient_zero_limit.comp ht).const_mul_atBot (show 0 < s-0 by simpa using hs.1)
  · have ht : Tendsto (angleMove Real.pi s) (𝓝[>] (0:ℝ)) (𝓝[<] Real.pi) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [angleMove] using (angleMove_hasDerivAt Real.pi s 0).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
        exact (angleMove_interior ⟨Real.pi_pos.le,le_rfl⟩ hs ht).2
    exact (angleGradient_pi_limit.comp ht).const_mul_atTop_of_neg (sub_neg.mpr hs.2)

lemma segmentGradient_bounded_above {x s : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi)
    (hs : s ∈ Ioo (0:ℝ) Real.pi) :
    ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0:ℝ), segmentGradient x s t ≤ C := by
  by_cases hb : x=0 ∨ x=Real.pi
  · exact ⟨0,(segmentGradient_boundary hs hb).eventually (eventually_le_atBot 0)⟩
  · have hi : x ∈ Ioo (0:ℝ) Real.pi :=
      ⟨lt_of_le_of_ne hx.1 (fun h => hb (Or.inl h.symm)),
       lt_of_le_of_ne hx.2 (fun h => hb (Or.inr h))⟩
    have h : ContinuousAt (segmentGradient x s) 0 := by
      apply ContinuousAt.const_mul
      have hh : ContinuousAt angleGradient (angleMove x s 0) := by
        simpa only [angleMove,zero_mul,add_zero] using angleGradient_continuousAt hi
      exact hh.comp (angleMove_hasDerivAt x s 0).continuousAt
    refine ⟨segmentGradient x s 0+1,?_⟩
    exact (h.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (eventually_le_nhds (by linarith))

lemma sum_tendsto_atBot_of_one {F : I → ℝ → ℝ} {l : Filter ℝ} (j : I)
    (hj : Tendsto (F j) l atBot) (hB : ∀ i, ∃ C : ℝ, ∀ᶠ t in l, F i t ≤ C) :
    Tendsto (fun t => ∑ i, F i t) l atBot := by
  classical
  choose C hC using hB
  apply tendsto_atBot.mpr
  intro b
  have hc : ∀ᶠ t in l, ∀ i, F i t ≤ C i := Filter.eventually_all.mpr hC
  filter_upwards [hc,hj.eventually (eventually_le_atBot (b-∑ i ∈ Finset.univ.erase j,C i))] with t hCt hjt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hh := Finset.sum_le_sum (s:=Finset.univ.erase j) (fun i _ => hCt i)
  linarith

lemma entropy_segment_hasDerivAt (x s : I → ℝ) {t : ℝ}
    (hx : ∀ i, x i ∈ Icc (0:ℝ) Real.pi) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => ∑ i, angleEntropy (angleMove (x i) (s i) u))
      (∑ i, segmentGradient (x i) (s i) t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  unfold segmentGradient
  convert! (angleEntropy_hasDerivAt (angleMove_interior (hx i) (hs i) ht)).comp t
      (angleMove_hasDerivAt (x i) (s i) t) using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem entropy_boundary_descent (x s : I → ℝ)
    (hx : ∀ i, x i ∈ Icc (0:ℝ) Real.pi) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (hb : ∃ j, x j=0 ∨ x j=Real.pi) :
    ∃ t ∈ Ioo (0:ℝ) 1,
      (∑ i, angleEntropy (angleMove (x i) (s i) t)) < ∑ i, angleEntropy (x i) := by
  obtain ⟨j,hj⟩ := hb
  have hg : Tendsto (fun t => ∑ i, segmentGradient (x i) (s i) t) (𝓝[>] (0:ℝ)) atBot :=
    sum_tendsto_atBot_of_one j (segmentGradient_boundary (hs j) hj)
      (fun i => segmentGradient_bounded_above (hx i) (hs i))
  have hn := hg.eventually (eventually_lt_atBot (0:ℝ))
  obtain ⟨ε,hε,hne⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let e : ℝ := min (ε/2) (1/2)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have heε : e<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he1 : e<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hanti : StrictAntiOn (fun t => ∑ i, angleEntropy (angleMove (x i) (s i) t)) (Icc 0 e) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · apply Continuous.continuousOn
      apply continuous_finsetSum
      intro i _
      exact angleEntropy_continuous.comp (by unfold angleMove; fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans he1⟩
      rw [(entropy_segment_hasDerivAt x s hx hs ht1).deriv]
      apply hne
      exact ⟨by rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht.1]; exact ht.2.trans heε,ht.1⟩
  refine ⟨e,⟨he,he1⟩,?_⟩
  simpa [angleMove] using hanti (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,he.le⟩)
    (show e∈Icc 0 e from ⟨he.le,le_rfl⟩) he

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma angleSum_continuous : Continuous (angleSum (I:=I)) := by
  apply continuous_finsetSum
  intro i _
  exact angleEntropy_continuous.comp (continuous_apply i)

omit [Fintype I] [Fintype J] in
lemma angleFeasible_compact (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ) :
    IsCompact (angleFeasible L b) := by
  have hc : IsClosed {x : I → ℝ | ∀ j, L j x=b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_eq (L j).continuous continuous_const)
  have heq : angleFeasible L b = (Set.univ.pi (fun _ : I => Icc (0:ℝ) Real.pi)) ∩
      {x | ∀ j, L j x=b j} := by
    ext x
    simp only [angleFeasible,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_pi,Set.mem_univ,true_implies]
  rw [heq]
  exact (isCompact_univ_pi (fun _ : I => isCompact_Icc)).inter_right hc

omit [Fintype J] in
theorem exists_interior_angle_minimizer (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (s : I → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi) (hsL : ∀ j, L j s=b j) :
    ∃ x : I → ℝ, (∀ i, x i ∈ Ioo (0:ℝ) Real.pi) ∧ (∀ j, L j x=b j) ∧
      IsMinOn angleSum (angleFeasible L b) x := by
  have hsK : s ∈ angleFeasible L b := ⟨fun i => ⟨(hs i).1.le,(hs i).2.le⟩,hsL⟩
  obtain ⟨x,hxK,hmin⟩ := (angleFeasible_compact L b).exists_isMinOn ⟨s,hsK⟩ angleSum_continuous.continuousOn
  have hnob : ¬∃ i, x i=0 ∨ x i=Real.pi := by
    intro hb
    obtain ⟨t,ht,hdes⟩ := entropy_boundary_descent x s hxK.1 hs hb
    have hyK : (fun i => angleMove (x i) (s i) t) ∈ angleFeasible L b := by
      constructor
      · intro i
        exact ⟨(angleMove_interior (hxK.1 i) (hs i) ht).1.le,
          (angleMove_interior (hxK.1 i) (hs i) ht).2.le⟩
      · intro j
        change L j (x + t • (s-x))=b j
        rw [map_add,map_smul,map_sub,hxK.2 j,hsL j]
        simp
    exact (not_lt_of_ge (hmin hyK)) hdes
  refine ⟨x,fun i => ⟨?_,?_⟩,hxK.2,hmin⟩
  · exact lt_of_le_of_ne (hxK.1 i).1 (fun h => hnob ⟨i,Or.inl h.symm⟩)
  · exact lt_of_le_of_ne (hxK.1 i).2 (fun h => hnob ⟨i,Or.inr h⟩)

lemma angleSum_line_derivative (x v : I → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) Real.pi) :
    HasDerivAt (fun t : ℝ => angleSum (x+t • v)) (∑ i, angleGradient (x i)*v i) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hinner : HasDerivAt (fun t : ℝ => x i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)
  have ho : HasDerivAt angleEntropy (angleGradient (x i)) (x i+0*v i) := by
    simpa only [zero_mul,add_zero] using angleEntropy_hasDerivAt (hx i)
  have hd := ho.comp 0 hinner
  exact hd

omit [Fintype J] in
lemma angle_minimizer_stationary (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (x : I → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) Real.pi) (hxL : ∀ j, L j x=b j)
    (hmin : IsMinOn angleSum (angleFeasible L b) x)
    (v : I → ℝ) (hv : ∀ j, L j v=0) : ∑ i, angleGradient (x i)*v i=0 := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ∈ Ioo (0:ℝ) Real.pi := by
    apply Filter.eventually_all.mpr
    intro i
    have h : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
    have hh := h.tendsto.eventually (Ioo_mem_nhds (show 0<x i+0*v i by simpa using (hx i).1)
      (show x i+0*v i<Real.pi by simpa using (hx i).2))
    exact hh
  have hm : IsLocalMin (fun t : ℝ => angleSum (x+t • v)) 0 := by
    filter_upwards [he] with t ht
    simp only [zero_smul,add_zero]
    apply hmin
    constructor
    · intro i
      exact ⟨(ht i).1.le,(ht i).2.le⟩
    · intro j
      rw [map_add,map_smul,hxL j,hv j,smul_zero,add_zero]
  exact hm.hasDerivAt_eq_zero (angleSum_line_derivative x v hx)

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set Filter Topology

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem exists_angle_multipliers [DecidableEq I] (L : J → (I → ℝ) →L[ℝ] ℝ) (b : J → ℝ)
    (s : I → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi) (hsL : ∀ j, L j s=b j) :
    ∃ (x : I → ℝ) (c : J → ℝ), (∀ i, x i ∈ Ioo (0:ℝ) Real.pi) ∧ (∀ j, L j x=b j) ∧
      ∀ i, angleGradient (x i) = ∑ j, c j * L j (Pi.single i 1) := by
  classical
  obtain ⟨x,hx,hxL,hmin⟩ := exists_interior_angle_minimizer L b s hs hsL
  let K : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, angleGradient (x i) • LinearMap.proj i
  have hK (v : I → ℝ) : K v=∑ i, angleGradient (x i)*v i := by
    simp only [K,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]
  have hker : (⨅ j, LinearMap.ker (L j).toLinearMap) ≤ LinearMap.ker K := by
    intro v hv
    change K v=0
    rw [hK]
    apply angle_minimizer_stationary L b x hx hxL hmin v
    intro j
    exact ((Submodule.mem_iInf _).mp hv j)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨x,c,hx,hxL,fun i => ?_⟩
  have he := LinearMap.congr_fun hc (Pi.single i (1:ℝ))
  rw [hK] at he
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_eq_mul,
    Pi.single_apply,mul_ite,Finset.sum_ite_irrel,Finset.mem_univ,ite_true,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq] using he.symm

end
end CannonPackingGeometry

namespace CannonPackingGeometry
open Set

noncomputable section
variable {F V : Type*} [Fintype F] [Fintype V] [DecidableEq F] [DecidableEq V]

omit [Fintype V] [DecidableEq F] in
lemma vertexCornerSum_apply (vertex : F × Fin 3 → V) (v : V) (θ : F × Fin 3 → ℝ) :
    vertexCornerSum vertex v θ=∑ i : F × Fin 3, if vertex i=v then θ i else 0 := by
  unfold vertexCornerSum
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

omit [Fintype F] in
lemma faceCornerSum_single (f : F) (i : F × Fin 3) :
    faceCornerSum f (Pi.single i 1) = if f=i.1 then 1 else 0 := by
  classical
  rcases i with ⟨g,k⟩
  by_cases hfg : f=g
  · subst g
    simp [faceCornerSum,ContinuousLinearMap.proj_apply,
      Pi.single_apply,Prod.mk.injEq]
  · simp [faceCornerSum,ContinuousLinearMap.proj_apply,Prod.mk.injEq,hfg]

omit [Fintype V] in
lemma vertexCornerSum_single (vertex : F × Fin 3 → V) (v : V) (i : F × Fin 3) :
    vertexCornerSum vertex v (Pi.single i 1) = if vertex i=v then 1 else 0 := by
  classical
  simp only [vertexCornerSum,sum_apply]
  have he : ∀ j : F × Fin 3,
      (if vertex j=v then ContinuousLinearMap.proj j else (0 : ((F × Fin 3) → ℝ) →L[ℝ] ℝ)) (Pi.single i 1) =
      if j=i then (if vertex i=v then 1 else 0) else 0 := by
    intro j
    by_cases hji : j=i
    · subst j
      by_cases hv : vertex i=v <;> simp [hv]
    · by_cases hv : vertex j=v <;> simp [hv,hji]
  simp_rw [he]
  simp

lemma exp_angleGradient {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    Real.exp (angleGradient θ)=Real.tan (θ/2) := by
  have hh := half_trig_pos hθ
  rw [Real.tan_eq_sin_div_cos,angleGradient,← Real.log_div hh.1.ne' hh.2.ne']
  exact Real.exp_log (div_pos hh.1 hh.2)

theorem coherent_angles_give_radii (vertex : F × Fin 3 → V) (target : V → ℝ)
    (s : F × Fin 3 → ℝ) (hs : ∀ i, s i ∈ Ioo (0:ℝ) Real.pi)
    (hsface : ∀ f, ∑ k : Fin 3, s (f,k)=Real.pi)
    (hsvertex : ∀ v, (∑ i : F × Fin 3, if vertex i=v then s i else 0)=target v) :
    ∃ (θ : F × Fin 3 → ℝ) (r : V → ℝ) (q : F → ℝ),
      (∀ i, θ i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, θ (f,k)=Real.pi) ∧
      (∀ v, (∑ i : F × Fin 3, if vertex i=v then θ i else 0)=target v) ∧
      (∀ v, 0 < r v) ∧ (∀ f, 0<q f) ∧
      ∀ i, Real.tan (θ i/2)=q i.1/r (vertex i) := by
  classical
  let L := cornerConstraint vertex
  let b : F ⊕ V → ℝ := Sum.elim (fun _ => Real.pi) target
  have hsL : ∀ j, L j s=b j := by
    intro j
    cases j with
    | inl f => simpa [L,b,cornerConstraint,faceCornerSum,sum_apply] using hsface f
    | inr v =>
      simpa only [L,b,cornerConstraint,Sum.elim_inr,vertexCornerSum_apply] using hsvertex v
  obtain ⟨θ,c,hθ,hθL,hgrad⟩ := exists_angle_multipliers L b s hs hsL
  refine ⟨θ,(fun v => Real.exp (-c (Sum.inr v))),(fun f => Real.exp (c (Sum.inl f))),
    hθ,?_,?_,fun _ => Real.exp_pos _,fun _ => Real.exp_pos _,?_⟩
  · intro f
    simpa [L,b,cornerConstraint,faceCornerSum,sum_apply] using hθL (Sum.inl f)
  · intro v
    simpa only [L,b,cornerConstraint,Sum.elim_inr,vertexCornerSum_apply] using hθL (Sum.inr v)
  · intro i
    have he : angleGradient (θ i)=c (Sum.inl i.1)+c (Sum.inr (vertex i)) := by
      rw [hgrad, Fintype.sum_sum_type]
      simp only [L,cornerConstraint,Sum.elim_inl,Sum.elim_inr,
        faceCornerSum_single,vertexCornerSum_single,mul_ite,mul_one,mul_zero]
      simp [eq_comm]
    rw [← exp_angleGradient (hθ i),he,← Real.exp_sub]
    congr 1
    ring

end
end CannonPackingGeometry

end
section
noncomputable section
namespace CannonPackingGeometry
open Finset Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

omit [DecidableEq F] in
theorem weighted_hall_equiv (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ)
    (hcut : ∀ S : Finset V, ∑ v∈S, d v ≤ ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ e : (Σ v, Fin (d v)) ≃ (Σ f, Fin (c f)), ∀ a, R a.1 (e a).1 := by
  classical
  let A := Σ v, Fin (d v)
  let B := Σ f, Fin (c f)
  have hh : ∀ S : Finset A,
      S.card ≤ (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)).card := by
    intro S
    let T : Finset V := S.image Sigma.fst
    have hS : S ⊆ T.sigma (fun v => (univ : Finset (Fin (d v)))) := by
      intro a ha
      exact mem_sigma.mpr ⟨mem_image.mpr ⟨a,ha,rfl⟩,mem_univ _⟩
    have hN : (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)) =
        (neighborFaces R T).sigma (fun f => (univ : Finset (Fin (c f)))) := by
      ext b
      constructor
      · intro hb
        obtain ⟨a,ha,hR⟩ := (mem_filter.mp hb).2
        apply Finset.mem_sigma.mpr
        exact ⟨mem_filter.mpr ⟨mem_univ _,a.1,mem_image.mpr ⟨a,ha,rfl⟩,hR⟩,
          mem_univ _⟩
      · intro hb
        have hb' := Finset.mem_sigma.mp hb
        obtain ⟨v,hv,hR⟩ := (mem_filter.mp hb'.1).2
        obtain ⟨a,ha,hav⟩ := mem_image.mp hv
        apply mem_filter.mpr
        exact ⟨mem_univ _,a,ha,hav.symm ▸ hR⟩
    calc
      S.card ≤ (T.sigma (fun v => (univ : Finset (Fin (d v))))).card := card_le_card hS
      _ = ∑ v∈T, d v := by simp [card_sigma]
      _ ≤ ∑ f∈neighborFaces R T, c f := hcut T
      _ = (univ.filter (fun b : B => ∃ a∈S, R a.1 b.1)).card := by rw [hN,card_sigma]; simp only [card_univ,Fintype.card_fin]
  obtain ⟨g,hg,hgR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (a : A) (b : B) => R a.1 b.1)).mp hh
  have hcard : Fintype.card A = Fintype.card B := by
    simpa [A,B,Fintype.card_sigma] using htotal
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hcard⟩),hgR⟩

theorem integer_transport (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ)
    (hcut : ∀ S : Finset V, ∑ v∈S, d v ≤ ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ w : V → F → ℕ,
      (∀ v, ∑ f, w v f = d v) ∧ (∀ f, ∑ v, w v f = c f) ∧
      ∀ v f, ¬R v f → w v f=0 := by
  classical
  obtain ⟨e,he⟩ := weighted_hall_equiv R d c hcut htotal
  let A := Σ v, Fin (d v)
  let B := Σ f, Fin (c f)
  let w : V → F → ℕ := fun v f =>
    ∑ a : A, if a.1=v ∧ (e a).1=f then 1 else 0
  refine ⟨w,?_,?_,?_⟩
  · intro v
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ a : A, ∑ f, if a.1=v ∧ (e a).1=f then 1 else 0) =
          ∑ a : A, if a.1=v then 1 else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases ha : a.1=v <;> simp [ha]
      _ = d v := by
        change (∑ a : (Σ v, Fin (d v)), if a.1=v then 1 else 0)=d v
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ x : V, if x=v then d x else 0 := by
            apply sum_congr rfl
            intro x _
            by_cases h : x=v <;> simp [h]
          _ = d v := by simp
  · intro f
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ a : A, ∑ v, if a.1=v ∧ (e a).1=f then 1 else 0) =
          ∑ a : A, if (e a).1=f then 1 else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases ha : (e a).1=f <;> simp [ha]
      _ = ∑ b : B, if b.1=f then 1 else 0 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = c f := by
        change (∑ b : (Σ f, Fin (c f)), if b.1=f then 1 else 0)=c f
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ x : F, if x=f then c x else 0 := by
            apply sum_congr rfl
            intro x _
            by_cases h : x=f <;> simp [h]
          _ = c f := by simp
  · intro v f hnot
    apply sum_eq_zero
    intro a _
    split_ifs with h
    · exact (hnot (h.1 ▸ h.2 ▸ he a)).elim
    · rfl

end CannonPackingGeometry

namespace CannonPackingGeometry
open Finset Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem positive_transport (R : V → F → Prop) [DecidableRel R]
    (d : V → ℕ) (c : F → ℕ) (hd : ∀ v, 0<d v) (hc : ∀ f, 0 < c f)
    (hactive : ∀ f, ∃ v, R v f)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ →
      (∑ v∈S, d v) < ∑ f∈neighborFaces R S, c f)
    (htotal : ∑ v, d v = ∑ f, c f) :
    ∃ w : V → F → ℝ,
      (∀ v f, R v f → 0<w v f) ∧ (∀ v f, ¬R v f → w v f=0) ∧
      (∀ v, ∑ f, w v f = d v) ∧ (∀ f, ∑ v, w v f = c f) := by
  classical
  let dv : V → ℕ := fun v => ∑ f, if R v f then 1 else 0
  let df : F → ℕ := fun f => ∑ v, if R v f then 1 else 0
  let E : ℕ := ∑ v, dv v
  let Q : ℕ := E+1
  have hQ : 0<Q := Nat.succ_pos _
  have hE : ∑ f, df f=E := by dsimp [E,dv,df]; rw [sum_comm]
  have hdv (v : V) : dv v ≤ Q*d v := by
    have hh : dv v≤E := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    have hp : 1≤d v := hd v
    have hQE : E<Q := Nat.lt_succ_self _
    nlinarith
  have hdf (f : F) : df f ≤ Q*c f := by
    have hh : df f≤E := (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ f)).trans_eq hE
    have hp : 1 ≤ c f := hc f
    have hQE : E<Q := Nat.lt_succ_self _
    nlinarith
  let D : V → ℕ := fun v => Q*d v-dv v
  let C : F → ℕ := fun f => Q*c f-df f
  have hD (S : Finset V) : (∑ v∈S,D v)+(∑ v∈S,dv v)=Q*(∑ v∈S,d v) := by
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel (hdv v))
  have hC (T : Finset F) : (∑ f∈T,C f)+(∑ f∈T,df f)=Q*(∑ f∈T,c f) := by
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun f _ => Nat.sub_add_cancel (hdf f))
  have hfull : ∑ v,D v=∑ f,C f := by
    have hv := hD univ
    have hf := hC univ
    rw [hE,←htotal] at hf
    change (∑ v,D v)+E=Q*(∑ v,d v) at hv
    omega
  have hrescut (S : Finset V) : ∑ v∈S,D v ≤ ∑ f∈neighborFaces R S,C f := by
    by_cases hs : S=∅
    · subst S
      simp
    by_cases ht : S=univ
    · subst S
      have hn : neighborFaces R univ=univ := by
        ext f
        simp only [neighborFaces,mem_filter,mem_univ,true_and]
        exact iff_true_intro (by obtain ⟨v,hv⟩ := hactive f; exact ⟨v,hv⟩)
      rw [hn]
      exact hfull.le
    have hgap := hcut S (nonempty_iff_ne_empty.mpr hs) ht
    have hmul := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt hgap)
    simp only [Nat.succ_eq_add_one,mul_add,mul_one] at hmul
    have hv := hD S
    have hf := hC (neighborFaces R S)
    have hde : ∑ f∈neighborFaces R S, df f ≤ E := by
      rw [←hE]
      exact sum_le_sum_of_subset (subset_univ _)
    have hQE : E<Q := Nat.lt_succ_self _
    rw [←hv,←hf] at hmul
    omega
  obtain ⟨w,hwv,hwf,hwzero⟩ := integer_transport R D C hrescut hfull
  let p : V → F → ℕ := fun v f => w v f + if R v f then 1 else 0
  have hpv (v : V) : ∑ f,p v f=Q*d v := by
    simp only [p,sum_add_distrib,hwv]
    exact Nat.sub_add_cancel (hdv v)
  have hpf (f : F) : ∑ v,p v f=Q*c f := by
    simp only [p,sum_add_distrib,hwf]
    exact Nat.sub_add_cancel (hdf f)
  have hpzero (v : V) (f : F) (h : ¬R v f) : p v f=0 := by simp [p,h,hwzero v f h]
  refine ⟨fun v f => (p v f : ℝ)/(Q:ℝ),?_,?_,?_,?_⟩
  · intro v f hR
    apply div_pos
    · exact_mod_cast (show 0<p v f by simp [p,hR])
    · exact_mod_cast hQ
  · intro v f hR
    change (p v f : ℝ)/(Q:ℝ)=0
    rw [hpzero v f hR]
    simp
  · intro v
    rw [←sum_div,←Nat.cast_sum,hpv,Nat.cast_mul]
    exact mul_div_cancel_left₀ (d v : ℝ) (by exact_mod_cast hQ.ne')
  · intro f
    rw [←sum_div,←Nat.cast_sum,hpf,Nat.cast_mul]
    exact mul_div_cancel_left₀ (c f : ℝ) (by exact_mod_cast hQ.ne')

end CannonPackingGeometry

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_StrictCutsGiveAngles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict cut inequalities yield coherent angles and circle radii. -/

section
section
section
section
noncomputable section
namespace CannonPackingGeometry
open Finset Set Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem strict_cuts_give_angles (vertex : F × Fin 3 → V)
    (hinj : ∀ f, Injective (fun k => vertex (f,k)))
    (d : V → ℕ) (hd : ∀ v, 0<d v)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠Finset.univ →
      (∑ v∈S,d v) < 3 * (neighborFaces (fun v f => ∃ k, vertex (f,k)=v) S).card)
    (htotal : ∑ v,d v = 3 * Fintype.card F) :
    ∃ s : F × Fin 3 → ℝ, (∀ i, s i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, s (f,k)=Real.pi) ∧
      ∀ v, (∑ i : F × Fin 3, if vertex i=v then s i else 0)=Real.pi/3*(d v:ℝ) := by
  classical
  let R : V → F → Prop := fun v f => ∃ k, vertex (f,k)=v
  obtain ⟨w,hwp,hwz,hwv,hwf⟩ := positive_transport R d (fun _ => 3) hd
    (fun _ => by norm_num) (fun f => ⟨vertex (f,0),0,rfl⟩)
    (by intro S hs ht; simpa [R,sum_const,smul_eq_mul,mul_comm] using hcut S hs ht)
    (by simpa [sum_const,smul_eq_mul,mul_comm] using htotal)
  have hface (f : F) : ∑ k : Fin 3, w (vertex (f,k)) f=3 := by
    calc
      _ = ∑ v, w v f := Fintype.sum_of_injective (fun k => vertex (f,k)) (hinj f)
        _ _ (fun v hv => hwz v f hv) (fun _ => rfl)
      _ = 3 := by simpa using hwf f
  have hpos (f : F) (k : Fin 3) : 0<w (vertex (f,k)) f := hwp _ _ ⟨k,rfl⟩
  have hlt (f : F) (k : Fin 3) : w (vertex (f,k)) f<3 := by
    have hh := hface f
    simp only [Fin.sum_univ_three] at hh
    have h0 := hpos f 0
    have h1 := hpos f 1
    have h2 := hpos f 2
    fin_cases k
    · change w (vertex (f,0)) f<3
      linarith
    · change w (vertex (f,1)) f<3
      linarith
    · change w (vertex (f,2)) f<3
      linarith
  have hvertex (v : V) (f : F) :
      ∑ k : Fin 3, (if vertex (f,k)=v then w (vertex (f,k)) f else 0)=w v f := by
    calc
      _ = ∑ u : V, if u=v then w u f else 0 := by
        apply Fintype.sum_of_injective (fun k => vertex (f,k)) (hinj f)
        · intro u hu
          by_cases huv : u=v
          · subst u
            simp [hwz v f hu]
          · simp [huv]
        · intro k
          rfl
      _ = w v f := by simp
  let s : F × Fin 3 → ℝ := fun i => Real.pi/3*w (vertex i) i.1
  refine ⟨s,?_,?_,?_⟩
  · rintro ⟨f,k⟩
    have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
    constructor
    · exact mul_pos hp (hpos f k)
    · have hh := mul_lt_mul_of_pos_left (hlt f k) hp
      dsimp [s]
      nlinarith
  · intro f
    change (∑ k : Fin 3, Real.pi/3*w (vertex (f,k)) f)=Real.pi
    rw [←mul_sum,hface]
    ring
  · intro v
    have hi (i : F × Fin 3) :
        (if vertex i=v then s i else 0) = Real.pi/3*(if vertex i=v then w (vertex i) i.1 else 0) := by
      by_cases h : vertex i=v <;> simp [s,h]
    simp_rw [hi]
    rw [←mul_sum,Fintype.sum_prod_type]
    simp_rw [hvertex]
    rw [hwv]

end CannonPackingGeometry

end
end
namespace CannonPackingGeometry
open Set Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem strict_cuts_give_radii (vertex : F × Fin 3 → V)
    (hinj : ∀ f, Injective (fun k => vertex (f,k)))
    (d : V → ℕ) (hd : ∀ v, 0<d v)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠Finset.univ →
      (∑ v∈S,d v) < 3 * (neighborFaces (fun v f => ∃ k, vertex (f,k)=v) S).card)
    (htotal : ∑ v,d v = 3 * Fintype.card F) :
    ∃ (θ : F × Fin 3 → ℝ) (r : V → ℝ) (q : F → ℝ),
      (∀ i, θ i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, θ (f,k)=Real.pi) ∧
      (∀ v, (∑ i : F × Fin 3, if vertex i=v then θ i else 0)=Real.pi/3*(d v:ℝ)) ∧
      (∀ v, 0 < r v) ∧ (∀ f, 0<q f) ∧
      ∀ i, Real.tan (θ i/2)=q i.1/r (vertex i) := by
  obtain ⟨s,hs,hsf,hsv⟩ := strict_cuts_give_angles vertex hinj d hd hcut htotal
  exact coherent_angles_give_radii vertex (fun v => Real.pi/3*(d v:ℝ)) s hs hsf hsv
end CannonPackingGeometry

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoncutEdgeTwoFaces
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
noncomputable section
noncomputable section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem noncut_facial_vertices_edges (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (faceVertices F d).card=Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let V := faceVertices F d
  let C (q : V) : Set E := {e | q.val∈range (F e.val)}
  let B (e : E) : Set V := {q | q.val∈range (F e.val)}
  have hC (q : V) : Nat.card (C q)=2 := by
    have hq := (mem_faceVertices F d q.val).mp q.property
    have hq' := hq.2
    have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
    change closure (face F d)=face F d∪⋃ e∈E,range (F e) at hcl
    rw [hcl] at hq'
    have hs : q.val∈⋃ e∈E,range (F e) := hq'.resolve_left (fun hh=>hh.1 (vertex_mem_support F hq.1))
    obtain ⟨i,hi,hqi⟩ := mem_iUnion₂.mp hs
    obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF Q hQ hK d hq.1 hi hqi
    let i' : E := ⟨i,hi⟩
    let j' : E := ⟨j,hj⟩
    change (C q).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨i',j',fun he=>hji (congrArg Subtype.val he).symm,?_⟩
    ext k
    constructor
    · intro hk
      rcases face_edge_eq F hF Q hQ hq.1 (hK q.val) d hji.symm hi hj k.property hqi hqj hk with h|h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl|rfl)
      · exact hqi
      · exact hqj
  have hB (e : E) : Nat.card (B e)=2 := by
    have hend (t : I) (ht : t=0 ∨ t=1) : F e.val t∈V := by
      apply (mem_faceVertices F d _).mpr
      refine ⟨⟨e.val,?_⟩,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe e.property (mem_range_self t)⟩
      rcases ht with rfl|rfl <;> simp
    let a : V := ⟨F e.val 0,hend 0 (Or.inl rfl)⟩
    let b : V := ⟨F e.val 1,hend 1 (Or.inr rfl)⟩
    change (B e).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨a,b,fun he=>(F e.val).endpoints_ne (congrArg Subtype.val he),?_⟩
    ext q
    constructor
    · rintro ⟨t,ht⟩
      have hv := (mem_faceVertices F d q.val).mp q.property |>.1
      rcases vertex_parameter F hF e.val (ht.symm ▸ hv) with h|h
      · subst t
        exact Or.inl (Subtype.ext ht.symm)
      · subst t
        exact Or.inr (Subtype.ext ht.symm)
    · rintro (rfl|rfl)
      · exact mem_range_self 0
      · exact mem_range_self 1
  let e : (Σ q : V,C q) ≃ Σ i : E,B i :=
    { toFun := fun ⟨q,i⟩=>⟨i.val,⟨q,i.property⟩⟩
      invFun := fun ⟨i,q⟩=>⟨q.val,⟨i,q.property⟩⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  have hh := Nat.card_congr e
  rw [Nat.card_sigma,Nat.card_sigma] at hh
  simp only [hC,hB,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  simp only [Fintype.card_coe] at hh
  have heq : V.card=Fintype.card E := by omega
  simpa only [V,E,Nat.card_eq_fintype_card] using heq

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
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IntrinsicCircleData
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
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem triangular_graph_radii (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (htri : ∀ d : Faces F,∃ i j k : ι,i≠j ∧ j≠k ∧ k≠i ∧
      closure (face F d)=face F d∪(range (F i)∪range (F j)∪range (F k)))
    (out : Faces F) :
    let _ : Finite (Faces F) := faces_finite F hF Q hQ
    let _ := Fintype.ofFinite (Faces F)
    let _ := Classical.decEq (Faces F)
    let V := vertices F Finset.univ
    let A := {d : Faces F // d≠out}
    ∃ vertex : A × Fin 3 → V,
      (∀ f,Function.Injective (fun k=>vertex (f,k))) ∧
      (∀ f,range (fun k=>(vertex (f,k)).val)=(faceVertices F f.val : Set ℂ)) ∧
      ∃ θ : A × Fin 3 → ℝ, ∃ r : V → ℝ,∃ q : A → ℝ,
        (∀ i,θ i∈Ioo (0:ℝ) Real.pi) ∧
        (∀ f,∑ k:Fin 3,θ (f,k)=Real.pi) ∧
        (∀ v,(∑ i : A×Fin 3,if vertex i=v then θ i else 0)=
          if v.val∈faceVertices F out then Real.pi/3 else 2*Real.pi) ∧
        (∀ v,0 < r v) ∧ (∀ f,0<q f) ∧
        ∀ i,Real.tan (θ i/2)=q i.1/r (vertex i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ := Fintype.ofFinite (Faces F)
  dsimp only
  let V := vertices F Finset.univ
  let A := {d : Faces F // d≠out}
  let corners : Faces F → Finset V := fun d=>Finset.univ.filter (fun v=>v.val∈faceVertices F d)
  have himage (d : Faces F) : (corners d).image (fun v:V=>v.val)=faceVertices F d := by
    ext z
    simp only [Finset.mem_image,corners,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hz
      have hv : z∈V := by
        obtain ⟨i,hi⟩ := ((mem_faceVertices F d z).mp hz).1
        exact (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
      exact ⟨⟨z,hv⟩,hz,rfl⟩
  obtain ⟨hcorner,hEuler,_⟩ := CannonPlanarEuler.triangular_counts F hF Q hQ hK htri
  have hthree (d : Faces F) : (corners d).card=3 := by
    rw [←hcorner d,←himage d,Finset.card_image_of_injective _ Subtype.val_injective]
  have hregion (d : Faces F) : 3≤Nat.card (regionEdges F ConnectedComponents.mk d) := by
    rw [←noncut_facial_vertices_edges F hF Q hQ hK d,hcorner d]
  have hbounds (T : Finset V) (hT : T≠Finset.univ) (hB : ∃ d,corners d⊆T) :
      (Finset.univ.filter fun d=>corners d⊆T).card+5≤2*T.card := by
    let U := T.image (fun v:V=>v.val)
    have heq (d : Faces F) : corners d⊆T ↔ faceVertices F d⊆U := by
      rw [←himage d]
      exact (Finset.image_subset_image_iff Subtype.val_injective).symm
    have hproper : ¬vertices F Finset.univ⊆U := by
      intro hh
      apply hT
      apply Finset.eq_univ_of_forall
      intro v
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hh v.property)
      have : w=v := Subtype.ext he
      exact this ▸ hw
    have hb : ∃ d,faceVertices F d⊆U := by
      obtain ⟨d,hd⟩ := hB
      exact ⟨d,(heq d).mp hd⟩
    have hp := proper_facial_bound F hF Q hQ hregion U hproper hb
    have hn : Nat.card {d : Faces F | faceVertices F d⊆U}=
        (Finset.univ.filter fun d=>corners d⊆T).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype _ (fun d=>by simp only [Finset.mem_filter,Finset.mem_univ,true_and,heq,Set.mem_ofPred_eq])
    rw [hn,Finset.card_image_of_injective _ Subtype.val_injective] at hp
    exact hp
  have hE : Fintype.card (Faces F)+4=2*Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hEuler
  obtain ⟨htotal,hcut⟩ := CannonTriangleCuts.disk_demands corners out (hthree out) hE hbounds
  let en (d : Faces F) : Fin 3 ≃ corners d := (Finset.equivFinOfCardEq (hthree d)).symm
  let vertex : A×Fin 3 → V := fun i=>(en i.1.val i.2).val
  have hinj (f:A) : Function.Injective (fun k=>vertex (f,k)) :=
    Subtype.val_injective.comp (en f.val).injective
  have hmem (f:A) (v:V) : (∃ k,vertex (f,k)=v) ↔ v.val∈faceVertices F f.val := by
    constructor
    · rintro ⟨k,rfl⟩
      exact (Finset.mem_filter.mp (en f.val k).property).2
    · intro hv
      have hh : v∈corners f.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      obtain ⟨k,hk⟩ := (en f.val).surjective ⟨v,hh⟩
      exact ⟨k,congrArg Subtype.val hk⟩
  have hcut' (S : Finset V) (hs:S.Nonempty) (hsp:S≠Finset.univ) :
      (∑ v∈S,CannonTriangleCuts.demand (corners out) v)<
      3*(CannonPackingGeometry.neighborFaces (fun v f=>∃ k,vertex (f,k)=v) S).card := by
    convert hcut S hs hsp using 2
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext f
    simp only [CannonPackingGeometry.neighborFaces,Finset.mem_filter,Finset.mem_univ,true_and,hmem,corners]
  obtain ⟨θ,r,q,hθ,hθf,hθv,hr,hq,htan⟩ := CannonPackingGeometry.strict_cuts_give_radii
    vertex hinj (CannonTriangleCuts.demand (corners out))
    (CannonTriangleCuts.demand_pos _) hcut' htotal
  refine ⟨vertex,hinj,?_,θ,r,q,hθ,hθf,?_,hr,hq,htan⟩
  · intro f
    ext z
    constructor
    · rintro ⟨k,rfl⟩
      exact (hmem f _).mp ⟨k,rfl⟩
    · intro hz
      have hv : z∈V := by
        obtain ⟨i,hi⟩ := ((mem_faceVertices F f.val z).mp hz).1
        exact (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
      obtain ⟨k,hk⟩ := (hmem f ⟨z,hv⟩).mpr hz
      exact ⟨k,congrArg Subtype.val hk⟩
  · intro v
    rw [hθv]
    simp only [CannonTriangleCuts.demand,corners,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> norm_num
    ring
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryUniformCirclePacking
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform circle packings associated with boundary triangulations. -/

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_circle_packing_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ,1≤M ∧ 1≤L ∧ 0 < r₀ ∧ ∃ N : ℕ,
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
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ v : ℂ,Nat.card {i : κ | v∈range (H i)}≤N) ∧
        (∀ d : Faces H,(faceVertices H d).card=3) ∧
        ∃ _ : Fintype (Faces H),∀ out : Faces H,
          ∃ B : DevelopedFaces H out, ∃ z : ℂ → ℂ,
            (∀ d,d≠out → ∀ q∈faceVertices H d,z q=B.chart d q) ∧
            (∀ i,dist (z (H i 0)) (z (H i 1))=B.radius (H i 0)+B.radius (H i 1)) ∧
            (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v →
              B.radius u+B.radius v≤dist (z u) (z v)) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,hgraph⟩ := boundary_uniform_triangular_graphs D hδ φ
  refine ⟨M,L,r₀,hM,hL,hr₀,N,?_⟩
  intro r hr hrs T hsep hcover p hp
  obtain ⟨e,he,heR,κ,H,hκ,hκn,hH,⟨Q,hQ⟩,hT,hK,hE,hD,hN,htri⟩ :=
    hgraph r hr hrs T hsep hcover p hp
  let _ : Finite κ := hκ
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Nonempty κ := hκn
  have htri' (d : Faces H) : ∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
      closure (face H d)=face H d∪(range (H i)∪range (H j)∪range (H k)) := by
    obtain ⟨i,j,k,hij,hjk,hki,-,hc⟩ := htri d
    exact ⟨i,j,k,hij,hjk,hki,hc⟩
  let _ : Finite (Faces H) := faces_finite H hH Q hQ
  let _ : Fintype (Faces H) := Fintype.ofFinite (Faces H)
  refine ⟨e,he,heR,κ,inferInstance,Classical.decEq κ,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,?_,?_,inferInstance,?_⟩
  · intro v
    apply (Nat.card_le_card_of_injective (β:={i : κ | ∃ t:I,dist (e (H i t)) (e v)<2*M*r})
      (fun (i : {i : κ | v∈range (H i)})=>⟨i.val,?_⟩) (fun a b h=>Subtype.ext (congrArg (fun z : {i : κ | ∃ t:I,dist (e (H i t)) (e v)<2*M*r}=>z.val) h))).trans (hN (e v))
    obtain ⟨t,ht⟩ := i.property
    refine ⟨t,?_⟩
    rw [ht,dist_self]
    positivity
  · exact (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1
  · intro out
    have hdata : HasIntrinsicCircleData H out := triangular_graph_radii H hH Q hQ hK htri' out
    obtain ⟨B⟩ := intrinsic_developed_faces H hH Q hQ hK out
      (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1 hdata
    exact ⟨B,B.circle_packing hH Q hQ hK (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1⟩
end CannonRelease

end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonRelease.boundary_uniform_circle_packing_oai.{u_1} := @OAI.CannonRelease.boundary_uniform_circle_packing_oai.{u_1}
