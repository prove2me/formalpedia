-- Prove2me | solution 1 for OAI.CannonRelease.cannon
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:16:01.868399+00:00
-- url     : https://prove2.me/submissions/5fcd2b2c-35f5-48b4-a986-a9aab0b6458a

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonMobius_sphere_action_straightening
import Theorems.Thm_OAI_CannonRelease_boundary_quasiMobius_uniformizer

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

local instance instSetoidBasedRay_2_rc97258_1 : Setoid (BasedRay D) := raySetoid D
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

lemma translated_product2_bound (g : G) (r s : BasedRay D) (n : ℕ) :
    product2 (G := D.graph) 1 (r.val n) (s.val n) ≤
      product2 (G := D.graph) 1 ((translateRay D ⟨δ,hδ⟩ g r).val n)
        ((translateRay D ⟨δ,hδ⟩ g s).val n) + 2*(3*D.graph.dist 1 g+4*δ) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  let s' := translateRay D ⟨δ,hδ⟩ g s
  have hp := product2_ray_sum D.connected r s n
  have hp' := product2_ray_sum D.connected r' s' n
  have ht₁ := @SimpleGraph.Connected.dist_triangle _ D.graph (r'.val n) (g*r.val n) (s'.val n) D.connected
  have ht₂ := @SimpleGraph.Connected.dist_triangle _ D.graph (g*r.val n) (g*s.val n) (s'.val n) D.connected
  rw [D.dist_mul_left g, SimpleGraph.dist_comm (u := g*s.val n) (v := s'.val n)] at ht₂
  have hr := translateRay_uniform D hδ g r n
  have hs := translateRay_uniform D hδ g s n
  change D.graph.dist (r'.val n) (g*r.val n) ≤ _ at hr
  change D.graph.dist (s'.val n) (g*s.val n) ≤ _ at hs
  change _ ≤ product2 (G := D.graph) 1 (r'.val n) (s'.val n) + _
  dsimp only [CayleyData.graph] at *
  omega

lemma translated_preDist_le (g : G) (r s : BasedRay D) :
    (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g r)
      (translateRay D ⟨δ,hδ⟩ g s) : ℝ) ≤
    Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ)) *
      (preDist (visualExponent δ) r s : ℝ) := by
  let r' := translateRay D ⟨δ,hδ⟩ g r
  let s' := translateRay D ⟨δ,hδ⟩ g s
  apply le_of_tendsto_of_tendsto
    (NNReal.continuous_coe.tendsto _ |>.comp (tendsto_decay D.connected (visualExponent_pos δ).le r' s'))
    ((NNReal.continuous_coe.tendsto _ |>.comp
      (tendsto_decay D.connected (visualExponent_pos δ).le r s)).const_mul _)
  apply Filter.Eventually.of_forall
  intro n
  change Real.exp _ ≤ Real.exp _ * Real.exp _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : (product2 (G := D.graph) 1 (r.val n) (s.val n) : ℝ) ≤
      (product2 (G := D.graph) 1 (r'.val n) (s'.val n) : ℝ) +
        (2*(3*D.graph.dist 1 g+4*δ) : ℕ) := by
    exact_mod_cast translated_product2_bound D hδ g r s n
  have he := visualExponent_pos δ
  change -visualExponent δ * _ ≤ _ + -visualExponent δ * _
  dsimp only [CayleyData.graph] at *
  nlinarith

local instance instSetoidBasedRay_3_rc97258_1 : Setoid (BasedRay D) := raySetoid D
lemma boundaryTranslate_lipschitz_bound (g : G) (x y : Boundary D) :
    @dist _ (visualMetricSpace D hδ).toDist (boundaryTranslate D ⟨δ,hδ⟩ g x)
      (boundaryTranslate D ⟨δ,hδ⟩ g y) ≤
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ))) *
        @dist _ (visualMetricSpace D hδ).toDist x y := by
  induction x,y using Quotient.inductionOn₂ with
  | h r s =>
    have h₁ := (visualMetric_comparison D hδ (translateRay D ⟨δ,hδ⟩ g r)
      (translateRay D ⟨δ,hδ⟩ g s)).1
    have h₂ := translated_preDist_le D hδ g r s
    have h₃ := (visualMetric_comparison D hδ r s).2
    have h₄ := mul_le_mul_of_nonneg_left h₃
      (Real.exp_pos (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ))).le
    exact (h₁.trans h₂).trans (h₄.trans_eq (by
      dsimp only [Quotient.mk', CayleyData.graph, Thin]
      ring))

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

lemma product2_base_cross (hG : G.Connected) (o v a b c d : V) :
    product2 (G := G) o a b + product2 (G := G) o c d +
      product2 (G := G) v a d + product2 (G := G) v b c =
    product2 (G := G) o a d + product2 (G := G) o b c +
      product2 (G := G) v a b + product2 (G := G) v c d := by
  have h₁ := product2_add_dist hG o a b
  have h₂ := product2_add_dist hG o c d
  have h₃ := product2_add_dist hG o a d
  have h₄ := product2_add_dist hG o b c
  have h₅ := product2_add_dist hG v a b
  have h₆ := product2_add_dist hG v c d
  have h₇ := product2_add_dist hG v a d
  have h₈ := product2_add_dist hG v b c
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

local instance instSetoidBasedRay_4_rc97258_1 : Setoid (BasedRay D) := raySetoid D
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

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma translated_product2_cross (g a b c d : G) :
    product2 (G := D.graph) 1 (g*a) (g*b) + product2 (G := D.graph) 1 (g*c) (g*d) +
      product2 (G := D.graph) 1 a d + product2 (G := D.graph) 1 b c =
    product2 (G := D.graph) 1 (g*a) (g*d) + product2 (G := D.graph) 1 (g*b) (g*c) +
      product2 (G := D.graph) 1 a b + product2 (G := D.graph) 1 c d := by
  have hm (x y : G) : product2 (G := D.graph) g (g*x) (g*y) = product2 (G := D.graph) 1 x y := by
    simpa only [mul_one] using product2_mul D g 1 x y
  have h := product2_base_cross D.connected 1 g (g*a) (g*b) (g*c) (g*d)
  dsimp only [CayleyData.graph] at h hm ⊢
  simpa only [hm] using h

local instance instSetoidBasedRay_5_rc97258_1 : Setoid (BasedRay D) := raySetoid D
lemma translated_preDist_crossratio (g : G) (a b c d : BasedRay D)
    (hab : ¬ (raySetoid D).r a b) (hcd : ¬ (raySetoid D).r c d)
    (had : ¬ (raySetoid D).r a d) (hbc : ¬ (raySetoid D).r b c) :
    (preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g a) (translateRay D ⟨δ,hδ⟩ g b) : ℝ) *
      preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g c) (translateRay D ⟨δ,hδ⟩ g d) *
      preDist (visualExponent δ) a d * preDist (visualExponent δ) b c ≤
    Real.exp (visualExponent δ * (8*(8*δ+6) : ℕ)) *
      ((preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g a) (translateRay D ⟨δ,hδ⟩ g d) : ℝ) *
      preDist (visualExponent δ) (translateRay D ⟨δ,hδ⟩ g b) (translateRay D ⟨δ,hδ⟩ g c) *
      preDist (visualExponent δ) a b * preDist (visualExponent δ) c d) := by
  let a' := translateRay D ⟨δ,hδ⟩ g a
  let b' := translateRay D ⟨δ,hδ⟩ g b
  let c' := translateRay D ⟨δ,hδ⟩ g c
  let d' := translateRay D ⟨δ,hδ⟩ g d
  have hlim (r s : BasedRay D) : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_decay D.connected (visualExponent_pos δ).le r s)
  apply le_of_tendsto_of_tendsto
    ((((hlim a' b').mul (hlim c' d')).mul (hlim a d)).mul (hlim b c))
    (((((hlim a' d').mul (hlim b' c')).mul (hlim a b)).mul (hlim c d)).const_mul _)
  filter_upwards [translated_product_independent_error D hδ g a b hab,
    translated_product_independent_error D hδ g c d hcd,
    translated_product_independent_error D hδ g a d had,
    translated_product_independent_error D hδ g b c hbc] with n hab' hcd' had' hbc'
  have hident := translated_product2_cross D g (a.val n) (b.val n) (c.val n) (d.val n)
  have hsum : product2 (G := D.graph) 1 (a'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (b'.val n) (c'.val n) +
      product2 (G := D.graph) 1 (a.val n) (b.val n) +
      product2 (G := D.graph) 1 (c.val n) (d.val n) ≤
    product2 (G := D.graph) 1 (a'.val n) (b'.val n) +
      product2 (G := D.graph) 1 (c'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (a.val n) (d.val n) +
      product2 (G := D.graph) 1 (b.val n) (c.val n) + 8*(8*δ+6) := by
    dsimp only [a',b',c',d']
    omega
  have hsum' : (product2 (G := D.graph) 1 (a'.val n) (d'.val n) : ℝ) +
      product2 (G := D.graph) 1 (b'.val n) (c'.val n) +
      product2 (G := D.graph) 1 (a.val n) (b.val n) +
      product2 (G := D.graph) 1 (c.val n) (d.val n) ≤
    (product2 (G := D.graph) 1 (a'.val n) (b'.val n) : ℝ) +
      product2 (G := D.graph) 1 (c'.val n) (d'.val n) +
      product2 (G := D.graph) 1 (a.val n) (d.val n) +
      product2 (G := D.graph) 1 (b.val n) (c.val n) + (8*(8*δ+6) : ℕ) := by
    exact_mod_cast hsum
  change Real.exp _ * Real.exp _ * Real.exp _ * Real.exp _ ≤
    Real.exp _ * (Real.exp _ * Real.exp _ * Real.exp _ * Real.exp _)
  repeat rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := visualExponent_pos δ
  dsimp only [CayleyData.graph] at *
  nlinarith

end CannonRelease

namespace CannonReal
lemma mul_four_le {a b c d A B C D : ℝ} (ha : a ≤ A) (hb : b ≤ B)
    (hc : c ≤ C) (hd : d ≤ D) (hb₀ : 0 ≤ b) (hd₀ : 0 ≤ d)
    (hc₀ : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    a*b*c*d ≤ A*B*C*D := by
  have h₁ := mul_le_mul ha hb hb₀ hA
  have h₂ := mul_le_mul hc hd hd₀ hC
  simpa only [mul_assoc] using mul_le_mul h₁ h₂ (mul_nonneg hc₀ hd₀) (mul_nonneg hA hB)
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_6_rc97258_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_uniform_cross_bound (g : G) (x y z w : Boundary D)
    (hxy : x ≠ y) (hzw : z ≠ w) (hxw : x ≠ w) (hyz : y ≠ z) :
    let _ := visualMetricSpace D hδ
    (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g z) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) x w * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) y z ≤
    (16*Real.exp (visualExponent δ * (8*(8*δ+6):ℕ))) *
      ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) *
      (@dist (Boundary D) (visualMetricSpace D hδ).toDist) x y * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) z w) := by
  let _ := visualMetricSpace D hδ
  induction x,y using Quotient.inductionOn₂ with | h a b =>
    induction z,w using Quotient.inductionOn₂ with | h c d =>
      let a' := translateRay D ⟨δ,hδ⟩ g a
      let b' := translateRay D ⟨δ,hδ⟩ g b
      let c' := translateRay D ⟨δ,hδ⟩ g c
      let d' := translateRay D ⟨δ,hδ⟩ g d
      have hab : ¬ (raySetoid D).r a b := fun h => hxy (Quotient.sound h)
      have hcd : ¬ (raySetoid D).r c d := fun h => hzw (Quotient.sound h)
      have had : ¬ (raySetoid D).r a d := fun h => hxw (Quotient.sound h)
      have hbc : ¬ (raySetoid D).r b c := fun h => hyz (Quotient.sound h)
      have huv := translated_preDist_crossratio D hδ g a b c d hab hcd had hbc
      have hlow := CannonReal.mul_four_le
        (visualMetric_comparison D hδ a' b').1 (visualMetric_comparison D hδ c' d').1
        (visualMetric_comparison D hδ a d).1 (visualMetric_comparison D hδ b c).1
        dist_nonneg dist_nonneg dist_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
      have hupp := CannonReal.mul_four_le
        (visualMetric_comparison D hδ a' d').2 (visualMetric_comparison D hδ b' c').2
        (visualMetric_comparison D hδ a b).2 (visualMetric_comparison D hδ c d).2
        (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
        (mul_nonneg (by norm_num) dist_nonneg) (mul_nonneg (by norm_num) dist_nonneg)
        (mul_nonneg (by norm_num) dist_nonneg)
      have hfinal := (hlow.trans huv).trans (mul_le_mul_of_nonneg_left hupp
        (Real.exp_pos (visualExponent δ * (8*(8*δ+6):ℕ))).le)
      change (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' b' : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' c' : Boundary D) (Quotient.mk' d' : Boundary D) *
        (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' d : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' b : Boundary D) (Quotient.mk' c : Boundary D) ≤
        (16*Real.exp (visualExponent δ * (8*(8*δ+6):ℕ))) *
          ((@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a' : Boundary D) (Quotient.mk' d' : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' b' : Boundary D) (Quotient.mk' c' : Boundary D) *
            (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' a : Boundary D) (Quotient.mk' b : Boundary D) * (@dist (Boundary D) (visualMetricSpace D hδ).toDist) (Quotient.mk' c : Boundary D) (Quotient.mk' d : Boundary D))
      exact hfinal.trans_eq (by ring)

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

local instance instSetoidBasedRay_7_rc97258_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_rc97258_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_rc97258_1 : Setoid (BasedRay D) := raySetoid D
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

namespace CannonGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {o : V}

lemma product2_replace_one (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (o v a b : V) (hab : 2*G.dist o v < product2 (G := G) o a b) :
    product2 (G := G) o v a ≤ product2 (G := G) o v b + (8*δ+6) ∧
    product2 (G := G) o v b ≤ product2 (G := G) o v a + (8*δ+6) := by
  have h₁ := product2_hyperbolic hG hδ o v a b
  have h₂ := product2_hyperbolic hG hδ o v b a
  rw [product2_comm (o := o) (x := b) (y := a)] at h₂
  have h₃ := product2_le_twice_left hG o v a
  have h₄ := product2_le_twice_left hG o v b
  constructor <;> omega

lemma product2_complement (hG : G.Connected) (o v a : V) :
    product2 (G := G) v o a + product2 (G := G) o v a = 2*G.dist o v := by
  have h₁ := product2_add_dist hG v o a
  have h₂ := product2_add_dist hG o v a
  rw [SimpleGraph.dist_comm (u := v) (v := o)] at h₁
  omega

lemma vertex_close_to_ray (hG : G.Connected) {δ : ℕ} (hδ : Thin G δ)
    (s : CannonVisual.Ray G o) (v : V) (n C : ℕ)
    (hn : G.dist o v ≤ n)
    (hprod : 2*G.dist o v ≤ product2 (G := G) o v (s.val n) + C) :
    G.dist v (s.val (G.dist o v)) ≤ 2*C+4*δ+2 := by
  let w := G.dist o v
  have hs (i : ℕ) : G.dist o (s.val i) = i := by
    simpa only [s.property.1,Nat.dist_zero_left] using s.property.2 0 i
  by_cases hw : w ≤ C+δ+1
  · have h := @Connected.dist_triangle _ G v o (s.val w) hG
    rw [SimpleGraph.dist_comm (u := v) (v := o),hs] at h
    change G.dist v (s.val w) ≤ _
    dsimp [w] at *
    omega
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist o v
  let q : G.Walk o (s.val n) := (raySegment s.val s.property.2 n).copy s.property.1 rfl
  have hq : q.length = G.dist o (s.val n) := by simp only [q,Walk.length_copy,raySegment_length,hs]
  let m := w-(C+δ+1)
  have hm : m ≤ p.length := by dsimp [m,w]; omega
  have hm' : m ≤ q.length := by rw [hq,hs]; dsimp [m,w]; omega
  have had := product2_add_dist hG o v (s.val n)
  have hclose := fellow_travel_below_product hG hδ p q hp hq hm hm' (by dsimp [m,w] at *; omega)
  have hpm := getVert_end_dist hG p hp hm
  have hqm : q.getVert m = s.val m := by
    simp only [q,Walk.getVert_copy,raySegment_getVert s.val s.property.2 (show m ≤ n by dsimp [m,w]; omega)]
  rw [hqm] at hclose
  have h₁ := @Connected.dist_triangle _ G v (p.getVert m) (s.val m) hG
  have h₂ := @Connected.dist_triangle _ G v (s.val m) (s.val w) hG
  rw [SimpleGraph.dist_comm (u := v) (v := p.getVert m)] at h₁
  rw [s.property.2,Nat.dist_eq_sub_of_le (show m ≤ w by dsimp [m]; omega)] at h₂
  change G.dist v (s.val w) ≤ _
  dsimp [m,w] at *
  omega

end CannonGraph

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

include hδ in

theorem coarse_prefix_of_distinct_rays (r s : BasedRay D)
    (hrs : ¬ (raySetoid D).r r s) :
    ∃ B : ℕ, ∀ v : G, ∃ t : BasedRay D,
      D.graph.dist v (t.val (D.graph.dist 1 v)) ≤ B := by
  obtain ⟨C,hC⟩ := product2_ray_bounded D hδ hrs
  refine ⟨2*(C+2*(8*δ+6))+4*δ+2,?_⟩
  intro v
  let r' := translateRay D ⟨δ,hδ⟩ v r
  let s' := translateRay D ⟨δ,hδ⟩ v s
  have he := (translated_mixed_product_large D hδ v r (2*D.graph.dist 1 v)).and
    ((translated_mixed_product_large D hδ v s (2*D.graph.dist 1 v)).and
      (Filter.eventually_ge_atTop (D.graph.dist 1 v)))
  obtain ⟨n,hr,hs,hn⟩ := he.exists
  have hrb := product2_replace_one D.connected hδ 1 v (v*r.val n) (r'.val n) hr
  have hsb := product2_replace_one D.connected hδ 1 v (v*s.val n) (s'.val n) hs
  have hmin := product2_hyperbolic D.connected hδ v (v*r.val n) 1 (v*s.val n)
  have hp₁ := product2_complement D.connected 1 v (v*r.val n)
  have hp₂ := product2_complement D.connected 1 v (v*s.val n)
  have heq : product2 (G := D.graph) v (v*r.val n) (v*s.val n) =
      product2 (G := D.graph) 1 (r.val n) (s.val n) := by
    simpa only [mul_one] using product2_mul D v 1 (r.val n) (s.val n)
  have hb := hC n
  dsimp only [CayleyData.graph] at *
  rw [heq,product2_comm (o := v) (x := v*r.val n) (y := 1)] at hmin
  have hposs : 2*(SimpleGraph.mulCayley ↑D.generators).dist 1 v ≤
      product2 (G := D.graph) 1 v (r'.val n) + (C+2*(8*δ+6)) ∨
      2*(SimpleGraph.mulCayley ↑D.generators).dist 1 v ≤
      product2 (G := D.graph) 1 v (s'.val n) + (C+2*(8*δ+6)) := by
    dsimp only [CayleyData.graph]
    omega
  rcases hposs with hr' | hs'
  · exact ⟨r',vertex_close_to_ray D.connected hδ r' v n (C+2*(8*δ+6)) hn hr'⟩
  · exact ⟨s',vertex_close_to_ray D.connected hδ s' v n (C+2*(8*δ+6)) hn hs'⟩

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

lemma visualScale_tendsto_zero (δ : ℕ) :
    Filter.Tendsto (visualScale δ) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun k => visualScale δ k) Filter.atTop (nhds 0)
  simpa only [visualScale_eq_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-(2*visualExponent δ))).le
    (show Real.exp (-(2*visualExponent δ)) < 1 by
      rw [Real.exp_lt_one_iff]; have := visualExponent_pos δ; linarith)
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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Distinct
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
noncomputable section
namespace CannonQM
open Metric
open scoped NNReal

lemma Distinct.map {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x y z w : X} (h : Distinct x y z w) : Distinct (f x) (f y) (f z) (f w) := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨fun h => hxy (hf h),fun h => hxz (hf h),fun h => hxw (hf h),
    fun h => hyz (hf h),fun h => hyw (hf h),fun h => hzw (hf h)⟩

lemma Distinct.flip {X : Type*} {x y z w : X} (h : Distinct x y z w) : Distinct x w z y := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨hxw,hxz,hxy,hzw.symm,hyw.symm,hyz.symm⟩

lemma nndist_pos {X : Type*} [MetricSpace X] {x y : X} : 0 < nndist x y ↔ x ≠ y := by
  rw [pos_iff_ne_zero,ne_eq,nndist_eq_zero]

lemma crossRatio_pos {X : Type*} [MetricSpace X] {x y z w : X}
    (h : Distinct x y z w) : 0 < crossRatio x y z w := by
  exact div_pos (mul_pos (nndist_pos.mpr h.1) (nndist_pos.mpr h.2.2.2.2.2))
    (mul_pos (nndist_pos.mpr h.2.2.1) (nndist_pos.mpr h.2.2.2.1))

lemma crossRatio_flip {X : Type*} [MetricSpace X] (x y z w : X) :
    crossRatio x w z y = (crossRatio x y z w)⁻¹ := by
  simp only [crossRatio,inv_div,nndist_comm z y,nndist_comm w z]

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

lemma Controlled.comp {f : X → Y} {g : Y → Z} {η θ : Distortion}
    (hg : Controlled g θ) (hf : Controlled f η) (hinj : Function.Injective f) :
    Controlled (g ∘ f) (η.trans θ) := by
  intro x y z w hh
  exact (hg _ _ _ _ (hh.map hinj)).trans (θ.monotone (hf _ _ _ _ hh))

lemma Controlled.inverse (f : X ≃ₜ Y) {η : Distortion} (hf : Controlled f η) :
    Controlled f.symm (reciprocal η.symm) := by
  intro x y z w hh
  have hh' := hh.map f.symm.injective
  have H := hf _ _ _ _ hh'.flip
  simp only [f.apply_symm_apply] at H
  rw [crossRatio_flip x y z w, crossRatio_flip (f.symm x) (f.symm y) (f.symm z) (f.symm w)] at H
  have H' := η.symm.monotone H
  simp only [OrderIso.symm_apply_apply] at H'
  change crossRatio (f.symm x) (f.symm y) (f.symm z) (f.symm w) ≤ (η.symm (crossRatio x y z w)⁻¹)⁻¹
  have hpos : 0 < η.symm (crossRatio x y z w)⁻¹ := by
    simpa only [distortion_zero] using η.symm.strictMono (inv_pos.mpr (crossRatio_pos hh))
  have hi := (inv_le_inv₀ (inv_pos.mpr (crossRatio_pos hh')) hpos).mpr H'
  simpa only [inv_inv] using hi

lemma controlled_conjugates {ι : Type*} (ψ : X ≃ₜ Y) {η θ : Distortion}
    (hψ : Controlled ψ η) (f : ι → X ≃ₜ X) (hf : ∀ i, Controlled (f i) θ) :
    ∀ i, Controlled (ψ ∘ (f i) ∘ ψ.symm)
      (((reciprocal η.symm).trans θ).trans η) := by
  intro i
  exact hψ.comp ((hf i).comp (hψ.inverse ψ) ψ.symm.injective)
    ((f i).injective.comp ψ.symm.injective)

end CannonQM

namespace CannonQM
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma controlled_of_product_bound (f : X → Y) (hf : Function.Injective f)
    (C : ℝ≥0) (hC : 0 < C)
    (h : ∀ x y z w, Distinct x y z w →
      nndist (f x) (f y)*nndist (f z) (f w)*nndist x w*nndist y z ≤
      C*(nndist (f x) (f w)*nndist (f y) (f z)*nndist x y*nndist z w)) :
    Controlled f (OrderIso.mulLeft₀ C hC) := by
  intro x y z w hh
  have hhf := hh.map hf
  change crossRatio (f x) (f y) (f z) (f w) ≤ C*crossRatio x y z w
  unfold crossRatio
  rw [← mul_div_assoc,div_le_div_iff₀
    (mul_pos (nndist_pos.mpr hhf.2.2.1) (nndist_pos.mpr hhf.2.2.2.1))
    (mul_pos (nndist_pos.mpr hh.2.2.1) (nndist_pos.mpr hh.2.2.2.1))]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h x y z w hh

end CannonQM

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_BoundaryUniformQuasiMobius
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
namespace CannonRelease
open CannonGraph CannonVisual CannonQM
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_quasiMobius :
    let _ := visualMetricSpace D hδ
    ∃ η : Distortion, ∀ g : G, Controlled (boundaryHomeomorph D ⟨δ,hδ⟩ g) η := by
  let _ := visualMetricSpace D hδ
  let C : ℝ≥0 := ⟨16*Real.exp (visualExponent δ*(8*(8*δ+6):ℕ)),by positivity⟩
  have hC : 0 < C := by change 0 < (16*Real.exp (visualExponent δ*(8*(8*δ+6):ℕ)):ℝ); positivity
  refine ⟨OrderIso.mulLeft₀ C hC,?_⟩
  intro g
  apply controlled_of_product_bound _ (boundaryHomeomorph D ⟨δ,hδ⟩ g).injective C hC
  intro x y z w hh
  have H := boundary_uniform_cross_bound D hδ g x y z w hh.1 hh.2.2.2.2.2 hh.2.2.1 hh.2.2.2.1
  change (nndist (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) *
    nndist (boundaryTranslate D ⟨δ,hδ⟩ g z) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
    nndist x w * nndist y z) ≤ C *
      (nndist (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
       nndist (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) *
       nndist x y * nndist z w)
  exact_mod_cast H

theorem boundary_uniform_conjugates {Y : Type*} [MetricSpace Y] (ψ : Boundary D ≃ₜ Y) :
    let _ := visualMetricSpace D hδ
    QuasiMobius ψ → ∃ η : Distortion, ∀ g : G,
      Controlled (ψ ∘ boundaryHomeomorph D ⟨δ,hδ⟩ g ∘ ψ.symm) η := by
  let _ := visualMetricSpace D hδ
  dsimp only
  rintro ⟨θ,hθ⟩
  obtain ⟨η,hη⟩ := boundary_uniform_quasiMobius D hδ
  exact ⟨((reciprocal θ.symm).trans η).trans θ,
    controlled_conjugates ψ hθ (boundaryHomeomorph D ⟨δ,hδ⟩) hη⟩

end CannonRelease

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Proper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Properness and cocompactness transferred through equivariant maps. -/

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonActions
open Set

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace X] [TopologicalSpace Y]

theorem proper_descends {A : Γ →* (X ≃ₜ X)} {B : Γ →* (Y ≃ₜ Y)}
    {p : X → Y} (hp : IsProperMap p) (hs : Function.Surjective p)
    (he : ∀ g x, p (A g x)=B g (p x)) (hA : Proper A) : Proper B := by
  intro K hK
  apply (hA (p ⁻¹' K) (hp.isCompact_preimage hK)).subset
  rintro g ⟨y,hy,hgy⟩
  obtain ⟨x,rfl⟩ := hs y
  exact ⟨x,hy,by simpa only [mem_preimage,he] using hgy⟩

theorem cocompact_descends {A : Γ →* (X ≃ₜ X)} {B : Γ →* (Y ≃ₜ Y)}
    {p : X → Y} (hp : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (A g x)=B g (p x)) (hA : Cocompact A) : Cocompact B := by
  obtain ⟨K,hK,hAK⟩ := hA
  refine ⟨p '' K,hK.image hp,?_⟩
  intro y
  obtain ⟨x,rfl⟩ := hs y
  obtain ⟨g,z,hz,rfl⟩ := hAK x
  exact ⟨g,p z,mem_image_of_mem p hz,(he g z).symm⟩

theorem proper_finite_kernel [Nonempty X] {A : Γ →* (X ≃ₜ X)} (hA : Proper A) :
    (A.ker : Set Γ).Finite := by
  obtain ⟨x⟩ := ‹Nonempty X›
  apply (hA {x} isCompact_singleton).subset
  intro g hg
  have hh : A g=1 := hg
  exact ⟨x,mem_singleton x,by simp only [hh,Homeomorph.one_apply,mem_singleton_iff]⟩

lemma conjugate_equivariant (ψ : X ≃ₜ Y) (A : Γ →* (X ≃ₜ X)) (g : Γ) (x : X) :
    ψ (A g x)=conjugate ψ A g (ψ x) := by
  change ψ (A g x)=ψ (A g (ψ.symm (ψ x)))
  rw [ψ.symm_apply_apply]

theorem proper_conjugate (ψ : X ≃ₜ Y) {A : Γ →* (X ≃ₜ X)} (hA : Proper A) :
    Proper (conjugate ψ A) :=
  proper_descends ψ.isProperMap ψ.surjective (conjugate_equivariant ψ A) hA

theorem cocompact_conjugate (ψ : X ≃ₜ Y) {A : Γ →* (X ≃ₜ X)} (hA : Cocompact A) :
    Cocompact (conjugate ψ A) :=
  cocompact_descends ψ.continuous ψ.surjective (conjugate_equivariant ψ A) hA

end CannonActions

namespace CannonActions
open Set

variable {X Y Z Γ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [Group Γ]

lemma triples_conjugate (A : Γ →* (X ≃ₜ X)) (ψ : X ≃ₜ Y) :
    triplesAction (conjugate ψ A)=conjugate (triplesCongr ψ) (triplesAction A) := by
  apply MonoidHom.ext
  intro g
  apply Homeomorph.ext
  intro t
  rfl
end CannonActions

end
end
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

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma continuous_tripleMap (f : Sphere ≃ₜ Sphere) : Continuous (tripleMap f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact f.continuous.comp ((continuous_apply i).comp continuous_subtype_val)

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_Height
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open Set Filter Topology
open scoped OnePoint

namespace CannonH3
open Set

lemma extensionHom_compatible (f : boundaryGroup) :
    Compatible f.val ((coords.symm.trans (extensionHom f).val).trans coords) := by
  let p : paired := (MonoidHom.ofInjective boundaryProjection_injective).symm f
  have he : boundaryProjection p=f.val := by
    have hh := (MonoidHom.ofInjective boundaryProjection_injective).apply_symm_apply f
    exact congrArg Subtype.val hh
  intro x y z
  have hh := p.property.1 x y z
  rw [show p.val.1=f.val from he] at hh
  change potential (coords (coords.symm (p.val.2 (coords (coords.symm x))))) (f.val z)*potential y z=
    potential x z*potential (coords (coords.symm (p.val.2 (coords (coords.symm y))))) (f.val z)
  simpa only [coords.apply_symm_apply] using hh
end CannonH3

noncomputable section
open Set Filter Topology

namespace CannonH3
lemma compatible_unique {f : Boundary ≃ₜ Boundary} {F G : Half ≃ₜ Half}
    (hF : Compatible f F) (hG : Compatible f G) : F=G := by
  have hh := compatible_mul hF (compatible_inv hG)
  rw [mul_inv_cancel] at hh
  exact mul_inv_eq_one.mp (compatible_identity_unique hh)

lemma interior_compatible (f : boundaryGroup) : Compatible f.val (interior f) :=
  extensionHom_compatible f
lemma interior_mul (f g : boundaryGroup) : interior (f*g)=interior f*interior g :=
  compatible_unique (interior_compatible (f*g)) (compatible_mul (interior_compatible f) (interior_compatible g))
lemma interior_affine (a b : ℂ) (ha : a ≠ 0) :
    interior ⟨CannonMobius.affine a b ha,affine_mem_boundaryGroup a b ha⟩=affine a b ha := by
  apply compatible_unique (interior_compatible _)
  have he : CannonMobius.affine a b ha=boundaryAffine a b ha := by
    apply Homeomorph.ext
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  change Compatible (CannonMobius.affine a b ha) (affine a b ha)
  rw [he]
  exact affine_compatible a b ha
lemma interior_inversion : interior ⟨CannonMobius.inversion,inversion_mem_boundaryGroup⟩=inversion :=
  compatible_unique (interior_compatible _) inversion_compatible
lemma interior_reflection : interior ⟨boundaryReflection,reflection_mem_boundaryGroup⟩=reflection :=
  compatible_unique (interior_compatible _) reflection_compatible
end CannonH3

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
namespace CannonReal
lemma expansion_separation {R r s t q L A B C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hq : 1 ≤ q) (hL : 0 < L)
    (hrR : r ≤ R) (hRq : R ≤ q*r) (hrs : r ≤ s) (hrt : r ≤ t)
    (htri : s ≤ r+t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h₁ : R*r ≤ L*(A*R*max R r))
    (h₂ : R*s ≤ L*(B*R*max R s))
    (h₃ : R*t ≤ L*(C*max R r*max R s)) :
    1/(2*L*q) ≤ A ∧ 1/(2*L*q) ≤ B ∧ 1/(2*L*q) ≤ C := by
  have hq₀ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hs : 0 < s := hr.trans_le hrs
  have ht : 0 < t := hr.trans_le hrt
  have hm : max R s ≤ q*s := max_le (hRq.trans (mul_le_mul_of_nonneg_left hrs hq₀.le))
    (by nlinarith)
  rw [max_eq_left hrR] at h₁ h₃
  have ha : r ≤ L*A*R := by nlinarith [hR]
  have ha' : r ≤ L*A*(q*r) := ha.trans (mul_le_mul_of_nonneg_left hRq (mul_nonneg hL.le hA))
  have hb : s ≤ L*B*max R s := by nlinarith [hR]
  have hb' : s ≤ L*B*(q*s) := hb.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hL.le hB))
  have hc : t ≤ L*C*max R s := by nlinarith [hR]
  have hc' : t ≤ L*C*(q*s) := hc.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hL.le hC))
  have hst : s ≤ 2*t := by linarith
  have hc'' : t ≤ L*C*(q*(2*t)) := hc'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hst hq₀.le) (mul_nonneg hL.le hC))
  have hden : 0 < 2*L*q := by positivity
  refine ⟨(div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_⟩
  · have : 1 ≤ L*A*q := by nlinarith
    nlinarith
  · have : 1 ≤ L*B*q := by nlinarith
    nlinarith
  · have : 1 ≤ 2*L*C*q := by nlinarith
    nlinarith
end CannonReal

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_10_rc97258_1 : Setoid (BasedRay D) := raySetoid D
lemma boundaryDist_le_one (x y : Boundary D) : boundaryDist D hδ x y ≤ 1 := by
  induction x,y using Quotient.inductionOn₂ with | h r s =>
    dsimp only [boundaryDist, Quotient.mk', CayleyData.graph, Thin] at *
    apply (visualMetric_comparison D hδ r s).1.trans
    have hh := preDist_le_decay (visualExponent δ) r s 0
    have hh' : (preDist (visualExponent δ) r s : ℝ) ≤ (decay (visualExponent δ) r s 0 : ℝ) := by exact_mod_cast hh
    apply hh'.trans_eq
    simp [decay,product2,r.property.1,s.property.1]
    rfl

lemma normalize_closest (x y z : Boundary D) (hxy : x ≠ y)
    (hmin₁ : boundaryDist D hδ x y ≤ boundaryDist D hδ x z)
    (hmin₂ : boundaryDist D hδ x y ≤ boundaryDist D hδ y z) :
    ∃ g : G,
      let e := 1/(2*(8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*Real.exp (2*visualExponent δ))
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) := by
  let _ := visualMetricSpace D hδ
  have hr : 0 < boundaryDist D hδ x y := dist_pos.mpr hxy
  obtain ⟨k,hk₁,hk₂⟩ := visualScale_near δ hr (boundaryDist_le_one D hδ x y)
  obtain ⟨r,hrx⟩ := Quotient.exists_rep x
  subst x
  let g := (r.val k)⁻¹
  refine ⟨g,?_⟩
  have he₁ := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
  have he₂ := (visual_expansion_ray D hδ r k (Quotient.mk' r) z).2
  have he₃ := (visual_expansion_ray D hδ r k y z).2
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r) = 0 := dist_self _
  change visualScale δ k * boundaryDist D hδ (Quotient.mk' r) y ≤
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*
      (boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g (Quotient.mk' r))
        (boundaryTranslate D ⟨δ,hδ⟩ g y) * max (visualScale δ k)
        (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at he₁
  change visualScale δ k * boundaryDist D hδ (Quotient.mk' r) z ≤
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*
      (boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g (Quotient.mk' r))
        (boundaryTranslate D ⟨δ,hδ⟩ g z) * max (visualScale δ k)
        (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) z)) at he₂
  rw [hself,max_eq_left (visualScale_pos δ k).le] at he₁ he₂
  exact CannonReal.expansion_separation (visualScale_pos δ k) hr
    (by rw [Real.one_le_exp_iff]; have := visualExponent_pos δ; linarith)
    (by positivity) hk₁ hk₂ hmin₁ hmin₂ (dist_triangle _ _ _)
    dist_nonneg dist_nonneg dist_nonneg he₁ he₂ he₃

end CannonRelease

namespace CannonMetric
variable {X : Type*} [MetricSpace X]
lemma two_far_from_center (p x y z : X) {e : ℝ}
    (hxy : e ≤ dist x y) (hxz : e ≤ dist x z) (hyz : e ≤ dist y z) :
    (e/2 ≤ dist p x ∧ e/2 ≤ dist p y) ∨
    (e/2 ≤ dist p x ∧ e/2 ≤ dist p z) ∨
    (e/2 ≤ dist p y ∧ e/2 ≤ dist p z) := by
  have h₁ := dist_triangle_left x y p
  have h₂ := dist_triangle_left x z p
  have h₃ := dist_triangle_left y z p
  by_cases hx : e/2 ≤ dist p x
  · by_cases hy : e/2 ≤ dist p y
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr (Or.inl ⟨hx,by linarith⟩)
  · exact Or.inr (Or.inr ⟨by linarith,by linarith⟩)
end CannonMetric

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_11_rc97258_1 : Setoid (BasedRay D) := raySetoid D
lemma expansion_contraction (r : BasedRay D) (k : ℕ) (y z : Boundary D)
    {e : ℝ} (he : 0 ≤ e)
    (hy : e ≤ boundaryDist D hδ (Quotient.mk' r) y)
    (hz : e ≤ boundaryDist D hδ (Quotient.mk' r) z) :
    boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
        (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z) * (e*e) ≤
      (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*visualScale δ k := by
  let _ := visualMetricSpace D hδ
  have h := (visual_expansion_ray D hδ r k y z).1
  have h₁ := mul_le_mul (hy.trans (le_max_right (visualScale δ k) _)) (hz.trans (le_max_right (visualScale δ k) _))
    he ((visualScale_pos δ k).le.trans (le_max_left _ _))
  have h₂ := mul_le_mul_of_nonneg_left h₁
    (show 0 ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ y)
      (boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹ z) from dist_nonneg)
  have h₃ := mul_le_mul_of_nonneg_left (boundaryDist_le_one D hδ y z)
    (show 0 ≤ (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))*visualScale δ k from
      mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (visualScale_pos δ k).le)
  rw [mul_one] at h₃
  exact h₂.trans (by simpa only [mul_assoc] using h.trans h₃)

lemma bounded_translate_lipschitz {B : ℕ} {g : G} (hg : D.graph.dist 1 g ≤ B)
    (x y : Boundary D) :
    boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ≤
      (2*Real.exp (visualExponent δ*(2*(3*B+4*δ):ℕ)))*boundaryDist D hδ x y := by
  let _ := visualMetricSpace D hδ
  apply (boundaryTranslate_lipschitz_bound D hδ g x y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (visualExponent_pos δ).le
  exact_mod_cast (show 2*(3*D.graph.dist 1 g+4*δ) ≤ 2*(3*B+4*δ) by omega)

include hδ in
lemma proper_triple_word_bound (r s : BasedRay D) (hrs : ¬ (raySetoid D).r r s)
    {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ g : G, ∀ x y z : Boundary D,
      e ≤ boundaryDist D hδ x y → e ≤ boundaryDist D hδ x z → e ≤ boundaryDist D hδ y z →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) →
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) →
      D.graph.dist 1 g⁻¹ ≤ N := by
  let _ := visualMetricSpace D hδ
  obtain ⟨B,hB⟩ := coarse_prefix_of_distinct_rays D hδ r s hrs
  let M := 2*Real.exp (visualExponent δ*(2*(3*B+4*δ):ℕ))
  let U := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  have hM : 0 < M := by positivity
  have hU : 0 < U := by positivity
  have hlim := (visualScale_tendsto_zero δ).const_mul (M*U)
  have hpos : 0 < e*(e/2*(e/2)) := by positivity
  have hsmall : ∀ᶠ k in atTop, M*U*visualScale δ k < e*(e/2*(e/2)) := by
    exact (tendsto_order.1 (by simpa only [mul_zero] using hlim)).2 _ hpos
  obtain ⟨N,hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N,?_⟩
  intro g x y z hxy hxz hyz hgxy hgxz hgyz
  let k := D.graph.dist 1 g⁻¹
  obtain ⟨t,ht⟩ := hB g⁻¹
  let a := g*t.val k
  have ha : D.graph.dist 1 a ≤ B := by
    have hh := D.dist_mul_left g g⁻¹ (t.val k)
    rw [mul_inv_cancel] at hh
    exact hh.symm ▸ ht
  have hfac : a*(t.val k)⁻¹ = g := by simp only [a,mul_assoc,mul_inv_cancel,mul_one]
  have hpair (u v : Boundary D)
      (hu : e/2 ≤ boundaryDist D hδ (Quotient.mk' t) u)
      (hv : e/2 ≤ boundaryDist D hδ (Quotient.mk' t) v)
      (hguv : e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g u)
        (boundaryTranslate D ⟨δ,hδ⟩ g v)) : k ≤ N := by
    have hc := expansion_contraction D hδ t k u v (by positivity) hu hv
    have hl := bounded_translate_lipschitz D hδ ha
      (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ u) (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ v)
    rw [← boundaryTranslate_mul D ⟨δ,hδ⟩ a (t.val k)⁻¹ u,
      ← boundaryTranslate_mul D ⟨δ,hδ⟩ a (t.val k)⁻¹ v,hfac] at hl
    have hh := mul_le_mul_of_nonneg_right (hguv.trans hl)
      (show 0 ≤ e/2*(e/2) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hc hM.le
    have hh'' : e*(e/2*(e/2)) ≤ M*U*visualScale δ k := by
      calc
        e*(e/2*(e/2)) ≤ M*(boundaryDist D hδ
          (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ u)
          (boundaryTranslate D ⟨δ,hδ⟩ (t.val k)⁻¹ v) * (e/2*(e/2))) := by
            simpa only [M,mul_assoc] using hh
        _ ≤ M*(U*visualScale δ k) := hh'
        _ = M*U*visualScale δ k := (mul_assoc _ _ _).symm
    by_contra hn
    exact (not_lt_of_ge hh'') (hN k (by omega))
  rcases @CannonMetric.two_far_from_center (Boundary D) (visualMetricSpace D hδ) (Quotient.mk' t : Boundary D) x y z e hxy hxz hyz with
    ⟨hx,hy⟩ | ⟨hx,hz⟩ | ⟨hy,hz⟩
  · exact hpair x y hx hy hgxy
  · exact hpair x z hx hz hgxz
  · exact hpair y z hy hz hgyz

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

local instance instSetoidBasedRay_27_rc97258_1 : Setoid (BasedRay D) := raySetoid D
lemma finite_triple_translates (r s : BasedRay D) (hrs : ¬ (raySetoid D).r r s)
    {e : ℝ} (he : 0 < e) :
    {g : G | ∃ x y z : Boundary D,
      e ≤ boundaryDist D hδ x y ∧ e ≤ boundaryDist D hδ x z ∧ e ≤ boundaryDist D hδ y z ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g z) ∧
      e ≤ boundaryDist D hδ (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z)}.Finite := by
  obtain ⟨N,hN⟩ := proper_triple_word_bound D hδ r s hrs he
  have hfin := finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 N
  apply (hfin.preimage (f := fun g : G => g⁻¹) inv_injective.injOn).subset
  rintro g ⟨x,y,z,hxy,hxz,hyz,hgxy,hgxz,hgyz⟩
  exact hN g x y z hxy hxz hyz hgxy hgxz hgyz

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
-- module Solutions.OAIQ046_CN.Cannon_Actions_Triples
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
section
namespace CannonTriples

open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma separation_pos (t : Triples X) : 0 < separation t.val := by
  apply lt_min
  · exact dist_pos.mpr (fun hh => (by decide : (0:Fin 3) ≠ 1) (t.property hh))
  · apply lt_min
    · exact dist_pos.mpr (fun hh => (by decide : (0:Fin 3) ≠ 2) (t.property hh))
    · exact dist_pos.mpr (fun hh => (by decide : (1:Fin 3) ≠ 2) (t.property hh))

lemma separation_le (t : Fin 3 → X) (i j : Fin 3) (hij : i ≠ j) : separation t ≤ dist (t i) (t j) := by
  have h₀ := min_le_left (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  have h₁ := (min_le_right (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))).trans
    (min_le_left (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  have h₂ := (min_le_right (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))).trans
    (min_le_right (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h₀
    | exact h₁
    | exact h₂
    | exact h₀.trans_eq (dist_comm _ _)
    | exact h₁.trans_eq (dist_comm _ _)
    | exact h₂.trans_eq (dist_comm _ _)

lemma injective_of_separation_pos {t : Fin 3 → X} (ht : 0 < separation t) : Function.Injective t := by
  intro i j he
  by_contra hn
  have hh := ht.trans_le (separation_le t i j hn)
  simp only [he,dist_self,lt_self_iff_false] at hh

lemma continuous_separation : Continuous (separation : (Fin 3 → X) → ℝ) := by
  unfold separation
  fun_prop

theorem compact_uniform_separation {K : Set (Triples X)} (hK : IsCompact K) :
    ∃ e : ℝ, 0 < e ∧ ∀ t ∈ K, e ≤ separation t.val := by
  by_cases hn : K.Nonempty
  · obtain ⟨t,_,hmin⟩ := hK.exists_isMinOn hn
      (continuous_separation.comp continuous_subtype_val).continuousOn
    exact ⟨separation t.val,separation_pos t,fun _ hu => hmin hu⟩
  · exact ⟨1,by norm_num,fun t ht => (hn ⟨t,ht⟩).elim⟩

theorem separated_compact [CompactSpace X] {e : ℝ} (he : 0 < e) :
    IsCompact {t : Triples X | e ≤ separation t.val} := by
  rw [Subtype.isCompact_iff]
  have him : Subtype.val '' {t : Triples X | e ≤ separation t.val} =
      {t : Fin 3 → X | e ≤ separation t} := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro ht
      exact ⟨⟨t,injective_of_separation_pos (he.trans_le ht)⟩,ht,rfl⟩
  rw [him]
  exact (isClosed_le continuous_const continuous_separation).isCompact

end CannonTriples

end

namespace CannonRelease
open CannonGraph CannonVisual CannonTriples Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance triplesSetoid_rc97258_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_triples_proper :
    let _ := visualMetricSpace D hδ
    ∀ K : Set (Triples (Boundary D)), IsCompact K →
      {g : G | ∃ t ∈ K, CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t ∈ K}.Finite := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro K hK
  by_cases hn : K.Nonempty
  · obtain ⟨t,_⟩ := hn
    obtain ⟨r,hr⟩ := Quotient.exists_rep (t.val 0)
    obtain ⟨s,hs⟩ := Quotient.exists_rep (t.val 1)
    have hrs : ¬ (raySetoid D).r r s := by
      intro hh
      have he : t.val 0 = t.val 1 := hr.symm.trans ((Quotient.sound hh).trans hs)
      exact (by decide : (0:Fin 3) ≠ 1) (t.property he)
    obtain ⟨e,he,hsep⟩ := compact_uniform_separation hK
    apply (finite_triple_translates D hδ r s hrs he).subset
    rintro g ⟨u,hu,hgu⟩
    have hh := hsep u hu
    have hhg := hsep _ hgu
    refine ⟨u.val 0,u.val 1,u.val 2,?_,?_,?_,?_,?_,?_⟩
    · exact hh.trans (separation_le _ 0 1 (by decide))
    · exact hh.trans (separation_le _ 0 2 (by decide))
    · exact hh.trans (separation_le _ 1 2 (by decide))
    · exact hhg.trans (separation_le _ 0 1 (by decide))
    · exact hhg.trans (separation_le _ 0 2 (by decide))
    · exact hhg.trans (separation_le _ 1 2 (by decide))
  · apply Set.finite_empty.subset
    rintro _ ⟨t,ht,_⟩
    exact (hn ⟨t,ht⟩).elim

theorem boundary_triples_normalize :
    let _ := visualMetricSpace D hδ
    ∃ e : ℝ, 0 < e ∧ ∀ t : Triples (Boundary D), ∃ g : G,
      e ≤ separation (CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t).val := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let e := 1/(2*(8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*Real.exp (2*visualExponent δ))
  refine ⟨e,by dsimp [e]; positivity,?_⟩
  intro t
  have h01 : t.val 0 ≠ t.val 1 := fun h => (by decide : (0:Fin 3) ≠ 1) (t.property h)
  have h02 : t.val 0 ≠ t.val 2 := fun h => (by decide : (0:Fin 3) ≠ 2) (t.property h)
  have h12 : t.val 1 ≠ t.val 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (t.property h)
  by_cases hA : dist (t.val 0) (t.val 1) ≤ dist (t.val 0) (t.val 2)
  · by_cases hB : dist (t.val 0) (t.val 1) ≤ dist (t.val 1) (t.val 2)
    · obtain ⟨g,hg01,hg02,hg12⟩ := normalize_closest D hδ _ _ _ h01 hA hB
      exact ⟨g,le_min hg01 (le_min hg02 hg12)⟩
    · obtain ⟨g,hg12,hg10,hg20⟩ := normalize_closest D hδ _ _ _ h12
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hB))
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hB).trans hA)
      refine ⟨g,le_min ?_ (le_min ?_ hg12)⟩
      · exact hg10.trans_eq (dist_comm _ _)
      · exact hg20.trans_eq (dist_comm _ _)
  · by_cases hC : dist (t.val 0) (t.val 2) ≤ dist (t.val 1) (t.val 2)
    · obtain ⟨g,hg02,hg01,hg21⟩ := normalize_closest D hδ _ _ _ h02
        (le_of_not_ge hA) (by simpa only [boundaryDist,dist_comm] using hC)
      refine ⟨g,le_min hg01 (le_min hg02 ?_)⟩
      exact hg21.trans_eq (dist_comm _ _)
    · obtain ⟨g,hg12,hg10,hg20⟩ := normalize_closest D hδ _ _ _ h12
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hC).trans (le_of_not_ge hA))
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hC))
      refine ⟨g,le_min ?_ (le_min ?_ hg12)⟩
      · exact hg10.trans_eq (dist_comm _ _)
      · exact hg20.trans_eq (dist_comm _ _)

theorem boundary_triples_cocompact :
    let _ := visualMetricSpace D hδ
    ∃ K : Set (Triples (Boundary D)), IsCompact K ∧
      ∀ t : Triples (Boundary D), ∃ g : G, ∃ u ∈ K,
        CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) u = t := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨e,he,hsep⟩ := boundary_triples_normalize D hδ
  refine ⟨{t | e ≤ separation t.val},separated_compact he,?_⟩
  intro t
  obtain ⟨g,hg⟩ := hsep t
  refine ⟨g⁻¹,CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t,hg,?_⟩
  apply Subtype.ext
  funext i
  change boundaryTranslate D ⟨δ,hδ⟩ g⁻¹ (boundaryTranslate D ⟨δ,hδ⟩ g (t.val i)) = t.val i
  exact (boundaryHomeomorph D ⟨δ,hδ⟩ g).left_inv (t.val i)

end CannonRelease

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Normalizer
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
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma biholomorphic_stabilizer {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic)
    (ht : tripleMap f standard=standard) : f=1 := by
  have hi (i : Fin 3) : f (std i)=std i := congrFun (congrArg Subtype.val ht) i
  obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_eq_affine f (hi 0) hf
  have h0 := hi 1
  have h1 := hi 2
  rw [he] at h0 h1
  change affine a b ha (0:ℂ)=((0:ℂ):Sphere) at h0
  change affine a b ha (1:ℂ)=((1:ℂ):Sphere) at h1
  rw [affine_coe] at h0 h1
  have hb : b=0 := by simpa using h0
  have ha1 : a=1 := by simpa [hb] using h1
  rw [he]
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [affine,affinePlane,ha1,hb]

lemma triple_normalizer_unique {f g : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic)
    (hg : g ∈ biholomorphic) (he : tripleMap f standard=tripleMap g standard) : f=g := by
  have h : tripleMap (g⁻¹*f) standard=standard := by
    rw [tripleMap_mul,he]
    apply Subtype.ext
    funext i
    exact g.symm_apply_apply _
  have hh := biholomorphic_stabilizer (biholomorphic.mul_mem (biholomorphic.inv_mem hg) hf) h
  exact (inv_mul_eq_one.mp hh).symm
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

lemma reflection_inv : boundaryReflection⁻¹=boundaryReflection :=
  inv_eq_of_mul_eq_one_left boundaryReflection_sq
lemma reflection_affine (a b : ℂ) (ha : a ≠ 0) :
    boundaryReflection*affine a b ha*boundaryReflection=affine (star a) (star b) (star_ne_zero.mpr ha) := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change ((star (a*star z+b):ℂ):Sphere)=((star a*z+star b:ℂ):Sphere)
    rw [star_add,star_mul,star_star,mul_comm z]
lemma reflection_inversion : boundaryReflection*inversion*boundaryReflection=inversion := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty =>
    change boundaryReflection (inv ∞)=inv ∞
    rw [inv_infty]
    change ((star (0:ℂ):ℂ):Sphere)=((0:ℂ):Sphere)
    simp
  | coe z =>
    by_cases hz : z=0
    · subst z
      change boundaryReflection (inv ((star (0:ℂ):ℂ):Sphere))=inv ((0:ℂ):Sphere)
      simp only [star_zero,inv_zero]
      rfl
    · change boundaryReflection (inv ((star z:ℂ):Sphere))=inv (z:Sphere)
      rw [inv_coe (star_ne_zero.mpr hz),inv_coe hz]
      change ((star ((star z)⁻¹):ℂ):Sphere)=((z⁻¹:ℂ):Sphere)
      rw [star_inv₀,star_star]

lemma reflection_conjugate_biholomorphic {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic) :
    boundaryReflection*f*boundaryReflection ∈ biholomorphic := by
  let C : MulAut (Sphere ≃ₜ Sphere) := MulAut.conj boundaryReflection
  have he (g : Sphere ≃ₜ Sphere) : C g=boundaryReflection*g*boundaryReflection := by
    simp [C,MulAut.conj_apply,reflection_inv]
  have ha (a b : ℂ) (h : a ≠ 0) : C (affine a b h) ∈ biholomorphic := by
    rw [he,reflection_affine]
    exact affine_biholomorphic _ _ _
  have hi : C inversion ∈ biholomorphic := by rw [he,reflection_inversion]; exact inversion_biholomorphic
  rw [← he]
  rcases biholomorphic_normal_form f hf with ⟨a,b,h,rfl⟩|⟨p,a,b,h,rfl⟩
  · exact ha a b h
  · rw [map_mul,map_mul]
    exact biholomorphic.mul_mem (biholomorphic.mul_mem (ha 1 p one_ne_zero) hi) (ha a b h)

lemma reflection_standard : tripleMap boundaryReflection standard=standard := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [tripleMap,standard,std,boundaryReflection]

lemma normalizer_spec (t : Triple) : tripleMap (normalizer t).val standard=t :=
  (exists_triple_normalizer t).choose_spec.2

lemma center_orbit (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    center (tripleMap f standard)=interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint := by
  have he : (normalizer (tripleMap f standard)).val=f :=
    triple_normalizer_unique (normalizer _).property hf (normalizer_spec _)
  unfold center
  congr 2
  exact Subtype.ext he

lemma center_biholomorphic (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) (t : Triple) :
    center (tripleMap f t)=interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ (center t) := by
  have he : tripleMap (f*(normalizer t).val) standard=tripleMap f t := by
    rw [tripleMap_mul,normalizer_spec]
  rw [← he,center_orbit _ (biholomorphic.mul_mem hf (normalizer t).property)]
  change CannonH3.interior (⟨f,biholomorphic_mem_boundaryGroup hf⟩*
    ⟨(normalizer t).val,biholomorphic_mem_boundaryGroup (normalizer t).property⟩) basepoint=_
  rw [interior_mul]
  rfl

lemma center_reflection (t : Triple) : center (tripleMap boundaryReflection t)=reflection (center t) := by
  let f := (normalizer t).val
  have hf : f ∈ biholomorphic := (normalizer t).property
  have hfc := reflection_conjugate_biholomorphic hf
  have he : tripleMap (boundaryReflection*f*boundaryReflection) standard=tripleMap boundaryReflection t := by
    rw [tripleMap_mul,tripleMap_mul,reflection_standard,normalizer_spec]
  rw [← he,center_orbit _ hfc]
  change CannonH3.interior (⟨boundaryReflection,reflection_mem_boundaryGroup⟩*
    ⟨f,biholomorphic_mem_boundaryGroup hf⟩*⟨boundaryReflection,reflection_mem_boundaryGroup⟩) basepoint=_
  rw [interior_mul,interior_mul,interior_reflection]
  have hb : reflection basepoint=basepoint := by
    apply Prod.ext
    · change star (0:ℂ)=0
      exact star_zero _
    · rfl
  change reflection (CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ (reflection basepoint))=_
  rw [hb]
  rfl

lemma center_conformal (f : Sphere ≃ₜ Sphere)
    (hf : f ∈ biholomorphic ∨ boundaryReflection*f ∈ biholomorphic) (t : Triple) :
    center (tripleMap f t)=interior ⟨f,conformal_or_anticonformal_mem hf⟩ (center t) := by
  rcases hf with hf|hf
  · exact center_biholomorphic f hf t
  · have he : boundaryReflection*(boundaryReflection*f)=f := by rw [← mul_assoc,boundaryReflection_sq,one_mul]
    have hs : (⟨f,conformal_or_anticonformal_mem (Or.inr hf)⟩ : boundaryGroup)=
        ⟨boundaryReflection,reflection_mem_boundaryGroup⟩*
        ⟨boundaryReflection*f,biholomorphic_mem_boundaryGroup hf⟩ := Subtype.ext he.symm
    rw [hs,interior_mul,interior_reflection]
    conv_lhs => rw [← he,tripleMap_mul,center_reflection,center_biholomorphic _ hf]
    rfl

lemma center_surjective : Function.Surjective center := by
  intro x
  have ht : (x.2.val:ℂ) ≠ 0 := by exact_mod_cast x.2.property.ne'
  refine ⟨tripleMap (affine (x.2.val:ℂ) x.1 ht) standard,?_⟩
  rw [center_orbit _ (affine_biholomorphic _ _ _),interior_affine]
  apply Prod.ext
  · change (x.2.val:ℂ)*0+x.1=x.1
    simp
  · apply Subtype.ext
    change ‖(x.2.val:ℂ)‖*1=x.2.val
    simp [Complex.norm_real,abs_of_pos x.2.property]
end CannonMobius

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_FiniteB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

lemma finiteNormalizer_spec (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    tripleMap (finiteNormalizer t ht) standard=t := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  have h10 : p 1-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1:Fin 3) ≠ 0) (hinj h))
  have h20 : p 2-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (2:Fin 3) ≠ 0) (hinj h))
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  change tripleMap (affine 1 (p 0) one_ne_zero*inversion*affine a b ha) standard=t
  apply Subtype.ext
  funext i
  fin_cases i
  · change affine 1 (p 0) one_ne_zero (inv ∞)=t.val 0
    rw [inv_infty,affine_coe]
    simpa using hp 0
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (0:ℂ)))=t.val 1
    rw [affine_coe]
    simp only [mul_zero,zero_add]
    rw [inv_coe (inv_ne_zero h10),affine_coe]
    simpa [b] using hp 1
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (1:ℂ)))=t.val 2
    rw [affine_coe]
    have he : a*1+b=(p 2-p 0)⁻¹ := by dsimp [a]; ring
    rw [he,inv_coe (inv_ne_zero h20),affine_coe]
    simpa using hp 2

lemma finiteNormalizer_biholomorphic (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    finiteNormalizer t ht ∈ biholomorphic :=
  biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
    (affine_biholomorphic _ _ _)

lemma center_finite (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ((center t).1,(center t).2.val)=finiteCenterRaw t := by
  have h := center_orbit (finiteNormalizer t ht) (finiteNormalizer_biholomorphic t ht)
  rw [finiteNormalizer_spec] at h
  rw [h]
  change ( (CannonH3.interior (⟨affine 1 (coordinate (t.val 0)) one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht),
    affine_mem_boundaryGroup _ _ _⟩) basepoint).1,
    (CannonH3.interior (⟨affine 1 (coordinate (t.val 0)) one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht),
    affine_mem_boundaryGroup _ _ _⟩) basepoint).2.val)=_
  rw [interior_mul,interior_mul,interior_affine,interior_inversion,interior_affine]
  simp only [Homeomorph.mul_apply]
  change (1*(star (finiteA t*0+finiteB t)/((‖finiteA t*0+finiteB t‖^2+(‖finiteA t‖*1)^2:ℝ):ℂ))+coordinate (t.val 0),
    ‖(1:ℂ)‖*((‖finiteA t‖*1)/(‖finiteA t*0+finiteB t‖^2+(‖finiteA t‖*1)^2)))=_
  simp [finiteCenterRaw,add_comm]

lemma continuousAt_finiteCenterRaw (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ContinuousAt finiteCenterRaw t := by
  have hc (i : Fin 3) : ContinuousAt (fun s : Triple => coordinate (s.val i)) t :=
    (continuousAt_coordinate (ht i)).comp (f := fun s : Triple => s.val i)
      (show ContinuousAt (fun s : Triple => s.val i) t from
        ((continuous_apply i).comp continuous_subtype_val).continuousAt)
  have h10 : coordinate (t.val 1)-coordinate (t.val 0) ≠ 0 := by
    intro hh
    have he := congrArg (fun z : ℂ => (z:Sphere)) (sub_eq_zero.mp hh)
    rw [coe_coordinate (ht 1),coe_coordinate (ht 0)] at he
    exact (by decide : (1:Fin 3) ≠ 0) (t.property he)
  have h20 : coordinate (t.val 2)-coordinate (t.val 0) ≠ 0 := by
    intro hh
    have he := congrArg (fun z : ℂ => (z:Sphere)) (sub_eq_zero.mp hh)
    rw [coe_coordinate (ht 2),coe_coordinate (ht 0)] at he
    exact (by decide : (2:Fin 3) ≠ 0) (t.property he)
  have hb : ContinuousAt finiteB t := ((hc 1).sub (hc 0)).inv₀ h10
  have ha : ContinuousAt finiteA t := (((hc 2).sub (hc 0)).inv₀ h20).sub hb
  have hq : ContinuousAt (fun s : Triple => ‖finiteB s‖^2+‖finiteA s‖^2) t :=
    (hb.norm.pow 2).add (ha.norm.pow 2)
  have hpos : 0 < ‖finiteB t‖^2+‖finiteA t‖^2 := by
    have hh := norm_pos_iff.mpr (finiteA_ne_zero t ht)
    nlinarith [sq_nonneg ‖finiteB t‖]
  exact ((hc 0).add (hb.star.div (Complex.continuous_ofReal.continuousAt.comp hq)
    (by change (↑(‖finiteB t‖^2+‖finiteA t‖^2):ℂ) ≠ 0; exact_mod_cast hpos.ne'))).prodMk (ha.norm.div hq hpos.ne')

lemma continuousAt_center_finite (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : ContinuousAt center t := by
  have he : ∀ᶠ s : Triple in 𝓝 t, ∀ i, s.val i ≠ ∞ := by
    apply Filter.eventually_all.2
    intro i
    exact (((continuous_apply i).comp continuous_subtype_val).continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds (ht i))
  have hh : ContinuousAt (fun s : Triple => ((center s).1,(center s).2.val)) t := by
    apply (continuousAt_finiteCenterRaw t ht).congr_of_eventuallyEq
    filter_upwards [he] with s hs
    exact center_finite s hs
  exact hh.fst.prodMk (hh.snd.codRestrict (fun s => (center s).2.property))

lemma continuous_center : Continuous center := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨p,hp⟩ := exists_pole_avoiding t
  let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
  have hN : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic (affine_biholomorphic _ _ _)
  have hNp : N (p:Sphere)=∞ := by
    change inv (affine 1 (-p) one_ne_zero p)=∞
    rw [affine_coe]
    simp only [one_mul,add_neg_cancel,inv_zero]
  have ht (i : Fin 3) : (tripleMap N t).val i ≠ ∞ := fun he => hp i (N.injective (he.trans hNp.symm))
  have hc := (continuousAt_center_finite (tripleMap N t) ht).comp (continuous_tripleMap N).continuousAt
  let F := CannonH3.interior ⟨N,biholomorphic_mem_boundaryGroup hN⟩
  have he : (fun s : Triple => F.symm (center (tripleMap N s)))=center := by
    funext s
    rw [center_biholomorphic N hN]
    exact F.symm_apply_apply _
  have hh := F.symm.continuous.continuousAt.comp hc
  rwa [show (F.symm ∘ center ∘ tripleMap N) = center from he] at hh
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma matrixHomeomorph_apply (M : Mat) (hM : M.det ≠ 0) (p : Sphere) :
    matrixHomeomorph M hM p=matrixFun M p := (matrixFun_eq_smul _ p).symm

end CannonMobius

namespace CannonMobius
open Set Filter Topology
open CannonH3
open scoped Matrix.Norms.Elementwise

lemma rowNorm_pos (M : Mat) (hM : M.det ≠ 0) : 0 < rowNorm M := by
  have hn : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    simp [Matrix.det_fin_two,h.1,h.2] at hM
  rcases hn with hn|hn <;> have hh := norm_pos_iff.mpr hn <;>
    unfold rowNorm <;> nlinarith [sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]

lemma complex_gram (a b c d : ℂ) :
    (‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2)=‖a*star c+b*star d‖^2+‖a*d-b*c‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma matrixEnergy_center (M : Mat) (hM : ‖M.det‖=1) :
    matrixEnergy M=(‖(matrixCenterRaw M).1‖^2+(matrixCenterRaw M).2^2+1)/(matrixCenterRaw M).2 := by
  have hn : M.det ≠ 0 := fun hh => by simp [hh] at hM
  have hr := (rowNorm_pos M hn).ne'
  have he := complex_gram (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  rw [← Matrix.det_fin_two,hM,one_pow] at he
  unfold matrixCenterRaw
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (rowNorm_pos M hn),hM]
  unfold numerator rowNorm matrixEnergy at *
  field_simp
  nlinarith

lemma continuous_rowNorm : Continuous rowNorm := by unfold rowNorm; fun_prop
lemma continuous_numerator : Continuous numerator := by unfold numerator; fun_prop
lemma continuousAt_matrixCenterRaw {M : Mat} (hM : M.det ≠ 0) : ContinuousAt matrixCenterRaw M := by
  unfold matrixCenterRaw
  apply ContinuousAt.prodMk
  · exact continuous_numerator.continuousAt.div
      (Complex.continuous_ofReal.comp continuous_rowNorm).continuousAt
      (by exact_mod_cast (rowNorm_pos M hM).ne')
  · exact (continuous_id.matrix_det.norm).continuousAt.div continuous_rowNorm.continuousAt
      (rowNorm_pos M hM).ne'

lemma continuous_halfInclusion : Continuous halfInclusion :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

lemma continuous_centerEnergy : Continuous centerEnergy := by
  apply Continuous.div _ (continuous_subtype_val.comp continuous_snd) (fun x => x.2.property.ne')
  fun_prop

theorem compact_matrix_parameters (K : Set Half) (hK : IsCompact K) :
    IsCompact ({M : Mat | ‖M.det‖=1} ∩ matrixCenterRaw ⁻¹' (halfInclusion '' K)) := by
  have hS : IsClosed {M : Mat | ‖M.det‖=1} := isClosed_eq continuous_id.matrix_det.norm continuous_const
  have hcont : ContinuousOn matrixCenterRaw {M : Mat | ‖M.det‖=1} := by
    intro M hM
    apply (continuousAt_matrixCenterRaw ?_).continuousWithinAt
    intro hh
    simp [hh] at hM
  apply Metric.isCompact_of_isClosed_isBounded
    (hcont.preimage_isClosed_of_isClosed hS (hK.image continuous_halfInclusion).isClosed)
  obtain ⟨B,hB⟩ := hK.bddAbove_image continuous_centerEnergy.continuousOn
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max B 1,?_⟩
  rintro M ⟨hM,x,hx,he⟩
  have hE : matrixEnergy M ≤ B := by
    rw [matrixEnergy_center M hM,← he]
    exact hB (mem_image_of_mem centerEnergy hx)
  have hsq (i j : Fin 2) : ‖M i j‖^2 ≤ B := by
    unfold matrixEnergy at hE
    fin_cases i <;> fin_cases j
    · change ‖M 0 0‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 0 1‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 1 0‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 1 1‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 0‖]
  apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right B 1))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right B 1))).mpr
  intro j
  have hb := hsq i j
  have hb' := le_max_left B 1
  have h1 := le_max_right B 1
  nlinarith [norm_nonneg (M i j)]
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

lemma affineMatrix_det (a b : ℂ) : (affineMatrix a b).det=a := by simp [affineMatrix,Matrix.det_fin_two]
lemma generalMatrix_det (p a b : ℂ) : (generalMatrix p a b).det= -a := by
  simp [generalMatrix,Matrix.det_fin_two]
  ring
lemma affineMatrix_fun (a b : ℂ) (ha : a ≠ 0) : matrixFun (affineMatrix a b)=affine a b ha := by
  funext z
  induction z using OnePoint.rec with
  | infty => simp [matrixFun_infty,affineMatrix,affine]
  | coe z => simp [matrixFun_coe,affineMatrix,ratio,affine_coe]
lemma generalMatrix_fun (p a b : ℂ) (ha : a ≠ 0) :
    matrixFun (generalMatrix p a b)=affine 1 p one_ne_zero*inversion*affine a b ha := by
  funext z
  induction z using OnePoint.rec with
  | infty =>
    change ratio (p*a) a=affine 1 p one_ne_zero (inv ∞)
    rw [ratio_of_ne ha,inv_infty,affine_coe]
    simp [ha]
  | coe z =>
    change ratio ((p*a)*z+(p*b+1)) (a*z+b)=affine 1 p one_ne_zero (inv (affine a b ha (z:ℂ)))
    rw [affine_coe]
    by_cases hh : a*z+b=0
    · rw [hh,ratio_zero,inv_zero]
      rfl
    · rw [ratio_of_ne hh,inv_coe hh,affine_coe]
      congr 1
      field_simp
      ring
lemma affineMatrix_center (a b : ℂ) : matrixCenterRaw (affineMatrix a b)=(b,‖a‖) := by
  simp [matrixCenterRaw,numerator,rowNorm,affineMatrix,Matrix.det_fin_two]
lemma generalMatrix_center (p a b : ℂ) (ha : a ≠ 0) :
    matrixCenterRaw (generalMatrix p a b)=
      (p+star b/((‖b‖^2+‖a‖^2:ℝ):ℂ),‖a‖/(‖b‖^2+‖a‖^2)) := by
  have hq : 0 < ‖a‖^2+‖b‖^2 := by have hh := norm_pos_iff.mpr ha; nlinarith [sq_nonneg ‖b‖]
  have han : a*star a=(‖a‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
  have hbn : b*star b=(‖b‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
  have hu : numerator (generalMatrix p a b)=p*((‖a‖^2+‖b‖^2:ℝ):ℂ)+star b := by
    change (p*a)*star a+(p*b+1)*star b=_
    rw [Complex.ofReal_add,← han,← hbn]
    ring
  apply Prod.ext
  · change numerator (generalMatrix p a b)/(rowNorm (generalMatrix p a b):ℂ)=_
    rw [hu]
    change (p*((‖a‖^2+‖b‖^2:ℝ):ℂ)+star b)/((‖a‖^2+‖b‖^2:ℝ):ℂ)=_
    rw [add_comm (‖b‖^2) (‖a‖^2)]
    have hn : ((‖a‖^2+‖b‖^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  · change ‖(generalMatrix p a b).det‖/rowNorm (generalMatrix p a b)=_
    rw [generalMatrix_det,norm_neg]
    simp [rowNorm,generalMatrix,add_comm]

lemma center_normal_form (p a b : ℂ) (ha : a ≠ 0) :
    let f := affine 1 p one_ne_zero*inversion*affine a b ha
    let hf := biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic 1 p one_ne_zero)
      inversion_biholomorphic) (affine_biholomorphic a b ha)
    let x := CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint
    (x.1,x.2.val)=(p+star b/((‖b‖^2+‖a‖^2:ℝ):ℂ),‖a‖/(‖b‖^2+‖a‖^2)) := by
  change ( (CannonH3.interior (⟨affine 1 p one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine a b ha,affine_mem_boundaryGroup _ _ _⟩) basepoint).1,
    (CannonH3.interior (⟨affine 1 p one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine a b ha,affine_mem_boundaryGroup _ _ _⟩) basepoint).2.val)=_
  rw [interior_mul,interior_mul,interior_affine,interior_inversion,interior_affine]
  simp only [Homeomorph.mul_apply]
  change (1*(star (a*0+b)/((‖a*0+b‖^2+(‖a‖*1)^2:ℝ):ℂ))+p,
    ‖(1:ℂ)‖*((‖a‖*1)/(‖a*0+b‖^2+(‖a‖*1)^2)))=_
  simp [add_comm]

lemma exists_center_matrix (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    ∃ M : Mat, M.det ≠ 0 ∧ matrixFun M=f ∧
      matrixCenterRaw M=((CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint).1,
        (CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint).2.val) := by
  rcases biholomorphic_normal_form f hf with ⟨a,b,ha,rfl⟩|⟨p,a,b,ha,rfl⟩
  · refine ⟨affineMatrix a b,by simpa [affineMatrix_det] using ha,affineMatrix_fun a b ha,?_⟩
    rw [affineMatrix_center,interior_affine]
    simp [CannonH3.affine,complexAffine,heightScale,basepoint]
  · exact ⟨generalMatrix p a b,by simpa [generalMatrix_det] using ha,generalMatrix_fun p a b ha,
      (generalMatrix_center p a b ha).trans (center_normal_form p a b ha).symm⟩
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

lemma rescale_det (r : ℝ) (M : Mat) : (rescale r M).det=(r:ℂ)^2*M.det := by
  simp only [rescale,Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul]
  ring
lemma rescale_rowNorm (r : ℝ) (M : Mat) : rowNorm (rescale r M)=r^2*rowNorm M := by
  simp only [rowNorm,rescale,Matrix.smul_apply,smul_eq_mul,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring
lemma rescale_numerator (r : ℝ) (M : Mat) : numerator (rescale r M)=(r:ℂ)^2*numerator M := by
  simp only [numerator,rescale,Matrix.smul_apply,smul_eq_mul,star_mul,Complex.star_def,Complex.conj_ofReal]
  ring
lemma rescale_matrixFun (r : ℝ) (hr : r ≠ 0) (M : Mat) : matrixFun (rescale r M)=matrixFun M := by
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  funext p
  induction p using OnePoint.rec with
  | infty => exact ratio_scale _ _ _ hr'
  | coe z =>
    change ratio ((r:ℂ)*M 0 0*z+(r:ℂ)*M 0 1) ((r:ℂ)*M 1 0*z+(r:ℂ)*M 1 1)=_
    rw [show (r:ℂ)*M 0 0*z+(r:ℂ)*M 0 1=(r:ℂ)*(M 0 0*z+M 0 1) by ring,
      show (r:ℂ)*M 1 0*z+(r:ℂ)*M 1 1=(r:ℂ)*(M 1 0*z+M 1 1) by ring]
    exact ratio_scale _ _ _ hr'
lemma rescale_center (r : ℝ) (hr : r ≠ 0) (M : Mat) :
    matrixCenterRaw (rescale r M)=matrixCenterRaw M := by
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  apply Prod.ext
  · change numerator (rescale r M)/(rowNorm (rescale r M):ℂ)=_
    rw [rescale_numerator,rescale_rowNorm,Complex.ofReal_mul,Complex.ofReal_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hr')
  · change ‖(rescale r M).det‖/rowNorm (rescale r M)=_
    rw [rescale_det,rescale_rowNorm,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)
lemma exists_normalized_matrix (M : Mat) (hM : M.det ≠ 0) :
    ∃ N : Mat, ‖N.det‖=1 ∧ matrixFun N=matrixFun M ∧ matrixCenterRaw N=matrixCenterRaw M := by
  have hnp : 0 < ‖M.det‖ := norm_pos_iff.mpr hM
  let r := (Real.sqrt ‖M.det‖)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnp)
  refine ⟨rescale r M,?_,rescale_matrixFun r hr.ne' M,rescale_center r hr.ne' M⟩
  rw [rescale_det,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  dsimp [r]
  rw [inv_pow,Real.sq_sqrt hnp.le,inv_mul_cancel₀ hnp.ne']

lemma exists_normalized_triple_matrix (t : Triple) :
    ∃ M : Mat, ‖M.det‖=1 ∧ (∀ i, matrixFun M (std i)=t.val i) ∧
      matrixCenterRaw M=((center t).1,(center t).2.val) := by
  obtain ⟨M,hM,hMf,hMc⟩ := exists_center_matrix (normalizer t).val (normalizer t).property
  obtain ⟨N,hN,hNf,hNc⟩ := exists_normalized_matrix M hM
  refine ⟨N,hN,?_,hNc.trans hMc⟩
  intro i
  rw [hNf,hMf]
  exact congrFun (congrArg Subtype.val (normalizer_spec t)) i

lemma compact_center_preimage {K : Set Half} (hK : IsCompact K) : IsCompact (center ⁻¹' K) := by
  let P : Set Mat := {M | ‖M.det‖=1 ∧ ∃ x ∈ K, (x.1,x.2.val)=matrixCenterRaw M}
  have hP : IsCompact P := compact_matrix_parameters K hK
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP
  have hd (M : P) : M.val.det ≠ 0 := by
    intro he
    have hh := M.property.1
    rw [he,norm_zero] at hh
    norm_num at hh
  let F : P → Triple := fun M => tripleMap (matrixHomeomorph M.val (hd M)) standard
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have he : (fun M : P => (F M).val i)=(fun M : P => matrixFun M.val (std i)) := by
      funext M
      exact matrixHomeomorph_apply M.val (hd M) _
    change Continuous (fun M : P => (F M).val i)
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun M => matrixFun_continuous continuous_subtype_val.continuousAt
      continuous_const.continuousAt (hd M))
  apply (isCompact_range hF).of_isClosed_subset (hK.isClosed.preimage continuous_center)
  intro t ht
  obtain ⟨M,hM,hMt,hMc⟩ := exists_normalized_triple_matrix t
  have hh : M ∈ P := ⟨hM,center t,ht,hMc.symm⟩
  refine ⟨⟨M,hh⟩,?_⟩
  apply Subtype.ext
  funext i
  exact (matrixHomeomorph_apply M (hd ⟨M,hh⟩) (std i)).trans (hMt i)

lemma proper_center : IsProperMap center :=
  isProperMap_iff_isCompact_preimage.mpr ⟨continuous_center,fun _ => compact_center_preimage⟩
end CannonMobius

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_GeometricConformalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonH3
open CannonMobius CannonActions CannonRelease

variable {G : Type*} [Group G]

theorem geometric_conformal_action (σ : G →* (Sphere ≃ₜ Sphere))
    (hσ : ∀ g, σ g ∈ biholomorphic ∨ boundaryReflection*σ g ∈ biholomorphic)
    (hP : Proper (triplesAction σ)) (hC : Cocompact (triplesAction σ)) :
    ProperAction (conformalActionExtension σ hσ) ∧ CocompactAction (conformalActionExtension σ hσ) ∧
      ((conformalActionExtension σ hσ).ker : Set G).Finite := by
  let ρ := conformalActionExtension σ hσ
  let B : G →* (HyperbolicThree ≃ₜ HyperbolicThree) := hyperbolicIsometries.subtype.comp ρ
  let p : Triple → HyperbolicThree := coords.symm ∘ center
  have hp : IsProperMap p := coords.symm.isProperMap.comp proper_center
  have hs : Function.Surjective p := coords.symm.surjective.comp center_surjective
  have he (g : G) (t : Triple) : p (triplesAction σ g t)= B g (p t) := by
    change coords.symm (center (tripleMap (σ g) t))=(ρ g).val (coords.symm (center t))
    rw [center_conformal _ (hσ g)]
    change coords.symm (coords ((extensionHom ⟨σ g,conformal_or_anticonformal_mem (hσ g)⟩).val
      (coords.symm (center t))))=_
    rw [coords.symm_apply_apply]
    rfl
  have hBP : Proper B := proper_descends hp hs he hP
  have hBC : Cocompact B := cocompact_descends hp.continuous hs he hC
  refine ⟨hBP,hBC,?_⟩
  let _ : Nonempty HyperbolicThree := ⟨coords.symm basepoint⟩
  apply (proper_finite_kernel hBP).subset
  intro g hg
  change B g=1
  change ρ g=1 at hg
  change (ρ g).val=1
  rw [hg]
  rfl
end CannonH3

namespace CannonRelease
open CannonGraph CannonVisual CannonActions CannonMobius CannonH3

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_conformal_action (ψ : Boundary D ≃ₜ Sphere)
    (hψ : ∀ g, conjugate ψ (boundaryAction D ⟨δ,hδ⟩) g ∈ biholomorphic ∨
      boundaryReflection*conjugate ψ (boundaryAction D ⟨δ,hδ⟩) g ∈ biholomorphic) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧ (ρ.ker : Set G).Finite := by
  let _ := visualMetricSpace D hδ
  let A := boundaryAction D ⟨δ,hδ⟩
  let σ := conjugate ψ A
  have hP : Proper (triplesAction A) := boundary_triples_proper D hδ
  have hC : Cocompact (triplesAction A) := boundary_triples_cocompact D hδ
  have hPσ : Proper (triplesAction σ) := by
    rw [show σ=conjugate ψ A from rfl,triples_conjugate]
    exact proper_conjugate (triplesCongr ψ) hP
  have hCσ : Cocompact (triplesAction σ) := by
    rw [show σ=conjugate ψ A from rfl,triples_conjugate]
    exact cocompact_conjugate (triplesCongr ψ) hC
  exact ⟨conformalActionExtension σ hψ,geometric_conformal_action σ hψ hPσ hCσ⟩
end CannonRelease

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Actions_BoundaryAction
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
open Set

universe v
variable {G : Type v} [Group G]

theorem CayleyData.countable (D : CayleyData G) : Countable G := by
  apply Set.countable_univ_iff.mp
  have hfin (n : ℕ) : {g : G | D.graph.dist 1 g ≤ n}.Finite :=
    CannonGraph.finite_graph_ball D.connected (CannonGraph.finite_cayley_neighbors D.generators) 1 n
  have hcover : (⋃ n : ℕ, {g : G | D.graph.dist 1 g ≤ n}) = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro g
    exact Set.mem_iUnion.mpr ⟨D.graph.dist 1 g,by change D.graph.dist 1 g ≤ D.graph.dist 1 g; rfl⟩
  rw [← hcover]
  exact Set.countable_iUnion (fun n => (hfin n).countable)

end CannonRelease

end
end
noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual CannonQM CannonActions CannonMobius CannonH3

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniformized_action (ψ : Boundary D ≃ₜ Sphere) :
    let _ := visualMetricSpace D hδ
    QuasiMobius ψ →
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧ (ρ.ker : Set G).Finite := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro hψ
  let : Countable G := D.countable
  obtain ⟨η,hη⟩ := boundary_uniform_conjugates D hδ ψ hψ
  let A := boundaryAction D ⟨δ,hδ⟩
  obtain ⟨F,hF⟩ := sphere_action_straightening (conjugate ψ A) hη
  apply boundary_conformal_action D hδ (ψ.trans F)
  intro g
  have he : conjugate (ψ.trans F) (boundaryAction D ⟨δ,hδ⟩) g =
      F*conjugate ψ A g*F.symm := by
    ext z
    rfl
  simpa only [he] using hF g

end CannonRelease

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A group with a hyperbolic Cayley graph and spherical boundary admits a proper, cocompact action on hyperbolic three-space with finite kernel. -/

section
noncomputable section
namespace CannonRelease
universe u

theorem cannon_oai (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G) (hthin : D.ThinTriangles)
    (hsphere : Nonempty (Boundary D ≃ₜ SphereTwo)) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite := by
  obtain ⟨δ,hδ⟩ := hthin
  obtain ⟨φ⟩ := hsphere
  let _ := visualMetricSpace D hδ
  obtain ⟨ψ,hψ⟩ := boundary_quasiMobius_uniformizer D hδ φ
  exact boundary_uniformized_action D hδ ψ hψ
end CannonRelease

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.CannonRelease.cannon_oai.{u} := @OAI.CannonRelease.cannon_oai.{u}
