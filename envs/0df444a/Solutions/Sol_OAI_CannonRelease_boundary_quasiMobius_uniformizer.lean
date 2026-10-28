-- Prove2me | solution 1 for OAI.CannonRelease.boundary_quasiMobius_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:10:52.526916+00:00
-- url     : https://prove2.me/submissions/90085ca2-0eb6-4876-a7ce-b9bd5b24724e

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonRelease_boundary_modulus_subexponential
import Theorems.Thm_OAI_CannonRelease_boundary_no_record_flow
import Theorems.Thm_OAI_CannonRelease_boundary_packing_relative_tests
import Theorems.Thm_OAI_CannonRelease_boundary_record_data

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_Radius
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
section
section
section
section
section
section
section
section
open Filter Topology

namespace CannonNode

lemma radius_ratio (ell : ℝ) (k d : ℕ) : radius ell k/radius ell (k+d) = Real.exp (ell*d) := by
  simp only [radius, ← Real.exp_sub, Nat.cast_add]
  congr 1
  ring

lemma radius_sub_ratio (ell : ℝ) (k d e : ℕ) (hed : e ≤ d) :
    radius ell (k+d)/radius ell (k+e) = radius ell (d-e) := by
  simp only [radius,← Real.exp_sub,Nat.cast_add,Nat.cast_sub hed]
  congr 1
  ring

lemma radius_antitone {ell : ℝ} (hell : 0 ≤ ell) : Antitone (radius ell) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  have hh : (i:ℝ) ≤ j := by exact_mod_cast hij
  exact mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr hell)

lemma radius_eq_power (ell : ℝ) (k : ℕ) : radius ell k = (Real.exp ell^k)⁻¹ := by
  rw [← Real.exp_nat_mul,← Real.exp_neg]
  unfold radius
  congr 1
  ring

lemma radius_tendsto {ell : ℝ} (hell : 0 < ell) : Tendsto (radius ell) atTop (𝓝 0) := by
  have he : Real.exp (-ell) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hell)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-ell)).le he
  change Tendsto (fun n : ℕ => Real.exp (-ell*n)) atTop (𝓝 0)
  simpa only [radius,← Real.exp_nat_mul, mul_comm] using ht

lemma nat_mul_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => d*n) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n)
  · intro n
    exact Nat.le_mul_of_pos_left n hd
  · exact tendsto_id

theorem eventually_flow_scales (qdim : ℕ) (ell c₀ H C : ℝ) (hell : 0 < ell) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      c₀*radius ell (160*(qdim+1)*n) ≤ 1 ∧
      2*(H+3)*radius ell (160*(qdim+1)*n) ≤ 1 ∧
      radius ell (2*n) ≤ 1/4 ∧
      C*radius ell ((160*(qdim+1)-2)*n) ≤ 1 := by
  have hd : 0 < 160*(qdim+1) := by omega
  have he : 0 < 160*(qdim+1)-2 := by omega
  have hdl : Tendsto (fun n : ℕ => radius ell (160*(qdim+1)*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto hd)
  have hel : Tendsto (fun n : ℕ => radius ell ((160*(qdim+1)-2)*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto he)
  have h₂l : Tendsto (fun n : ℕ => radius ell (2*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto (by norm_num : 0 < (2:ℕ)))
  have hcl : Tendsto (fun n : ℕ => c₀*radius ell (160*(qdim+1)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdl.const_mul c₀
  have hHl : Tendsto (fun n : ℕ => 2*(H+3)*radius ell (160*(qdim+1)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdl.const_mul (2*(H+3))
  have hCl : Tendsto (fun n : ℕ => C*radius ell ((160*(qdim+1)-2)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hel.const_mul C
  filter_upwards [eventually_gt_atTop (0:ℕ),
    hdl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hcl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hHl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    h₂l.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hCl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn hdn hcn hHn h₂n hCn
  exact ⟨hn,hdn,hcn.le,hHn.le,h₂n.le,hCn.le⟩

end CannonNode

end

end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Lower
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
section
section
section
section
section
section
section
section
open Set Metric

namespace CannonNode

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma ball_range {f : X → ℝ} {y : X} {r : ℝ}
    (hf : ContinuousOn f (closedBall y r)) {z : X} (hz : z ∈ closedBall y r) :
    lower f y r ≤ f z ∧ f z ≤ upper f y r := by
  have hc := (isCompact_closedBall y r).image_of_continuousOn hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hz),
    le_csSup hc.bddAbove (mem_image_of_mem f hz)⟩

lemma ball_extrema {f : X → ℝ} {y : X} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall y r)) :
    (∃ z ∈ closedBall y r, f z = lower f y r) ∧
    (∃ z ∈ closedBall y r, f z = upper f y r) := by
  have hc := (isCompact_closedBall y r).image_of_continuousOn hf
  have hne : (f '' closedBall y r).Nonempty := ⟨f y,y,mem_closedBall_self hr,rfl⟩
  exact ⟨hc.sInf_mem hne,hc.sSup_mem hne⟩

lemma lower_le_upper {f : X → ℝ} {y : X} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall y r)) : lower f y r ≤ upper f y r :=
  (ball_range hf (mem_closedBall_self hr)).1.trans (ball_range hf (mem_closedBall_self hr)).2

lemma ball_range_mono {f : X → ℝ} {y : X} {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hf : ContinuousOn f (closedBall y s)) :
    lower f y s ≤ lower f y r ∧ upper f y r ≤ upper f y s := by
  have hsub : closedBall y r ⊆ closedBall y s := closedBall_subset_closedBall hrs
  obtain ⟨⟨z,hz,hzv⟩,⟨w,hw,hwv⟩⟩ := ball_extrema hr (hf.mono hsub)
  exact ⟨hzv ▸ (ball_range hf (hsub hz)).1,hwv ▸ (ball_range hf (hsub hw)).2⟩

lemma fraction_nonneg {a b l u : ℝ} (hab : a < b) : 0 ≤ fraction a b l u :=
  div_nonneg (le_max_left _ _) (sub_pos.mpr hab).le

lemma positive_child_length {a b l u : ℝ} (hab : a < b)
    (hpos : 0 < fraction a b l u) :
    childUpper b u-childLower a l = (b-a)*fraction a b l u := by
  have hh := (fraction_pos_iff hab).mp hpos
  rw [fraction,max_eq_right (sub_nonneg.mpr hh.le)]
  field_simp [(sub_pos.mpr hab).ne']

end CannonNode

end

end
end
end
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

local instance instSetoidBasedRay_2_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_10_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_12_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

end
end
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

local instance instSetoidBasedRay_27_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_29_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_31_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
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
section
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace CannonNet

variable {X : Type*} [MetricSpace X]

theorem exists_finite_separated_net (A : Set X) (hA : TotallyBounded A)
    (r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X, (↑T : Set X) ⊆ A ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y) ∧
      (∀ x ∈ A, ∃ y ∈ T, dist x y ≤ r) := by
  classical
  let ε : ℝ≥0 := ⟨r,hr.le⟩
  have hε : ε / 2 ≠ 0 := div_ne_zero (by
    intro he
    exact hr.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) he)) (by norm_num)
  obtain ⟨C,_,hCf,hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded hε hA
  have hfinite : Metric.packingNumber ε A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf)
    calc
      Metric.packingNumber ε A = Metric.packingNumber (2*(ε/2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε/2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ C.encard := hcover.externalCoveringNumber_le_encard
  let T := Metric.maximalSeparatedSet ε A
  have hTA : T ⊆ A := Metric.maximalSeparatedSet_subset
  have hTf : T.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard ≠ ⊤
    rwa [Metric.encard_maximalSeparatedSet hfinite])
  have hsep : Metric.IsSeparated ε T := Metric.isSeparated_maximalSeparatedSet
  have htcover : Metric.IsCover ε A T := Metric.isCover_maximalSeparatedSet hfinite
  have hrr : (ε : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.coe_nnreal_eq ε
  refine ⟨hTf.toFinset,?_,?_,?_⟩
  · simpa using hTA
  · intro x hx y hy hxy
    have hh := hsep (by simpa using hx) (by simpa using hy) hxy
    rw [hrr, edist_dist] at hh
    exact le_of_not_gt (fun hh' => (not_lt_of_ge (ENNReal.ofReal_le_ofReal hh'.le)) hh)
  · intro x hx
    obtain ⟨y,hy,hd⟩ := htcover hx
    refine ⟨y,by simpa using hy,?_⟩
    change edist x y ≤ (ε : ℝ≥0∞) at hd
    rw [hrr, edist_dist] at hd
    exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp hd

theorem exists_compact_net [CompactSpace X] (r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X,
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y) ∧
      (∀ x : X, ∃ y ∈ T, dist x y ≤ r) ∧
      (∀ x : X, ∃ y ∈ T, x ∈ Metric.ball y (2*r)) := by
  obtain ⟨T,_,hsep,hcover⟩ := exists_finite_separated_net (univ : Set X) isCompact_univ.totallyBounded r hr
  refine ⟨T,hsep,fun x => hcover x (mem_univ x),?_⟩
  intro x
  obtain ⟨y,hy,hd⟩ := hcover x (mem_univ x)
  exact ⟨y,hy,show dist x y < 2*r by linarith⟩

end CannonNet

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Clip
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
section
section
section
section
section
section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators

namespace CannonAnnular

theorem weighted_open_interval_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Ioo a b,
      c ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    c * (b - a) ≤ ∑ i, w i * (U i - L i) := by
  have hint (l u v : ℝ) : Integrable ((Icc l u).indicator (fun _ : ℝ => v)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hinta : Integrable ((Ioo a b).indicator (fun _ : ℝ => c)) := by
    apply (integrable_indicator_iff measurableSet_Ioo).mpr
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hle : (Ioo a b).indicator (fun _ : ℝ => c) ≤
      fun t => ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t := by
    intro t
    by_cases ht : t ∈ Ioo a b
    · simpa [Set.indicator_of_mem ht] using hcover t ht
    · rw [Set.indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => hw i) _)
  have hi := integral_mono hinta
    (integrable_finsetSum _ (fun i _ => hint (L i) (U i) (w i))) hle
  rw [integral_finsetSum _ (fun i _ => hint (L i) (U i) (w i))] at hi
  simpa only [integral_indicator_const _ measurableSet_Ioo,
    integral_indicator_const _ measurableSet_Icc, Measure.real,
    Real.volume_Ioo, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hLU _)), smul_eq_mul, mul_comm] using hi

theorem overlap_energy {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (R : α → Finset β) (w : β → ℝ) (kr kc : ℕ)
    (hrow : ∀ i, (R i).card ≤ kr)
    (hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc) :
    (∑ i, (∑ j ∈ R i, w j)^2) ≤
      (kr : ℝ) * kc * (∑ j, (w j)^2) := by
  classical
  have hrowE (i : α) : (∑ j ∈ R i, w j)^2 ≤ (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R i) (fun _ => (1:ℝ)) w
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrow i)
      (Finset.sum_nonneg (fun j _ => sq_nonneg (w j))))
  have hswap : (∑ i, ∑ j ∈ R i, (w j)^2) =
      ∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2 := by
    calc
      _ = ∑ i, ∑ j : β, if j ∈ R i then (w j)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ R i), (w j)^2 := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by simp
  calc
    _ ≤ ∑ i, (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := Finset.sum_le_sum (fun i _ => hrowE i)
    _ = (kr : ℝ) * (∑ i, ∑ j ∈ R i, (w j)^2) := (Finset.mul_sum ..).symm
    _ = (kr : ℝ) * (∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2) := by rw [hswap]
    _ ≤ (kr : ℝ) * (∑ j, (kc : ℝ) * (w j)^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcol j) (sq_nonneg (w j)))
    _ = _ := by rw [← Finset.mul_sum]; ring

end CannonAnnular

namespace CannonAnnular

theorem finite_charge_cover {α β : Type*} [Fintype α] [Fintype β]
    (A : Finset α) (B : Finset β) (R : α → Finset β) (w : β → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hcharge : ∀ j ∈ B, ∃ i ∈ A, j ∈ R i) :
    (∑ j ∈ B, w j) ≤ ∑ i ∈ A, ∑ j ∈ R i, w j := by
  classical
  calc
    _ ≤ ∑ j ∈ B, ∑ i ∈ A, if j ∈ R i then w j else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨i, hi, hij⟩ := hcharge j hj
      have hh := Finset.single_le_sum (s := A) (f := fun i => if j ∈ R i then w j else 0)
        (fun i _ => by split_ifs; exact hw j; exact le_rfl) hi
      simpa only [ite_eq_left hij] using hh
    _ = ∑ i ∈ A, ∑ j ∈ B, if j ∈ R i then w j else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · exact fun j _ _ => hw j

end CannonAnnular

end

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

theorem bin_interval_detection {ι β : Type*} [Fintype ι] [Fintype β]
    (near : β → ι → Prop) (L U v t : ι → ℝ) (a b B : ℝ)
    (hab : a < b) (hLU : ∀ i, L i ≤ U i) (hv : ∀ i, 0 ≤ v i)
    (hlen : ∀ i, U i-L i = (b-a)*t i)
    (hmult : ∀ i, ((univ.filter (fun z : β => near z i)).card : ℝ) ≤ B)
    (hcover : ∀ z s, s ∈ Ioo a b →
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => if near z i then v i else 0) s) :
    (Fintype.card β : ℝ) ≤ B * ∑ i, v i*t i := by
  classical
  have ht : ∀ i, 0 ≤ t i := by
    intro i
    have := sub_nonneg.mpr (hLU i)
    rw [hlen] at this
    exact nonneg_of_mul_nonneg_right this (sub_pos.mpr hab)
  have hb (z : β) := CannonAnnular.weighted_open_interval_cover L U
    (fun i => if near z i then v i else 0) a b 1 hab.le hLU
    (fun i => by split_ifs; exact hv i; exact le_rfl) (hcover z)
  have hh := Finset.sum_le_sum (s := univ) (fun z _ => hb z)
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul] at hh
  have hr : ∑ z : β, ∑ i : ι, (if near z i then v i else 0)*(U i-L i) ≤
      (b-a)*(B * ∑ i, v i*t i) := by
    rw [sum_comm]
    calc
      _ = ∑ i : ι, ((univ.filter (fun z : β => near z i)).card : ℝ)*v i*((b-a)*t i) := by
        apply sum_congr rfl
        intro i _
        rw [← sum_mul,hlen,← sum_filter]
        simp
      _ ≤ ∑ i : ι, B*v i*((b-a)*t i) := by
        apply sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hmult i) (hv i)) (mul_nonneg (sub_pos.mpr hab).le (ht i))
      _ = _ := by simp_rw [show ∀ i, B*v i*((b-a)*t i) = (b-a)*B*(v i*t i) by intro i; ring]
                  rw [← mul_sum]; ring
  have hfinal := hh.trans hr
  rw [mul_comm (Fintype.card β : ℝ)] at hfinal
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp hfinal

theorem mixed_capacity_of_detection {ι : Type*} [Fintype ι]
    (t σ : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hσ : ∀ i, 0 ≤ σ i)
    {L Q C B E bins : ℝ} (hL : 0 < L) (hQ : 0 < Q) (_hC : 0 ≤ C)
    (hB : 0 < B) (hE : 0 ≤ E) (hb : 0 ≤ bins)
    (henergy : ∑ i, (σ i)^2 ≤ E)
    (hlarge : 2*B*C ≤ L*bins)
    (hsmall : 4*B^2*E*C < Q*bins^2)
    (hdetect : bins ≤ B * ∑ i, (if L ≤ Q*t i then 1 else σ i)*t i) :
    C ≤ ∑ i, min (L*t i) (Q*(t i)^2) := by
  classical
  let large := univ.filter (fun i => L ≤ Q*t i)
  let small := univ.filter (fun i => ¬ L ≤ Q*t i)
  have hnon : ∀ i, 0 ≤ min (L*t i) (Q*(t i)^2) :=
    fun i => le_min (mul_nonneg hL.le (ht i)) (mul_nonneg hQ.le (sq_nonneg _))
  by_contra hn
  have hcap : ∑ i, min (L*t i) (Q*(t i)^2) < C := lt_of_not_ge hn
  have hla : L * (∑ i ∈ large, t i) ≤ C := by
    calc
      _ = ∑ i ∈ large, min (L*t i) (Q*(t i)^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hh := (mem_filter.mp hi).2
        rw [min_eq_left (by nlinarith [mul_le_mul_of_nonneg_right hh (ht i)])]
      _ ≤ ∑ i, min (L*t i) (Q*(t i)^2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hnon i)
      _ ≤ C := hcap.le
  have hsm : Q * (∑ i ∈ small, (t i)^2) ≤ C := by
    calc
      _ = ∑ i ∈ small, min (L*t i) (Q*(t i)^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hh := le_of_not_ge (mem_filter.mp hi).2
        rw [min_eq_right (by nlinarith [mul_le_mul_of_nonneg_right hh (ht i)])]
      _ ≤ ∑ i, min (L*t i) (Q*(t i)^2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hnon i)
      _ ≤ C := hcap.le
  have hde : bins ≤ B*((∑ i ∈ large, t i) + ∑ i ∈ small, σ i*t i) := by
    convert hdetect using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    simp only [large,small,sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  have hmass : bins ≤ 2*B*(∑ i ∈ small, σ i*t i) := by
    nlinarith
  have hCS := sum_mul_sq_le_sq_mul_sq small σ t
  have hsumσ : ∑ i ∈ small, (σ i)^2 ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg _)).trans henergy
  have hsmt : 0 ≤ ∑ i ∈ small, (t i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsms : 0 ≤ ∑ i ∈ small, σ i*t i := sum_nonneg (fun i _ => mul_nonneg (hσ i) (ht i))
  have hsquare : bins^2 ≤ 4*B^2*(∑ i ∈ small, σ i*t i)^2 := by
    nlinarith [sq_le_sq₀ hb (mul_nonneg (by positivity) hsms) |>.mpr hmass]
  have hcs' : (∑ i ∈ small, σ i*t i)^2 ≤ E*(∑ i ∈ small, (t i)^2) :=
    hCS.trans (mul_le_mul_of_nonneg_right hsumσ hsmt)
  have hbound : Q*bins^2 ≤ 4*B^2*E*C := by
    calc
      _ ≤ Q*(4*B^2*(∑ i ∈ small, σ i*t i)^2) := mul_le_mul_of_nonneg_left hsquare hQ.le
      _ ≤ Q*(4*B^2*(E*(∑ i ∈ small, (t i)^2))) := by gcongr
      _ = (4*B^2*E)*(Q*(∑ i ∈ small, (t i)^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsm (by positivity)
  exact (not_lt_of_ge hbound) hsmall

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

theorem weighted_separated_subset {ι : Type*} (S : Finset ι) (rel : ι → ι → Prop)
    (hself : ∀ i, rel i i) (hsymm : ∀ i j, rel i j → rel j i)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (N : ℕ)
    (hN : ∀ i ∈ S, (S.filter (rel i)).card ≤ N) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ rel i j) ∧
      (∑ i ∈ S, w i) ≤ (N : ℝ) * ∑ i ∈ T, w i := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i,hi,hmax⟩ := S.exists_max_image w hS
      let U := S.filter (fun j => ¬ rel i j)
      have hUS : U ⊆ S := filter_subset _ _
      have hiU : i ∉ U := by simp [U,hself]
      have hss : U ⊂ S := by
        refine ⟨hUS,?_⟩
        intro hh
        exact hiU (hh hi)
      obtain ⟨T,hTU,hsep,hbound⟩ := ih U hss
        (fun j hj => hw j (hUS hj)) (by
          intro j hj
          exact (Finset.card_le_card (Finset.filter_subset_filter _ hUS)).trans (hN j (hUS hj)))
      have hiT : i ∉ T := fun h => hiU (hTU h)
      refine ⟨insert i T,Finset.insert_subset_iff.mpr ⟨hi,hTU.trans hUS⟩,?_,?_⟩
      · intro j hj k hk hjk
        rcases mem_insert.mp hj with rfl | hjT
        · rcases mem_insert.mp hk with rfl | hk
          · exact fun _ => hjk rfl
          · exact (mem_filter.mp (hTU hk)).2
        · rcases mem_insert.mp hk with rfl | hk
          · exact fun h => (mem_filter.mp (hTU hjT)).2 (hsymm _ _ h)
          · exact hsep j hjT k hk hjk
      · have hnear : ∑ j ∈ S.filter (rel i), w j ≤ (N : ℝ)*w i := by
          calc
            _ ≤ ∑ j ∈ S.filter (rel i), w i := by
              exact Finset.sum_le_sum (fun j hj => hmax j (mem_filter.mp hj).1)
            _ = ((S.filter (rel i)).card : ℝ)*w i := by simp
            _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hN i hi) (hw i hi)
        have hsplit : (∑ j ∈ S, w j) =
            (∑ j ∈ S.filter (rel i), w j) + ∑ j ∈ U, w j := by
          symm
          exact Finset.sum_filter_add_sum_filter_not S (rel i) w
        rw [hsplit,Finset.sum_insert hiT]
        nlinarith
    · refine ⟨∅,empty_subset _,by simp,?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

lemma clip_mono (a b : ℝ) : Monotone (clip a b) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

lemma mem_clipped_iff {a b l u t : ℝ} (ht : t ∈ Ioo a b) :
    t ∈ Icc (clip a b l) (clip a b u) ↔ t ∈ Icc l u := by
  simp only [Set.mem_Icc,clip]
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · by_contra hh
      have hh' : t < l := lt_of_not_ge hh
      have : t < min b l := lt_min ht.2 hh'
      exact (not_lt_of_ge ((le_max_right _ _).trans hl)) this
    · by_contra hh
      have hh' : u < t := lt_of_not_ge hh
      have : max a (min b u) < t := max_lt ht.1 (lt_of_le_of_lt (min_le_right _ _) hh')
      exact (not_lt_of_ge hu) this
  · rintro ⟨hl,hu⟩
    exact ⟨max_le ht.1.le ((min_le_right _ _).trans hl),
      (le_min ht.2.le hu).trans (le_max_right _ _)⟩

lemma clip_difference {a b l u : ℝ} (hab : a ≤ b) (hlu : l ≤ u) :
    clip a b u-clip a b l = max 0 (min b u-max a l) := by
  unfold clip
  rcases le_total l a with hla | hal
  · rw [min_eq_right (hla.trans hab),max_eq_left hla]
    rw [← max_sub_sub_right]
    simp only [sub_self,max_comm]
  · by_cases hlb : l ≤ b
    · rw [min_eq_right hlb,max_eq_right hal]
      have hmin : l ≤ min b u := le_min hlb hlu
      rw [max_eq_right (hal.trans hmin),max_eq_right (sub_nonneg.mpr hmin)]
    · have hbl := le_of_not_ge hlb
      simp only [min_eq_left (hbl.trans hlu),min_eq_left hbl,max_eq_right hab,sub_self,
        max_eq_right hal]
      exact (max_eq_left (by linarith)).symm

theorem clipped_bin_detection {ι β : Type*} [Fintype ι] [Fintype β]
    (lo hi t σ : ι → ℝ) (large : ι → Prop) (near : β → ι → Prop)
    (a b B : ℝ) (hab : a < b) (hlohi : ∀ i, lo i ≤ hi i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hσ : ∀ i, 0 ≤ σ i)
    (hmult : ∀ i, ((univ.filter (fun z => near z i)).card : ℝ) ≤ B)
    (hunmarked : ∀ z s, s ∈ Ioo a b →
      (∀ i, large i → near z i → s ∈ Icc (lo i) (hi i) → False) →
      1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
        (fun _ : ℝ => if near z i ∧ ¬large i then σ i else 0) s) :
    (Fintype.card β : ℝ) ≤ B * ∑ i, (if large i then 1 else σ i)*t i := by
  apply bin_interval_detection near (fun i => clip a b (lo i))
    (fun i => clip a b (hi i)) (fun i => if large i then 1 else σ i) t
    a b B hab (fun i => clip_mono a b (hlohi i))
    (fun i => by split_ifs; norm_num; exact hσ i) hlen hmult
  intro z s hs
  by_cases hm : ∃ i, large i ∧ near z i ∧ s ∈ Icc (lo i) (hi i)
  · obtain ⟨i,hiL,hiN,hit⟩ := hm
    calc
      1 = (Icc (clip a b (lo i)) (clip a b (hi i))).indicator
          (fun _ : ℝ => if near z i then if large i then 1 else σ i else 0) s := by
        rw [indicator_of_mem ((mem_clipped_iff hs).mpr hit),ite_eq_left hiN,ite_eq_left hiL]
      _ ≤ ∑ j, (Icc (clip a b (lo j)) (clip a b (hi j))).indicator
          (fun _ : ℝ => if near z j then if large j then 1 else σ j else 0) s := by
        apply single_le_sum _ (mem_univ i)
        intro j _
        apply Set.indicator_nonneg
        intro _ _
        split_ifs; norm_num; exact hσ j; exact le_rfl
  · apply (hunmarked z s hs (by simpa only [not_exists,not_and] using hm)).trans
    apply sum_le_sum
    intro i _
    by_cases hit : s ∈ Icc (lo i) (hi i)
    · rw [indicator_of_mem hit,indicator_of_mem ((mem_clipped_iff hs).mpr hit)]
      by_cases hn : near z i <;> by_cases hl : large i <;> simp [hn,hl]
    · rw [indicator_of_notMem hit,indicator_of_notMem (fun hh => hit ((mem_clipped_iff hs).mp hh))]

theorem separated_capacity_of_detection {X : Type*} [MetricSpace X]
    {ι β : Type*} [Fintype ι] [Fintype β]
    (q : ι → X) (lo hi t σ : ι → ℝ) (near : β → ι → Prop)
    (a b B L Q E H r : ℝ) (N : ℕ) (hab : a < b)
    (hlohi : ∀ i, lo i ≤ hi i) (ht : ∀ i, 0 ≤ t i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hσ : ∀ i, 0 ≤ σ i) (hL : 0 < L) (hQ : 0 < Q) (hB : 0 < B) (hE : 0 ≤ E)
    (hHr : 0 ≤ H*r) (hN : 0 < N)
    (hdegree : ∀ i, (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N)
    (hmult : ∀ i, ((univ.filter (fun z => near z i)).card : ℝ) ≤ B)
    (henergy : ∑ i, (σ i)^2 ≤ E)
    (hlarge : 2*B*N ≤ L*Fintype.card β)
    (hsmall : 4*B^2*E*N < Q*(Fintype.card β : ℝ)^2)
    (hunmarked : ∀ z s, s ∈ Ioo a b →
      (∀ i, L ≤ Q*t i → near z i → s ∈ Icc (lo i) (hi i) → False) →
      1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
        (fun _ : ℝ => if near z i ∧ ¬L ≤ Q*t i then σ i else 0) s) :
    ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2) := by
  have hdetect := clipped_bin_detection lo hi t σ (fun i => L ≤ Q*t i) near a b B
    hab hlohi hlen hσ hmult hunmarked
  have hcap := mixed_capacity_of_detection t σ ht hσ hL hQ (by positivity : (0:ℝ) ≤ N)
    hB hE (by positivity) henergy hlarge hsmall hdetect
  obtain ⟨S,hS,hsep,hbound⟩ := weighted_separated_subset univ
    (fun i j => dist (q i) (q j) ≤ H*r) (by simpa using fun _i : ι => hHr)
    (fun i j h => by simpa only [dist_comm] using h)
    (fun i => min (L*t i) (Q*(t i)^2))
    (fun i _ => le_min (mul_nonneg hL.le (ht i)) (mul_nonneg hQ.le (sq_nonneg _))) N
    (fun i _ => hdegree i)
  refine ⟨S,fun i hi j hj hij => lt_of_not_ge (hsep i hi j hj hij),?_⟩
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  nlinarith [hcap.trans hbound]

end CannonCapacity

end

section

section

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

theorem radial_subpath {X : Type*} [PseudoMetricSpace X] (o x y : X)
    (p : Path x y) (r s : ℝ) (hrs : r < s)
    (hx : dist x o ≤ r) (hy : s ≤ dist y o) :
    ∃ u v : X, ∃ q : Path u v,
      Set.range q ⊆ Set.range p ∧ dist u o = r ∧ dist v o = s ∧
      s-r ≤ dist u v ∧ ∀ t, dist (q t) o ∈ Icc r s := by
  obtain ⟨a, b, hab, ha, hb, hbetween⟩ := radial_subinterval
    (fun t => dist (p t) o) (p.continuous.dist continuous_const) r s hrs
    (by simpa using hx) (by simpa using hy)
  refine ⟨p a, p b, p.subpath a b, ?_, ha, hb, ?_, ?_⟩
  · rw [Path.range_subpath_of_le _ _ _ hab.le]
    exact Set.image_subset_range _ _
  · have hh := dist_triangle (p b) (p a) o
    rw [dist_comm (p b) (p a), ha, hb] at hh
    linarith
  · intro t
    have ht : (p.subpath a b) t ∈ Set.range (p.subpath a b) := Set.mem_range_self _
    rw [Path.range_subpath_of_le _ _ _ hab.le] at ht
    obtain ⟨z, hz, hzt⟩ := ht
    rw [← hzt]
    exact hbetween z hz

theorem continuum_neighborhood_path {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {K V : Set X} (hK : IsPreconnected K)
    (hV : IsOpen V) (hKV : K ⊆ V) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    JoinedIn V x y := by
  let : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  let f : K → V := fun z => ⟨z.val, hKV z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hconn : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hmem : f ⟨y,hy⟩ ∈ connectedComponent (f ⟨x,hx⟩) :=
    hconn.subset_connectedComponent ⟨⟨x,hx⟩, rfl⟩ ⟨⟨y,hy⟩, rfl⟩
  rw [← pathComponent_eq_connectedComponent] at hmem
  obtain ⟨p⟩ := hmem
  exact ⟨p.map continuous_subtype_val, fun t => (p t).property⟩

theorem annular_path_near_continuum {X : Type*} [PseudoMetricSpace X]
    [LocallyPathConnectedSpace X] (o : X) (r s : ℝ) (hrs : r < s)
    (K V : Set X) (hK : IsPreconnected K) (hV : IsOpen V) (hKV : K ⊆ V)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxr : dist x o ≤ r) (hys : s ≤ dist y o) :
    ∃ u v : X, ∃ q : Path u v,
      Set.range q ⊆ V ∧ dist u o = r ∧ dist v o = s ∧
      s-r ≤ dist u v ∧ ∀ t, dist (q t) o ∈ Icc r s := by
  obtain ⟨p, hp⟩ := continuum_neighborhood_path hK hV hKV hx hy
  obtain ⟨u, v, q, hqp, hu, hv, huv, hq⟩ := radial_subpath o x y p r s hrs hxr hys
  refine ⟨u, v, q, ?_, hu, hv, huv, hq⟩
  rintro z hz
  obtain ⟨t, rfl⟩ := hqp hz
  exact hp t

end CannonAnnular

end
end
end
end
end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_PathCellIndices
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
section
section
section
section
section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

open Metric

lemma exists_outer_point {X : Type*} [PseudoMetricSpace X] (o : X) (R : ℝ)
    (hR : 0 ≤ R) {K : Set X} (hdiam : 4*R < diam K) :
    ∃ y ∈ K, 2*R ≤ dist y o := by
  by_contra hn
  push Not at hn
  have hh : diam K ≤ 4*R := by
    apply diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    have hh := dist_triangle x o y
    rw [dist_comm o y] at hh
    linarith [hn x hx, hn y hy]
  exact (not_lt_of_ge hh) hdiam

end CannonAnnular

open Set Metric

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

lemma level_radial_hit {X : Type*} [MetricSpace X] (x : X) (K : Set X)
    (hK : IsPreconnected K) {b : ℝ} (hb : 0 ≤ b)
    (hinner : ∃ y ∈ K, dist y x ≤ b) (hdiam : 2*b < diam K) :
    ∃ w ∈ K, dist w x = b := by
  obtain ⟨y,hy,hyb⟩ := hinner
  obtain ⟨z,hz,hzb⟩ := exists_outer_point x (b/2) (by linarith) (by linarith : 4*(b/2) < diam K)
  exact hK.intermediate_value hy hz (continuous_id.dist continuous_const).continuousOn
    ⟨hyb,by dsimp; linarith⟩

theorem unmarked_level_detection {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] {ι β : Type*} [Fintype ι] [Fintype β]
    (q : ι → X) (ξ : β → X) (h : X → X) (hh : Continuous h)
    (x w z : X) (A Ω K : Set X) (f : X → ℝ) (lo hi σ : ι → ℝ)
    (large : ι → Prop) (r s C d₀ b t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hC : 0 ≤ C)
    (hK : IsPreconnected K) (hwK : w ∈ K) (hdiam : 4*s < diam K)
    (hwb : dist w x = b) (hwz : dist w z ≤ s)
    (hregion : ∀ v, dist v w ≤ s → v ∈ A)
    (hdomain : ∀ v, dist v w ≤ s+r/4 → v ∈ Ω)
    (hlevel : ∀ v ∈ K, v ∈ Ω → f v = t)
    (hnet : ∀ v ∈ A, ∃ i, dist (q i) v ≤ r)
    (hupper : ∀ v v', dist v z ≤ 3*s → dist v' z ≤ 3*s →
      dist (h v) (h v') ≤ C/s*dist v v')
    (hlower : ∀ v v', dist v z ≤ 2*s → dist v' z ≤ 2*s →
      s ≤ dist v v' → d₀ ≤ dist (h v) (h v'))
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/s) d₀ ω)
    (hσ : ∀ i, 0 ≤ σ i)
    (hpay : ∀ i, dist (q i) z ≤ 3*s →
      (∑ j ∈ univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/s)), ω j) ≤ σ i)
    (hunmarked : ∀ i, large i → |dist (q i) x-b| ≤ 5*s → t ∈ Icc (lo i) (hi i) → False) :
    1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
      (fun _ : ℝ => if |dist (q i) x-b| ≤ 5*s ∧ ¬ large i then σ i else 0) t := by
  classical
  let V : Set X := ⋃ v ∈ K, ball v (r/4)
  have hV : IsOpen V := isOpen_iUnion (fun v => isOpen_iUnion (fun _ => isOpen_ball))
  have hKV : K ⊆ V := by
    intro v hv
    exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,by simp [hr]⟩⟩
  obtain ⟨v,hv,hvs⟩ := exists_outer_point w s hs.le hdiam
  obtain ⟨u,v',π,hπV,hu,hv',huv,hπ⟩ := annular_path_near_continuum w 0 s hs K V
    hK hV hKV hwK hv (by simp) (by linarith)
  have hzπ : ∀ a, dist (π a) z ≤ 2*s := by
    intro a
    exact (dist_triangle (π a) w z).trans (by linarith [(hπ a).2])
  let π' := π.map hh
  have hmacro : d₀ ≤ diam (range π') := by
    have h₁ : dist u z ≤ 2*s := by simpa only [π.source] using hzπ 0
    have h₂ : dist v' z ≤ 2*s := by simpa only [π.target] using hzπ 1
    exact (hlower u v' h₁ h₂ (by linarith)).trans
      (dist_le_diam_of_mem (isCompact_range π'.continuous).isBounded
        ⟨0,π'.source⟩ ⟨1,π'.target⟩)
  have hadm := hω.2 (h u) (h v') π' hmacro
  let eligible := univ.filter (fun i => |dist (q i) x-b| ≤ 5*s ∧
    ¬ large i ∧ t ∈ Icc (lo i) (hi i) ∧ dist (q i) z ≤ 3*s)
  let rel i := univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/s))
  have hcharge : ∀ j ∈ pathCellIndices ξ (r/s) π', ∃ i ∈ eligible, j ∈ rel i := by
    intro j hj
    obtain ⟨a,ha⟩ := (mem_filter.mp hj).2
    obtain ⟨i,hqi⟩ := hnet (π a) (hregion _ (hπ a).2)
    have hiw : dist (q i) w ≤ r+s := (dist_triangle (q i) (π a) w).trans (by linarith [(hπ a).2])
    have hiz : dist (q i) z ≤ 3*s := (dist_triangle (q i) w z).trans (by linarith)
    obtain ⟨v',hv'⟩ := mem_iUnion.mp (hπV (mem_range_self a))
    obtain ⟨hv'K,hv'π⟩ := mem_iUnion.mp hv'
    have hv'π : dist v' (π a) < r/4 := by simpa only [mem_ball,dist_comm] using hv'π
    have hv'Ω : v' ∈ Ω := hdomain _ ((dist_triangle v' (π a) w).trans (by linarith [(hπ a).2]))
    have htv : t ∈ Icc (lo i) (hi i) := by
      rw [← hlevel v' hv'K hv'Ω]
      apply hrange i v' hv'Ω
      have hd := dist_triangle v' (π a) (q i)
      rw [dist_comm (π a) (q i)] at hd
      linarith
    have hib : |dist (q i) x-b| ≤ 5*s := by
      rw [← hwb]
      exact (abs_dist_sub_le (q i) w x).trans (by linarith)
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,hib,fun hl => hunmarked i hl hib htv,htv,hiz⟩,?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have ht : dist (h (π a)) (h (q i)) ≤ C/s*r := by
      apply (hupper _ _ (by linarith [hzπ a]) hiz).trans
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hqi) (div_nonneg hC hs.le)
    have ha' : dist (ξ j) (h (π a)) ≤ 2*(r/s) := by
      simpa only [Path.map_coe,π',dist_comm,Function.comp_apply] using ha.le
    calc
      _ ≤ dist (ξ j) (h (π a)) + dist (h (π a)) (h (q i)) := dist_triangle _ _ _
      _ ≤ 2*(r/s)+C/s*r := add_le_add ha' ht
      _ = _ := by ring
  have hchargeSum := finite_charge_cover eligible (pathCellIndices ξ (r/s) π') rel ω hω.1 hcharge
  have hbound : (∑ i ∈ eligible, ∑ j ∈ rel i, ω j) ≤ ∑ i ∈ eligible, σ i := by
    apply sum_le_sum
    intro i hi
    exact hpay i (mem_filter.mp hi).2.2.2.2
  apply hadm.trans (hchargeSum.trans (hbound.trans _))
  rw [sum_filter]
  apply sum_le_sum
  intro i _
  by_cases he : |dist (q i) x-b| ≤ 5*s ∧ ¬ large i ∧ t ∈ Icc (lo i) (hi i) ∧ dist (q i) z ≤ 3*s
  · have hnear : |dist (q i) x-b| ≤ 5*s ∧ ¬ large i := ⟨he.1,he.2.1⟩
    simp only [ite_eq_left he,indicator_of_mem he.2.2.1,ite_eq_left hnear]
    exact le_rfl
  · rw [ite_eq_right he]
    exact Set.indicator_nonneg (fun _ _ => by split_ifs; exact hσ i; exact le_rfl) _

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

lemma sparse_transfer_energy {ι β : Type*} [Fintype ι] [Fintype β]
    (f : β → ι → ℝ) (near : β → ι → Prop) (N : ℕ) (E : ℝ)
    (hsupport : ∀ z i, ¬ near z i → f z i = 0)
    (hmult : ∀ i, (univ.filter (fun z => near z i)).card ≤ N)
    (he : ∀ z, ∑ i, (f z i)^2 ≤ E) :
    (∑ i, (∑ z, f z i)^2) ≤ (N : ℝ) * Fintype.card β * E := by
  classical
  have hrow (i : ι) : (∑ z, f z i)^2 ≤ (N : ℝ)*∑ z, (f z i)^2 := by
    let S := univ.filter (fun z => near z i)
    have heq : ∑ z, f z i = ∑ z ∈ S, f z i := by
      symm
      apply sum_filter_of_ne
      intro z _ hz
      by_contra hn
      exact hz (hsupport z i hn)
    rw [heq]
    have hCS := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun z => f z i)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hCS
    calc
      _ ≤ (S.card : ℝ)*(∑ z ∈ S, (f z i)^2) := hCS
      _ ≤ (N : ℝ)*(∑ z, (f z i)^2) := by
        apply mul_le_mul (by exact_mod_cast hmult i)
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun z _ _ => sq_nonneg _))
          (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  calc
    _ ≤ ∑ i, (N : ℝ)*∑ z, (f z i)^2 := sum_le_sum (fun i _ => hrow i)
    _ = (N : ℝ)*∑ z, ∑ i, (f z i)^2 := by rw [← mul_sum,sum_comm]
    _ ≤ (N : ℝ)*∑ _z : β, E := mul_le_mul_of_nonneg_left (sum_le_sum (fun z _ => he z)) (by positivity)
    _ = _ := by simp; ring

theorem exists_local_transfer_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP A c : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hA : 0 < A) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι β : Type*} [Fintype ι] [Fintype β]
      (q : ι → X) (ξ : β → X) (h : X → X) (z : X) (r s : ℝ),
      0 < r → 0 < s → max A (max c 1)*(r/s) ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ v v', dist v z ≤ 3*s → dist v' z ≤ 3*s →
        c/s*dist v v' ≤ dist (h v) (h v')) →
      ∀ ω : β → ℝ,
      (∑ i, (if dist (q i) z ≤ 3*s then
        ∑ j ∈ univ.filter (fun j => dist (ξ j) (h (q i)) ≤ A*(r/s)), ω j else 0)^2) ≤
        E*∑ j, (ω j)^2 := by
  classical
  obtain ⟨kr,hkr⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  obtain ⟨kc,hkc⟩ := exists_overlap_bound Q CP A c hpack hCP hA hc
  refine ⟨(kr:ℝ)*kc,by positivity,?_⟩
  intro ι β _ _ q ξ h z r s hr hs hscale hq hξ hlow ω
  let rel i := if dist (q i) z ≤ 3*s then
    univ.filter (fun j => dist (ξ j) (h (q i)) ≤ A*(r/s)) else ∅
  let S := univ.filter (fun i => dist (q i) z ≤ 3*s)
  have hratio : 0 < r/s := div_pos hr hs
  have hscale₁ : max A 1*(r/s) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_right ..)) hratio.le).trans hscale
  have hscalec : max A c*(r/s) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_left ..)) hratio.le).trans hscale
  have hrow (i : ι) : (rel i).card ≤ kr := by
    dsimp only [rel]
    split_ifs
    · have hh := hkr ξ univ (h (q i)) (r/s) hratio hscale₁ (by simpa using hξ)
      simpa only [dist_comm] using hh
    · simp
  have hcol (j : β) : (univ.filter (fun i => j ∈ rel i)).card ≤ kc := by
    have him : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c*(r/s) ≤ dist (h (q i)) (h (q j)) := by
      intro i hi j hj hij
      calc
        _ = c/s*r := by ring
        _ ≤ c/s*dist (q i) (q j) := mul_le_mul_of_nonneg_left (hq i j hij) (div_nonneg hc.le hs.le)
        _ ≤ _ := hlow _ _ (mem_filter.mp hi).2 (mem_filter.mp hj).2
    have hh := hkc (fun i => h (q i)) S (ξ j) (r/s) hratio hscalec him
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext i
    by_cases hi : dist (q i) z ≤ 3*s <;> simp [S,rel,hi]
  have he := overlap_energy rel ω kr kc hrow hcol
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext i
  simp only [rel]
  split_ifs <;> simp

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

theorem node_separated_capacity {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X]
    {ι β ζ δ : Type*} [Fintype ι] [Fintype β] [Fintype ζ] [Fintype δ]
    (q : ι → X) (bin : β → ℝ) (aux : ζ → X) (ξ : δ → X)
    (h : ζ → X ≃ₜ X) (x : X) (Ω : Set X) (f : X → ℝ)
    (K : ℝ → Set X) (lo hi t : ι → ℝ)
    (a b A B₀ R r s C c d₀ H L Q E M BinMul : ℝ) (N Naux : ℕ)
    (hab : a < b) (hA : 1 ≤ A) (hAB : A+2 ≤ B₀)
    (hR : 0 < R) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hsR : s ≤ R/4)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c)
    (hbin : ∀ j, (A+1)*R ≤ bin j ∧ bin j ≤ (B₀-1)*R)
    (hnet : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R →
      ∃ i, dist (q i) v ≤ r)
    (haux : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R →
      ∃ z, dist v (aux z) ≤ s)
    (hΩ : ∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω)
    (hK : ∀ v ∈ Ioo a b, IsPreconnected (K v))
    (hinner : ∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R)
    (hdiam : ∀ v ∈ Ioo a b, 2*B₀*R < diam (K v))
    (hlevel : ∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y = v)
    (hlohi : ∀ i, lo i ≤ hi i) (ht : ∀ i, 0 ≤ t i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i))
    (hupper : ∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
      dist (h z v) (h z v') ≤ C/s*dist v v')
    (hlower : ∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
      c/s*dist v v' ≤ dist (h z v) (h z v'))
    (ω : δ → ℝ) (hω : MacroscopicAdmissible ξ (r/s) d₀ ω)
    (hωmass : ∑ j, (ω j)^2 ≤ M)
    (hlocal : ∀ z, (∑ i, (if dist (q i) (aux z) ≤ 3*s then
      ∑ j ∈ univ.filter (fun j => dist (ξ j) (h z (q i)) ≤ (C+2)*(r/s)), ω j else 0)^2)
      ≤ E*∑ j, (ω j)^2)
    (hmultaux : ∀ i, (univ.filter (fun z => dist (q i) (aux z) ≤ 3*s)).card ≤ Naux)
    (hL : 0 < L) (hQ : 0 < Q) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hBinMul : 0 < BinMul) (hHr : 0 ≤ H*r) (hN : 0 < N)
    (hdegree : ∀ i, (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N)
    (hmult : ∀ i, ((univ.filter (fun j => |dist (q i) x-bin j| ≤ 5*s)).card : ℝ) ≤ BinMul)
    (hlarge : 2*BinMul*N ≤ L*Fintype.card β)
    (hsmall : 4*BinMul^2*((Naux:ℝ)*Fintype.card ζ*(E*M))*N < Q*(Fintype.card β : ℝ)^2) :
    ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2) := by
  classical
  let σz : ζ → ι → ℝ := fun z i => if dist (q i) (aux z) ≤ 3*s then
    ∑ j ∈ univ.filter (fun j => dist (ξ j) (h z (q i)) ≤ (C+2)*(r/s)), ω j else 0
  let σ : ι → ℝ := fun i => ∑ z, σz z i
  have hσz : ∀ z i, 0 ≤ σz z i := by
    intro z i
    dsimp only [σz]
    split_ifs
    · exact sum_nonneg (fun j _ => hω.1 j)
    · exact le_rfl
  have hσ : ∀ i, 0 ≤ σ i := fun i => sum_nonneg (fun z _ => hσz z i)
  have he := sparse_transfer_energy σz (fun z i => dist (q i) (aux z) ≤ 3*s) Naux (E*M)
    (by intro z i hn; simp only [σz,ite_eq_right hn]) hmultaux
    (fun z => (hlocal z).trans (mul_le_mul_of_nonneg_left hωmass hE))
  apply separated_capacity_of_detection q lo hi t σ
    (fun j i => |dist (q i) x-bin j| ≤ 5*s) a b BinMul L Q
    ((Naux:ℝ)*Fintype.card ζ*(E*M)) H r N hab hlohi ht hlen hσ hL hQ hBinMul
    (by positivity) hHr hN hdegree hmult he hlarge hsmall
  intro j v hv hunmarked
  have hbnon : 0 ≤ bin j := by nlinarith only [(hbin j).1,hA,hR]
  obtain ⟨w,hwK,hwb⟩ := level_radial_hit x (K v) (hK v hv) hbnon (by
    obtain ⟨y,hy,hyA⟩ := hinner v hv
    exact ⟨y,hy,by nlinarith only [(hbin j).1,hyA,hR]⟩) (by nlinarith only [hdiam v hv,(hbin j).2,hR])
  have hwann : (A-1)*R ≤ dist w x ∧ dist w x ≤ (B₀+1)*R := by
    rw [hwb]
    constructor <;> nlinarith only [(hbin j).1,(hbin j).2,hR]
  obtain ⟨z,hwz⟩ := haux w hwann.1 hwann.2
  apply unmarked_level_detection q ξ (h z) (h z).continuous x w (aux z)
    {v | (A-1)*R ≤ dist v x ∧ dist v x ≤ (B₀+1)*R} Ω (K v) f lo hi σ
    (fun i => L ≤ Q*t i) r s C d₀ (bin j) v hr hs hrs hC (hK v hv) hwK
    (by nlinarith only [hdiam v hv,hAB,hA,hR,hsR]) hwb hwz
    (by
      intro y hy
      have hyw := dist_triangle y w x
      have hwy := dist_triangle w y x
      rw [dist_comm w y] at hwy
      constructor <;> nlinarith only [(hbin j).1,(hbin j).2,hy,hyw,hwy,hwb,hsR,hR])
    (by
      intro y hy
      apply hΩ
      have hh := dist_triangle y w x
      nlinarith only [(hbin j).2,hh,hy,hwb,hsR,hrs,hR])
    (hlevel v hv) (by intro y hy; exact hnet y hy.1 hy.2)
    (hupper z)
    (by
      intro y y' hy hy' hyy'
      have hh := hlower z y y' (by linarith only [hy,hs]) (by linarith only [hy',hs])
      have hsne : s ≠ 0 := ne_of_gt hs
      have hcs : c/s*s = c := by field_simp
      have hm := mul_le_mul_of_nonneg_left hyy' (div_nonneg hc.le hs.le)
      rw [hcs] at hm
      exact hdc.trans (hm.trans hh))
    hrange ω hω hσ (by
      intro i hi
      have hh : σz z i ≤ σ i := single_le_sum (fun z _ => hσz z i) (mem_univ z)
      simpa only [σz,ite_eq_left hi] using hh)
    hunmarked

end CannonCapacity

end

end
end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_BinNearCard
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
section
section
section
section
section
section
section
section
section
open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

lemma bin_near_card (n : ℕ) (offset s d : ℝ) (hs : 0 < s) :
    (univ.filter (fun i : Fin n => |d-(offset+(i:ℝ)*s)| ≤ 5*s)).card ≤ 11 := by
  classical
  let S := univ.filter (fun i : Fin n => |d-(offset+(i:ℝ)*s)| ≤ 5*s)
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => i.val) hS
    have hsub : S.image (fun i => i.val) ⊆ Finset.Icc i.val (i.val+10) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
      refine Finset.mem_Icc.mpr ⟨hmin j hj,?_⟩
      have hi' := abs_le.mp (mem_filter.mp hi).2
      have hj' := abs_le.mp (mem_filter.mp hj).2
      have hr : (j.val:ℝ) ≤ (i.val:ℝ)+10 := by
        change -(5*s) ≤ d-(offset+(i.val:ℝ)*s) ∧ _ at hi'
        change -(5*s) ≤ d-(offset+(j.val:ℝ)*s) ∧ _ at hj'
        nlinarith
      exact_mod_cast hr
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
    exact hc.trans (by simp; omega)
  · change S.card ≤ 11
    rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    norm_num

theorem exists_radial_bins (A R s : ℝ) (hs : 0 < s) (hscale : 2*s ≤ R) :
    ∃ n : ℕ, ∃ bin : Fin n → ℝ,
      R/(2*s) ≤ (n:ℝ) ∧
      (∀ i, (A+1)*R ≤ bin i ∧ bin i ≤ (A+2)*R) ∧
      (∀ i j, i ≠ j → s ≤ |bin i-bin j|) ∧
      (∀ d, (univ.filter (fun i => |d-bin i| ≤ 5*s)).card ≤ 11) := by
  let n := ⌊R/s⌋₊
  let bin : Fin n → ℝ := fun i => (A+1)*R+(i:ℝ)*s
  have hR : 0 < R := by linarith
  have hrs : 0 ≤ R/s := div_nonneg hR.le hs.le
  have hfloor : (n:ℝ) ≤ R/s := Nat.floor_le hrs
  have hfloor' : R/s < (n:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨n,bin,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
    have hf := (div_lt_iff₀ hs).mp hfloor'
    nlinarith
  · intro i
    have hi : (i:ℝ) < (n:ℝ) := by exact_mod_cast i.isLt
    have hni : (0:ℝ) ≤ (i:ℝ) := by positivity
    dsimp [bin]
    constructor
    · nlinarith
    · have hns := (le_div_iff₀ hs).mp hfloor
      nlinarith
  · intro i j hij
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hd : 1 ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
      rcases lt_or_gt_of_ne hv with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt h)))]
        have : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt h)))]
        have : (j.val:ℝ)+1 ≤ (i.val:ℝ) := by exact_mod_cast h
        linarith
    dsimp only [bin]
    rw [show (A+1)*R+(i:ℝ)*s-((A+1)*R+(j:ℝ)*s) = ((i:ℝ)-(j:ℝ))*s by ring,
      abs_mul,abs_of_pos hs]
    nlinarith
  · intro d
    exact bin_near_card n ((A+1)*R) s d hs

end CannonCapacity

end

section

open Filter Topology

namespace CannonCapacity

lemma subexponential_stretch (M : ℕ → ℝ)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (m : ℕ) (hm : 0 < m) (ell : ℝ) (hell : 0 < ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, M (m*n) ≤ C*Real.exp (ell*n) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨C,hC,hbound⟩ := hM (Real.exp (ell/m))
    (Real.one_lt_exp_iff.mpr (div_pos hell hm'))
  refine ⟨C,hC,fun n => ?_⟩
  have hh := hbound (m*n)
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  push_cast
  field_simp

lemma eventually_exp_domination (a b C : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp (a*n) < Real.exp (b*n) := by
  have ht : Tendsto (fun n : ℕ => (b-a)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hab)
  have hh := (Real.tendsto_exp_atTop.comp ht).eventually (eventually_gt_atTop C)
  filter_upwards [hh] with n hn
  have hm := mul_lt_mul_of_pos_right hn (Real.exp_pos (a*n))
  dsimp only [Function.comp_apply] at hm
  rw [← Real.exp_add] at hm
  convert hm using 1; congr 1; ring

theorem eventually_capacity_thresholds (qdim : ℕ) (ell C N : ℝ)
    (hell : 0 < ell) (hC : 0 ≤ C) (hN : 0 < N) (M : ℕ → ℝ)
    (_hMnon : ∀ n, 0 ≤ M n)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ bins E : ℝ,
      Real.exp (2*ell*n)/2 ≤ bins →
      0 ≤ E → E ≤ C*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) →
      22*N ≤ Real.exp (-ell*n)*bins ∧
      484*E*N < Real.exp (8*(qdim+1)*ell*n)*bins^2 := by
  have hqdim : (0:ℝ) ≤ qdim := Nat.cast_nonneg _
  obtain ⟨C₁,hC₁,hstretch⟩ := subexponential_stretch M hM (160*(qdim+1)-2) (by omega) ell hell
  have hlarge := eventually_exp_domination 0 ell (44*N) hell
  have hsmall := eventually_exp_domination ((2*qdim+1)*ell) ((8*(qdim+1)+4)*ell)
    (1936*C*C₁*N) (by nlinarith only [hell,hqdim])
  filter_upwards [hlarge,hsmall] with n hn hn'
  simp only [zero_mul,Real.exp_zero,mul_one] at hn
  intro bins E hbins hE hEb
  have hx : 0 < Real.exp (ell*n) := Real.exp_pos _
  have hxn : 0 < Real.exp (-ell*n) := Real.exp_pos _
  have hx2 : 0 < Real.exp (2*ell*n) := Real.exp_pos _
  have hqq : 0 < Real.exp (8*(qdim+1)*ell*n) := Real.exp_pos _
  have hEbound : E ≤ C*C₁*Real.exp ((2*qdim+1)*ell*n) := by
    calc
      E ≤ C*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) := hEb
      _ ≤ C*Real.exp (2*qdim*ell*n)*(C₁*Real.exp (ell*n)) :=
        mul_le_mul_of_nonneg_left (hstretch n) (mul_nonneg hC (Real.exp_pos _).le)
      _ = _ := by rw [show C*Real.exp (2*qdim*ell*n)*(C₁*Real.exp (ell*n)) =
          C*C₁*(Real.exp (2*qdim*ell*n)*Real.exp (ell*n)) by ring,← Real.exp_add]; congr 2; ring
  constructor
  · have hm := mul_le_mul_of_nonneg_left hbins hxn.le
    have hid : Real.exp (-ell*n)*(Real.exp (2*ell*n)/2) = Real.exp (ell*n)/2 := by
      rw [← mul_div_assoc,← Real.exp_add]
      congr 2
      ring
    rw [hid] at hm
    linarith only [hm,hn]
  · have he := mul_le_mul_of_nonneg_right hEbound (by positivity : 0 ≤ (484:ℝ)*N)
    have hbnon : 0 ≤ bins := (div_pos hx2 (by norm_num)).le.trans hbins
    have hsquare := mul_le_mul hbins hbins (by positivity) hbnon
    have htarget := mul_le_mul_of_nonneg_left hsquare hqq.le
    have hid : Real.exp (8*(qdim+1)*ell*n)*((Real.exp (2*ell*n)/2)*(Real.exp (2*ell*n)/2)) =
        Real.exp ((8*(qdim+1)+4)*ell*n)/4 := by
      rw [show (Real.exp (2*ell*n)/2)*(Real.exp (2*ell*n)/2) =
        (Real.exp (2*ell*n)*Real.exp (2*ell*n))/4 by ring, ← mul_div_assoc,
        ← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    rw [hid] at htarget
    nlinarith only [he,htarget,hn']

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

theorem uniform_separated_capacity {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B₀ H C c d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B₀) (hH : 0 < H)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι ζ δ : Type*} [Fintype ι] [Fintype ζ] [Fintype δ]
      (q : ι → X) (aux : ζ → X) (ξ : δ → X) (h : ζ → X ≃ₜ X)
      (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X)
      (lo hi t : ι → ℝ) (a b R r s : ℝ),
      a < b → 0 < R → 0 < r → 0 < s → r ≤ s → s ≤ R/4 →
      (B₀+1)*R ≤ 1 → max H 1*r ≤ 1 → 3*s ≤ 1 →
      max (C+2) (max c 1)*(r/s) ≤ 1 →
      R/s = Real.exp (2*ell*n) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → s ≤ dist (aux i) (aux j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ z, dist x (aux z) ≤ (B₀+1)*R) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ i, dist (q i) v ≤ r) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ z, dist v (aux z) ≤ s) →
      (∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω) →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B₀*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      (∀ i, lo i ≤ hi i) → (∀ i, 0 ≤ t i) →
      (∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i) →
      (∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i)) →
      (∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
        dist (h z v) (h z v') ≤ C/s*dist v v' ∧ c/s*dist v v' ≤ dist (h z v) (h z v')) →
      ∀ ω : δ → ℝ, MacroscopicAdmissible ξ (r/s) d₀ ω →
      (∑ i, (ω i)^2) ≤ M ((160*(qdim+1)-2)*n) →
      ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
        1 ≤ ∑ i ∈ S, min (Real.exp (-ell*n)*t i) (Real.exp (8*(qdim+1)*ell*n)*(t i)^2) := by
  classical
  obtain ⟨Nt,hNt,htransfer⟩ := exists_local_transfer_constant qdim CP (C+2) c
    hpack hCP (by linarith) hc
  obtain ⟨Naux,hauxcount⟩ := exists_overlap_bound qdim CP 3 1 hpack hCP (by norm_num) zero_lt_one
  obtain ⟨Ndeg,hdegcount⟩ := exists_overlap_bound qdim CP H 1 hpack hCP hH zero_lt_one
  let N := Ndeg+1
  have hN : 0 < N := by dsimp [N]; omega
  have hB : 0 ≤ B₀+1 := by linarith
  let Ctotal := (Naux:ℝ)*CP*(B₀+1)^qdim*Nt
  have hCt : 0 ≤ Ctotal := by dsimp [Ctotal]; positivity
  have hthresh := eventually_capacity_thresholds qdim ell Ctotal N hell hCt
    (by exact_mod_cast hN) M hMnon hM
  filter_upwards [hthresh] with n hn
  intro ι ζ δ _ _ _ q aux ξ h x Ω f K lo hi t a b R r s hab hR hr hs hrs hsR
    hrad hdegscale hauxscale htransscale hratio hq haux hξ hauxloc hnet hauxnet hΩ
    hK hinner hdiam hlevel hlohi ht hlen hrange hmap ω hω hωmass
  obtain ⟨nb,bin,hnb,hbin,_hbinsep,hbinmul⟩ := exists_radial_bins A R s hs (by linarith)
  have hdegree (i : ι) : (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N := by
    exact (hdegcount q univ (q i) r hr hdegscale (by intro i _ j _ hij; simpa only [one_mul] using hq i j hij)).trans (by dsimp [N]; omega)
  have hmultaux (i : ι) : (univ.filter (fun z => dist (q i) (aux z) ≤ 3*s)).card ≤ Naux := by
    exact hauxcount aux univ (q i) s hs (by simpa using hauxscale) (by intro i _ j _ hij; simpa only [one_mul] using haux i j hij)
  have hcardaux : (Fintype.card ζ:ℝ) ≤ CP*(B₀+1)^qdim*Real.exp (2*qdim*ell*n) := by
    have hh := indexed_packing qdim CP hpack aux univ x ((B₀+1)*R) s hs
      (by nlinarith only [hsR,hA,hAB,hR]) hrad (by simpa using hauxloc) (by simpa using haux)
    simp only [card_univ] at hh
    have hid : CP*((B₀+1)*R/s)^qdim = CP*(B₀+1)^qdim*Real.exp (2*qdim*ell*n) := by
      rw [mul_div_assoc,hratio,mul_pow,← Real.exp_nat_mul, ← mul_assoc]
      congr 2
      ring
    exact hh.trans_eq hid
  let Etot := (Naux:ℝ)*Fintype.card ζ*(Nt*M ((160*(qdim+1)-2)*n))
  have hEtot : 0 ≤ Etot := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg hNt (hMnon _))
  have hEtotbound : Etot ≤ Ctotal*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) := by
    have hh := mul_le_mul_of_nonneg_left hcardaux (by positivity : (0:ℝ) ≤ Naux)
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hNt (hMnon ((160*(qdim+1)-2)*n)))
    convert hh' using 1 <;> (try dsimp [Etot,Ctotal]) <;> first | rfl | ring
  have hbinlower : Real.exp (2*ell*n)/2 ≤ (Fintype.card (Fin nb):ℝ) := by
    rw [← hratio,Fintype.card_fin]
    convert hnb using 1 <;> first | rfl | ring
  obtain ⟨hlarge,hsmall⟩ := hn (Fintype.card (Fin nb)) Etot hbinlower hEtot hEtotbound
  apply node_separated_capacity q bin aux ξ h x Ω f K lo hi t a b A B₀ R r s C c d₀ H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) Nt (M ((160*(qdim+1)-2)*n)) 11 N Naux
    hab hA (by linarith) hR hr hs hrs hsR hC hc hdc ?_ hnet hauxnet hΩ hK hinner hdiam hlevel
    hlohi ht hlen hrange (fun z v v' hv hv' => (hmap z v v' hv hv').1)
    (fun z v v' hv hv' => (hmap z v v' hv hv').2) ω hω hωmass ?_ hmultaux
    (Real.exp_pos _) (Real.exp_pos _) hNt (hMnon _) (by norm_num)
    (mul_nonneg hH.le hr.le) hN hdegree ?_ ?_ ?_
  · intro j
    obtain ⟨hl,hu⟩ := hbin j
    exact ⟨hl,hu.trans (by nlinarith only [hAB,hR])⟩
  · intro z
    exact htransfer q ξ (h z) (aux z) r s hr hs htransscale hq hξ
      (fun v v' hv hv' => (hmap z v v' hv hv').2) ω
  · intro i
    exact_mod_cast hbinmul (dist (q i) x)
  · linarith only [hlarge]
  · dsimp only [Etot] at hsmall
    nlinarith only [hsmall]

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

lemma clip_mem {a b x : ℝ} (hab : a ≤ b) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma positive_clip_endpoints {a b l u : ℝ} (hab : a < b)
    (hlen : 0 < clip a b u-clip a b l) : l < b ∧ a < u := by
  constructor
  · by_contra hh
    have hbl : b ≤ l := le_of_not_gt hh
    have hclip : clip a b l = b := by simp only [clip,min_eq_left hbl,max_eq_right hab.le]
    rw [hclip] at hlen
    linarith only [hlen,(clip_mem (x := u) hab.le).2]
  · by_contra hh
    have hua : u ≤ a := le_of_not_gt hh
    have hclip : clip a b u = a := by
      simp only [clip,min_eq_right (hua.trans hab.le),max_eq_left hua]
    rw [hclip] at hlen
    linarith only [hlen,(clip_mem (x := l) hab.le).1]

lemma exists_wide_active_range {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (active : ι → Prop) (a b w : ℝ) (hab : a < b)
    (hlohi : ∀ i, lo i ≤ hi i) (hw : 0 ≤ w)
    (hcard : (Fintype.card ι : ℝ)*w < b-a)
    (hcover : ∀ s ∈ Ioo a b, ∃ i, active i ∧ s ∈ Icc (lo i) (hi i)) :
    ∃ i, active i ∧ w ≤ clip a b (hi i)-clip a b (lo i) := by
  classical
  have hh := CannonAnnular.weighted_open_interval_cover
    (fun i => clip a b (lo i)) (fun i => clip a b (hi i))
    (fun i => if active i then (1:ℝ) else 0) a b 1 hab.le
    (fun i => clip_mono a b (hlohi i)) (fun i => by split_ifs <;> norm_num) (by
      intro s hs
      obtain ⟨i,hai,his⟩ := hcover s hs
      calc
        1 = (Icc (clip a b (lo i)) (clip a b (hi i))).indicator
            (fun _ : ℝ => if active i then (1:ℝ) else 0) s := by
          rw [indicator_of_mem ((mem_clipped_iff hs).mpr his),ite_eq_left hai]
        _ ≤ ∑ j, (Icc (clip a b (lo j)) (clip a b (hi j))).indicator
            (fun _ : ℝ => if active j then (1:ℝ) else 0) s := by
          apply single_le_sum _ (mem_univ i)
          intro j _
          apply Set.indicator_nonneg
          intro _ _
          split_ifs <;> norm_num)
  simp only [one_mul] at hh
  by_contra hn
  have hbound : (∑ i, (if active i then (1:ℝ) else 0)*
      (clip a b (hi i)-clip a b (lo i))) ≤ (Fintype.card ι : ℝ)*w := by
    calc
      _ ≤ ∑ _i : ι, w := by
        apply sum_le_sum
        intro i _
        by_cases ha : active i
        · rw [ite_eq_left ha,one_mul]
          exact le_of_lt (lt_of_not_ge (fun hh => hn ⟨i,ha,hh⟩))
        · simp only [ite_eq_right ha,zero_mul]
          exact hw
      _ = _ := by simp
  linarith only [hh,hbound,hcard]

lemma small_outer_lower_end {a b l u : ℝ} (hab : a < b)
    (hl : l ≤ a+(b-a)/4)
    (hsmall : clip a b u-clip a b l < (b-a)/8) : u < a+3*(b-a)/8 := by
  by_contra hu
  have htarget : a+3*(b-a)/8 ≤ u := le_of_not_gt hu
  have hcL : clip a b l ≤ a+(b-a)/4 :=
    max_le (by linarith only [hab]) ((min_le_right _ _).trans hl)
  have hcU : a+3*(b-a)/8 ≤ clip a b u :=
    (le_min (by linarith only [hab]) htarget).trans (le_max_right _ _)
  linarith only [hsmall,hcL,hcU]

lemma small_outer_upper_start {a b l u : ℝ} (hab : a < b)
    (hu : a+3*(b-a)/4 ≤ u)
    (hsmall : clip a b u-clip a b l < (b-a)/8) : a+5*(b-a)/8 < l := by
  by_contra hl
  have htarget : l ≤ a+5*(b-a)/8 := le_of_not_gt hl
  have hcL : clip a b l ≤ a+5*(b-a)/8 :=
    max_le (by linarith only [hab]) ((min_le_right _ _).trans htarget)
  have hcU : a+3*(b-a)/4 ≤ clip a b u :=
    (le_min (by linarith only [hab]) hu).trans (le_max_right _ _)
  linarith only [hsmall,hcL,hcU]

theorem bad_node_large_range {ι : Type*} [Fintype ι]
    (li ui lo uo : ι → ℝ) (near : ι → Prop) (a b κ : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι : ℝ)*κ ≤ 1/8)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hcover : ∀ s ∈ Ioo a b, ∃ i, near i ∧ s ∈ Icc (li i) (ui i))
    (hbad : ¬ ∃ i j,
      κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
      κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
      uo i+(b-a)/4 ≤ lo j) :
    ∃ i, near i ∧ (b-a)/8 ≤ clip a b (uo i)-clip a b (lo i) := by
  have hΔ : 0 < b-a := sub_pos.mpr hab
  have hw : 0 < κ*(b-a) := mul_pos hκ hΔ
  have hcount' : (Fintype.card ι : ℝ)*(κ*(b-a)) ≤ (b-a)/8 := by nlinarith only [hcount,hΔ]
  obtain ⟨i,hni,hwi⟩ := exists_wide_active_range li ui near a (a+(b-a)/4) (κ*(b-a))
    (by linarith only [hab]) hinner hw.le (by linarith only [hcount',hΔ]) (by
      intro s hs
      apply hcover s
      exact ⟨hs.1,by linarith only [hs.2,hab]⟩)
  obtain ⟨j,hnj,hwj⟩ := exists_wide_active_range li ui near (a+3*(b-a)/4) b (κ*(b-a))
    (by linarith only [hab]) hinner hw.le (by linarith only [hcount',hΔ]) (by
      intro s hs
      apply hcover s
      exact ⟨by linarith only [hs.1,hab],hs.2⟩)
  by_contra hn
  have hsi : clip a b (uo i)-clip a b (lo i) < (b-a)/8 :=
    lt_of_not_ge (fun h => hn ⟨i,hni,h⟩)
  have hsj : clip a b (uo j)-clip a b (lo j) < (b-a)/8 :=
    lt_of_not_ge (fun h => hn ⟨j,hnj,h⟩)
  have hiend := (positive_clip_endpoints (by linarith only [hab]) (hw.trans_le hwi)).1
  have hjstart := (positive_clip_endpoints (by linarith only [hab]) (hw.trans_le hwj)).2
  have he := small_outer_lower_end hab ((hlo i).trans hiend.le) hsi
  have hs := small_outer_upper_start hab (hjstart.le.trans (huo j)) hsj
  exact hbad ⟨i,j,hwi,hwj,by linarith only [he,hs]⟩

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

theorem node_radial_cover {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X)
    (li ui : ι → ℝ) (a b A B R r rad : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hA : 0 ≤ A) (hrad : A*R ≤ rad ∧ rad ≤ B*R)
    (hnet : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R → ∃ i, dist (q i) v ≤ r)
    (hΩ : ∀ v, dist v x ≤ (B+1)*R → v ∈ Ω)
    (hK : ∀ t ∈ Ioo a b, IsPreconnected (K t))
    (hinner : ∀ t ∈ Ioo a b, ∃ y ∈ K t, dist y x ≤ A*R)
    (hdiam : ∀ t ∈ Ioo a b, 2*B*R < diam (K t))
    (hlevel : ∀ t ∈ Ioo a b, ∀ v ∈ K t, v ∈ Ω → f v=t)
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (li i) (ui i)) :
    ∀ t ∈ Ioo a b, ∃ i, |dist (q i) x-rad| ≤ r ∧ t ∈ Icc (li i) (ui i) := by
  intro t ht
  obtain ⟨w,hw,hwr⟩ := level_radial_hit x (K t) (hK t ht)
    ((mul_nonneg hA hR.le).trans hrad.1)
    (by obtain ⟨y,hy,hyD⟩ := hinner t ht; exact ⟨y,hy,hyD.trans hrad.1⟩)
    (by nlinarith only [hdiam t ht,hrad.2])
  obtain ⟨i,hi⟩ := hnet w (by rw [hwr]; nlinarith only [hrad.1,hR])
    (by rw [hwr]; nlinarith only [hrad.2,hR])
  have hwΩ := hΩ w (by rw [hwr]; nlinarith only [hrad.2,hR])
  refine ⟨i,?_,?_⟩
  · rw [← hwr]
    exact (abs_dist_sub_le (q i) w x).trans hi
  · rw [← hlevel t ht w hw hwΩ]
    apply hrange i w hwΩ
    rw [dist_comm]
    linarith only [hi,hr]

theorem bad_node_many_children {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (li ui lo uo t : ι → ℝ) (a b κ A B R r H : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι:ℝ)*κ ≤ 1/8)
    (hR : 0 < R) (hr : 0 < r) (hH : 0 < H) (hAB : A+2 ≤ B)
    (hscale : 2*((H+3)*r) ≤ R)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hlen : ∀ i, clip a b (uo i)-clip a b (lo i) = (b-a)*t i)
    (hcover : ∀ rad, A*R ≤ rad → rad ≤ B*R → ∀ s ∈ Ioo a b,
      ∃ i, |dist (q i) x-rad| ≤ r ∧ s ∈ Icc (li i) (ui i))
    (hbad : ¬ ∃ i j,
      κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
      κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
      uo i+(b-a)/4 ≤ lo j) :
    ∃ S : Finset ι, R/(2*(H+3)*r) ≤ (S.card:ℝ) ∧
      (∀ i ∈ S, 1/8 ≤ t i) ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j) := by
  classical
  obtain ⟨n,bin,hnb,hbin,hsep,_⟩ := exists_radial_bins A R ((H+3)*r)
    (mul_pos (by linarith) hr) hscale
  have hchoose (z : Fin n) : ∃ i, |dist (q i) x-bin z| ≤ r ∧ 1/8 ≤ t i := by
    obtain ⟨i,hi,ht⟩ := bad_node_large_range li ui lo uo
      (fun i => |dist (q i) x-bin z| ≤ r) a b κ hab hκ hcount hinner hlo huo
      (hcover (bin z) (by nlinarith only [(hbin z).1,hR])
        (by nlinarith only [(hbin z).2,hAB,hR])) hbad
    refine ⟨i,hi,?_⟩
    rw [hlen] at ht
    nlinarith only [ht,hab]
  choose choose hnear ht using hchoose
  have hdist {z w : Fin n} (hzw : z ≠ w) : H*r < dist (q (choose z)) (q (choose w)) := by
    have hz := hnear z
    have hw := hnear w
    have hm := hsep z w hzw
    have hd := abs_dist_sub_le (q (choose z)) (q (choose w)) x
    have htri : |bin z-bin w| ≤ |bin z-dist (q (choose z)) x| +
        |dist (q (choose z)) x-dist (q (choose w)) x| +
        |dist (q (choose w)) x-bin w| := by
      simpa only [Real.dist_eq] using dist_triangle4 (bin z)
        (dist (q (choose z)) x) (dist (q (choose w)) x) (bin w)
    rw [abs_sub_comm (bin z) (dist (q (choose z)) x)] at htri
    nlinarith only [hz,hw,hm,hd,htri,hr]
  have hinj : Function.Injective choose := by
    intro z w hzw
    by_contra hn
    have hd := hdist hn
    rw [hzw,dist_self] at hd
    have hh := mul_pos hH hr
    linarith only [hd,hh]
  refine ⟨univ.image choose,?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,card_univ,Fintype.card_fin]
    convert hnb using 1 <;> first | rfl | ring
  · intro i hi
    obtain ⟨z,_,rfl⟩ := mem_image.mp hi
    exact ht z
  · intro i hi j hj hij
    obtain ⟨z,_,rfl⟩ := mem_image.mp hi
    obtain ⟨w,_,rfl⟩ := mem_image.mp hj
    exact hdist (fun hz => hij (congrArg choose hz))

end CannonCapacity

end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_PositiveCapacityTransitions
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
section
section
section
section
section
section
section
section
open Finset Filter Topology

namespace CannonFlow

theorem positive_capacity_transitions {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q) (ht : ∀ i ∈ S, 0 ≤ t i)
    (hc : 1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2)) :
    ∃ T : Finset ι, T ⊆ S ∧ (∀ i ∈ T, 0 < t i) ∧ ∃ p : T → ℝ,
      (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*t i) ∧ ∀ i, p i ≤ Q*(t i)^2 := by
  classical
  let T := S.filter (fun i => 0 < t i)
  let cap : ι → ℝ := fun i => min (L*t i) (Q*(t i)^2)
  have hsum : (∑ i : T, cap i) = ∑ i ∈ S, cap i := by
    rw [Finset.sum_coe_sort]
    change (∑ i ∈ S.filter (fun i => 0 < t i), cap i) = ∑ i ∈ S, cap i
    apply sum_subset (filter_subset _ _) (fun i hi hit => ?_)
    have hn : ¬ 0 < t i := fun hh => hit (mem_filter.mpr ⟨hi,hh⟩)
    have hz : t i=0 := le_antisymm (le_of_not_gt hn) (ht i hi)
    simp [cap,hz]
  let Z := ∑ i : T, cap i
  have hZ : 1 ≤ Z := by rw [show Z = _ from hsum]; exact hc
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  refine ⟨T,filter_subset _ _,fun i hi => (mem_filter.mp hi).2,
    fun i => cap i/Z,?_,?_,?_,?_⟩
  · intro i
    have hti := (mem_filter.mp i.property).2
    exact div_pos (lt_min (mul_pos hL hti) (mul_pos hQ (sq_pos_of_pos hti))) hZpos
  · rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  · intro i
    have hti := (mem_filter.mp i.property).2
    have hcap : 0 ≤ cap i := le_min (mul_nonneg hL.le hti.le) (mul_nonneg hQ.le (sq_nonneg _))
    have hh : cap i/Z ≤ cap i := (div_le_iff₀ hZpos).mpr (by nlinarith only [hZ,hcap])
    exact hh.trans (min_le_left _ _)
  · intro i
    have hti := (mem_filter.mp i.property).2
    have hcap : 0 ≤ cap i := le_min (mul_nonneg hL.le hti.le) (mul_nonneg hQ.le (sq_nonneg _))
    have hh : cap i/Z ≤ cap i := (div_le_iff₀ hZpos).mpr (by nlinarith only [hZ,hcap])
    exact hh.trans (min_le_right _ _)

theorem uniform_bad_transitions {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q)
    (ht : ∀ i ∈ S, (1:ℝ)/8 ≤ t i)
    (hcardL : 8 ≤ L*(S.card:ℝ)) (hcardQ : 64 ≤ Q*(S.card:ℝ)) :
    ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*t i) ∧ ∀ i, p i ≤ Q*(t i)^2 := by
  classical
  have hcard : 0 < (S.card:ℝ) := by
    have hc : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
    by_contra hn
    have hz : (S.card:ℝ)=0 := le_antisymm (le_of_not_gt hn) hc
    rw [hz,mul_zero] at hcardL
    norm_num at hcardL
  refine ⟨fun _ => 1/(S.card:ℝ),fun _ => div_pos zero_lt_one hcard,?_,?_,?_⟩
  · simp only [sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_coe]
    exact mul_div_cancel₀ 1 hcard.ne'
  · intro i
    apply (div_le_iff₀ hcard).mpr
    have hh := mul_le_mul_of_nonneg_right (ht i i.property)
      (mul_nonneg hL.le hcard.le)
    nlinarith only [hh,hcardL]
  · intro i
    apply (div_le_iff₀ hcard).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/8) (ht i i.property) 2
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hQ.le hcard.le)
    nlinarith only [hh',hcardQ]

end CannonFlow

end

end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_GoodCandidates
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
section
section
section
section
section
section
section
namespace CannonFlow

open CannonCapacity Filter Topology Finset

theorem eventually_bad_transition_thresholds (qdim : ℕ) (ell H : ℝ)
    (hell : 0 < ell) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℝ,
      Real.exp ((160*(qdim+1):ℝ)*ell*n)/(2*(H+3)) ≤ N →
      8 ≤ Real.exp (-ell*n)*N ∧
      64 ≤ Real.exp (-((80*(qdim+1):ℝ)*ell*n))*N := by
  have hq : (0:ℝ) ≤ qdim := Nat.cast_nonneg _
  have h₁ := eventually_exp_domination ell ((160*(qdim+1):ℝ)*ell) (16*(H+3))
    (by nlinarith only [hell,hq])
  have h₂ := eventually_exp_domination ((80*(qdim+1):ℝ)*ell)
    ((160*(qdim+1):ℝ)*ell) (128*(H+3)) (by nlinarith only [hell,hq])
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro N hN
  have hden : 0 < 2*(H+3) := by linarith only [hH]
  have hb := (div_le_iff₀ hden).mp hN
  have hprod (a : ℝ) : Real.exp (-(a*n))*Real.exp (a*n)=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  constructor
  · have hN' : 8*Real.exp (ell*n) ≤ N := by nlinarith only [hb,hn₁,hden]
    have hh := mul_le_mul_of_nonneg_left hN' (Real.exp_pos (-(ell*n))).le
    rw [show Real.exp (-(ell*n))*(8*Real.exp (ell*n)) =
      8*(Real.exp (-(ell*n))*Real.exp (ell*n)) by ring,hprod, mul_one] at hh
    simpa only [neg_mul] using hh
  · have hN' : 64*Real.exp ((80*(qdim+1):ℝ)*ell*n) ≤ N := by
      nlinarith only [hb,hn₂,hden]
    have hh := mul_le_mul_of_nonneg_left hN'
      (Real.exp_pos (-(((80*(qdim+1):ℝ)*ell)*n))).le
    rw [show Real.exp (-(((80*(qdim+1):ℝ)*ell)*n)) *
        (64*Real.exp (((80*(qdim+1):ℝ)*ell)*n)) =
      64*(Real.exp (-(((80*(qdim+1):ℝ)*ell)*n))*Real.exp (((80*(qdim+1):ℝ)*ell)*n)) by ring,
      hprod,mul_one] at hh
    exact hh

end CannonFlow

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

lemma fraction_clip {a b l u : ℝ} (hab : a < b) (hlu : l ≤ u) :
    clip a b u-clip a b l = (b-a)*fraction a b l u := by
  rw [clip_difference hab.le hlu]
  unfold fraction childUpper childLower
  exact (mul_div_cancel₀ _ (sub_pos.mpr hab).ne').symm

theorem candidate_subdivision {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (li ui lo uo : ι → ℝ)
    (a b κ A B R r H L Qg Qb : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι:ℝ)*κ ≤ 1/8)
    (hR : 0 < R) (hr : 0 < r) (hH : 0 < H) (hAB : A+2 ≤ B)
    (hscale : 2*((H+3)*r) ≤ R)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hcover : ∀ rad, A*R ≤ rad → rad ≤ B*R → ∀ s ∈ Ioo a b,
      ∃ i, |dist (q i) x-rad| ≤ r ∧ s ∈ Icc (li i) (ui i))
    (hL : 0 < L) (hQg : 0 < Qg) (hQb : 0 < Qb)
    (hcardL : 8 ≤ L*(R/(2*(H+3)*r)))
    (hcardQ : 64 ≤ Qb*(R/(2*(H+3)*r)))
    (hcap : ∃ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*fraction a b (lo i) (uo i))
        (Qg*(fraction a b (lo i) (uo i))^2)) :
    ∃ S : Finset ι, (∀ i ∈ S, 0 < fraction a b (lo i) (uo i)) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*fraction a b (lo i) (uo i)) ∧
      ∀ i, p i ≤ (if GoodCandidates li ui lo uo a b κ then Qg else Qb)*
        (fraction a b (lo i) (uo i))^2 := by
  classical
  let t := fun i => fraction a b (lo i) (uo i)
  by_cases hg : GoodCandidates li ui lo uo a b κ
  · obtain ⟨S,hsep,hS⟩ := hcap
    obtain ⟨T,hTS,hT,p,hp,hsum,hl,hq⟩ := positive_capacity_transitions S t hL hQg
      (fun _ _ => fraction_nonneg hab) hS
    exact ⟨T,hT,fun i hi j hj hij => hsep i (hTS hi) j (hTS hj) hij,
      p,hp,hsum,hl,fun i => by simpa only [ite_eq_left hg] using hq i⟩
  · obtain ⟨S,hcard,ht,hsep⟩ := bad_node_many_children q x li ui lo uo t a b κ A B R r H
      hab hκ hcount hR hr hH hAB hscale hinner hlo huo
      (fun i => fraction_clip hab ((hlo i).trans ((hinner i).trans (huo i)))) hcover hg
    obtain ⟨p,hp,hsum,hl,hq⟩ := uniform_bad_transitions S t hL hQb ht
      (hcardL.trans (mul_le_mul_of_nonneg_left hcard hL.le))
      (hcardQ.trans (mul_le_mul_of_nonneg_left hcard hQb.le))
    exact ⟨S,fun i hi => lt_of_lt_of_le (by norm_num) (ht i hi),hsep,
      p,hp,hsum,hl,fun i => by simpa only [ite_eq_right hg] using hq i⟩

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

theorem uniform_literal_subdivision {X : Type*} [MetricSpace X] [ProperSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B₀ H c₀ C c d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B₀) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι ζ δ : Type*} [Fintype ι] [Fintype ζ] [Fintype δ]
      (q : ι → X) (aux : ζ → X) (ξ : δ → X) (h : ζ → X ≃ₜ X)
      (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X) (a b κ R r s : ℝ),
      a < b → 0 < κ → (Fintype.card ι:ℝ)*κ ≤ 1/8 →
      0 < R → 0 < r → 0 < s → r ≤ s → s ≤ R/4 →
      c₀*r ≤ R → 2*((H+3)*r) ≤ R →
      (B₀+1)*R ≤ 1 → max H 1*r ≤ 1 → 3*s ≤ 1 →
      max (C+2) (max c 1)*(r/s) ≤ 1 →
      R/s = Real.exp (2*ell*n) → R/r = Real.exp ((160*(qdim+1):ℝ)*ell*n) →
      (∀ i, dist (q i) x ≤ (B₀+1)*R) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → s ≤ dist (aux i) (aux j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ z, dist x (aux z) ≤ (B₀+1)*R) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ i, dist (q i) v ≤ r) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ z, dist v (aux z) ≤ s) →
      (∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω) → ContinuousOn f Ω →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B₀*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      (∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
        dist (h z v) (h z v') ≤ C/s*dist v v' ∧ c/s*dist v v' ≤ dist (h z v) (h z v')) →
      ∀ ω : δ → ℝ, MacroscopicAdmissible ξ (r/s) d₀ ω →
      (∑ i, (ω i)^2) ≤ M ((160*(qdim+1)-2)*n) →
      let lo := fun i => lower f (q i) (c₀*r)
      let uo := fun i => upper f (q i) (c₀*r)
      let li := fun i => lower f (q i) (2*r)
      let ui := fun i => upper f (q i) (2*r)
      ∃ S : Finset ι, (∀ i ∈ S, 0 < fraction a b (lo i) (uo i)) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
        ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
        (∀ i, p i ≤ Real.exp (-ell*n)*fraction a b (lo i) (uo i)) ∧
        ∀ i, p i ≤ (if GoodCandidates li ui lo uo a b κ
          then Real.exp (8*(qdim+1)*ell*n) else Real.exp (-((80*(qdim+1):ℝ)*ell*n)))*
          (fraction a b (lo i) (uo i))^2 := by
  have hcap := uniform_separated_capacity qdim CP A B₀ H C c d₀ ell
    hpack hCP hA hAB hH hC hc hdc hell M hMnon hM
  have hbad := eventually_bad_transition_thresholds qdim ell H hell hH
  filter_upwards [hcap,hbad] with n hn hnb
  intro ι ζ δ _ _ _ q aux ξ h x Ω f K a b κ R r s hab hκ hcount hR hr hs hrs hsR
    hsmall hsparse hrad hdegscale hauxscale htransscale hratio hratioR
    hqloc hq haux hξ hauxloc hnet hauxnet hΩ hf hK hinner hdiam hlevel hmap ω hω hωmass
  dsimp only
  let lo := fun i => lower f (q i) (c₀*r)
  let uo := fun i => upper f (q i) (c₀*r)
  let li := fun i => lower f (q i) (2*r)
  let ui := fun i => upper f (q i) (2*r)
  let t := fun i => fraction a b (lo i) (uo i)
  have hr₂ : 0 ≤ 2*r := by positivity
  have hro : 0 ≤ c₀*r := mul_nonneg (by linarith only [hc₀]) hr.le
  have hsub (i : ι) : closedBall (q i) (2*r) ⊆ closedBall (q i) (c₀*r) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hc₀ hr.le)
  have hloc (i : ι) : closedBall (q i) (c₀*r) ⊆ Ω := by
    intro v hv
    have hvd := mem_closedBall.mp hv
    have hd := dist_triangle v (q i) x
    exact hΩ v (by nlinarith only [hd,hvd,hqloc i,hsmall])
  have hfo (i : ι) := hf.mono (hloc i)
  have hfi (i : ι) := (hfo i).mono (hsub i)
  have hlohi (i : ι) : lo i ≤ uo i := lower_le_upper hro (hfo i)
  have hliui (i : ι) : li i ≤ ui i := lower_le_upper hr₂ (hfi i)
  have hcontain (i : ι) : lo i ≤ li i ∧ ui i ≤ uo i :=
    ball_range_mono hr₂ (mul_le_mul_of_nonneg_right hc₀ hr.le) (hfo i)
  have hlen (i : ι) : clip a b (uo i)-clip a b (lo i) = (b-a)*t i :=
    fraction_clip hab (hlohi i)
  have hout (i : ι) (v : X) (_hvΩ : v ∈ Ω) (hv : dist v (q i) ≤ 2*r) :
      f v ∈ Icc (lo i) (uo i) := ball_range (hfo i) (hsub i (mem_closedBall.mpr hv))
  have hin (i : ι) (v : X) (_hvΩ : v ∈ Ω) (hv : dist v (q i) ≤ 2*r) :
      f v ∈ Icc (li i) (ui i) := ball_range (hfi i) (mem_closedBall.mpr hv)
  have hcapnode := hn q aux ξ h x Ω f K lo uo t a b R r s hab hR hr hs hrs hsR
    hrad hdegscale hauxscale htransscale hratio hq haux hξ hauxloc hnet hauxnet hΩ
    hK hinner hdiam hlevel hlohi (fun _ => fraction_nonneg hab) hlen hout hmap ω hω hωmass
  have hcover (rad : ℝ) (hl : A*R ≤ rad) (hu : rad ≤ B₀*R) :=
    node_radial_cover q x Ω f K li ui a b A B₀ R r rad hR hr.le
      (by linarith only [hA]) ⟨hl,hu⟩ hnet
      (fun v hv => hΩ v (by nlinarith only [hv,hR])) hK hinner hdiam hlevel hin
  have hb := hnb (R/(2*(H+3)*r)) (by
    rw [← hratioR]
    exact le_of_eq (by field_simp))
  exact candidate_subdivision q x li ui lo uo a b κ A B₀ R r H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n)))
    hab hκ hcount hR hr hH (by linarith only [hAB]) hsparse hliui
    (fun i => (hcontain i).1) (fun i => (hcontain i).2) hcover
    (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _) hb.1 hb.2 hcapnode

end CannonNode

end

end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_AnnularNet
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
section
section
section
section
section
section
section
open Set Metric
open scoped NNReal ENNReal

namespace CannonNode

open Set Metric

theorem annular_net {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : X) (A B R r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X,
      (∀ y ∈ T, (A-1)*R ≤ dist y x ∧ dist y x ≤ (B+1)*R) ∧
      (∀ y ∈ T, ∀ z ∈ T, y ≠ z → r ≤ dist y z) ∧
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R →
        ∃ y ∈ T, dist v y ≤ r) := by
  let W := {v : X | (A-1)*R ≤ dist v x ∧ dist v x ≤ (B+1)*R}
  obtain ⟨T,hT,hsep,hcover⟩ := CannonNet.exists_finite_separated_net W
    (isCompact_univ.totallyBounded.subset (subset_univ W)) r hr
  exact ⟨T,fun y hy => hT hy,hsep,fun v hl hu => hcover v ⟨hl,hu⟩⟩

end CannonNode

end

end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Node
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
section
section
section
section
section
section
section
namespace CannonNode

open Set Metric

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ B : ℝ} {kmin : ℕ}

namespace SourceNode

lemma length_pos (v : SourceNode f x₀ ε ell c₀ B kmin) : 0 < v.length := sub_pos.mpr v.ab

lemma child_length (v : SourceNode f x₀ ε ell c₀ B kmin) (D : ℕ) (y : X)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (hy : dist y v.center ≤ B*radius ell v.depth)
    (ht : 0 < fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
      (upper f y (c₀*radius ell (v.depth+D)))) :
    (v.child D y hB hθ hy ht).length = v.length *
      fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
        (upper f y (c₀*radius ell (v.depth+D))) := by
  exact positive_child_length v.ab ht

lemma center_mem (v : SourceNode f x₀ ε ell c₀ B kmin) (hB : 0 ≤ B) :
    v.center ∈ closedBall x₀ ε := by
  have hh : 0 ≤ 2*B*radius ell v.depth := mul_nonneg (mul_nonneg (by norm_num) hB) (radius_pos ell v.depth).le
  exact mem_closedBall.mpr (by linarith only [v.reserve,hh])

end SourceNode

end CannonNode

end

section

open Set Metric

namespace CannonMagnification

lemma expansion_ball_bounds {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x : X) (r C L B : ℝ) (hr : 0 < r) (hL : 0 < L) (hB : 1 ≤ B)
    (hexp : Expansion h x r C L) (y z : X)
    (hy : dist y x ≤ B*r) (hz : dist z x ≤ B*r) :
    dist (h y) (h z) ≤ C/r*dist y z ∧
      (1/(L*B^2))/r*dist y z ≤ dist (h y) (h z) := by
  have hE : 0 ≤ dist (h y) (h z) := dist_nonneg
  have hBr : r ≤ B*r := by nlinarith
  have hby : max r (dist x y) ≤ B*r := max_le hBr (by simpa only [dist_comm] using hy)
  have hbz : max r (dist x z) ≤ B*r := max_le hBr (by simpa only [dist_comm] using hz)
  have hmy : 0 ≤ max r (dist x y) := hr.le.trans (le_max_left _ _)
  have hmz : 0 ≤ max r (dist x z) := hr.le.trans (le_max_left _ _)
  have h₁ : dist (h y) (h z)*r*r ≤ C*r*dist y z := by
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (le_max_left _ _) hE)
      (le_max_left _ _) hr.le (mul_nonneg hE hmy)).trans (hexp y z).1
  have h₂ : r*dist y z ≤ L*dist (h y) (h z)*(B*r)*(B*r) := by
    exact (hexp y z).2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hby (mul_nonneg hL.le hE))
      hbz hmz (by positivity))
  constructor
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).mpr
    have hh : (dist (h y) (h z)*r)*r ≤ (C*dist y z)*r := by nlinarith [h₁]
    exact (mul_le_mul_iff_left₀ hr).mp hh
  · have hden : 0 < L*B^2*r := mul_pos (mul_pos hL (sq_pos_of_pos (zero_lt_one.trans_le hB))) hr
    have hraw : dist y z ≤ dist (h y) (h z)*(L*B^2*r) := by
      apply (mul_le_mul_iff_left₀ hr).mp
      nlinarith [h₂]
    have hdiv : dist y z/(L*B^2*r) ≤ dist (h y) (h z) := (div_le_iff₀ hden).mpr hraw
    convert hdiv using 1 <;> first | rfl | ring

end CannonMagnification

end

section

open Set Metric

namespace CannonNode

open Set Metric

theorem node_level_hits {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (Ω : Set X) (K : ℝ → Set X) (x : X) (R c₀ L a b : ℝ)
    (hR : 0 < R) (hc₀ : 0 < c₀) (hL : 1 ≤ L)
    (hf : ContinuousOn f Ω) (hloc : closedBall x (L*c₀*R) ⊆ Ω)
    (hnode : lower f x (c₀*R) ≤ a ∧ b ≤ upper f x (c₀*R))
    (hpaths : ∀ u v, u ∈ closedBall x (c₀*R) → v ∈ closedBall x (c₀*R) →
      JoinedIn (ball x (L*c₀*R)) u v)
    (hhit : ∀ t ∈ Ioo a b, ∀ u v, ∀ p : Path u v, Set.range p ⊆ Ω →
      f u < t → t < f v → (K t ∩ Set.range p).Nonempty) :
    ∀ t ∈ Ioo a b, ∃ y ∈ K t, dist y x ≤ L*c₀*R := by
  have hsub : closedBall x (c₀*R) ⊆ closedBall x (L*c₀*R) :=
    closedBall_subset_closedBall (by nlinarith only [hL,mul_pos hc₀ hR])
  obtain ⟨⟨u,hu,huv⟩,⟨v,hv,hvv⟩⟩ := ball_extrema (mul_pos hc₀ hR).le (hf.mono (hsub.trans hloc))
  obtain ⟨p,hp⟩ := hpaths u v hu hv
  have hpΩ : range p ⊆ Ω := by
    rintro _ ⟨t,rfl⟩
    exact hloc (ball_subset_closedBall (hp t))
  intro t ht
  have hu' : f u < t := by rw [huv]; exact hnode.1.trans_lt ht.1
  have hv' : t < f v := by rw [hvv]; exact ht.2.trans_le hnode.2
  obtain ⟨z,hz,⟨s,rfl⟩⟩ := hhit t ht u v p hpΩ hu' hv'
  exact ⟨p s,hz,(mem_ball.mp (hp s)).le⟩

lemma exists_node_interval {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (x : X) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall x r))
    (hunit : ∀ y ∈ closedBall x r, f y ∈ Icc (0:ℝ) 1)
    (hvar : ∃ y ∈ closedBall x r, ∃ z ∈ closedBall x r, f y ≠ f z) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ lower f x r < a ∧ b < upper f x r := by
  obtain ⟨⟨v,hv,hvv⟩,⟨w,hw,hww⟩⟩ := ball_extrema hr hf
  have hlu : lower f x r < upper f x r := by
    obtain ⟨y,hy,z,hz,hneq⟩ := hvar
    have hylu := ball_range hf hy
    have hzlu := ball_range hf hz
    by_contra hn
    have hh := le_of_not_gt hn
    have hyz : f y=f z := by linarith only [hylu.1,hylu.2,hzlu.1,hzlu.2,hh]
    exact hneq hyz
  have hl : 0 ≤ lower f x r := by rw [← hvv]; exact (hunit v hv).1
  have hu : upper f x r ≤ 1 := by rw [← hww]; exact (hunit w hw).2
  refine ⟨(2*lower f x r+upper f x r)/3,(lower f x r+2*upper f x r)/3,?_,?_,?_,?_,?_⟩ <;>
    linarith only [hlu,hl,hu]

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

lemma candidate_slack {X : Type*} [MetricSpace X] (Q : ℕ) (CP B ell : ℝ)
    (hCP : 0 ≤ CP) (hB : 0 ≤ B) (D : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Y : Finset X) (R r : ℝ), 0 < r →
      (Y.card:ℝ) ≤ CP*((B+1)*R/r)^Q → R/r=Real.exp (ell*D) →
      (Y.card:ℝ)*κ ≤ 1/8 := by
  let C := CP*(B+1)^Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let E := Real.exp (ell*D)^Q
  have hE : 0 < E := pow_pos (Real.exp_pos _) _
  let κ := 1/(8*max C 1*E)
  have hmax : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hden : 0 < 8*max C 1*E := by positivity
  refine ⟨κ,one_div_pos.mpr hden,?_⟩
  intro Y R r _hr hcard hratio
  have hcard' : (Y.card:ℝ) ≤ C*E := by
    convert hcard using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_div_assoc, hratio,mul_pow]
    dsimp [C,E]
    ring
  have hh : (Y.card:ℝ) ≤ max C 1*E := hcard'.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le)
  change (Y.card:ℝ)*(1/(8*max C 1*E)) ≤ 1/8
  rw [mul_one_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hh]

theorem eventually_scaled_subdivision {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B H c₀ C LE d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hLE : 0 < LE) (hdc : d₀ ≤ 1/(9*LE)) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) C LE) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ (x : X) (k : ℕ) (Y : Finset X)
        (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X) (a b : ℝ),
      let R := radius ell k
      let r := radius ell (k+160*(qdim+1)*n)
      a < b → (B+1)*R ≤ 1 → max H 1*R ≤ 1 → 3*R ≤ 1 →
      (∀ y ∈ Y, (A-1)*R ≤ dist y x ∧ dist y x ≤ (B+1)*R) →
      (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → r ≤ dist y z) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R → ∃ y ∈ Y, dist v y ≤ r) →
      (∀ v, dist v x ≤ (B+2)*R → v ∈ Ω) → ContinuousOn f Ω →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      LiteralTransitions f Y c₀ r a b κ H (Real.exp (-ell*n))
        (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n))) := by
  have hB : 0 ≤ B := by linarith only [hA,hAB]
  have hc : 0 < 1/(9*LE) := by positivity
  have hs := uniform_literal_subdivision qdim CP A B H c₀ C (1/(9*LE)) d₀ ell
    hpack hCP hA hAB hH hc₀ hC hc hdc hell M hMnon hM
  have hsc := eventually_flow_scales qdim ell c₀ H (max (C+2) (max (1/(9*LE)) 1)) hell
  filter_upwards [hs,hsc] with n hn hscale
  obtain ⟨κ,hκ,hκcount⟩ := candidate_slack (X:=X) qdim CP B ell hCP hB (160*(qdim+1)*n)
  refine ⟨hscale.1,hscale.2.1,κ,hκ,?_⟩
  intro x k Y Ω f K a b
  dsimp only
  let R := radius ell k
  let r := radius ell (k+160*(qdim+1)*n)
  let s := radius ell (k+2*n)
  have hR : 0 < R := radius_pos _ _
  have hr : 0 < r := radius_pos _ _
  have hsp : 0 < s := radius_pos _ _
  intro hab hRone hCone hthree hY hYsep hYnet hΩ hf hK hinner hdiam hlevel
  have hd : 2 ≤ 160*(qdim+1) := by omega
  have hdr : 2*n ≤ 160*(qdim+1)*n := Nat.mul_le_mul_right n hd
  have hrs : r ≤ s := radius_antitone hell.le (Nat.add_le_add_left hdr k)
  have hsR : s ≤ R := radius_antitone hell.le (Nat.le_add_right k (2*n))
  have hrR : r ≤ R := hrs.trans hsR
  have hSR : s ≤ R/4 := by
    dsimp [s,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.2.2.1 hR.le]
  have hcR : c₀*r ≤ R := by
    dsimp [r,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.1 hR.le]
  have hHR : 2*((H+3)*r) ≤ R := by
    dsimp [r,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.2.1 hR.le]
  have hratioS : R/s=Real.exp (2*ell*n) := by
    dsimp [R,s]
    rw [radius_ratio]
    congr 1
    push_cast
    ring
  have hratioR : R/r=Real.exp ((160*(qdim+1):ℝ)*ell*n) := by
    dsimp [R,r]
    rw [radius_ratio]
    congr 1
    push_cast
    ring
  have hrr : r/s=radius ell ((160*(qdim+1)-2)*n) := by
    dsimp [r,s]
    rw [radius_sub_ratio ell k _ _ hdr, Nat.sub_mul]
  have hκY : (Fintype.card Y:ℝ)*κ ≤ 1/8 := by
    rw [Fintype.card_coe]
    apply hκcount Y R r hr
    · exact hpack x ((B+1)*R) r hr (hrR.trans (by nlinarith only [hB,hR])) hRone Y
        (fun y hy => by simpa only [dist_comm] using (hY y hy).2) hYsep
    · dsimp [R,r]
      exact radius_ratio _ _ _
  obtain ⟨T,hT,hTsep,hTnet⟩ := annular_net x A B R s hsp
  have htrans : max (C+2) (max (1/(9*LE)) 1)*(r/s) ≤ 1 := by
    rw [hrr]
    exact hscale.2.2.2.2.2
  have hmap (z : T) (v v' : X) (hv : dist v (z:X) ≤ 3*s) (hv' : dist v' (z:X) ≤ 3*s) :
      dist (h z (k+2*n) v) (h z (k+2*n) v') ≤ C/s*dist v v' ∧
      (1/(9*LE))/s*dist v v' ≤ dist (h z (k+2*n) v) (h z (k+2*n) v') := by
    have hh := expansion_ball_bounds (h z (k+2*n)) z s C LE 3 hsp hLE (by norm_num)
      (hexp z (k+2*n)) v v' hv hv'
    simpa only [show (3 : ℝ)^2 = 9 by norm_num, mul_comm LE 9] using hh
  have htarget : ∀ i j, i ≠ j → r/s ≤ dist (ξ ((160*(qdim+1)-2)*n) i) (ξ ((160*(qdim+1)-2)*n) j) := by
    rw [hrr]
    exact hξ _
  have hweight : MacroscopicAdmissible (ξ ((160*(qdim+1)-2)*n)) (r/s) d₀
      (ω ((160*(qdim+1)-2)*n)) := by rw [hrr]; exact hω _
  exact hn (fun y : Y => (y:X)) (fun z : T => (z:X)) (ξ ((160*(qdim+1)-2)*n))
    (fun z : T => h z (k+2*n)) x Ω f K a b κ R r s hab hκ hκY hR hr hsp hrs hSR hcR hHR
    hRone ((mul_le_mul_of_nonneg_left hrR (le_max_right H 1 |>.trans' zero_le_one)).trans hCone)
    ((mul_le_mul_of_nonneg_left hsR (by norm_num : (0:ℝ) ≤ 3)).trans hthree) htrans hratioS hratioR
    (fun y => (hY y y.property).2)
    (fun y z hyz => hYsep y y.property z z.property (fun he => hyz (Subtype.ext he)))
    (fun y z hyz => hTsep y y.property z z.property (fun he => hyz (Subtype.ext he)))
    htarget (fun z => by simpa only [dist_comm] using (hT z z.property).2)
    (fun v hl hu => by obtain ⟨y,hy,hd⟩ := hYnet v hl hu; exact ⟨⟨y,hy⟩,by simpa only [dist_comm] using hd⟩)
    (fun v hl hu => by obtain ⟨z,hz,hd⟩ := hTnet v hl hu; exact ⟨⟨z,hz⟩,hd⟩)
    hΩ hf hK hinner hdiam hlevel hmap (ω ((160*(qdim+1)-2)*n)) hweight (hωmass _)

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

lemma conserve_expectation (n : ℕ) (f : Fin (T.size n) → ℝ) :
    ∑ v, T.weight n v * f v = ∑ w, T.weight (n+1) w * f (T.parent n w) := by
  classical
  simp_rw [T.conserves n, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro w hw
  simp only [ite_mul, zero_mul]
  simp

lemma total_mass (n : ℕ) : ∑ v, T.weight n v = 1 := by
  induction n with
  | zero => exact T.root_mass
  | succ n ih =>
    have h := T.conserve_expectation n (fun _ => 1)
    simpa only [mul_one] using h.symm.trans (by simpa only [mul_one] using ih)

lemma badMass_nonneg (n : ℕ) : 0 ≤ T.badMass n := by
  classical
  apply sum_nonneg
  intro v hv
  exact mul_nonneg (T.nonneg n v) (by split_ifs <;> norm_num)

lemma good_add_bad (n : ℕ) : T.goodMass n + T.badMass n = 1 := by
  classical
  unfold goodMass badMass
  rw [← sum_add_distrib]
  convert T.total_mass n using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro v hv
  split_ifs <;> ring

lemma expectedBad_succ (n : ℕ) : T.expectedBad (n+1) = T.expectedBad n + T.badMass n := by
  classical
  unfold expectedBad badMass
  simp only [badCount, Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, mul_add, sum_add_distrib]
  exact congrArg₂ (· + ·)
    (T.conserve_expectation n (fun v => (T.badCount n v : ℝ))).symm
    (T.conserve_expectation n (fun v => if T.good n v then 0 else 1)).symm

lemma expectedBad_eq_sum (n : ℕ) : T.expectedBad n = ∑ k ∈ range n, T.badMass k := by
  induction n with
  | zero => simp [expectedBad, badCount]
  | succ n ih => rw [T.expectedBad_succ, ih, sum_range_succ]

lemma expectedBad_bound {c E : ℝ} (_hc : 0 < c)
    (henergy : ∀ n, ∑ v, T.weight n v *
      Real.exp (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n)) ≤ E)
    (n : ℕ) : c * ((11 / 20 : ℝ) * T.expectedBad n - (1 / 20 : ℝ) * n) + 1 ≤ E := by
  have htan : ∑ v, T.weight n v *
      (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n) + 1) ≤ E := by
    apply le_trans _ (henergy n)
    apply sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (T.nonneg n v)
  have heq : (∑ v, T.weight n v *
      (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n) + 1)) =
      c * ((11 / 20 : ℝ) * T.expectedBad n - (1 / 20 : ℝ) * n) + 1 := by
    calc
      _ = ∑ v, ((c * (11 / 20 : ℝ)) * (T.weight n v * T.badCount n v) +
            (1 - c * (1 / 20 : ℝ) * n) * T.weight n v) := by
        apply sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, T.total_mass]; unfold expectedBad; ring
  rwa [heq] at htan

theorem arbitrarily_late_good_levels {c E : ℝ} (hc : 0 < c)
    (henergy : ∀ n, ∑ v, T.weight n v *
      Real.exp (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n)) ≤ E) :
    ∀ N : ℕ, ∃ n ≥ N, (1 / 2 : ℝ) ≤ T.goodMass n := by
  classical
  intro N
  by_contra hn
  have hbad : ∀ n, N ≤ n → (1 / 2 : ℝ) ≤ T.badMass n := by
    intro n hnN
    have hg : T.goodMass n < 1 / 2 := lt_of_not_ge (fun h => hn ⟨n,hnN,h⟩)
    linarith [T.good_add_bad n]
  have hlarge : ∃ n : ℕ, N ≤ n ∧ E + c * (11 / 40 : ℝ) * N < c * (9 / 40 : ℝ) * n + 1 := by
    obtain ⟨m,hm⟩ := exists_nat_gt ((E + c * (11 / 40 : ℝ) * N) / (c * (9 / 40 : ℝ)))
    refine ⟨max m N,le_max_right _ _,?_⟩
    have hd : 0 < c * (9 / 40 : ℝ) := by positivity
    have hh : E + c * (11 / 40 : ℝ) * N < c * (9 / 40 : ℝ) * m := by simpa [mul_comm] using (div_lt_iff₀ hd).mp hm
    have hmn : (m : ℝ) ≤ max m N := by exact_mod_cast le_max_left m N
    nlinarith
  obtain ⟨n,hnN,hnE⟩ := hlarge
  have hsum : ((n - N : ℕ) : ℝ) * (1 / 2 : ℝ) ≤ T.expectedBad n := by
    rw [T.expectedBad_eq_sum]
    have he := sum_le_sum (s := Ico N n) (fun k hk => hbad k (mem_Ico.mp hk).1)
    have hs : ∑ k ∈ Ico N n, T.badMass k ≤ ∑ k ∈ range n, T.badMass k :=
      sum_le_sum_of_subset_of_nonneg (by intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2)
        (fun k _ _ => T.badMass_nonneg k)
    simpa using he.trans hs
  rw [Nat.cast_sub hnN] at hsum
  have hb := T.expectedBad_bound hc henergy n
  nlinarith

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

lemma weight_le_one (n : ℕ) (v : Fin (T.size n)) : T.weight n v ≤ 1 := by
  rw [← T.total_mass n]
  exact Finset.single_le_sum (fun w _ => T.nonneg n w) (Finset.mem_univ v)

lemma badCount_exp_succ (c : ℝ) (n : ℕ) (v : Fin (T.size (n+1))) :
    Real.exp (c * ((11/20:ℝ) * T.badCount (n+1) v - (1/20:ℝ) * (n+1))) =
      Real.exp (c * ((11/20:ℝ) * T.badCount n (T.parent n v) - (1/20:ℝ)*n)) *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) := by
  rw [← Real.exp_add]
  congr 1
  simp only [badCount, Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  split_ifs <;> ring

lemma quadratic_transition_product
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ c : ℝ}
    (hroot : ∀ v, Δ 0 v = Δ₀) (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hq : ∀ n v, p n v *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) *
      (Δ n (T.parent n v))^2 ≤ (Δ (n+1) v)^2) :
    ∀ n v, Δ₀^2 * T.weight n v *
      Real.exp (c * ((11/20:ℝ) * T.badCount n v - (1/20:ℝ) * n)) ≤ (Δ n v)^2 := by
  intro n
  induction n with
  | zero =>
    intro v
    simpa [badCount,hroot] using
      mul_le_mul_of_nonneg_left (T.weight_le_one 0 v) (sq_nonneg Δ₀)
  | succ n ih =>
    intro v
    rw [hstep, Nat.cast_add, Nat.cast_one, T.badCount_exp_succ]
    calc
      _ = (p n v * Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2))) *
        (Δ₀^2 * T.weight n (T.parent n v) *
          Real.exp (c * ((11/20:ℝ) * T.badCount n (T.parent n v) - (1/20:ℝ) * n))) := by ring
      _ ≤ (p n v * Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2))) *
          (Δ n (T.parent n v))^2 :=
        mul_le_mul_of_nonneg_left (ih _) (mul_nonneg (hp n v) (Real.exp_pos _).le)
      _ ≤ _ := hq n v

theorem good_levels_of_transitions
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ c E : ℝ}
    (hΔ₀ : 0 < Δ₀) (hc : 0 < c)
    (hroot : ∀ v, Δ 0 v = Δ₀) (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hq : ∀ n v, p n v *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) *
      (Δ n (T.parent n v))^2 ≤ (Δ (n+1) v)^2)
    (henergy : ∀ n, ∑ v, (Δ n v)^2 ≤ E) :
    ∀ N : ℕ, ∃ n ≥ N, (1/2:ℝ) ≤ T.goodMass n := by
  apply T.arbitrarily_late_good_levels hc (E := E / Δ₀^2)
  intro n
  apply (le_div_iff₀ (sq_pos_of_pos hΔ₀)).mpr
  have h := (Finset.sum_le_sum fun v _ =>
    T.quadratic_transition_product p Δ hroot hp hstep hq n v).trans (henergy n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end FiniteFlow

end CannonFlow

end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryBasedRay
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
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open Set Metric

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

attribute [local instance] OAI.CannonRelease.boundaryBasedRaySetoid
omit [TopologicalSpace G] [DiscreteTopology G] in
lemma boundaryBasedRay_rep (x : Boundary D) : Quotient.mk' (boundaryBasedRay D x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

lemma boundaryExpansion_formula (x : Boundary D) (k : ℕ) :
    let _ := visualMetricSpace D hδ
    Expansion (boundaryExpansion D hδ x k) x ((Real.exp (2*visualExponent δ)^k)⁻¹)
      (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
      (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  have hscale : (Real.exp (2*visualExponent δ)^k)⁻¹ = visualScale δ k := by
    rw [visualScale_eq_pow,Real.exp_neg,inv_pow]
  rw [hscale]
  intro y z
  have hh := visual_expansion_ray D hδ (boundaryBasedRay D x) k y z
  rw [boundaryBasedRay_rep D x] at hh
  have heq (z : Boundary D) : (boundaryExpansion D hδ x k) z =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D x).val k)⁻¹ z := rfl
  rw [heq y,heq z]
  exact ⟨hh.1,by simpa only [mul_assoc] using hh.2⟩

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Weights
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
open scoped InnerProductSpace
open Set

namespace CannonDuality

variable {ι : Type*} [Fintype ι]

lemma inner_bound_convexHull {V : Set (Weights ι)} {w : Weights ι} {c : ℝ}
    (h : ∀ v ∈ V, c ≤ ⟪w, v⟫_ℝ) :
    ∀ v ∈ convexHull ℝ V, c ≤ ⟪w, v⟫_ℝ := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab
  change c ≤ ⟪w, a • x + b • y⟫_ℝ
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  change c ≤ ⟪w, x⟫_ℝ at hx
  change c ≤ ⟪w, y⟫_ℝ at hy
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * ⟪w, x⟫_ℝ + b * ⟪w, y⟫_ℝ :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma nonnegative_convexHull {V : Set (Weights ι)}
    (h : ∀ v ∈ V, Nonnegative v) :
    ∀ v ∈ convexHull ℝ V, Nonnegative v := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab i
  change 0 ≤ a * x i + b * y i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem exists_dual_minimizer (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧ ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ := by
  have hK : (convexHull ℝ (V : Set (Weights ι))).Nonempty :=
    hne.to_set.mono (subset_convexHull ℝ _)
  obtain ⟨P, hP, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hK
    ((V.finite_toSet.isCompact_convexHull ℝ).isComplete)
    (convex_convexHull ℝ _) (0 : Weights ι)
  refine ⟨P, hP, nonnegative_convexHull hnonneg P hP, ?_, ?_⟩
  · let one : Weights ι := (WithLp.toLp 2 fun _ => (1 : ℝ))
    have hsum : ∀ v ∈ (V : Set (Weights ι)), 1 ≤ ⟪one, v⟫_ℝ := by
      intro v hv
      simpa [one, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using hpositive v hv
    have hb := inner_bound_convexHull hsum P hP
    intro hz
    norm_num [hz] at hb
  · have hproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _)
      hP).mp hmin
    intro v hv
    have hi := hproj v (subset_convexHull ℝ _ hv)
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    linarith

lemma normalized_admissible {V : Set (Weights ι)} {P : Weights ι}
    (hP : Nonnegative P) (hPne : P ≠ 0)
    (hdual : ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ) :
    Admissible V ((‖P‖ ^ 2)⁻¹ • P) := by
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  constructor
  · intro i
    change 0 ≤ (‖P‖ ^ 2)⁻¹ * P i
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hP i)
  · intro v hv
    rw [real_inner_smul_left]
    calc
      1 = (‖P‖ ^ 2)⁻¹ * ‖P‖ ^ 2 := (inv_mul_cancel₀ hp.ne').symm
      _ ≤ (‖P‖ ^ 2)⁻¹ * ⟪P, v⟫_ℝ :=
        mul_le_mul_of_nonneg_left (hdual v hv) (inv_nonneg.mpr hp.le)

lemma normalized_energy {P : Weights ι} (hPne : P ≠ 0) :
    ‖(‖P‖ ^ 2)⁻¹ • P‖ ^ 2 = (‖P‖ ^ 2)⁻¹ := by
  have hp : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hPne
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

lemma admissible_energy_lower {V : Set (Weights ι)} {P : Weights ι}
    (hP : P ∈ convexHull ℝ V) (hPne : P ≠ 0)
    {w : Weights ι} (hw : Admissible V w) :
    (‖P‖ ^ 2)⁻¹ ≤ ‖w‖ ^ 2 := by
  have hpair : 1 ≤ ⟪w, P⟫_ℝ := inner_bound_convexHull hw.2 P hP
  have hcs := real_inner_mul_inner_self_le w P
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hprod : 1 ≤ ‖w‖ ^ 2 * ‖P‖ ^ 2 := by nlinarith
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  simpa only [one_div] using (div_le_iff₀ hp).mpr hprod

theorem modulus_eq_inverse_dual_energy (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧
      Modulus (V : Set (Weights ι)) = (‖P‖ ^ 2)⁻¹ ∧
      Admissible (V : Set (Weights ι)) ((‖P‖ ^ 2)⁻¹ • P) := by
  obtain ⟨P, hP, hnon, hneP, hdual⟩ := exists_dual_minimizer V hne hnonneg hpositive
  have hadm := normalized_admissible hnon hneP hdual
  have henergy := normalized_energy hneP
  refine ⟨P, hP, hnon, hneP, ?_, hadm⟩
  apply le_antisymm
  · apply csInf_le
    · use 0
      rintro _ ⟨w, _, rfl⟩
      exact sq_nonneg ‖w‖
    · exact ⟨_, hadm, henergy.symm⟩
  · apply le_csInf
    · exact ⟨_, _, hadm, rfl⟩
    · rintro e ⟨w, hw, rfl⟩
      exact admissible_energy_lower hP hneP hw

end CannonDuality

namespace CannonCells
open Set CannonDuality
open scoped InnerProductSpace

variable {X ι : Type*} [Fintype ι]

lemma mem_familyVectors (C : ι → Set X) (F : Set (Set X)) (v : Weights ι) :
    v ∈ familyVectors C F ↔ ∃ A ∈ F, incidence C A = v := by
  classical
  simp only [familyVectors,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_image,incidence]
  constructor
  · rintro ⟨s,⟨A,hA,rfl⟩,hv⟩
    exact ⟨A,hA,hv⟩
  · rintro ⟨A,hA,hv⟩
    exact ⟨indices C A,⟨A,hA,rfl⟩,hv⟩

lemma incidence_nonnegative (C : ι → Set X) (A : Set X) : Nonnegative (incidence C A) := by
  classical
  intro i
  change 0 ≤ if i ∈ indices C A then (1:ℝ) else 0
  split <;> norm_num

lemma incidence_at (C : ι → Set X) (A : Set X) {i : ι} (hi : (A ∩ C i).Nonempty) :
    incidence C A i = 1 := by
  classical
  change (if i ∈ indices C A then (1:ℝ) else 0) = 1
  rw [ite_eq_left ((mem_indices C A i).mpr hi)]

lemma incidence_positive (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {A : Set X} (hA : A.Nonempty) : 1 ≤ ∑ i, incidence C A i := by
  classical
  obtain ⟨x,hx⟩ := hA
  obtain ⟨i,hi⟩ := hC x
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => incidence_nonnegative C A j)
    (Finset.mem_univ i)
  rwa [incidence_at C A ⟨x,hx,hi⟩] at h

lemma admissible_iff (C : ι → Set X) (F : Set (Set X)) (w : Weights ι) :
    Admissible (familyVectors C F : Set (Weights ι)) w ↔
      Nonnegative w ∧ ∀ A ∈ F, 1 ≤ ∑ i ∈ indices C A, w i := by
  classical
  have hinner (A : Set X) : ⟪w,incidence C A⟫_ℝ = ∑ i ∈ indices C A, w i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [incidence,weight,dotProduct]
  constructor
  · rintro ⟨hn,hw⟩
    refine ⟨hn,fun A hA => ?_⟩
    rw [← hinner]
    exact hw _ ((mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩)
  · rintro ⟨hn,hw⟩
    refine ⟨hn,?_⟩
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    rw [hinner]
    exact hw A hA

lemma familyVectors_nonempty (C : ι → Set X) {F : Set (Set X)} (hF : F.Nonempty) :
    (familyVectors C F).Nonempty := by
  obtain ⟨A,hA⟩ := hF
  exact ⟨incidence C A,(mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩⟩

theorem modulus_minimum (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F : Set (Set X)} (hF : F.Nonempty) (hFn : ∀ A ∈ F, A.Nonempty) :
    0 < modulus C F ∧ ∃ w : Weights ι,
      Admissible (familyVectors C F : Set (Weights ι)) w ∧ ‖w‖^2 = modulus C F := by
  have hn : ∀ v ∈ familyVectors C F, Nonnegative v := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_nonnegative C A
  have hp : ∀ v ∈ familyVectors C F, 1 ≤ ∑ i, v i := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_positive C hC (hFn A hA)
  obtain ⟨P,_,_,hP,hmod,hadm⟩ := modulus_eq_inverse_dual_energy
    (familyVectors C F) (familyVectors_nonempty C hF) hn hp
  have hpositive : 0 < ‖P‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hP)
  refine ⟨?_,(‖P‖^2)⁻¹ • P,hadm,?_⟩
  · change 0 < Modulus _
    rw [hmod]
    exact inv_pos.mpr hpositive
  · exact (normalized_energy hP).trans hmod.symm

end CannonCells
end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ModulusEnergy
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
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCells

open CannonDuality Set Filter

variable {X ι J : Type*} [Fintype ι] [Fintype J]

lemma modulus_le_energy (C : ι → Set X) (F : Set (Set X)) (w : Weights ι)
    (hw : Admissible (familyVectors C F : Set (Weights ι)) w) :
    modulus C F ≤ ‖w‖^2 := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro a ⟨v,_,rfl⟩
    exact sq_nonneg _
  · exact ⟨w,hw,rfl⟩

end CannonCells

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SpherePathConnected
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
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonCharts

open CannonCells CannonDuality CannonAnnular

lemma sphere_pathConnected : PathConnectedSpace SphereTwo := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  simp

lemma macroFamily_nonempty {X : Type*} [MetricSpace X] [PathConnectedSpace X]
    {d : ℝ} (hd : 0 < d) (hdia : d < diam (univ : Set X)) :
    (macroFamily (X := X) d).Nonempty := by
  have hp : ∃ x y : X, d < dist x y := by
    by_contra hn
    push Not at hn
    exact not_le_of_gt hdia (diam_le_of_forall_dist_le hd.le (fun x _ y _ => hn x y))
  obtain ⟨x,y,hxy⟩ := hp
  let p := PathConnectedSpace.somePath x y
  refine ⟨range p,p,p.continuous,rfl,?_⟩
  exact hxy.le.trans (dist_le_diam_of_mem (isCompact_range p.continuous).isBounded
    ⟨0,p.source⟩ ⟨1,p.target⟩)

theorem sphere_macro_modulus_minimum {X ι : Type*} [MetricSpace X] [Fintype ι]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (p : ι → X) (r : ℝ) (hcover : ∀ x, ∃ i, x ∈ ball (p i) (2*r)) :
    0 < modulus (fun i => ball (p i) (2*r)) (macroFamily d) ∧
      ∃ ω : ι → ℝ, MacroscopicAdmissible p r d ω ∧
        (∑ i, (ω i)^2) = modulus (fun i => ball (p i) (2*r)) (macroFamily d) := by
  let : PathConnectedSpace SphereTwo := sphere_pathConnected
  let : PathConnectedSpace X := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let C := fun i => ball (p i) (2*r)
  obtain ⟨hpos,w,hw,he⟩ := modulus_minimum C hcover (macroFamily_nonempty hd hdia)
    (fun A hA => by obtain ⟨p,_,rfl,_⟩ := hA; exact ⟨p 0,⟨0,rfl⟩⟩)
  refine ⟨hpos,(fun i => w i),?_,?_⟩
  · have ha := (admissible_iff C (macroFamily d) w).mp hw
    refine ⟨ha.1,fun u v q hq => ?_⟩
    have hh := ha.2 (range q) ⟨q,q.continuous,rfl,hq⟩
    have hi : indices C (range q) = pathCellIndices p r q := by
      ext i
      simp only [mem_indices,pathCellIndices,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨x,⟨t,rfl⟩,ht⟩
        exact ⟨t,ht⟩
      · rintro ⟨t,ht⟩
        exact ⟨q t,⟨t,rfl⟩,ht⟩
    rw [hi] at hh
    exact hh
  · rw [← he,EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]

end CannonCharts

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Subdivision
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
section
section
section
section
section
section
section
open Set Filter Finset

namespace CannonFlow.FiniteFlow

open Finset

variable (T : CannonFlow.FiniteFlow)

theorem centers_separated {X : Type*} [MetricSpace X]
    (center : (n : ℕ) → Fin (T.size n) → X) (r : ℕ → ℝ)
    (B H θ : ℝ) (hr : ∀ n, 0 ≤ r n)
    (hscale : ∀ n, r (n+1) = θ*r n) (hbudget : H*θ ≤ H-2*B)
    (hroot : ∀ i j, i ≠ j → H*r 0 ≤ dist (center 0 i) (center 0 j))
    (hstep : ∀ n v, dist (center (n+1) v) (center n (T.parent n v)) ≤ B*r n)
    (hsibling : ∀ n i j, T.parent n i = T.parent n j → i ≠ j →
      H*r (n+1) ≤ dist (center (n+1) i) (center (n+1) j)) :
    ∀ n i j, i ≠ j → H*r n ≤ dist (center n i) (center n j) := by
  intro n
  induction n with
  | zero => exact hroot
  | succ n ih =>
    intro i j hij
    by_cases hp : T.parent n i = T.parent n j
    · exact hsibling n i j hp hij
    · have hpar := ih _ _ hp
      have hii := hstep n i
      have hjj := hstep n j
      have ht₁ := dist_triangle (center n (T.parent n i)) (center (n+1) i)
        (center n (T.parent n j))
      have ht₂ := dist_triangle (center (n+1) i) (center (n+1) j)
        (center n (T.parent n j))
      rw [dist_comm (center n (T.parent n i)) (center (n+1) i)] at ht₁
      have hb := mul_le_mul_of_nonneg_right hbudget (hr n)
      rw [hscale]
      nlinarith only [hpar,hii,hjj,ht₁,ht₂,hb]

end CannonFlow.FiniteFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

theorem source_rule_of_subdivisions {X : Type*} [MetricSpace X]
    (f : X → ℝ) (x₀ : X) (ε ell c₀ B H L Qg Qb : ℝ) (kmin D : ℕ)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (Y : SourceNode f x₀ ε ell c₀ B kmin → Finset X)
    (good : SourceNode f x₀ ε ell c₀ B kmin → Prop)
    (hY : ∀ v, ∀ y ∈ Y v, dist y v.center ≤ B*radius ell v.depth)
    (htrans : ∀ v,
      ∃ S : Finset (Y v),
        (∀ y ∈ S, 0 < fraction v.a v.b
          (lower f y (c₀*radius ell (v.depth+D))) (upper f y (c₀*radius ell (v.depth+D)))) ∧
        (∀ y ∈ S, ∀ z ∈ S, y ≠ z →
          H*radius ell (v.depth+D) < dist (y:X) z) ∧
        ∃ p : S → ℝ, (∀ y, 0 < p y) ∧ (∑ y, p y = 1) ∧
        (∀ y, p y ≤ L*fraction v.a v.b
          (lower f (y.val:X) (c₀*radius ell (v.depth+D)))
          (upper f (y.val:X) (c₀*radius ell (v.depth+D)))) ∧
        ∀ y, p y ≤ (if good v then Qg else Qb)*
          (fraction v.a v.b (lower f (y.val:X) (c₀*radius ell (v.depth+D)))
            (upper f (y.val:X) (c₀*radius ell (v.depth+D))))^2) :
    ∃ R : Subdivision (SourceNode f x₀ ε ell c₀ B kmin),
      (∀ v i, (R.child v i).depth=v.depth+D) ∧
      (∀ v i, dist (R.child v i).center v.center ≤ B*radius ell v.depth) ∧
      (∀ v i j, i ≠ j → H*radius ell (v.depth+D) <
        dist (R.child v i).center (R.child v j).center) ∧
      (∀ v i, R.prob v i*v.length ≤ L*(R.child v i).length) ∧
      (∀ v i, R.prob v i*v.length^2 ≤
        (if good v then Qg else Qb)*(R.child v i).length^2) ∧
      ∀ v i, (R.child v i).length ≤ v.length := by
  classical
  choose S hpos hsep p hp hsum hl hq using htrans
  let e := fun v => (Fintype.equivFin (S v)).symm
  let child := fun (v : SourceNode f x₀ ε ell c₀ B kmin) (i : Fin (Fintype.card (S v))) => v.child D ((e v i).val:X) hB hθ
    (hY v (e v i).val (e v i).val.property) (hpos v (e v i).val (e v i).property)
  let R : Subdivision (SourceNode f x₀ ε ell c₀ B kmin) := {
    degree := fun v => Fintype.card (S v)
    child := child
    prob := fun v i => p v (e v i)
    prob_pos := fun v i => hp v (e v i)
    prob_sum := fun v => by
      exact (Fintype.sum_equiv (e v) (fun i => p v (e v i)) (p v) (fun _ => rfl)).trans (hsum v) }
  have hlength (v) (i : Fin (R.degree v)) :
      (R.child v i).length = v.length * fraction v.a v.b
        (lower f ((e v i).val:X) (c₀*radius ell (v.depth+D)))
        (upper f ((e v i).val:X) (c₀*radius ell (v.depth+D))) := by
    exact SourceNode.child_length v D ((e v i).val:X) hB hθ
      (hY v (e v i).val (e v i).val.property) (hpos v (e v i).val (e v i).property)
  refine ⟨R,fun _ _ => rfl,fun v i => hY v (e v i).val (e v i).val.property,?_,?_,?_,?_⟩
  · intro v i j hij
    apply hsep v (e v i).val (e v i).property (e v j).val (e v j).property
    intro he
    exact hij ((e v).injective (Subtype.ext he))
  · intro v i
    change p v (e v i)*v.length ≤ L*(R.child v i).length
    have hh := mul_le_mul_of_nonneg_right (hl v (e v i)) v.length_pos.le
    calc
      _ ≤ _ := hh
      _ = _ := by rw [hlength]; ring
  · intro v i
    change p v (e v i)*v.length^2 ≤ (if good v then Qg else Qb)*(R.child v i).length^2
    have hh := mul_le_mul_of_nonneg_right (hq v (e v i)) (sq_nonneg v.length)
    calc
      _ ≤ _ := hh
      _ = _ := by rw [hlength]; ring
  · intro v i
    change min v.b _ - max v.a _ ≤ v.b-v.a
    exact sub_le_sub (min_le_left _ _) (le_max_left _ _)

end CannonNode

end

section

open Set Metric

namespace CannonNode

open Set Metric Filter Topology

theorem root_at_scale {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (x : X) (Ω : Set X) (c₀ R : ℝ)
    (hc₀ : 0 < c₀) (hR : 0 < R) (hf : ContinuousOn f Ω)
    (hloc : closedBall x (c₀*R) ⊆ Ω)
    (hunit : ∀ y ∈ Ω, f y ∈ Icc (0:ℝ) 1)
    (hvar : ∀ r : ℝ, 0 < r → ∃ y ∈ ball x r, f y ≠ f x) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      lower f x (c₀*R) < a ∧ b < upper f x (c₀*R) := by
  obtain ⟨y,hy,hneq⟩ := hvar (c₀*R) (mul_pos hc₀ hR)
  exact exists_node_interval f x (c₀*R) (mul_pos hc₀ hR).le (hf.mono hloc)
    (fun y hy => hunit y (hloc hy))
    ⟨y,ball_subset_closedBall hy,x,mem_closedBall_self (mul_pos hc₀ hR).le,hneq⟩

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

lemma exists_source_threshold (ell B H L c₀ ε d₁ ρ : ℝ)
    (hell : 0 < ell) (hε : 0 < ε) (hd₁ : 0 < d₁) (hρ : 0 < ρ) :
    ∃ kmin : ℕ, ∀ k ≥ kmin,
      radius ell k ≤ ρ ∧ (B+1)*radius ell k ≤ 1 ∧ max H 1*radius ell k ≤ 1 ∧
      3*radius ell k ≤ 1 ∧ 2*B*radius ell k < d₁ ∧
      (B+2)*radius ell k ≤ ε ∧ 2*(B+1)*radius ell k ≤ ε ∧
      L*c₀*radius ell k ≤ ε := by
  have ht := radius_tendsto hell
  have hc (C t : ℝ) (ht' : 0 < t) : ∀ᶠ k : ℕ in atTop, C*radius ell k < t := by
    have hh : Tendsto (fun k => C*radius ell k) atTop (𝓝 0) := by
      simpa only [mul_zero] using ht.const_mul C
    exact hh.eventually (gt_mem_nhds ht')
  apply eventually_atTop.mp
  filter_upwards [ht.eventually (gt_mem_nhds hρ),hc (B+1) 1 zero_lt_one,
    hc (max H 1) 1 zero_lt_one,hc 3 1 zero_lt_one,hc (2*B) d₁ hd₁,
    hc (B+2) ε hε,hc (2*(B+1)) ε hε,hc (L*c₀) ε hε] with k hk hB hH h3 hd hε₁ hε₂ hL
  exact ⟨hk.le,hB.le,hH.le,h3.le,hd,hε₁.le,hε₂.le,hL.le⟩

theorem exists_source_construction {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B H c₀ C LE d₀ ell L : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hLE : 0 < LE) (hdc : d₀ ≤ 1/(9*LE)) (hell : 0 < ell)
    (hL : 1 ≤ L) (hLc : L*c₀ ≤ A)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) C LE)
    (hpaths : ∀ x u v : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist v x ≤ r →
      JoinedIn (ball x (L*r)) u v)
    (Ω : Set X) (f : X → ℝ) (hf : ContinuousOn f Ω)
    (hunit : ∀ y ∈ Ω, f y ∈ Icc (0:ℝ) 1)
    (K : ℝ → Set X) (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hK : ∀ t ∈ Ioo (0:ℝ) 1, IsPreconnected (K t) ∧ d₁ ≤ diam (K t) ∧
      ∀ y ∈ K t, y ∈ Ω → f y=t)
    (hhit : ∀ t ∈ Ioo (0:ℝ) 1, ∀ u v, ∀ p : Path u v, Set.range p ⊆ Ω →
      f u < t → t < f v → (K t ∩ Set.range p).Nonempty)
    (x₀ : X) (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ)
    (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (hvar : ∀ r : ℝ, 0 < r → ∃ y ∈ ball x₀ r, f y ≠ f x₀) :
    ∃ n : ℕ, 0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      Nonempty (SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n) := by
  obtain ⟨n,hns,hsc⟩ := ((eventually_scaled_subdivision qdim CP A B H c₀ C LE d₀ ell
    hpack hCP hA hAB hH hc₀ hC hLE hdc hell M hMnon hM δ ξ hξ ω hω hωmass h hexp).and
      (eventually_flow_scales qdim ell c₀ H C hell)).exists
  obtain ⟨hn,hθ,κ,hκ,hnode⟩ := hns
  obtain ⟨kmin,hsmall⟩ := exists_source_threshold ell B H L c₀ ε d₁ ρ hell hε hd₁ hρ
  have hB : 0 ≤ B+1 := by linarith only [hA,hAB]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀]
  let V := SourceNode f x₀ ε ell c₀ (B+1) kmin
  have hnodeΩ (v : V) (w : X) (hw : dist w v.center ≤ (B+2)*radius ell v.depth) : w ∈ Ω := by
    have hx := mem_closedBall.mp (v.center_mem hB)
    have ht := dist_triangle w v.center x₀
    have hs := (hsmall v.depth v.lowerDepth).2.2.2.2.2.1
    apply hloc
    rw [mem_closedBall]
    linarith only [hx,ht,hw,hs]
  have hlocal (v : V) : closedBall v.center (L*c₀*radius ell v.depth) ⊆ Ω := by
    intro w hw
    apply hnodeΩ v w
    have hmul := mul_le_mul_of_nonneg_right hLc (radius_pos ell v.depth).le
    have hm := mul_le_mul_of_nonneg_right (by linarith only [hAB] : A ≤ B+2)
      (radius_pos ell v.depth).le
    exact (mem_closedBall.mp hw).trans (hmul.trans hm)
  have hrootloc : closedBall x₀ (c₀*radius ell kmin) ⊆ Ω := by
    intro w hw
    apply hloc
    have hs := (hsmall kmin le_rfl).2.2.2.2.2.2.2
    have hmul := mul_le_mul_of_nonneg_right hL (mul_pos hc₀pos (radius_pos ell kmin)).le
    rw [mem_closedBall] at hw ⊢
    nlinarith only [hs,hmul,hw,hε]
  obtain ⟨a,b,ha,hab,hb,hla,hub⟩ := root_at_scale f x₀ Ω c₀ (radius ell kmin) hc₀pos
    (radius_pos ell kmin) hf hrootloc hunit hvar
  let root : V := ⟨x₀,kmin,le_rfl,a,b,ha,hab,hb,⟨hla.le,hub.le⟩,by
    simpa only [dist_self,zero_add] using (hsmall kmin le_rfl).2.2.2.2.2.2.1⟩
  choose Y hYloc hYsep hYnet using fun v : V => annular_net v.center A B (radius ell v.depth)
    (radius ell (v.depth+160*(qdim+1)*n)) (radius_pos _ _)
  let good := fun v : V => LiteralGood f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b κ
  have htrans (v : V) : LiteralTransitions f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n))
      v.a v.b κ H (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n))
        (Real.exp (-((80*(qdim+1):ℝ)*ell*n))) := by
    have hv (t : ℝ) (ht : t ∈ Ioo v.a v.b) : t ∈ Ioo (0:ℝ) 1 :=
      ⟨v.apos.trans ht.1,ht.2.trans v.bone⟩
    have hlevelhit := node_level_hits f Ω K v.center (radius ell v.depth) c₀ L v.a v.b
      (radius_pos _ _) hc₀pos hL hf (hlocal v) v.straddle
      (fun u w hu hw => by
        simpa only [mul_assoc] using hpaths v.center u w (c₀*radius ell v.depth)
          (mul_pos hc₀pos (radius_pos _ _)) (mem_closedBall.mp hu) (mem_closedBall.mp hw))
      (fun t ht => hhit t (hv t ht))
    have hk := hsmall v.depth v.lowerDepth
    exact hnode v.center v.depth (Y v) Ω f K v.a v.b v.ab hk.2.1 hk.2.2.1 hk.2.2.2.1
      (hYloc v) (hYsep v) (hYnet v) (hnodeΩ v) hf
      (fun t ht => (hK t (hv t ht)).1)
      (fun t ht => by
        obtain ⟨w,hw,hd⟩ := hlevelhit t ht
        exact ⟨w,hw,hd.trans (mul_le_mul_of_nonneg_right hLc (radius_pos _ _).le)⟩)
      (fun t ht => hk.2.2.2.2.1.trans_le (hK t (hv t ht)).2.1)
      (fun t ht => (hK t (hv t ht)).2.2)
  obtain ⟨R,hdepth,hmove,hsep,hlin,hquad,hlen⟩ := source_rule_of_subdivisions f x₀ ε ell c₀ (B+1) H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n)))
    kmin (160*(qdim+1)*n) hB (hθ.le.trans (by norm_num)) Y good
    (fun v y hy => (hYloc v y hy).2) htrans
  exact ⟨n,hn,hθ,⟨{
    kmin := kmin, small := fun k hk => (hsmall k hk).1, root := root, root_depth := rfl, pattern_small := hsc.2.2.1,
    κ := κ, κpos := hκ, Y := Y, Yloc := hYloc, Ysep := hYsep, Ynet := hYnet,
    rule := R, child_depth := hdepth, child_move := hmove, child_sep := hsep,
    child_linear := hlin, child_quadratic := hquad, child_length_le := hlen }⟩⟩

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow.Subdivision

open Finset

variable {X : Type*} (R : Subdivision X) (x : X)

lemma generation_depth (dep : X → ℕ) (D : ℕ)
    (hdep : ∀ y i, dep (R.child y i)=dep y+D) :
    ∀ n i, dep ((R.generation x n).state i)=dep x+D*n := by
  intro n
  induction n with
  | zero => intro i; simp [generation]
  | succ n ih =>
    intro i
    let u := ((Fintype.equivFin (R.Offspring (R.generation x n))).symm i)
    change dep (R.child ((R.generation x n).state u.1) u.2)=_
    rw [hdep,ih,Nat.mul_succ,Nat.add_assoc]

lemma generation_siblings {Z : Type*} [MetricSpace Z] (pos : X → Z)
    (sep : X → ℝ) (hs : ∀ y i j, i ≠ j → sep y ≤ dist (pos (R.child y i)) (pos (R.child y j)))
    (n : ℕ) (i j : Fin (R.generation x (n+1)).size)
    (hp : R.parentOf (R.generation x n) i=R.parentOf (R.generation x n) j) (hij : i ≠ j) :
    sep ((R.generation x n).state (R.parentOf (R.generation x n) i)) ≤
      dist (pos ((R.generation x (n+1)).state i)) (pos ((R.generation x (n+1)).state j)) := by
  let e := Fintype.equivFin (R.Offspring (R.generation x n))
  obtain ⟨⟨u,ui⟩,rfl⟩ := e.surjective i
  obtain ⟨⟨v,vj⟩,rfl⟩ := e.surjective j
  have huv : u=v := by
    change (e.symm (e ⟨u,ui⟩)).1 = (e.symm (e ⟨v,vj⟩)).1 at hp
    erw [e.symm_apply_apply, e.symm_apply_apply] at hp
    exact hp
  subst v
  have hne : ui ≠ vj := by
    intro he
    subst vj
    exact hij rfl
  change sep ((R.generation x n).state (e.symm (e ⟨u,ui⟩)).1) ≤
    dist (pos (R.child ((R.generation x n).state (e.symm (e ⟨u,ui⟩)).1)
      (e.symm (e ⟨u,ui⟩)).2))
      (pos (R.child ((R.generation x n).state (e.symm (e ⟨u,vj⟩)).1)
      (e.symm (e ⟨u,vj⟩)).2))
  erw [e.symm_apply_apply, e.symm_apply_apply]
  exact hs _ ui vj hne

end CannonFlow.Subdivision

end

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_State
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
section
section
section
section
section
open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

lemma sum_measure_le_multiplicity {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Finset I) (B : I → Set X)
    (hm : ∀ i ∈ s, MeasurableSet (B i)) {M : ℝ}
    (hM : ∀ x, (s.filter (fun i => x ∈ B i)).card ≤ M) :
    ∑ i ∈ s, μ.real (B i) ≤ M * μ.real univ := by
  classical
  have hint : ∀ i ∈ s, Integrable ((B i).indicator (fun _ => (1 : ℝ))) μ := by
    intro i hi
    exact (integrable_const 1).indicator (hm i hi)
  have hid : ∀ x, (∑ i ∈ s, (B i).indicator (fun _ => (1 : ℝ)) x) ≤ M := by
    intro x
    simpa only [Set.indicator_apply, Finset.sum_boole] using hM x
  have h := integral_mono (integrable_finsetSum s hint) (integrable_const M) hid
  rw [integral_finsetSum s hint, integral_const] at h
  have heq : (∑ i ∈ s, ∫ x, (B i).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      ∑ i ∈ s, μ.real (B i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ (hm i hi)]
    simp
  rw [heq] at h
  simpa only [smul_eq_mul, mul_comm] using h

end CannonPairCost

namespace CannonPairCost

open Metric

theorem separated_level_energy {X ι : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (x : ι → X) (Δ : ι → ℝ)
    (r H C E : ℝ) (hr : 0 < r) (hh : 2*C < H) (hE : 0 ≤ E)
    (hsep : ∀ i j, i ≠ j → H*r ≤ dist (x i) (x j))
    (hloc : ∀ i, (Δ i)^2 ≤ E*μ.real (closedBall (x i) (C*r))) :
    ∑ i, (Δ i)^2 ≤ E*μ.real Set.univ := by
  classical
  have hmul (z : X) : ((univ.filter (fun i => z ∈ closedBall (x i) (C*r))).card : ℝ) ≤ 1 := by
    have hc : (univ.filter (fun i => z ∈ closedBall (x i) (C*r))).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hd := hsep i j hij
      have hi' := mem_closedBall.mp (mem_filter.mp hi).2
      have hj' := mem_closedBall.mp (mem_filter.mp hj).2
      have ht := dist_triangle (x i) z (x j)
      rw [dist_comm (x i) z] at ht
      have hh' := mul_lt_mul_of_pos_right hh hr
      linarith
    exact_mod_cast hc
  have hm := sum_measure_le_multiplicity μ univ (fun i => closedBall (x i) (C*r))
    (fun _ _ => isClosed_closedBall.measurableSet) hmul
  calc
    _ ≤ ∑ i, E*μ.real (closedBall (x i) (C*r)) := sum_le_sum (fun i _ => hloc i)
    _ = E*∑ i, μ.real (closedBall (x i) (C*r)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hm) hE

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

lemma state_depth (g : ℕ) (i : Fin (S.flow.size g)) :
    (S.state g i).depth=S.kmin+160*(qdim+1)*n*g := by
  exact (S.rule.generation_depth S.root SourceNode.depth _ S.child_depth g i).trans
    (by rw [S.root_depth])

lemma scale_succ (g : ℕ) : S.scale (g+1)=radius ell (160*(qdim+1)*n)*S.scale g := by
  rw [scale,Nat.mul_succ,← Nat.add_assoc,radius_add]

lemma len_pos (g : ℕ) (i : Fin (S.flow.size g)) : 0 < S.len g i := (S.state g i).length_pos

lemma root_length (i : Fin (S.flow.size 0)) : S.len 0 i=S.root.length := rfl

lemma step_pos (g : ℕ) (i : Fin (S.flow.size (g+1))) : 0 < S.step g i := S.rule.prob_pos _ _

lemma weight_step (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.flow.weight (g+1) i=S.step g i*S.flow.weight g (S.flow.parent g i) := rfl

lemma center_step (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    dist (S.center (g+1) i) (S.center g (S.flow.parent g i)) ≤ (B+1)*S.scale g := by
  have h := S.child_move ((S.rule.generation S.root g).state (S.flow.parent g i))
    ((Fintype.equivFin (S.rule.Offspring (S.rule.generation S.root g))).symm i).2
  change dist (S.center (g+1) i) (S.center g (S.flow.parent g i)) ≤
    (B+1)*radius ell (S.state g (S.flow.parent g i)).depth at h
  rwa [S.state_depth] at h

lemma centers_separated (hθ : radius ell (160*(qdim+1)*n) < 1/4)
    (hB : 0 ≤ B+1) (hH : 4*(B+1) < H) :
    ∀ g i j, i ≠ j → H*S.scale g ≤ dist (S.center g i) (S.center g j) := by
  apply S.flow.centers_separated S.center S.scale (B+1) H (radius ell (160*(qdim+1)*n))
    (fun g => (radius_pos _ _).le) S.scale_succ
  · have hHp : 0 < H := by linarith only [hB,hH]
    nlinarith only [hθ,hB,hH,hHp]
  · intro i j hij
    change Fin 1 at i j
    exact (hij (Subsingleton.elim (α := Fin 1) i j)).elim
  · exact S.center_step
  · intro g i j hp hij
    have hs := S.rule.generation_siblings S.root SourceNode.center
      (fun v => H*radius ell (v.depth+160*(qdim+1)*n))
      (fun v i j hij => (S.child_sep v i j hij).le) g i j hp hij
    change H*radius ell ((S.state g (S.flow.parent g i)).depth+160*(qdim+1)*n) ≤
      dist (S.center (g+1) i) (S.center (g+1) j) at hs
    rw [S.state_depth] at hs
    simpa only [scale,Nat.mul_succ,Nat.add_assoc] using hs

lemma step_quadratic (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.step g i*Real.exp ((160*(qdim+1)*ell*n)*
      (if S.flow.good g (S.flow.parent g i) then -(1/20:ℝ) else 1/2))*
      (S.len g (S.flow.parent g i))^2 ≤ (S.len (g+1) i)^2 := by
  let v := S.state g (S.flow.parent g i)
  let j := ((Fintype.equivFin (S.rule.Offspring (S.rule.generation S.root g))).symm i).2
  have h := S.child_quadratic v j
  have he (t : ℝ) : Real.exp (-t)*Real.exp t=1 := by rw [← Real.exp_add]; simp

  by_cases hg : S.good v
  · simp only [ite_eq_left hg] at h
    change S.step g i*S.len g (S.flow.parent g i)^2 ≤
      Real.exp (8*(qdim+1)*ell*n)*S.len (g+1) i^2 at h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(8*(qdim+1)*ell*n))).le
    have heq : (160*(qdim+1)*ell*(n:ℝ))*(-(1/20:ℝ))=-(8*(qdim+1)*ell*n) := by ring
    change S.step g i*Real.exp ((160*(qdim+1)*ell*n)*(if S.good v then _ else _))*_ ≤ _
    rw [ite_eq_left hg,heq]
    calc
      _ = Real.exp (-(8*(qdim+1)*ell*n))*(S.step g i*S.len g (S.flow.parent g i)^2) := by ring
      _ ≤ _ := hh
      _ = _ := by rw [← mul_assoc,he,one_mul]
  · simp only [ite_eq_right hg] at h
    change S.step g i*S.len g (S.flow.parent g i)^2 ≤
      Real.exp (-((80*(qdim+1):ℝ)*ell*n))*S.len (g+1) i^2 at h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos ((80*(qdim+1):ℝ)*ell*n)).le
    have heq : (160*(qdim+1)*ell*(n:ℝ))*(1/2:ℝ)=(80*(qdim+1):ℝ)*ell*n := by ring
    change S.step g i*Real.exp ((160*(qdim+1)*ell*n)*(if S.good v then _ else _))*_ ≤ _
    rw [ite_eq_right hg,heq]
    calc
      _ = Real.exp ((80*(qdim+1):ℝ)*ell*n)*(S.step g i*S.len g (S.flow.parent g i)^2) := by ring
      _ ≤ _ := hh
      _ = _ := by rw [← mul_assoc, mul_comm (Real.exp _),he,one_mul]

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

lemma center_mem (hB : 0 ≤ B+1) (g : ℕ) (i : Fin (S.flow.size g)) :
    S.center g i ∈ closedBall x₀ ε := (S.state g i).center_mem hB

lemma level_energy [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Cμ E : ℝ) (hE : 0 ≤ E)
    (hB : 0 ≤ B+1) (hc₀ : 0 ≤ c₀)
    (hθ : radius ell (160*(qdim+1)*n) < 1/4) (hH : 4*(B+1) < H)
    (hHμ : 2*(Cμ*c₀) < H)
    (hf : ∀ x ∈ closedBall x₀ ε, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ContinuousOn f (closedBall x (c₀*r)))
    (hpair : ∀ x ∈ closedBall x₀ ε, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∀ y ∈ closedBall x (c₀*r), ∀ z ∈ closedBall x (c₀*r),
        (f y-f z)^2 ≤ E*μ.real (closedBall x (Cμ*(c₀*r)))) :
    ∀ g, ∑ i, (S.len g i)^2 ≤ E*μ.real univ := by
  intro g
  apply CannonPairCost.separated_level_energy μ (S.center g) (S.len g) (S.scale g) H
    (Cμ*c₀) E (radius_pos _ _) hHμ hE (S.centers_separated hθ hB hH g)
  intro i
  let v := S.state g i
  have hr : 0 < S.scale g := radius_pos _ _
  have hsmall : S.scale g ≤ ρ := by
    have hh := S.small v.depth v.lowerDepth
    simpa only [v,S.state_depth] using hh
  have hx := S.center_mem hB g i
  obtain ⟨⟨z,hz,hzv⟩,⟨y,hy,hyv⟩⟩ := ball_extrema (mul_nonneg hc₀ hr.le)
    (hf (S.center g i) hx (S.scale g) hr hsmall)
  have hs : lower f (S.center g i) (c₀*S.scale g) ≤ v.a ∧
      v.b ≤ upper f (S.center g i) (c₀*S.scale g) := by
    simpa only [v,S.state_depth] using v.straddle
  have hlen : S.len g i ≤ f y-f z := by
    change v.b-v.a ≤ _
    rw [hyv,hzv]
    linarith only [hs.1,hs.2]
  have hsq := pow_le_pow_left₀ (S.len_pos g i).le hlen 2
  have hp := hpair _ hx _ hr hsmall y hy z hz
  exact hsq.trans (by simpa only [mul_assoc] using hp)

theorem arbitrarily_late_good (hell : 0 < ell) (hn : 0 < n)
    (E : ℝ) (henergy : ∀ g, ∑ i, (S.len g i)^2 ≤ E) :
    ∀ N : ℕ, ∃ g ≥ N, (1/2:ℝ) ≤ S.flow.goodMass g := by
  apply S.flow.good_levels_of_transitions S.step S.len S.root.length_pos
    (show 0 < (160*(qdim+1):ℝ)*ell*n by positivity)
    S.root_length (fun g i => (S.step_pos g i).le) S.weight_step S.step_quadratic henergy

end CannonNode.SourceConstruction

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Oscillation
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
section
section

section

namespace CannonNode

theorem exists_flow_constants {Lp CE LE Cμ : ℝ}
    (hLp : 1 ≤ Lp) (hCE : 0 < CE) (hLE : 0 < LE) (_hCμ : 0 ≤ Cμ) :
    ∃ c₀ A B₀ cPat H : ℝ,
      2*Lp+2 < c₀ ∧ A=4*Lp*c₀+20 ∧ B₀=A+10 ∧
      cPat=2*CE*(2*Lp)/(A-2)^2 ∧ 0 < cPat ∧
      12*cPat*(B₀+2)^2*LE < c₀ ∧
      max (4*(B₀+1)) (max (4*Cμ*c₀) 2) < H := by
  let cIn := 2*Lp
  have hcin : 2 ≤ cIn := by dsimp [cIn]; linarith only [hLp]
  let c₀ := 100*CE*LE*cIn+cIn+3
  have hc₀ : cIn+2 < c₀ := by
    dsimp [c₀]
    have hh : 0 < CE*LE*cIn := by positivity
    nlinarith only [hh]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀,hcin]
  let A := 4*Lp*c₀+20
  have hA : 20 < A := by
    have hh : 0 < 4*Lp*c₀ := by positivity
    dsimp [A]
    linarith only [hh]
  let B₀ := A+10
  let cPat := 2*CE*cIn/(A-2)^2
  have hd : 0 < (A-2)^2 := sq_pos_of_pos (by linarith only [hA])
  have hratio : (B₀+2)^2 ≤ 4*(A-2)^2 := by
    have hh : 0 ≤ A-2 := by linarith only [hA]
    have hh' : 0 ≤ B₀+2 := by dsimp [B₀]; linarith only [hA]
    have hu : B₀+2 ≤ 2*(A-2) := by dsimp [B₀]; linarith only [hA]
    have hz := pow_le_pow_left₀ hh' hu 2
    nlinarith only [hz]
  have hmargin : 12*cPat*(B₀+2)^2*LE < c₀ := by
    have hco : 0 < 24*CE*cIn*LE := by positivity
    have hmul := mul_le_mul_of_nonneg_left hratio hco.le
    have hc : 96*CE*cIn*LE < c₀ := by
      dsimp [c₀]
      have hh : 0 < CE*LE*cIn := by positivity
      nlinarith only [hh,hcin]
    have hc' := mul_lt_mul_of_pos_right hc hd
    have heq : 12*cPat*(B₀+2)^2*LE = (24*CE*cIn*LE*(B₀+2)^2)/(A-2)^2 := by
      dsimp [cPat]
      ring
    rw [heq]
    apply (div_lt_iff₀ hd).mpr
    nlinarith only [hmul,hc']
  refine ⟨c₀,A,B₀,cPat,max (4*(B₀+1)) (max (4*Cμ*c₀) 2)+1,
    hc₀,rfl,rfl,rfl,div_pos (by positivity) hd,hmargin,?_⟩
  linarith

end CannonNode

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowSetup
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
section
section
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPacking CannonAnnular

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [LocallyPathConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
  {p : ∀ n, ι n → X} {r : ℕ → ℝ}

theorem RecordData.make_flow (R : RecordData action ι p r)
    (Q : ℕ) (CP CE LE ell L d₀ : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hCE : 0 < CE) (hLE : 0 < LE) (hell : 0 < ell) (hL : 1 ≤ L)
    (hdc : d₀ ≤ 1/(9*LE))
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) CE LE)
    (hpaths : ∀ x u v : X, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
      JoinedIn (ball x (L*s)) u v) :
    Nonempty (FlowSetup R ell L CE LE Q) := by
  classical
  obtain ⟨e,he,heΩ⟩ := Metric.isOpen_iff.mp R.isOpen R.x₀ R.x₀mem
  let ε := e/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hloc : closedBall R.x₀ (2*ε) ⊆ R.Ω :=
    (closedBall_subset_ball (by dsimp [ε]; linarith only [he])).trans heΩ
  have hKΩ : closedBall R.x₀ ε ⊆ R.Ω :=
    (closedBall_subset_closedBall (by linarith only [hε])).trans hloc
  obtain ⟨s₀,hs₀,hmeasure⟩ := R.measure_bound (closedBall R.x₀ ε) isClosed_closedBall.isCompact hKΩ
  obtain ⟨c₀,A,B,cPat,H,hcore,hinner,houter,hpattern,hcPat,hmargin,hsep⟩ :=
    exists_flow_constants hL hCE hLE R.Cμ_pos.le
  have hc₀ : 2 ≤ c₀ := by linarith only [hcore,hL]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀]
  have hA : 1 ≤ A := by rw [hinner]; nlinarith only [hL,hc₀]
  have hAB : A+3 ≤ B := by rw [houter]; linarith
  have hB : 0 ≤ B+1 := by linarith only [hA,hAB]
  have hB₂ : 0 < B+2 := by linarith only [hB]
  have hH : 0 < H := lt_trans (by norm_num : (0:ℝ) < 2)
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hsep))
  have hLc : L*c₀ ≤ A := by rw [hinner]; nlinarith only [mul_pos (zero_lt_one.trans_le hL) hc₀pos]
  let ρ := min (s₀/c₀) (min (ε/(B+2)) (ε/2))
  have hρ : 0 < ρ := lt_min (div_pos hs₀ hc₀pos)
    (lt_min (div_pos hε hB₂) (by positivity))
  have hρs : c₀*ρ ≤ s₀ := by
    have hh := (le_div_iff₀ hc₀pos).mp (min_le_left (s₀/c₀) (min (ε/(B+2)) (ε/2)))
    simpa only [mul_comm,ρ] using hh
  have hρB : (B+2)*ρ ≤ ε := by
    have hmin : ρ ≤ ε/(B+2) := (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ hB₂).mp hmin
    simpa only [mul_comm,ρ] using hh
  have hρcut : ρ ≤ ε/2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n,hn,hθ,⟨S⟩⟩ := exists_source_construction Q CP A B H c₀ CE LE d₀ ell L
    hpack hCP hA hAB hH hc₀ hCE.le hLE hdc hell hL hLc M hMnon hM δ ξ hξ ω hω hωmass
    h hexp hpaths R.Ω R.f R.continuous R.unit R.level R.diameter R.diameter_pos
    (fun t ht => ⟨(R.level_properties t ht).2.1.isPreconnected,
      (R.level_properties t ht).2.2.1,(R.level_properties t ht).2.2.2⟩)
    R.level_hits R.x₀ ε ρ hε hρ hloc R.variation
  have hE : ∀ g, ∑ i, (S.len g i)^2 ≤ R.E*(R.ν univ : ℝ) := by
    apply S.level_energy R.ν.toMeasure R.Cμ R.E R.E_nonneg hB hc₀pos.le hθ
      (lt_of_le_of_lt (le_max_left _ _) hsep) ?_ ?_ ?_
    · have hh := lt_of_le_of_lt (le_max_left (4*R.Cμ*c₀) 2)
        (lt_of_le_of_lt (le_max_right (4*(B+1)) _) hsep)
      nlinarith only [hh,mul_pos R.Cμ_pos hc₀pos]
    · intro x hx s hs hsr
      have hh := hmeasure (c₀*s) (mul_pos hc₀pos hs)
        ((mul_le_mul_of_nonneg_left hsr hc₀pos.le).trans hρs) x hx
      exact R.continuous.mono hh.1
    · intro x hx s hs hsr y hy z hz
      have hh := hmeasure (c₀*s) (mul_pos hc₀pos hs)
        ((mul_le_mul_of_nonneg_left hsr hc₀pos.le).trans hρs) x hx
      have hb := (isCompact_closedBall x (c₀*s)).image_of_continuousOn (R.continuous.mono hh.1)
      have hyl := csInf_le hb.bddBelow (mem_image_of_mem R.f hy)
      have hyu := le_csSup hb.bddAbove (mem_image_of_mem R.f hy)
      have hzl := csInf_le hb.bddBelow (mem_image_of_mem R.f hz)
      have hzu := le_csSup hb.bddAbove (mem_image_of_mem R.f hz)
      have hd : |R.f y-R.f z| ≤ CannonCrossEnergy.oscillation R.f (closedBall x (c₀*s)) := by
        unfold CannonCrossEnergy.oscillation
        exact abs_le.mpr ⟨by linarith only [hyl,hzu],by linarith only [hzl,hyu]⟩
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hd 2
      change (R.f y-R.f z)^2 ≤ R.E*(R.ν (closedBall x (R.Cμ*(c₀*s))) : ℝ)
      simpa only [sq_abs] using hsq.trans hh.2
  exact ⟨{
    ε := ε, εpos := hε, local_domain := hloc, c₀ := c₀, A := A, B := B,
    cPat := cPat, H := H, core := hcore, inner := hinner, outer := houter,
    pattern := hpattern, pattern_pos := hcPat, margin := hmargin, separation := hsep,
    ρ := ρ, ρpos := hρ, small := hρB, cutoff := hρcut, n := n, npos := hn, decay := hθ,
    S := S, energy := hE, good := S.arbitrarily_late_good hell hn _ hE }⟩

end CannonApprox

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_BoundaryRecordFlow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section
namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox CannonCells CannonCharts
open CannonNode CannonAnnular Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_record_flow (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let ell := 2*visualExponent δ
    let a := Real.exp ell
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    (∀ B : ℝ, ∃ n, B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)) →
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ CP : ℝ, 0 < CP ∧ PolynomialPacking (X:=Boundary D) Q CP ∧
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ x u v : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
        JoinedIn (ball x (L*s)) u v) ∧
    ∃ Ns : ℕ → ℕ, StrictMono Ns ∧ ∃ R : RecordData
      (boundaryHomeomorph D ⟨δ,hδ⟩) (fun n => ι (Ns n)) (fun n => p (Ns n))
        (fun n => (a^(Ns n))⁻¹), Nonempty (FlowSetup R ell L CE LE Q) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet hunbounded
  let ell := 2*visualExponent δ
  let a := Real.exp ell
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hell : 0 < ell := mul_pos (by norm_num) (visualExponent_pos δ)
  have hr (j : ℕ) : 0 < (a^j)⁻¹ := inv_pos.mpr (pow_pos (Real.exp_pos _) _)
  let M := fun j => modulus (fun i => ball (p j i) (2*(a^j)⁻¹)) (macroFamily d)
  have hmin (j : ℕ) : 0 < M j ∧ ∃ ω : ι j → ℝ,
      MacroscopicAdmissible (p j) ((a^j)⁻¹) d ω ∧ (∑ i, (ω i)^2)=M j := by
    apply sphere_macro_modulus_minimum φ d hd hdia (p j) ((a^j)⁻¹)
    intro x
    obtain ⟨i,hi⟩ := hpnet j x
    exact ⟨i,mem_ball.mpr (by rw [dist_comm]; linarith only [hi,hr j])⟩
  choose ω hω using fun j => (hmin j).2
  obtain ⟨Q,CP,hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨L,hL,hpaths⟩ := boundary_controlled_paths D hδ φ
  have hp : ∀ x u v : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
      JoinedIn (ball x (L*s)) u v := by
    intro x u v s hs hu hv
    convert hpaths x u v s hs (by simpa only [dist_comm] using hu) (by simpa only [dist_comm] using hv) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ball,mem_ofPred_eq,dist_comm]
  obtain ⟨Ns,hNs,⟨R⟩⟩ := boundary_record_data D hδ φ d hd hdia hdc ι p hpsep hpnet hunbounded
  refine ⟨Q,hQ,CP,hCP,hpack,L,hL,hp,Ns,hNs,R,?_⟩
  apply R.make_flow Q CP CE LE ell L d hpack hCP.le (by dsimp [CE]; positivity)
    (by dsimp [LE]; positivity) hell hL (by
      change d ≤ 1/(LE*3^2) at hdc
      simpa only [show (3:ℝ)^2=9 by norm_num,mul_comm LE 9] using hdc)
    M (fun j => (hmin j).1.le)
    (boundary_modulus_subexponential D hδ φ d hd hdia hdc ι p hpsep hpnet) ι p
    (fun j i i' hne => by simpa only [radius_eq_power] using hpsep j i i' hne) ω
    (fun j => by simpa only [radius_eq_power] using (hω j).1)
    (fun j => (hω j).2.le) (boundaryExpansion D hδ)
    (fun x j => by simpa only [radius_eq_power] using boundaryExpansion_formula D hδ x j) hp

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryModulusBounded
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox CannonCells CannonCharts
open CannonNode CannonAnnular Set Metric Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_modulus_bounded (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    ∃ B : ℝ, ∀ n, modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d) ≤ B := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet
  by_contra! hunbounded
  obtain ⟨Q,hQ,CP,hCP,hpack,L,hL,hpaths,Ns,hNs,R,⟨F⟩⟩ :=
    boundary_record_flow D hδ φ d hd hdia hdc ι p hpsep hpnet hunbounded
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  have hrlim : Tendsto (fun n => (a^(Ns n))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hNs.tendsto_atTop
  exact boundary_no_record_flow D hδ (fun n => ι (Ns n)) (fun n => p (Ns n))
    (fun n => (a^(Ns n))⁻¹) (fun _ => inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _))
    hrlim (fun n => hpnet (Ns n)) R Q (lt_of_lt_of_le (by norm_num : 0 < 2) hQ)
    CP hCP.le hpack L hL hpaths F

end CannonRelease

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_ApproxSelfSimilar
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
open CannonGraph CannonVisual CannonGeometry Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance approxSelfSimilarSetoid_r1667ec_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_approx_self_similar :
    let _ := visualMetricSpace D hδ
    ApproxSelfSimilar (Boundary D) := by
  let _ := visualMetricSpace D hδ
  let U := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < A := Real.exp_pos _
  have hLA : 0 < L*A := mul_pos hL hA
  refine ⟨1+U+L*A,by linarith,?_⟩
  intro x r hr hrdia
  have hdia : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _ => boundaryDist_le_one D hδ x y)
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hr (hrdia.trans hdia)
  obtain ⟨ray,hrep⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (ray.val k)⁻¹
  refine ⟨f,?_⟩
  intro y hy z hz
  have hy' : boundaryDist D hδ (Quotient.mk' ray) y ≤ visualScale δ k := by
    exact (dist_comm _ _).le.trans ((mem_ball.mp hy).le.trans hk)
  have hz' : boundaryDist D hδ (Quotient.mk' ray) z ≤ visualScale δ k := by
    exact (dist_comm _ _).le.trans ((mem_ball.mp hz).le.trans hk)
  have hh := visual_ball_expansion D hδ ray k y z hy' hz'
  change dist (f y) (f z)*visualScale δ k ≤ U*dist y z ∧
    dist y z ≤ L*dist (f y) (f z)*visualScale δ k at hh
  constructor
  · calc
      dist (f y) (f z)*r ≤ dist (f y) (f z)*visualScale δ k := mul_le_mul_of_nonneg_left hk dist_nonneg
      _ ≤ U*dist y z := hh.1
      _ ≤ (1+U+L*A)*dist y z := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  · calc
      dist y z ≤ L*dist (f y) (f z)*visualScale δ k := hh.2
      _ ≤ L*dist (f y) (f z)*(A*r) := mul_le_mul_of_nonneg_left hk'
        (mul_nonneg hL.le dist_nonneg)
      _ = (L*A)*dist (f y) (f z)*r := by ring
      _ ≤ (1+U+L*A)*dist (f y) (f z)*r := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg) hr.le

end CannonRelease

namespace CannonNet
open Set Metric

variable {X : Type*} [MetricSpace X]

lemma exists_scale_below {a s : ℝ} (ha : 1 < a) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, s/a < (a^n)⁻¹ ∧ (a^n)⁻¹ ≤ s := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hq : 0 < a⁻¹ := inv_pos.mpr hap
  have hq1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near_of_lt_one hs hs1 hq hq1
  rcases lt_or_eq_of_le hn' with hlt | heq
  · refine ⟨n+1,?_,?_⟩
    · rw [← inv_pow,pow_succ,div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hlt hq
    · simpa only [inv_pow] using hn.le
  · refine ⟨n,?_,?_⟩
    · rw [← inv_pow,← heq]
      exact (div_lt_self hs ha)
    · simpa only [inv_pow] using heq.ge

theorem exists_net_sequence [CompactSpace X] {a : ℝ} (ha : 1 < a) :
    ∃ T : ℕ → Finset X, ∀ n,
      (∀ x ∈ T n, ∀ y ∈ T n, x ≠ y → (a^n)⁻¹ ≤ dist x y) ∧
      (∀ x : X, ∃ y ∈ T n, dist y x ≤ (a^n)⁻¹) := by
  classical
  have h (n : ℕ) := exists_compact_net (X:=X) ((a^n)⁻¹)
    (inv_pos.mpr (pow_pos (zero_lt_one.trans ha) n))
  choose T hs hc _ using h
  exact ⟨T,fun n => ⟨hs n,by intro x; simpa only [dist_comm] using hc n x⟩⟩

end CannonNet

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ModulusSerialBound
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
open scoped InnerProductSpace
open Set

namespace CannonCells
open Set CannonDuality

variable {X ι J : Type*} [Fintype ι] [Fintype J]

theorem modulus_serial_bound [Nonempty J]
    (C : ι → Set X) (F : Set (Set X)) (H : J → Set (Set X))
    (w : J → Weights ι) (hw : ∀ j, Admissible (familyVectors C (H j) : Set (Weights ι)) (w j))
    (horth : ∀ i j k, j ≠ k → w j i*w k i=0)
    (hcross : ∀ A ∈ F, ∀ j, ∃ B ∈ H j, B ⊆ A) :
    modulus C F ≤ (∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 := by
  classical
  have hcard : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  let W : Weights ι := (Fintype.card J : ℝ)⁻¹ • ∑ j, w j
  have hw' (j : J) := (admissible_iff C (H j) (w j)).mp (hw j)
  have hpoint (i : ι) : W i=(Fintype.card J : ℝ)⁻¹ * ∑ j, w j i := by simp [W]
  have hW : Admissible (familyVectors C F : Set (Weights ι)) W := by
    rw [admissible_iff]
    refine ⟨?_,?_⟩
    · intro i
      rw [hpoint]
      exact mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg (fun j _ => (hw' j).1 i))
    · intro A hA
      have hsum (j : J) : 1 ≤ ∑ i ∈ indices C A, w j i := by
        obtain ⟨B,hB,hBA⟩ := hcross A hA j
        exact ((hw' j).2 B hB).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (indices_mono C hBA) (fun i _ _ => (hw' j).1 i))
      have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hsum j)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      calc
        1 = (Fintype.card J : ℝ)⁻¹ * Fintype.card J := (inv_mul_cancel₀ (ne_of_gt hcard)).symm
        _ ≤ (Fintype.card J : ℝ)⁻¹ * ∑ j, ∑ i ∈ indices C A, w j i :=
          mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hcard.le)
        _ = ∑ i ∈ indices C A, W i := by
          simp only [hpoint,Finset.mul_sum]
          rw [Finset.sum_comm]
  have hsquare (i : ι) : (∑ j, w j i)^2=∑ j, (w j i)^2 := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single j]
    · rw [pow_two]
    · intro k hk hkj
      exact horth i j k hkj.symm
    · simp
  have henergy : ‖W‖^2=(∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hpoint,mul_pow,hsquare]
    rw [← Finset.mul_sum]
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm]
    simp only [div_eq_mul_inv,inv_pow,mul_comm]
  exact (modulus_le_energy C F W hW).trans henergy.le

theorem modulus_serial_uniform [Nonempty J]
    (C : ι → Set X) (F : Set (Set X)) (H : J → Set (Set X))
    (w : J → Weights ι) (hw : ∀ j, Admissible (familyVectors C (H j) : Set (Weights ι)) (w j))
    (horth : ∀ i j k, j ≠ k → w j i*w k i=0)
    (hcross : ∀ A ∈ F, ∀ j, ∃ B ∈ H j, B ⊆ A)
    {B : ℝ} (henergy : ∀ j, ‖w j‖^2 ≤ B) :
    modulus C F ≤ B/(Fintype.card J : ℝ) := by
  have hcard : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 :=
      modulus_serial_bound C F H w hw horth hcross
    _ ≤ ((Fintype.card J : ℝ)*B)/(Fintype.card J : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=Finset.univ) (fun j _ => henergy j)
    _ = _ := by field_simp

end CannonCells

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_LayerFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
namespace CannonUniformization
open Set Metric unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X]

theorem exists_layer_transfer_constant (Q : ℕ) (CP K c : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP)
    (hCP : 0 ≤ CP) (hK : 0 < K) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι β : Type*} [Fintype ι] [Fintype β]
      (q : ι → X) (ξ : β → X) (h : X ≃ₜ X) (o : X) (r s d : ℝ),
      0 < r → 0 < s → r ≤ s/2 → d ≤ c →
      max (2+2*K) (max c 1)*(r/s) ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ x, ∃ i, dist (q i) x ≤ r) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ x y, dist x o ≤ 3*s → dist y o ≤ 3*s →
        c/s*dist x y ≤ dist (h x) (h y) ∧ dist (h x) (h y) ≤ K/s*dist x y) →
      ∀ ω : Weights β,
      Admissible (familyVectors (fun j => ball (ξ j) (2*(r/s))) (macroFamily d) :
        Set (Weights β)) ω →
      ∃ w : Weights ι,
        Admissible (familyVectors (fun i => ball (q i) (2*r)) (layerFamily o s) :
          Set (Weights ι)) w ∧
        (∀ i, dist (q i) o < s/2 ∨ 3*s < dist (q i) o → w i = 0) ∧
        ‖w‖^2 ≤ E*‖ω‖^2 := by
  classical
  obtain ⟨E,hE,hbound⟩ := CannonCapacity.exists_local_transfer_constant Q CP (2+2*K) c
    hpack hCP (by linarith) hc
  refine ⟨E,hE,?_⟩
  intro ι β _ _ q ξ h o r s d hr hs hrs hdc hscale hq hcover hξ hexp ω hω
  have hnω := (admissible_iff _ _ _).mp hω
  let band (i : ι) : Prop := s/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*s
  let rel (i : ι) : Finset β := if band i then
    Finset.univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (2+2*K)*(r/s)) else ∅
  let w : Weights ι := WithLp.toLp 2 (fun i => ∑ j ∈ rel i, ω j)
  have hwpoint (i : ι) : w i = ∑ j ∈ rel i, ω j := rfl
  have hw0 (i : ι) : 0 ≤ w i := Finset.sum_nonneg (fun j _ => hnω.1 j)
  refine ⟨w,?_,?_,?_⟩
  · rw [admissible_iff]
    refine ⟨hw0,?_⟩
    rintro A ⟨u,v,p,rfl,hu,hv,hp⟩
    have huB : dist u o ≤ 3*s := by rw [hu]; linarith
    have hvB : dist v o ≤ 3*s := by rw [hv]; linarith
    have hsep : s ≤ dist u v := by
      have hh := dist_triangle v u o
      rw [hu,hv,dist_comm v u] at hh
      linarith
    have hmacro : h '' range p ∈ macroFamily d := by
      refine ⟨h ∘ p,h.continuous.comp p.continuous,?_,?_⟩
      · exact Set.range_comp h p |>.symm
      · have hdiam : dist (h u) (h v) ≤ diam (h '' range p) :=
          dist_le_diam_of_mem ((isCompact_range p.continuous).image h.continuous).isBounded
            ⟨u,⟨0,p.source⟩,rfl⟩ ⟨v,⟨1,p.target⟩,rfl⟩
        have hh := (hexp u v huB hvB).1
        have hmul := mul_le_mul_of_nonneg_left hsep (div_nonneg hc.le hs.le)
        have hid : c/s*s=c := div_mul_cancel₀ c hs.ne'
        rw [hid] at hmul
        exact hdc.trans (hmul.trans (hh.trans hdiam))
    have hline := hnω.2 (h '' range p) hmacro
    have hcharge : ∀ j ∈ indices (fun j => ball (ξ j) (2*(r/s))) (h '' range p),
        ∃ i ∈ indices (fun i => ball (q i) (2*r)) (range p), j ∈ rel i := by
      intro j hj
      obtain ⟨z,⟨x,⟨t,rfl⟩,rfl⟩,hz⟩ := (mem_indices _ _ _).mp hj
      obtain ⟨i,hi⟩ := hcover (p t)
      have hiB : band i := by
        have htri := dist_triangle (p t) (q i) o
        have htri' := dist_triangle (q i) (p t) o
        rw [dist_comm (p t) (q i)] at htri
        dsimp only [band]
        constructor <;> linarith [(hp t).1,(hp t).2]
      refine ⟨i,(mem_indices _ _ _).mpr ⟨p t,mem_range_self t,?_⟩,?_⟩
      · change dist (p t) (q i) < 2*r
        rw [dist_comm]
        linarith
      · change j ∈ if band i then _ else _
        rw [ite_eq_left hiB,Finset.mem_filter]
        refine ⟨Finset.mem_univ _,?_⟩
        have hxB : dist (p t) o ≤ 3*s := by linarith [(hp t).2]
        have hmap := (hexp (q i) (p t) hiB.2 hxB).2
        have hmul := mul_le_mul_of_nonneg_left hi (div_nonneg hK.le hs.le)
        have hz' : dist (ξ j) (h (p t)) < 2*(r/s) := by simpa only [mem_ball,dist_comm] using hz
        have ht := dist_triangle (ξ j) (h (p t)) (h (q i))
        rw [dist_comm (h (p t)) (h (q i))] at ht
        have hnon : 0 ≤ K*(r/s) := mul_nonneg hK.le (div_nonneg hr.le hs.le)
        have hid : K/s*r=K*(r/s) := by ring
        rw [hid] at hmul
        nlinarith
    exact hline.trans (CannonAnnular.finite_charge_cover _ _ rel ω hnω.1 hcharge)
  · intro i hi
    rw [hwpoint]
    have hn : ¬ band i := by rcases hi with hi | hi <;> intro hh <;> linarith [hh.1,hh.2]
    simp [rel,hn]
  · have hb := hbound q ξ h o r s hr hs hscale hq hξ (fun x y hx hy => (hexp x y hx hy).1) ω
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro i _
    rw [hwpoint]
    by_cases hi : band i
    · simp only [rel,ite_eq_left hi,ite_eq_left hi.2,le_refl]
    · simp only [rel,ite_eq_right hi,Finset.sum_empty,zero_pow (by omega : 2 ≠ 0)]
      exact sq_nonneg _

end
end CannonUniformization

namespace CannonUniformization
open Set Metric unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X]

theorem annulus_modulus_serial {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]
    (q : ι → X) (o : X) (mesh r R : ℝ) (s : J → ℝ)
    (hs : ∀ j, 0 < s j) (hinner : ∀ j, r ≤ s j) (houter : ∀ j, 2*s j ≤ R)
    (hdisj : ∀ j k, j ≠ k → 3*s j < s k/2 ∨ 3*s k < s j/2)
    (w : J → Weights ι)
    (hw : ∀ j, Admissible (familyVectors (fun i => ball (q i) (2*mesh))
      (layerFamily o (s j)) : Set (Weights ι)) (w j))
    (hws : ∀ j i, dist (q i) o < s j/2 ∨ 3*s j < dist (q i) o → w j i = 0)
    {B : ℝ} (hE : ∀ j, ‖w j‖^2 ≤ B) :
    modulus (fun i => ball (q i) (2*mesh)) (annulusFamily o r R) ≤ B/(Fintype.card J : ℝ) := by
  apply modulus_serial_uniform _ _ (fun j => layerFamily o (s j)) w hw ?_ ?_ hE
  · intro i j k hjk
    by_cases hj : w j i = 0
    · rw [hj,zero_mul]
    by_cases hk : w k i = 0
    · rw [hk,mul_zero]
    have hjlo : s j/2 ≤ dist (q i) o := le_of_not_gt (fun hh => hj (hws j i (.inl hh)))
    have hjhi : dist (q i) o ≤ 3*s j := le_of_not_gt (fun hh => hj (hws j i (.inr hh)))
    have hklo : s k/2 ≤ dist (q i) o := le_of_not_gt (fun hh => hk (hws k i (.inl hh)))
    have hkhi : dist (q i) o ≤ 3*s k := le_of_not_gt (fun hh => hk (hws k i (.inr hh)))
    rcases hdisj j k hjk with hh | hh <;> linarith
  · rintro A ⟨u,v,p,rfl,hu,hv⟩ j
    obtain ⟨x,y,t,ht,hx,hy,_,hbet⟩ := CannonAnnular.radial_subpath o u v p (s j) (2*s j)
      (by linarith [hs j]) (hu.trans (hinner j)) ((houter j).trans hv)
    exact ⟨range t,⟨x,y,t,rfl,hx,hy,hbet⟩,ht⟩

theorem exists_annulus_transfer_constant (Q : ℕ) (CP K c : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP)
    (hCP : 0 ≤ CP) (hK : 0 < K) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]
      (β : J → Type*) [∀ j, Fintype (β j)]
      (q : ι → X) (ξ : ∀ j, β j → X) (h : J → X ≃ₜ X)
      (o : X) (mesh r R d B : ℝ) (s : J → ℝ),
      0 < mesh → (∀ j, 0 < s j) → (∀ j, mesh ≤ s j/2) → d ≤ c →
      (∀ j, max (2+2*K) (max c 1)*(mesh/s j) ≤ 1) →
      (∀ i j, i ≠ j → mesh ≤ dist (q i) (q j)) →
      (∀ x, ∃ i, dist (q i) x ≤ mesh) →
      (∀ j i k, i ≠ k → mesh/s j ≤ dist (ξ j i) (ξ j k)) →
      (∀ j x y, dist x o ≤ 3*s j → dist y o ≤ 3*s j →
        c/s j*dist x y ≤ dist (h j x) (h j y) ∧ dist (h j x) (h j y) ≤ K/s j*dist x y) →
      (∀ j, r ≤ s j) → (∀ j, 2*s j ≤ R) →
      (∀ j k, j ≠ k → 3*s j < s k/2 ∨ 3*s k < s j/2) →
      (∀ j, ∃ ω : Weights (β j),
        Admissible (familyVectors (fun i => ball (ξ j i) (2*(mesh/s j))) (macroFamily d) :
          Set (Weights (β j))) ω ∧ ‖ω‖^2 ≤ B) →
      modulus (fun i => ball (q i) (2*mesh)) (annulusFamily o r R) ≤ E*B/(Fintype.card J : ℝ) := by
  classical
  obtain ⟨E,hE,htrans⟩ := exists_layer_transfer_constant Q CP K c hpack hCP hK hc
  refine ⟨E,hE,?_⟩
  intro ι J _ _ _ β _ q ξ h o mesh r R d B s hm hs hms hd hscale hq hcover hξ hexp hi ho hdisj hω
  choose ω hωadm hωE using hω
  have hweights (j : J) : ∃ w : Weights ι,
      Admissible (familyVectors (fun i => ball (q i) (2*mesh)) (layerFamily o (s j)) :
        Set (Weights ι)) w ∧
      (∀ i, dist (q i) o < s j/2 ∨ 3*s j < dist (q i) o → w i = 0) ∧ ‖w‖^2 ≤ E*B := by
    obtain ⟨w,hw,hws,hwE⟩ := htrans q (ξ j) (h j) o mesh (s j) d hm (hs j) (hms j)
      hd (hscale j) hq hcover (hξ j) (hexp j) (ω j) (hωadm j)
    exact ⟨w,hw,hws,hwE.trans (mul_le_mul_of_nonneg_left (hωE j) hE)⟩
  choose w hw hws hwE using hweights
  exact annulus_modulus_serial q o mesh r R s hs hi ho hdisj w hw hws hwE

end
end CannonUniformization

namespace CannonUniformization
open Set Metric Filter Topology unitInterval CannonDuality CannonCells CannonCharts

noncomputable section

lemma inverse_power_ratio {a : ℝ} (ha : 0 < a) {k m : ℕ} (hkm : k ≤ m) :
    (a^m)⁻¹/(a^k)⁻¹ = (a^(m-k))⁻¹ := by
  have he : a^m=a^(m-k)*a^k := by rw [← pow_add,Nat.sub_add_cancel hkm]
  rw [he,mul_inv]
  field_simp

lemma inverse_power_antitone {a : ℝ} (ha : 1 < a) {k m : ℕ} (hkm : k ≤ m) :
    (a^m)⁻¹ ≤ (a^k)⁻¹ := by
  exact inv_le_inv₀ (pow_pos (zero_lt_one.trans ha) _) (pow_pos (zero_lt_one.trans ha) _)
    |>.mpr (pow_le_pow_right₀ ha.le hkm)

lemma spaced_inverse_powers {a : ℝ} (ha : 1 < a) (ℓ k₀ : ℕ) (hℓ : 8 ≤ a^ℓ)
    {j k : ℕ} (hjk : j < k) :
    3*(a^(k₀+ℓ*k))⁻¹ < (a^(k₀+ℓ*j))⁻¹/2 := by
  have hp : 0 < (a^(k₀+ℓ*j))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hs : (a^(k₀+ℓ*k))⁻¹ ≤ (a^(k₀+ℓ*j+ℓ))⁻¹ :=
    inverse_power_antitone ha (by
      have hh := Nat.add_le_add_left (Nat.mul_le_mul_left ℓ (Nat.succ_le_of_lt hjk)) k₀
      simpa only [Nat.mul_succ,Nat.add_assoc] using hh)
  have he : (a^(k₀+ℓ*j+ℓ))⁻¹=(a^(k₀+ℓ*j))⁻¹*(a^ℓ)⁻¹ := by rw [pow_add,mul_inv]
  have hi : (a^ℓ)⁻¹ ≤ (8:ℝ)⁻¹ := (inv_le_inv₀ (pow_pos (zero_lt_one.trans ha) ℓ) (by norm_num : (0:ℝ) < 8)).mpr hℓ
  rw [he] at hs
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi hp.le)
  norm_num at hh
  linarith

variable {X : Type*} [MetricSpace X] [PathConnectedSpace X]

theorem annular_modulus_decay (Q : ℕ) (CP L a : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hL : 1 ≤ L) (ha : 1 < a)
    (hsim : ∀ o : X, ∀ s : ℝ, 0 < s → s ≤ diam (univ : Set X) →
      ∃ f : X ≃ₜ X, ∀ x ∈ ball o s, ∀ y ∈ ball o s,
        dist (f x) (f y)*s ≤ L*dist x y ∧ dist x y ≤ L*dist (f x) (f y)*s)
    (ι : ℕ → Type*) [∀ m, Fintype (ι m)] (p : ∀ m, ι m → X)
    (hpsep : ∀ m i j, i ≠ j → (a^m)⁻¹ ≤ dist (p m i) (p m j))
    (hpnet : ∀ m x, ∃ i, dist (p m i) x ≤ (a^m)⁻¹)
    (d B : ℝ) (hd : 0 < d) (hdiam : d < diam (univ : Set X)) (hdL : d ≤ 1/(4*L))
    (hB : ∀ m, modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (macroFamily d) ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ℓ k₀ n : ℕ, 8 ≤ a^ℓ →
      4*(a^k₀)⁻¹ ≤ diam (univ : Set X) →
      ∀ᶠ m : ℕ in atTop, ∀ o : X,
        modulus (fun i => ball (p m i) (2*(a^m)⁻¹))
          (annulusFamily o (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹)) ≤ E*B/(n+1:ℝ) := by
  classical
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hap : 0 < a := zero_lt_one.trans ha
  have hc : 0 < 1/(4*L) := by positivity
  obtain ⟨E,hE,htrans⟩ := exists_annulus_transfer_constant Q CP L (1/(4*L)) hpack hCP hLp hc
  refine ⟨E,hE,?_⟩
  intro ℓ k₀ n hℓ hk₀
  let k (j : Fin (n+1)) := k₀+ℓ*j.val
  let s (j : Fin (n+1)) : ℝ := (a^(k j))⁻¹
  have hs (j : Fin (n+1)) : 0 < s j := inv_pos.mpr (pow_pos hap _)
  have hk (j : Fin (n+1)) : k j ≤ k₀+ℓ*n :=
    Nat.add_le_add_left (Nat.mul_le_mul_left ℓ (Nat.le_of_lt_succ j.isLt)) k₀
  have hsmall (j : Fin (n+1)) : s j ≤ (a^k₀)⁻¹ := inverse_power_antitone ha (by dsimp [k]; omega)
  have hlim : Tendsto (fun m : ℕ => (a^m)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr hap).le
      (inv_lt_one_of_one_lt₀ ha)
  have ht (j : Fin (n+1)) : ∀ᶠ m : ℕ in atTop,
      (a^m)⁻¹ ≤ s j/2 ∧ max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j) ≤ 1 := by
    have h₁ := hlim.eventually (eventually_lt_nhds (show 0 < s j/2 by positivity))
    have h₂lim : Tendsto (fun m : ℕ => max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j))
        atTop (𝓝 0) := by simpa using (hlim.div_const (s j)).const_mul (max (2+2*L) (max (1/(4*L)) 1))
    have h₂ := h₂lim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
    exact (h₁.and h₂).mono (fun _ hh => ⟨hh.1.le,hh.2.le⟩)
  have htall : ∀ᶠ m : ℕ in atTop, ∀ j : Fin (n+1),
      (a^m)⁻¹ ≤ s j/2 ∧ max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j) ≤ 1 :=
    Filter.eventually_all.mpr ht
  filter_upwards [htall,eventually_ge_atTop (k₀+ℓ*n)] with m hm hmge
  intro o
  have hexists (j : Fin (n+1)) : ∃ f : X ≃ₜ X, ∀ x y,
      dist x o ≤ 3*s j → dist y o ≤ 3*s j →
      (1/(4*L))/s j*dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ L/s j*dist x y := by
    obtain ⟨f,hf⟩ := hsim o (4*s j) (by positivity)
      ((mul_le_mul_of_nonneg_left (hsmall j) (by norm_num)).trans hk₀)
    refine ⟨f,?_⟩
    intro x y hx hy
    have hh := hf x (show x ∈ ball o (4*s j) by change dist x o < _; linarith [hs j])
      y (show y ∈ ball o (4*s j) by change dist y o < _; linarith [hs j])
    constructor
    · have hid : (1/(4*L))/s j*dist x y=dist x y/(L*(4*s j)) := by ring
      rw [hid,div_le_iff₀ (mul_pos hLp (by positivity))]
      nlinarith [hh.2]
    · rw [div_mul_eq_mul_div,le_div_iff₀ (hs j)]
      have hn := mul_nonneg (dist_nonneg (x:=f x) (y:=f y)) (hs j).le
      nlinarith [hh.1]
  choose f hf using hexists
  let β (j : Fin (n+1)) := ι (m-k j)
  let ξ (j : Fin (n+1)) : β j → X := p (m-k j)
  have hratio (j : Fin (n+1)) : (a^m)⁻¹/s j=(a^(m-k j))⁻¹ :=
    inverse_power_ratio hap ((hk j).trans hmge)
  have htarget (j : Fin (n+1)) : ∃ ω : Weights (β j),
      Admissible (familyVectors (fun i => ball (ξ j i) (2*((a^m)⁻¹/s j))) (macroFamily d) :
        Set (Weights (β j))) ω ∧ ‖ω‖^2 ≤ B := by
    obtain ⟨_,ω,hω,hωE⟩ := modulus_minimum
      (fun i => ball (p (m-k j) i) (2*(a^(m-k j))⁻¹)) (by
        intro x
        obtain ⟨i,hi⟩ := hpnet (m-k j) x
        refine ⟨i,?_⟩
        change dist x (p (m-k j) i) < _
        rw [dist_comm]
        have hh : 0 < (a^(m-k j))⁻¹ := by positivity
        linarith) (macroFamily_nonempty hd hdiam)
          (fun A hA => by obtain ⟨p,_,rfl,_⟩ := hA; exact range_nonempty p)
    refine ⟨ω,?_,hωE.le.trans (hB (m-k j))⟩
    simpa only [ξ,hratio] using hω
  have hres := htrans β (p m) ξ f o (a^m)⁻¹ (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹) d B s
    (by positivity) hs (fun j => (hm j).1) hdL (fun j => (hm j).2) (hpsep m) (hpnet m)
    (fun j i l hil => by rw [hratio]; exact hpsep _ i l hil) hf
    (fun j => inverse_power_antitone ha (hk j))
    (fun j => mul_le_mul_of_nonneg_left (hsmall j) (by norm_num))
    (fun j l hjl => by
      rcases lt_or_gt_of_ne (show j.val ≠ l.val from fun he => hjl (Fin.ext he)) with hh | hh
      · exact Or.inr (spaced_inverse_powers ha ℓ k₀ hℓ hh)
      · exact Or.inl (spaced_inverse_powers ha ℓ k₀ hℓ hh)) htarget
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hres

end
end CannonUniformization

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ModulusFamilyMono
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
namespace CannonCells
open Set CannonDuality

noncomputable section
variable {X ι : Type*} [Fintype ι]

lemma modulus_family_mono (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F H : Set (Set X)} (hFH : F ⊆ H) (hH : ∀ A ∈ H, A.Nonempty) :
    modulus C F ≤ modulus C H := by
  classical
  let w : Weights ι := WithLp.toLp 2 (fun _ => (1:ℝ))
  have hw : Admissible (familyVectors C H : Set (Weights ι)) w := by
    rw [admissible_iff]
    refine ⟨fun _ => zero_le_one,?_⟩
    intro A hA
    obtain ⟨x,hx⟩ := hH A hA
    obtain ⟨i,hi⟩ := hC x
    have hm : i ∈ indices C A := (mem_indices C A i).mpr ⟨x,hx,hi⟩
    exact Finset.single_le_sum (fun _ _ => zero_le_one) hm
  unfold modulus Modulus
  apply csInf_le_csInf
  · refine ⟨0,?_⟩
    rintro e ⟨z,_,rfl⟩
    exact sq_nonneg _
  · exact ⟨‖w‖^2,w,hw,rfl⟩
  · rintro e ⟨z,hz,rfl⟩
    refine ⟨z,?_,rfl⟩
    rw [admissible_iff] at hz ⊢
    exact ⟨hz.1,fun A hA => hz.2 A (hFH hA)⟩
end
end CannonCells

namespace CannonUniformization
open Set Metric Filter Topology unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X] [PathConnectedSpace X]

theorem annular_modulus_smallness (Q : ℕ) (CP L a : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hL : 1 ≤ L) (ha : 1 < a) (hdiam1 : diam (univ : Set X) ≤ 1)
    (hsim : ∀ o : X, ∀ s : ℝ, 0 < s → s ≤ diam (univ : Set X) →
      ∃ f : X ≃ₜ X, ∀ x ∈ ball o s, ∀ y ∈ ball o s,
        dist (f x) (f y)*s ≤ L*dist x y ∧ dist x y ≤ L*dist (f x) (f y)*s)
    (ι : ℕ → Type*) [∀ m, Fintype (ι m)] (p : ∀ m, ι m → X)
    (hpsep : ∀ m i j, i ≠ j → (a^m)⁻¹ ≤ dist (p m i) (p m j))
    (hpnet : ∀ m x, ∃ i, dist (p m i) x ≤ (a^m)⁻¹)
    (d B : ℝ) (hd : 0 < d) (hdiam : d < diam (univ : Set X)) (hdL : d ≤ 1/(4*L))
    (hB : ∀ m, modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (macroFamily d) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ ratio : ℝ, 1 < ratio ∧ ∀ R : ℝ,
      0 < R → R ≤ diam (univ : Set X) → ∀ᶠ m : ℕ in atTop, ∀ o : X,
        modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (annulusFamily o (R/ratio) R) < ε := by
  classical
  obtain ⟨E,hE,hdecay⟩ := annular_modulus_decay Q CP L a hpack hCP hL ha hsim
    ι p hpsep hpnet d B hd hdiam hdL hB
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_gt (E*B/ε)
  have hnε : E*B/(n+1:ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < n+1)]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith
  obtain ⟨ℓ,hℓ⟩ := pow_unbounded_of_one_lt (8:ℝ) ha
  let ratio := 8*a*a^(ℓ*n)
  have hap : 0 < a := zero_lt_one.trans ha
  have hpow : 1 ≤ a^(ℓ*n) := one_le_pow₀ ha.le
  have hratio : 1 < ratio := by dsimp [ratio]; nlinarith
  refine ⟨ratio,hratio,?_⟩
  intro R hR hRdia
  obtain ⟨k₀,hklo,hkhi⟩ := CannonNet.exists_scale_below ha
    (show 0 < R/4 by positivity) (show R/4 ≤ 1 by linarith [hRdia.trans hdiam1])
  have hk₀ : 4*(a^k₀)⁻¹ ≤ diam (univ : Set X) := by linarith
  have hr : R/ratio ≤ (a^(k₀+ℓ*n))⁻¹ := by
    rw [pow_add,mul_inv]
    have h₁ : R/(8*a) ≤ (a^k₀)⁻¹ := by
      have hid : R/4/a=R/(4*a) := by ring
      rw [hid] at hklo
      have hh : R/(8*a) ≤ R/(4*a) := div_le_div_of_nonneg_left hR.le (by positivity) (by nlinarith)
      exact hh.trans hklo.le
    have hh := mul_le_mul_of_nonneg_right h₁ (inv_nonneg.mpr (pow_nonneg hap.le (ℓ*n)))
    calc
      R/ratio = (R/(8*a))*(a^(ℓ*n))⁻¹ := by dsimp [ratio]; ring
      _ ≤ (a^k₀)⁻¹*(a^(ℓ*n))⁻¹ := hh
  have ht := hdecay ℓ k₀ n hℓ.le hk₀
  filter_upwards [ht] with m hm
  intro o
  have hmono : modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (annulusFamily o (R/ratio) R) ≤
      modulus (fun i => ball (p m i) (2*(a^m)⁻¹))
        (annulusFamily o (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹)) := by
    apply modulus_family_mono _ ?_ ?_ ?_
    · intro x
      obtain ⟨i,hi⟩ := hpnet m x
      refine ⟨i,?_⟩
      change dist x (p m i) < _
      rw [dist_comm]
      have hh : 0 < (a^m)⁻¹ := inv_pos.mpr (pow_pos hap _)
      linarith
    · rintro A ⟨u,v,p,rfl,hu,hv⟩
      exact ⟨u,v,p,rfl,hu.trans hr,(show 2*(a^k₀)⁻¹ ≤ R by linarith).trans hv⟩
    · rintro A ⟨u,v,p,rfl,_,_⟩
      exact range_nonempty p
  exact (hmono.trans (hm o)).trans_lt hnε

end
end CannonUniformization

end
namespace CannonRelease
open CannonGraph CannonVisual CannonGeometry CannonNet CannonCells CannonCharts
open Set Metric Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_annular_modulus_smallness (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    ∃ T : ℕ → Finset (Boundary D),
      (∀ n, (∀ x ∈ T n, ∀ y ∈ T n, x ≠ y → (a^n)⁻¹ ≤ dist x y) ∧
        (∀ x, ∃ y ∈ T n, dist y x ≤ (a^n)⁻¹)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ratio : ℝ, 1 < ratio ∧ ∀ R : ℝ,
        0 < R → R ≤ diam (univ : Set (Boundary D)) →
        ∀ᶠ m : ℕ in atTop, ∀ o : Boundary D,
          modulus (fun i : T m => ball i.val (2*(a^m)⁻¹))
            (CannonUniformization.annulusFamily o (R/ratio) R) < ε := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonCharts.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) :=
    φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  let a := Real.exp (2*visualExponent δ)
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hLE : 0 < LE := by dsimp [LE]; positivity
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  obtain ⟨T,hT⟩ := exists_net_sequence (X:=Boundary D) ha
  obtain ⟨L,hL,hsim⟩ := boundary_approx_self_similar D hδ
  obtain ⟨Q,CP,hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  have hdia1 : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _ => boundaryDist_le_one D hδ x y)
  have hdia : 0 < diam (univ : Set (Boundary D)) := by
    apply diam_pos ?_ (isCompact_univ.isBounded)
    let v : SphereTwo := ⟨EuclideanSpace.single 0 1,by simp⟩
    let w : SphereTwo := ⟨EuclideanSpace.single 0 (-1),by simp⟩
    refine ⟨φ.symm v,mem_univ _,φ.symm w,mem_univ _,?_⟩
    intro hh
    have he := congrArg (fun z : SphereTwo => z.val 0) (φ.symm.injective hh)
    norm_num [v,w] at he
  let d := min (diam (univ : Set (Boundary D))/2) (min (1/(LE*3^2)) (1/(4*L)))
  have hd : 0 < d := by dsimp [d]; exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hddia : d < diam (univ : Set (Boundary D)) :=
    (min_le_left _ _).trans_lt (by linarith)
  have hdLE : d ≤ 1/(LE*3^2) := (min_le_right _ _).trans (min_le_left _ _)
  have hdL : d ≤ 1/(4*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hsep (n : ℕ) (i j : T n) (hij : i ≠ j) : (a^n)⁻¹ ≤ dist i.val j.val :=
    (hT n).1 i.val i.property j.val j.property (fun hh => hij (Subtype.ext hh))
  have hnet (n : ℕ) (x : Boundary D) : ∃ i : T n, dist i.val x ≤ (a^n)⁻¹ := by
    obtain ⟨y,hy,hh⟩ := (hT n).2 x
    exact ⟨⟨y,hy⟩,hh⟩
  obtain ⟨B,hB⟩ := boundary_modulus_bounded D hδ φ d hd hddia hdLE
    (fun n => ↥(T n)) (fun n i => i.val) hsep hnet
  exact ⟨T,hT,CannonUniformization.annular_modulus_smallness Q CP L a hpack hCP.le hL ha
    hdia1 hsim (fun n => ↥(T n)) (fun n i => i.val) hsep hnet d B hd hddia hdL hB⟩

end CannonRelease

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_EventualRelativeShrink
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
namespace CannonRealization
open Set Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y]

omit [CompactSpace X] in
lemma EventualRelativeShrink.equicontinuous {F : ℕ → C(X,Y)}
    (hF : EventualRelativeShrink F) {p q : X} (hpq : p≠q) :
    Equicontinuous (fun n x => F n x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let B := diam (univ : Set Y)+1
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨τ,hτ,hτF⟩ := hF (ε/(2*B)) (by positivity)
  let R := dist p q/2
  have hR : 0<R := half_pos (dist_pos.mpr hpq)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hτF R hR)
  have hb : ∃ b : X, R≤dist x b := by
    by_cases hp : R≤dist x p
    · exact ⟨p,hp⟩
    · refine ⟨q,?_⟩
      have hh := dist_triangle p x q
      rw [dist_comm p x] at hh
      dsimp [R] at *
      linarith
  obtain ⟨b,hb⟩ := hb
  have hfinite : ∀ᶠ a in 𝓝 x, ∀ n ∈ Finset.range N, dist (F n x) (F n a)<ε := by
    apply (eventually_all_finset _).mpr
    intro n _
    simpa only [mem_ball,dist_comm] using
      (F n).continuous.continuousAt.eventually (ball_mem_nhds (F n x) hε)
  filter_upwards [hfinite,ball_mem_nhds x (mul_pos hτ hR)] with a ha hnear n
  by_cases hn : n<N
  · exact ha n (by simpa using hn)
  · have hsmall : dist x a≤τ*R := by simpa only [mem_ball,dist_comm] using (mem_ball.mp hnear).le
    have hh := hN n (le_of_not_gt hn) x a b hsmall hb
    have hdist : dist (F n x) (F n b)≤B :=
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans (by dsimp [B]; linarith)
    have hh' := mul_le_mul_of_nonneg_left hdist (show 0≤ε/(2*B) by positivity)
    have he : (ε/(2*B))*B=ε/2 := by field_simp
    rw [he] at hh'
    exact (hh.trans hh').trans_lt (half_lt_self hε)

lemma compact_map_subsequence (F : ℕ → C(X,Y))
    (heq : Equicontinuous (fun n x => F n x)) :
    ∃ f : C(X,Y), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 f) := by
  classical
  have : T2Space (UniformOnFun X Y {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X,Y) => (g : X → Y)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      have hindex : ∀ g : range F, ∃ n, F n=g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range F => (g.val : X → Y)) := by
        convert heq' using 1
        all_goals try with_reducible_and_instances rfl
        funext g x
        exact congrArg (fun h : C(X,Y) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _ x _
      exact ⟨univ,isCompact_univ,subset_univ _⟩
  obtain ⟨f,_,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨f,φ,hφ,ht⟩

omit [CompactSpace X] [CompactSpace Y] in
lemma EventualRelativeShrink.limit {F : ℕ → C(X,Y)} (hF : EventualRelativeShrink F)
    {f : C(X,Y)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (ht : Tendsto (F ∘ φ) atTop (𝓝 f)) : RelativeShrink f := by
  intro ε hε
  obtain ⟨τ,hτ,hbound⟩ := hF ε hε
  refine ⟨τ,hτ,?_⟩
  intro x a b hdist
  by_cases hb : x=b
  · subst b
    have ha : x=a := dist_le_zero.mp (by simpa using hdist)
    simp [←ha]
  · have heval (z : X) : Tendsto (fun n => F (φ n) z) atTop (𝓝 (f z)) :=
      (continuous_eval_const z).tendsto f |>.comp ht
    apply le_of_tendsto_of_tendsto ((heval x).dist (heval a))
      (((heval x).dist (heval b)).const_mul ε)
    exact (hφ.tendsto_atTop.eventually (hbound (dist x b) (dist_pos.mpr hb))).mono
      (fun n hn => hn x a b hdist le_rfl)

omit [CompactSpace X] [CompactSpace Y] in
theorem RelativeShrink.injective [PreconnectedSpace X] {f : C(X,Y)}
    (hf : RelativeShrink f) {p q : X} (hpq : f p≠f q) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  let S : Set X := {z | f z=f x}
  have hxS : x∈S := rfl
  have hyS : y∈S := hxy.symm
  have hSc : IsClosed S := isClosed_eq f.continuous continuous_const
  obtain ⟨τ,hτ,hbound⟩ := hf 1 zero_lt_one
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hw : ∃ w : X, w∈S ∧ z≠w := by
      by_cases hzx : z=x
      · exact ⟨y,hyS,by simpa [hzx] using hne⟩
      · exact ⟨x,hxS,hzx⟩
    obtain ⟨w,hw,hzw⟩ := hw
    apply mem_of_superset (ball_mem_nhds z (mul_pos hτ (dist_pos.mpr hzw)))
    intro a ha
    have hh := hbound z a w (by simpa only [mem_ball,dist_comm] using (mem_ball.mp ha).le)
    have hzw' : f z=f w := hz.trans hw.symm
    rw [hzw',dist_self,mul_zero] at hh
    have he : f w=f a := dist_le_zero.mp hh
    exact he.symm.trans hw
  have hSu : S=univ := IsClopen.eq_univ ⟨hSc,hSo⟩ ⟨x,hxS⟩
  have hp : p∈S := hSu ▸ mem_univ p
  have hq : q∈S := hSu ▸ mem_univ q
  exact hpq (hp.trans hq.symm)

omit [CompactSpace Y] in
lemma surjective_limit {F : ℕ → C(X,Y)} (hF : ∀ n, Function.Surjective (F n))
    {f : C(X,Y)} {φ : ℕ → ℕ} (ht : Tendsto (F ∘ φ) atTop (𝓝 f)) :
    Function.Surjective f := by
  intro y
  choose x hx using fun n => hF (φ n) y
  obtain ⟨z,_,ψ,hψ,hz⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (x n))
  have ht' := ht.comp hψ.tendsto_atTop
  have he := continuous_eval.tendsto (f,z) |>.comp (ht'.prodMk_nhds hz)
  have hy : Tendsto (fun _ : ℕ => y) atTop (𝓝 (f z)) := by
    simpa only [Function.comp_def,hx] using he
  exact ⟨z,tendsto_nhds_unique hy tendsto_const_nhds⟩

end CannonRealization

end
end
section
noncomputable section
open Set Metric

namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma radial_point [PreconnectedSpace Y] (u v : Y) {r : ℝ}
    (hr : 0 ≤ r) (hrv : r≤dist u v) : ∃ w : Y, dist u w=r := by
  have hh := isPreconnected_univ.intermediate_value (mem_univ u) (mem_univ v)
    ((continuous_const.dist continuous_id).continuousOn : ContinuousOn (fun w : Y => dist u w) univ)
  obtain ⟨w,_,hw⟩ := hh (by simpa only [id_eq,dist_self,mem_Icc] using And.intro hr hrv)
  exact ⟨w,hw⟩

theorem inverse_weakQS_ratio_bound [PreconnectedSpace Y]
    (f : X ≃ₜ Y) {Q : ℕ} {C H : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) (hH : 1≤H)
    (hf : WeakQS f.symm H) {t : ℝ} (ht : 1≤t) :
    ∃ K : ℝ, 0<K ∧ ∀ x a b : X, dist x a≤t*dist x b →
      dist (f x) (f a)≤K*dist (f x) (f b) := by
  classical
  have hHp : 0<H := zero_lt_one.trans_le hH
  have htp : 0<t := zero_lt_one.trans_le ht
  obtain ⟨N,hN⟩ := exists_nat_ge (C*(H^3*t)^Q)
  refine ⟨(2:ℝ)^N,pow_pos (by norm_num) _,?_⟩
  intro x a b hab
  by_cases hxb : x=b
  · subst b
    have hxa : x=a := dist_le_zero.mp (by simpa only [dist_self,mul_zero] using hab)
    simp [←hxa]
  have hR : 0<dist x b := dist_pos.mpr hxb
  have hB : 0<dist (f x) (f b) := dist_pos.mpr (fun hh => hxb (f.injective hh))
  by_contra hn
  have hlarge : (2:ℝ)^N*dist (f x) (f b) ≤ dist (f x) (f a) := (lt_of_not_ge hn).le
  have hpoints (i : Fin (N+1)) : ∃ z : Y, dist (f x) z=(2:ℝ)^i.val*dist (f x) (f b) := by
    apply radial_point (f x) (f a) (by positivity)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (Nat.le_of_lt_succ i.isLt)) hB.le).trans hlarge
  choose z hz using hpoints
  let p (i : Fin (N+1)) : X := f.symm (z i)
  let R := dist x b
  let r := min (H*t*R) 1
  let s := R/H^2
  have hs : 0 < s := div_pos hR (sq_pos_of_pos hHp)
  have hH2 : 1≤H^2 := one_le_pow₀ hH
  have hsR : s≤R := by
    apply (div_le_iff₀ (sq_pos_of_pos hHp)).mpr
    exact le_mul_of_one_le_right hR.le hH2
  have hRHt : R≤H*t*R := by
    exact le_mul_of_one_le_left hR.le (one_le_mul_of_one_le_of_one_le hH ht)
  have hsr : s ≤ r := le_min (hsR.trans hRHt) (hsR.trans (hdiam x b))
  have hball (i : Fin (N+1)) : dist x (p i) ≤ r := by
    have htop : dist (f x) (z i)≤dist (f x) (f a) := by
      rw [hz]
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
        (Nat.le_of_lt_succ i.isLt)) hB.le).trans hlarge
    have hh := hf (f x) (z i) (f a) htop
    simp only [f.symm_apply_apply] at hh
    have hh' : dist x (p i)≤H*t*R := by
      exact hh.trans (by dsimp [R]; nlinarith [mul_le_mul_of_nonneg_left hab hHp.le])
    exact le_min hh' (hdiam x (p i))
  have hlower (i : Fin (N+1)) : R≤H*dist x (p i) := by
    have hh := hf (f x) (f b) (z i) (by
      rw [hz]
      exact le_mul_of_one_le_left hB.le (one_le_pow₀ (by norm_num)))
    simpa only [f.symm_apply_apply] using hh
  have hsep_le (i j : Fin (N+1)) (hij : i.val<j.val) : s≤dist (p i) (p j) := by
    have hpow : 2*((2:ℝ)^i.val) ≤ (2:ℝ)^j.val := by
      rw [mul_comm,←pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij)
    have hzi : dist (z i) (f x)≤dist (z i) (z j) := by
      have hh := dist_triangle (f x) (z i) (z j)
      rw [hz i,hz j] at hh
      rw [dist_comm, hz i]
      nlinarith [mul_le_mul_of_nonneg_right hpow hB.le]
    have hh := hf (z i) (f x) (z j) hzi
    simp only [f.symm_apply_apply] at hh
    change dist (p i) x≤H*dist (p i) (p j) at hh
    rw [dist_comm (p i) x] at hh
    apply (div_le_iff₀ (sq_pos_of_pos hHp)).mpr
    have hl := hlower i
    nlinarith [mul_le_mul_of_nonneg_left hh hHp.le]
  have hsep (i j : Fin (N+1)) (hij : i≠j) : s≤dist (p i) (p j) := by
    rcases lt_or_gt_of_ne (fun hh => hij (Fin.ext hh)) with hh|hh
    · exact hsep_le i j hh
    · simpa only [dist_comm] using hsep_le j i hh
  have hh := CannonPacking.indexed_packing Q C hpack p Finset.univ x r s hs hsr
    (min_le_right _ _) (fun i _ => hball i) (fun i _ j _ hij => hsep i j hij)
  have hratio : r/s≤H^3*t := by
    apply (div_le_iff₀ hs).mpr
    have he : H^3*t*s=H*t*R := by dsimp [s]; field_simp
    rw [he]
    exact min_le_left _ _
  have htotal : (N+1:ℕ)≤C*(H^3*t)^Q := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (hs.le.trans hsr) hs.le) hratio Q) hC)
  have hhN : (N:ℝ)+1≤C*(H^3*t)^Q := by exact_mod_cast htotal
  linarith

end CannonRealization

end
end
noncomputable section
namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.inverse_weakQS (f : X ≃ₜ Y) (hf : RelativeShrink f) :
    ∃ H : ℝ, 1≤H ∧ WeakQS f.symm H := by
  obtain ⟨τ,hτ,hbound⟩ := hf (1/2) (by norm_num)
  refine ⟨max 1 τ⁻¹,le_max_left _ _,?_⟩
  intro x a b hab
  by_cases ha : x=a
  · subst a
    simp only [dist_self]
    positivity
  have hA : 0<dist x a := dist_pos.mpr ha
  have hh : τ*dist (f.symm x) (f.symm a)≤dist (f.symm x) (f.symm b) := by
    by_contra! hn
    have hz := hbound (f.symm x) (f.symm b) (f.symm a) hn.le
    simp only [f.apply_symm_apply] at hz
    linarith
  have hh' : dist (f.symm x) (f.symm a)≤τ⁻¹*dist (f.symm x) (f.symm b) := by
    have hz := (le_div_iff₀ hτ).mpr (show dist (f.symm x) (f.symm a)*τ≤dist (f.symm x) (f.symm b) by nlinarith [hh])
    simpa only [div_eq_mul_inv,mul_comm] using hz
  exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

theorem RelativeShrink.forward_ratio_bounds [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {C : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) :
    ∀ t : ℝ, 1≤t → ∃ K : ℝ, 0<K ∧ ∀ x a b : X,
      dist x a≤t*dist x b → dist (f x) (f a)≤K*dist (f x) (f b) := by
  obtain ⟨H,hH,hInv⟩ := hf.inverse_weakQS f
  intro t ht
  exact inverse_weakQS_ratio_bound f hpack hC hdiam hH hInv ht

theorem RelativeShrink.forward_weakQS [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {C : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) :
    ∃ H : ℝ, 1≤H ∧ WeakQS f H := by
  obtain ⟨K,hK,hbound⟩ := hf.forward_ratio_bounds f hpack hC hdiam 1 le_rfl
  refine ⟨max 1 K,le_max_left _ _,?_⟩
  intro x a b hab
  exact (hbound x a b (by simpa only [one_mul] using hab)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

end CannonRealization

namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma small_scale_geometric [PreconnectedSpace X] {f : X → Y} {H τ : ℝ}
    (_hH : 0≤H) (hf : WeakQS f H) (hτ : 0<τ) (hτ1 : τ≤1)
    (hc : ∀ x a b, dist x a≤τ*dist x b →
      dist (f x) (f a)≤(1/2:ℝ)*dist (f x) (f b))
    (n : ℕ) (x a b : X) (ha : dist x a≤τ^n*dist x b) :
    dist (f x) (f a)≤H*(1/2:ℝ)^n*dist (f x) (f b) := by
  induction n generalizing a with
  | zero => simpa only [pow_zero,mul_one,one_mul] using hf x a b (by simpa using ha)
  | succ n ih =>
    obtain ⟨c,hcR⟩ := radial_point x b (show 0≤τ^n*dist x b by positivity)
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hτ.le hτ1))
    have hh := hc x a c (by rw [hcR]; simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using ha)
    have hh' := ih c hcR.le
    rw [pow_succ]
    nlinarith

lemma large_scale_geometric [PreconnectedSpace X] {f : X → Y} {K : ℝ}
    (hK : 0≤K)
    (hf : ∀ x a b, dist x a≤2*dist x b → dist (f x) (f a)≤K*dist (f x) (f b))
    (n : ℕ) (x a b : X) (ha : dist x a≤(2:ℝ)^n*dist x b) :
    dist (f x) (f a)≤K^(n+1)*dist (f x) (f b) := by
  induction n generalizing a with
  | zero =>
    simpa only [zero_add,pow_one] using hf x a b (by simp only [pow_zero,one_mul] at ha; nlinarith [dist_nonneg (x:=x) (y:=b)])
  | succ n ih =>
    obtain ⟨c,hc⟩ := radial_point x a (show 0≤dist x a/2 by positivity) (by nlinarith [dist_nonneg (x:=x) (y:=a)])
    have h1 := hf x a c (by rw [hc]; linarith)
    have h2 := ih c (by rw [hc]; rw [pow_succ] at ha; nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    rw [pow_succ K (n+1)]
    nlinarith

theorem relative_small_power [PreconnectedSpace X] {f : X → Y} {H : ℝ}
    (hH : 0<H) (hf : WeakQS f H) (hshrink : RelativeShrink f) :
    ∃ α : ℝ, 0<α ∧ α≤1 ∧ ∀ t : ℝ, 0<t → t≤1 → ∀ x a b : X,
      dist x a≤t*dist x b →
      dist (f x) (f a)≤2*H*t^α*dist (f x) (f b) := by
  obtain ⟨τ,hτ,hc⟩ := hshrink (1/2) (by norm_num)
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (lt_min hτ (by norm_num : (0:ℝ)<1)) (by norm_num : (1/2:ℝ)<1)
  have hk0 : k≠0 := by intro h; subst k; norm_num at hk
  have hkpos : 0<k := Nat.pos_of_ne_zero hk0
  let σ : ℝ := (1/2:ℝ)^k
  have hσ : 0<σ := pow_pos (by norm_num) _
  have hστ : σ≤τ := hk.le.trans (min_le_left _ _)
  have hσ1 : σ<1 := hk.trans_le (min_le_right _ _)
  have hak : 0<(k:ℝ) := by exact_mod_cast hkpos
  have ha : 0<(k:ℝ)⁻¹ := inv_pos.mpr hak
  refine ⟨(k:ℝ)⁻¹,ha,?_,?_⟩
  · apply inv_le_one_of_one_le₀
    exact_mod_cast hkpos
  · intro t ht ht1 x a b hab
    obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near_of_lt_one ht ht1 hσ hσ1
    have hgeom := small_scale_geometric hH.le hf hσ hσ1.le (fun x a b hh =>
      hc x a b (hh.trans (mul_le_mul_of_nonneg_right hστ dist_nonneg))) n x a b
      (hab.trans (mul_le_mul_of_nonneg_right hnup dist_nonneg))
    have hid : σ^(k:ℝ)⁻¹=(1/2:ℝ) := Real.pow_rpow_inv_natCast (by norm_num) hk0
    have hp : (1/2:ℝ)^(n+1)≤t^(k:ℝ)⁻¹ := by
      have hh := Real.rpow_le_rpow (pow_nonneg hσ.le _) hnlow.le ha.le
      rw [←Real.rpow_pow_comm hσ.le,hid] at hh
      exact hh
    have hp' : (1/2:ℝ)^n≤2*t^(k:ℝ)⁻¹ := by rw [pow_succ] at hp; linarith
    exact hgeom.trans (by nlinarith [mul_le_mul_of_nonneg_left hp' (mul_nonneg hH.le (dist_nonneg (x:=f x) (y:=f b)))])

theorem relative_large_power [PreconnectedSpace X] {f : X → Y} {K : ℝ}
    (hK : 0<K)
    (hf : ∀ x a b, dist x a≤2*dist x b → dist (f x) (f a)≤K*dist (f x) (f b)) :
    ∃ β : ℕ, 0<β ∧ ∀ t : ℝ, 1≤t → ∀ x a b : X,
      dist x a≤t*dist x b →
      dist (f x) (f a)≤K^2*t^β*dist (f x) (f b) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (max K 1) (by norm_num : (1:ℝ)<2)
  have hk0 : 0<k := by
    by_contra! h
    have hz : k=0 := Nat.eq_zero_of_le_zero h
    rw [hz,pow_zero] at hk
    exact (not_lt_of_ge (le_max_right K 1)) hk
  have hkK : K≤(2:ℝ)^k := (le_max_left _ _).trans hk.le
  refine ⟨k,hk0,?_⟩
  intro t ht x a b hab
  obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near ht (by norm_num : (1:ℝ)<2)
  have hgeom := large_scale_geometric hK.le hf (n+1) x a b
    (hab.trans (mul_le_mul_of_nonneg_right hnup.le dist_nonneg))
  have hpow : K^n≤t^k := by
    calc
      _ ≤ ((2:ℝ)^k)^n := pow_le_pow_left₀ hK.le hkK _
      _ = ((2:ℝ)^n)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ t^k := pow_le_pow_left₀ (by positivity) hnlow _
  have hbound := mul_le_mul_of_nonneg_left hpow (sq_nonneg K)
  have he : K^(n+1+1)=K^2*K^n := by rw [show n+1+1=2+n by omega,pow_add]
  rw [he] at hgeom
  exact hgeom.trans (by nlinarith [mul_le_mul_of_nonneg_right hbound (dist_nonneg (x:=f x) (y:=f b))])

end CannonRealization

end
end
section
noncomputable section
namespace CannonDistortion
open Set
open scoped NNReal

lemma powerIso_coe (C : ℝ≥0) (hC : 0<C) (α β : ℝ) (hα : 0<α) (hβ : 0<β) (t : ℝ≥0) :
    ((powerIso C hC α β hα hβ t : ℝ≥0) : ℝ)=(C:ℝ)*powerGauge α β t := by
  rfl

lemma powerGauge_nonneg {α β t : ℝ} (ht : 0 ≤ t) : 0 ≤ powerGauge α β t :=
  (Real.rpow_nonneg ht α).trans (le_max_left _ _)

theorem mixed_power_bound {α β r : ℝ} (_hα : 0<α) (_hβ : 0<β) (hab : α ≤ β) (hr : 0 < r) :
    powerGauge α β (Real.sqrt r)*powerGauge α β (5*max r 1)  ≤
      (5:ℝ)^β*powerGauge (α/2) (3*β/2) r := by
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hbig : 1 ≤ 5*max r 1 := by nlinarith [le_max_right r 1]
  have hgb : powerGauge α β (5*max r 1)=(5*max r 1)^β :=
    max_eq_right (Real.rpow_le_rpow_of_exponent_le hbig hab)
  rw [hgb]
  rcases le_total r 1 with hr1|h1r
  · have hs1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
    have hgs : powerGauge α β (Real.sqrt r)=(Real.sqrt r)^α :=
      max_eq_left (Real.rpow_le_rpow_of_exponent_ge hs hs1 hab)
    rw [hgs,max_eq_right hr1,mul_one]
    have he : (Real.sqrt r)^α=r^(α/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
      congr 1
      ring
    rw [he,mul_comm]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg (by norm_num) β)
  · have hs1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h1r
    have hgs : powerGauge α β (Real.sqrt r)=(Real.sqrt r)^β :=
      max_eq_right (Real.rpow_le_rpow_of_exponent_le hs1 hab)
    rw [hgs,max_eq_left h1r,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5) hr.le]
    have he : (Real.sqrt r)^β*(5^β*r^β)=5^β*r^(3*β/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
      calc
        _ = 5^β*(r^((1/2:ℝ)*β)*r^β) := by ring
        _ = 5^β*r^((1/2:ℝ)*β+β) := by rw [Real.rpow_add hr]
        _ = _ := by congr 2; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg (by norm_num) β)

end CannonDistortion

end
end
namespace CannonRealization
open CannonDistortion Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.power_control [PreconnectedSpace X] [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {P : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q P) (hP : 0 ≤ P)
    (hdiam : ∀ x y : X, dist x y ≤ 1) :
    ∃ C α β : ℝ, 0<C ∧ 0<α ∧ α ≤ β ∧ 0<β ∧ ∀ t : ℝ, 0 ≤ t → ∀ x a b : X,
      dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ C*powerGauge α β t*dist (f x) (f b) := by
  obtain ⟨H,hH,hweak⟩ := hf.forward_weakQS f hpack hP hdiam
  have hHp : 0<H := zero_lt_one.trans_le hH
  obtain ⟨α,hα,hα1,hsmall⟩ := relative_small_power hHp hweak hf
  obtain ⟨K,hK,hKbound⟩ := hf.forward_ratio_bounds f hpack hP hdiam 2 (by norm_num)
  obtain ⟨β,hβ,hlarge⟩ := relative_large_power hK hKbound
  have hβ1 : (1:ℝ) ≤ (β:ℝ) := by exact_mod_cast hβ
  let C := max (2*H) (K^2)
  have hC : 0<C := (mul_pos (by norm_num) hHp).trans_le (le_max_left _ _)
  refine ⟨C,α,(β:ℝ),hC,hα,hα1.trans hβ1,zero_lt_one.trans_le hβ1,?_⟩
  intro t ht x a b hab
  by_cases ht0 : t=0
  · subst t
    have hxa : x=a := dist_le_zero.mp (by simpa only [zero_mul] using hab)
    rw [←hxa,dist_self]
    exact mul_nonneg (mul_nonneg hC.le (powerGauge_nonneg (by norm_num))) dist_nonneg
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  rcases le_total t 1 with ht1|h1t
  · have hh := hsmall t htp ht1 x a b hab
    apply hh.trans
    have hleft : 2*H*t^α ≤ C*powerGauge α (β:ℝ) t :=
      mul_le_mul (le_max_left _ _) (le_max_left _ _) (Real.rpow_nonneg ht _) hC.le
    exact mul_le_mul_of_nonneg_right hleft dist_nonneg
  · have hh := hlarge t h1t x a b hab
    apply hh.trans
    have hright : K^2*t^β ≤ C*powerGauge α (β:ℝ) t := by
      rw [←Real.rpow_natCast t β]
      exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (Real.rpow_nonneg ht _) hC.le
    exact mul_le_mul_of_nonneg_right hright dist_nonneg

end CannonRealization

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryEventualRelativeShrink
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Filter Topology CannonGraph CannonVisual CannonMobius CannonCells CannonUniformization
open CannonRealization

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_eventual_relative_shrink (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ F : ℕ → C(Boundary D,Sphere),(∀ n,Function.Surjective (F n)) ∧
      EventualRelativeShrink F := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,LI,σ,s,r₀,Z,hL,hLI,hσ,hσ1,hs,hr₀,hZ,V,hV,htests⟩ :=
    boundary_packing_relative_tests D hδ φ
  obtain ⟨T,hT,hmod⟩ := boundary_annular_modulus_smallness D hδ φ
  let α := Real.exp (2*visualExponent δ)
  have hα : 1<α := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let mesh : ℕ → ℝ := fun n => (α^n)⁻¹
  have hmpos (n : ℕ) : 0 < mesh n := inv_pos.mpr (pow_pos (zero_lt_one.trans hα) _)
  have hmt : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr (zero_lt_one.trans hα)).le (inv_lt_one_of_one_lt₀ hα)
  have hmaps : ∀ n : ℕ, ∃ g : C(Boundary D,Sphere),Function.Surjective g ∧
      (mesh n ≤ r₀ → (∀ x y,g x=g y → dist x y ≤ 2*(L*mesh n)) ∧
      ∀ (o a b : Boundary D) (r R ε : ℝ),0 < r → 0<R → R ≤ s →
        dist o a ≤ r → R ≤ dist o b → 0<dist (g o) (g b) → 0<ε →
        ε*dist (g o) (g b)<dist (g o) (g a) →
      V ε ≤ Z*modulus (fun i : T n =>ball i.val (2*mesh n)) (annulusFamily o (LI*r) (σ*R))) := by
    intro n
    by_cases hn : mesh n ≤ r₀
    · obtain ⟨g,hgs,hgf,hgc⟩ := htests (mesh n) (hmpos n) hn (T n) (hT n).1
        (fun x=>by obtain ⟨y,hy,hyx⟩ := (hT n).2 x; exact ⟨y,hy,by rwa [dist_comm]⟩)
      exact ⟨g,hgs,fun _=>⟨hgf,hgc⟩⟩
    · let g := φ.trans roundChart.symm
      exact ⟨⟨g,g.continuous⟩,g.surjective,fun h=>False.elim (hn h)⟩
  choose F hsurj hprops using hmaps
  refine ⟨F,hsurj,?_⟩
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hLIp : 0<LI := zero_lt_one.trans_le hLI
  have hdia1 : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _=>boundaryDist_le_one D hδ x y)
  intro ε hε
  let tol := V ε/(Z+1)
  have htol : 0<tol := div_pos (hV ε hε) (by linarith)
  obtain ⟨ratio,hratio,hsmall⟩ := hmod tol htol
  have hratiop : 0 < ratio := zero_lt_one.trans hratio
  let k := min 1 s
  have hk : 0<k := lt_min zero_lt_one hs
  let τ := σ*k/(ratio*LI)
  have hτ : 0<τ := div_pos (mul_pos hσ hk) (mul_pos hratiop hLIp)
  refine ⟨τ,hτ,?_⟩
  intro R hR
  by_cases hRD : R ≤ diam (univ : Set (Boundary D))
  · let S := min R s
    have hS : 0<S := lt_min hR hs
    have hSR : S ≤ R := min_le_left _ _
    have hSs : S ≤ s := min_le_right _ _
    have hR1 : R ≤ 1 := hRD.trans hdia1
    have hkR : k*R ≤ S := by
      apply le_min
      · exact mul_le_of_le_one_left hR.le (min_le_left _ _)
      · calc
          k*R ≤ s*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
          _ ≤ s := mul_le_of_le_one_right hs.le hR1
    let outer := σ*S
    have hout : 0<outer := mul_pos hσ hS
    have houtR : outer ≤ R := (mul_le_of_le_one_left hS.le hσ1).trans hSR
    let r := (outer/ratio)/LI
    have hr : 0 < r := div_pos (div_pos hout hratiop) hLIp
    have hrad : LI*r = outer/ratio := by dsimp [r]; field_simp
    have hnear : τ*R ≤ r := by
      calc
        τ*R = (σ*(k*R)/ratio)/LI := by dsimp [τ]; ring
        _ ≤ (σ*S/ratio)/LI := by gcongr
    have hgood : ∀ᶠ n : ℕ in atTop,mesh n ≤ r₀ :=
      (hmt.eventually (gt_mem_nhds hr₀)).mono (fun _ h=>h.le)
    have hfine : ∀ᶠ n : ℕ in atTop,mesh n < R/(2*L) :=
      hmt.eventually (gt_mem_nhds (div_pos hR (by positivity)))
    filter_upwards [hgood,hfine,hsmall outer hout (houtR.trans hRD)] with n hn hnf hnm
    intro o a b hoa hob
    have hden : 0<dist (F n o) (F n b) := by
      apply dist_pos.mpr
      intro heq
      have hf := (hprops n hn).1 o b heq
      have hm := (lt_div_iff₀ (show 0<2*L by positivity)).mp hnf
      nlinarith
    by_contra hfail
    have hcost := (hprops n hn).2 o a b r S ε hr hS hSs (hoa.trans hnear) (hSR.trans hob)
      hden hε (lt_of_not_ge hfail)
    rw [hrad] at hcost
    have hbound := mul_le_mul_of_nonneg_left (hnm o).le hZ
    have hid : tol*(Z+1)=V ε := by dsimp [tol]; field_simp
    nlinarith
  · filter_upwards [] with n o a b hoa hob
    exact False.elim (hRD (hob.trans (dist_le_diam_of_mem isCompact_univ.isBounded
      (mem_univ _) (mem_univ _))))
end CannonRelease

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

lemma nndist_pos {X : Type*} [MetricSpace X] {x y : X} : 0 < nndist x y ↔ x ≠ y := by
  rw [pos_iff_ne_zero,ne_eq,nndist_eq_zero]

lemma crossRatio_pos {X : Type*} [MetricSpace X] {x y z w : X}
    (h : Distinct x y z w) : 0 < crossRatio x y z w := by
  exact div_pos (mul_pos (nndist_pos.mpr h.1) (nndist_pos.mpr h.2.2.2.2.2))
    (mul_pos (nndist_pos.mpr h.2.2.1) (nndist_pos.mpr h.2.2.2.1))

end CannonQM

end
end
namespace CannonMetricQC
open Metric CannonQM

lemma cycle_sorted_bounds {a b c d T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hT : 1  ≤  T)
    (hab : a  ≤  b) (hcd : c  ≤  d) (hp : a*b  ≤  T*(c*d))
    (hbt : b  ≤  a+c+d) (hdt : d  ≤  a+b+c) :
    a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d := by
  have hT0 : 0 < T := by linarith
  constructor
  · by_contra hn
    have hn' : (2*T+3)*c < a := lt_of_not_ge hn
    have hhdt : d  ≤  2*b+c := by linarith
    have hm := mul_le_mul_of_nonneg_left hhdt (mul_nonneg hT0.le hc.le)
    have hTb : T*c < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hn') hb
    have hm2 := mul_pos (sub_pos.mpr hTb) hc
    nlinarith
  · by_contra hn
    have hn' : (2*T+3)*d < b := lt_of_not_ge hn
    have hha : T*d < a := by nlinarith
    have hhb : d < b := by nlinarith
    have hm1 := mul_pos (sub_pos.mpr hha) hb
    have hm2 := mul_nonneg (mul_nonneg hT0.le hd.le) (sub_nonneg.mpr hhb.le)
    have hm3 := mul_le_mul_of_nonneg_left hcd (mul_nonneg hT0.le hd.le)
    nlinarith

lemma crossRatio_pair_bounds {X : Type*} [MetricSpace X] (x y z w : X)
    (hh : Distinct x y z w) {T : ℝ} (hT : 1  ≤  T)
    (hp : dist x y*dist z w  ≤  T*(dist x w*dist y z)) :
    (dist x y  ≤  (2*T+3)*dist x w ∧ dist z w  ≤  (2*T+3)*dist y z) ∨
    (dist x y  ≤  (2*T+3)*dist y z ∧ dist z w  ≤  (2*T+3)*dist x w) := by
  let a := dist x y
  let b := dist z w
  let c := dist x w
  let d := dist y z
  have ha : 0 < a := dist_pos.mpr hh.1
  have hb : 0 < b := dist_pos.mpr hh.2.2.2.2.2
  have hc : 0 < c := dist_pos.mpr hh.2.2.1
  have hd : 0 < d := dist_pos.mpr hh.2.2.2.1
  have ht1 : a  ≤  b+c+d := by
    have h1 := dist_triangle x w y
    have h2 := dist_triangle w z y
    dsimp [a,b,c,d]
    rw [dist_comm w z,dist_comm z y] at h2
    linarith
  have ht2 : b  ≤  a+c+d := by
    have h1 := dist_triangle z y w
    have h2 := dist_triangle y x w
    dsimp [a,b,c,d]
    rw [dist_comm z y] at h1
    rw [dist_comm y x] at h2
    linarith
  have ht3 : c  ≤  a+b+d := by
    have h1 := dist_triangle x y w
    have h2 := dist_triangle y z w
    dsimp [a,b,c,d]
    linarith
  have ht4 : d  ≤  a+b+c := by
    have h1 := dist_triangle y x z
    have h2 := dist_triangle x w z
    dsimp [a,b,c,d]
    rw [dist_comm y x] at h1
    rw [dist_comm w z] at h2
    linarith
  change (a  ≤  (2*T+3)*c ∧ b  ≤  (2*T+3)*d) ∨
    (a  ≤  (2*T+3)*d ∧ b  ≤  (2*T+3)*c)
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · exact Or.inl (cycle_sorted_bounds ha hb hc hd hT hab hcd hp ht2 ht4)
  · exact Or.inr (cycle_sorted_bounds ha hb hd hc hT hab hdc (by nlinarith [hp])
      (by linarith) ht3)
  · have hh := cycle_sorted_bounds hb ha hc hd hT hba hcd (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inr ⟨hh.2,hh.1⟩
  · have hh := cycle_sorted_bounds hb ha hd hc hT hba hdc (by nlinarith [hp])
      (by linarith) (by linarith)
    exact Or.inl ⟨hh.2,hh.1⟩

end CannonMetricQC

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_ProductFactorSmall
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
namespace CannonDistortion
open CannonQM Metric
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma product_factor_small {a b c d r : ℝ}
    (ha : 0<a) (_hb : 0<b) (_hc : 0 < c) (hd : 0<d) (hr : 0 < r)
    (hp : a*b ≤ r*(c*d)) :
    a ≤ Real.sqrt r*c ∨ b ≤ Real.sqrt r*d := by
  by_contra! hn
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hm := mul_lt_mul hn.1 hn.2.le (mul_pos hs hd) ha.le
  have he : (Real.sqrt r*c)*(Real.sqrt r*d)=r*(c*d) := by
    calc
      _ = (Real.sqrt r)^2*(c*d) := by ring
      _ = _ := by rw [Real.sq_sqrt hr.le]
  rw [he] at hm
  exact (not_lt_of_ge hp) hm

lemma bounded_product {a b c d S L : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (_hd : 0 ≤ d) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hLa : a ≤ L*c) (hLb : b ≤ L*d) (hs : a ≤ S*c ∨ b ≤ S*d) :
    a*b ≤ S*L*(c*d) := by
  rcases hs with h|h
  · have hh := mul_le_mul h hLb hb (mul_nonneg hS hc)
    nlinarith
  · have hh := mul_le_mul hLa h hb (mul_nonneg hL hc)
    nlinarith

theorem power_control_crossRatio (f : X → Y) (hf : Function.Injective f)
    {K α β : ℝ} (hK : 0<K) (hα : 0<α) (hβ : 0<β) (hab : α ≤ β)
    (hcontrol : ∀ t : ℝ, 0 ≤ t → ∀ x a b : X, dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ K*powerGauge α β t*dist (f x) (f b))
    (x y z w : X) (hh : Distinct x y z w) :
    (crossRatio (f x) (f y) (f z) (f w) : ℝ)  ≤
      (K^2*5^β)*powerGauge (α/2) (3*β/2) (crossRatio x y z w) := by
  let r : ℝ := crossRatio x y z w
  have hr : 0 < r := by exact_mod_cast crossRatio_pos hh
  have hden : 0<dist x w*dist y z := mul_pos (dist_pos.mpr hh.2.2.1) (dist_pos.mpr hh.2.2.2.1)
  have hprod : dist x y*dist z w=r*(dist x w*dist y z) := by
    exact (div_mul_cancel₀ _ hden.ne').symm
  have hprod' : dist x y*dist z w ≤ max r 1*(dist x w*dist y z) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hden.le
  have hfh := hh.map hf
  have hfden : 0<dist (f x) (f w)*dist (f y) (f z) :=
    mul_pos (dist_pos.mpr hfh.2.2.1) (dist_pos.mpr hfh.2.2.2.1)
  let s := Real.sqrt r
  let L := 5*max r 1
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; nlinarith [le_max_right r 1]
  have hbig : 2*max r 1+3 ≤ L := by dsimp [L]; nlinarith [le_max_right r 1]
  have hKs : 0 ≤ K*powerGauge α β s := mul_nonneg hK.le (powerGauge_nonneg hs)
  have hKL : 0 ≤ K*powerGauge α β L := mul_nonneg hK.le (powerGauge_nonneg hL)
  have htarget : dist (f x) (f y)*dist (f z) (f w)  ≤
      (K*powerGauge α β s)*(K*powerGauge α β L)*(dist (f x) (f w)*dist (f y) (f z)) := by
    rcases CannonMetricQC.crossRatio_pair_bounds x y z w hh (le_max_right _ _) hprod' with hpair|hpair
    · have haL := hcontrol L hL x y w (hpair.1.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      have hbL := hcontrol L hL z w y (by
        rw [dist_comm z y]
        exact hpair.2.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      rw [dist_comm (f z) (f y)] at hbL
      have hsmall := product_factor_small (dist_pos.mpr hh.1) (dist_pos.mpr hh.2.2.2.2.2)
        (dist_pos.mpr hh.2.2.1) (dist_pos.mpr hh.2.2.2.1) hr hprod.le
      apply bounded_product dist_nonneg dist_nonneg dist_nonneg dist_nonneg hKs hKL haL hbL
      rcases hsmall with h|h
      · exact Or.inl (hcontrol s hs x y w h)
      · exact Or.inr (by simpa only [dist_comm] using hcontrol s hs z w y (by simpa only [dist_comm] using h))
    · have haL := hcontrol L hL y x z (by
        rw [dist_comm y x]
        exact hpair.1.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      have hbL := hcontrol L hL w z x (by
        rw [dist_comm w z,dist_comm w x]
        exact hpair.2.trans (mul_le_mul_of_nonneg_right hbig dist_nonneg))
      rw [dist_comm (f y) (f x)] at haL
      rw [dist_comm (f w) (f z),dist_comm (f w) (f x)] at hbL
      have hsmall := product_factor_small (dist_pos.mpr hh.1) (dist_pos.mpr hh.2.2.2.2.2)
        (dist_pos.mpr hh.2.2.2.1) (dist_pos.mpr hh.2.2.1) hr (by nlinarith [hprod])
      have he := bounded_product (a:=dist (f x) (f y)) (b:=dist (f z) (f w))
        dist_nonneg dist_nonneg dist_nonneg dist_nonneg hKs hKL haL hbL (by
        rcases hsmall with h|h
        · exact Or.inl (by simpa only [dist_comm] using hcontrol s hs y x z (by simpa only [dist_comm] using h))
        · exact Or.inr (by simpa only [dist_comm] using hcontrol s hs w z x (by simpa only [dist_comm] using h)))
      simpa only [mul_comm (dist (f y) (f z)) (dist (f x) (f w))] using he
  have hratio : (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤
      K^2*(powerGauge α β s*powerGauge α β L) := by
    change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z)) ≤ _
    apply (div_le_iff₀ hfden).mpr
    calc
      _ ≤ (K*powerGauge α β s)*(K*powerGauge α β L)*(dist (f x) (f w)*dist (f y) (f z)) := htarget
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left (mixed_power_bound hα hβ hab hr) (sq_nonneg K)
  exact hratio.trans (by simpa only [s,L,mul_assoc] using hm)

theorem power_control_quasiMobius (f : X → Y) (hf : Function.Injective f)
    {K α β : ℝ} (hK : 0<K) (hα : 0<α) (hβ : 0<β) (hab : α ≤ β)
    (hcontrol : ∀ t : ℝ, 0 ≤ t → ∀ x a b : X, dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ K*powerGauge α β t*dist (f x) (f b)) : QuasiMobius f := by
  let C : ℝ≥0 := ⟨K^2*5^β,by positivity⟩
  have hC : 0<C := by change (0:ℝ)<K^2*5^β; positivity
  refine ⟨powerIso C hC (α/2) (3*β/2) (by positivity) (by positivity),?_⟩
  intro x y z w hh
  apply NNReal.coe_le_coe.mp
  rw [powerIso_coe]
  exact power_control_crossRatio f hf hK hα hβ hab hcontrol x y z w hh

end CannonDistortion

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_QuasiMobius
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quasi-Möbius maps and distortion of cross ratios. -/

section
section
namespace CannonRealization
open Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.quasiMobius [PreconnectedSpace X] [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {P : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q P) (hP : 0 ≤ P)
    (hdiam : ∀ x y : X, dist x y ≤ 1) : CannonQM.QuasiMobius f := by
  obtain ⟨C,α,β,hC,hα,hab,hβ,hcontrol⟩ := hf.power_control f hpack hP hdiam
  exact CannonDistortion.power_control_quasiMobius f f.injective hC hα hβ hab hcontrol

end CannonRealization

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Uniformization_SurjectiveRealizationHomeomorphLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A homeomorphism obtained as the limit of surjective finite realizations. -/

section
section
namespace CannonRealization
open Set Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [PreconnectedSpace X] [Nontrivial Y]

theorem surjective_realization_homeomorph_limit
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F) :
    ∃ f : X ≃ₜ Y, RelativeShrink f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  obtain ⟨u,v,huv⟩ := exists_pair_ne Y
  obtain ⟨p,hp⟩ := hsurj 0 u
  obtain ⟨q,hq⟩ := hsurj 0 v
  have hpq : p≠q := by intro h; exact huv (hp.symm.trans ((congrArg (F 0) h).trans hq))
  obtain ⟨f,φ,hφ,ht⟩ := compact_map_subsequence F (hshrink.equicontinuous hpq)
  have hf := hshrink.limit hφ ht
  have hfs := surjective_limit hsurj ht
  obtain ⟨p',hp'⟩ := hfs u
  obtain ⟨q',hq'⟩ := hfs v
  have hn : f p'≠f q' := by rwa [hp',hq']
  let H := (Equiv.ofBijective f ⟨hf.injective hn,hfs⟩).toHomeomorphOfContinuousClosed
    f.continuous f.continuous.isClosedMap
  exact ⟨H,hf,φ,hφ,ht⟩

theorem surjective_realization_quasiMobius_limit [PreconnectedSpace Y]
    {Q : ℕ} {P : ℝ} (hpack : CannonPacking.PolynomialPacking (X:=X) Q P)
    (hP : 0 ≤ P) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F) :
    ∃ f : X ≃ₜ Y, CannonQM.QuasiMobius f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  obtain ⟨f,hf,φ,hφ,ht⟩ := surjective_realization_homeomorph_limit F hsurj hshrink
  exact ⟨f,hf.quasiMobius f hpack hP hdiam,φ,hφ,ht⟩
end CannonRealization

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_PreservesProducts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Filter Topology CannonGraph CannonVisual CannonMobius CannonRealization

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_quasiMobius_uniformizer_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ ψ : Boundary D ≃ₜ Sphere,CannonQM.QuasiMobius ψ := by
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonCharts.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) :=
    φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let _ : PathConnectedSpace Sphere :=
    roundChart.symm.surjective.pathConnectedSpace roundChart.symm.continuous
  dsimp only
  obtain ⟨F,hF,hshrink⟩ := boundary_eventual_relative_shrink D hδ φ
  obtain ⟨Q,P,hQ,hP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨ψ,hψ,rest⟩ := surjective_realization_quasiMobius_limit hpack hP.le
    (boundaryDist_le_one D hδ) F hF hshrink
  exact ⟨ψ,hψ⟩
end CannonRelease

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.CannonRelease.boundary_quasiMobius_uniformizer_oai.{u} := @OAI.CannonRelease.boundary_quasiMobius_uniformizer_oai.{u}
