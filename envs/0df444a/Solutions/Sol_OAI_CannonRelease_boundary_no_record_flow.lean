-- Prove2me | solution 1 for OAI.CannonRelease.boundary_no_record_flow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:07:55.677442+00:00
-- url     : https://prove2.me/submissions/d94fdbf4-5121-4095-a211-c9d6133b5e9b

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002

section
-- module Solutions.OAIQ046_CN.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

local instance instSetoidBasedRay_2_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_10_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

namespace CannonMetric
open Set Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma compact_packing_bound {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ s : Finset X, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → e ≤ dist x y) → s.card ≤ N := by
  classical
  obtain ⟨t,_,ht,hcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls (show 0 < e/3 by positivity)
  let T := ht.toFinset
  have hT (x : X) : ∃ y ∈ T, dist x y < e/3 := by
    have := hcover (mem_univ x)
    obtain ⟨y,hy⟩ := mem_iUnion.mp this
    obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
    exact ⟨y,ht.mem_toFinset.mpr hyt,hxy⟩
  choose f hf hf' using hT
  refine ⟨T.card,fun s hs => ?_⟩
  let F : ↥s → ↥T := fun x => ⟨f x,hf x⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hn
    have h := dist_triangle x.val (f x.val) y.val
    have hh : f x.val = f y.val := congrArg Subtype.val hxy
    rw [hh,dist_comm (f y.val) y.val] at h
    have h₁ := hf' x.val
    have h₂ := hf' y.val
    rw [hh] at h₁
    have h₃ := hs x.val x.property y.val y.property hn
    linarith
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hinj

end CannonMetric

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_27_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

namespace CannonRelease
open CannonGraph CannonVisual Filter Topology Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_28_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
theorem relative_packing_bound {q : ℝ} (hq : 0 < q) :
    ∃ N : ℕ, ∀ (x : Boundary D) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ s : Finset (Boundary D),
      (∀ y ∈ s, boundaryDist D hδ x y ≤ r) →
      (∀ y ∈ s, ∀ z ∈ s, y ≠ z → q*r ≤ boundaryDist D hδ y z) → s.card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < A := Real.exp_pos _
  have he : 0 < q/(L*A) := div_pos hq (mul_pos hL hA)
  obtain ⟨N,hN⟩ := CannonMetric.compact_packing_bound (X := Boundary D) he
  refine ⟨N,fun x t ht ht₁ s hs hsep => ?_⟩
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ ht ht₁
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryTranslate D ⟨δ,hδ⟩ (r.val k)⁻¹
  have hinj : Function.Injective f := (boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹).injective
  have himage := hN (s.image f) (by
    intro y hy z hz hyz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun heq => hyz (congrArg f heq)
    have hh := (visual_ball_expansion D hδ r k u v ((hs u hu).trans hk) ((hs v hv).trans hk)).2
    change boundaryDist D hδ u v ≤ L*boundaryDist D hδ (f u) (f v)*visualScale δ k at hh
    have hn : 0 ≤ boundaryDist D hδ (f u) (f v) := dist_nonneg
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hk' (mul_nonneg hL.le hn))
    have hh'' := hsep u hu v hv huv
    have hc : q ≤ L*boundaryDist D hδ (f u) (f v)*A := by
      apply (mul_le_mul_iff_left₀ ht).mp
      calc
        q*t ≤ boundaryDist D hδ u v := hh''
        _ ≤ L*boundaryDist D hδ (f u) (f v)*(A*t) := hh'
        _ = L*boundaryDist D hδ (f u) (f v)*A*t := by ring
    apply (div_le_iff₀ (mul_pos hL hA)).mpr
    nlinarith)
  rwa [Finset.card_image_of_injective s hinj] at himage

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_29_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
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

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

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

lemma center_mem (v : SourceNode f x₀ ε ell c₀ B kmin) (hB : 0 ≤ B) :
    v.center ∈ closedBall x₀ ε := by
  have hh : 0 ≤ 2*B*radius ell v.depth := mul_nonneg (mul_nonneg (by norm_num) hB) (radius_pos ell v.depth).le
  exact mem_closedBall.mpr (by linarith only [v.reserve,hh])

end SourceNode

end CannonNode

end

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

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

lemma weight_le_one (n : ℕ) (v : Fin (T.size n)) : T.weight n v ≤ 1 := by
  rw [← T.total_mass n]
  exact Finset.single_le_sum (fun w _ => T.nonneg n w) (Finset.mem_univ v)

lemma linear_transition_product
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ α : ℝ}
    (hΔ₀ : 0 ≤ Δ₀) (hα : 0 ≤ α) (hroot : ∀ v, Δ 0 v = Δ₀)
    (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hlin : ∀ n v, p n v * Δ n (T.parent n v) ≤ α * Δ (n+1) v) :
    ∀ n v, Δ₀ * T.weight n v ≤ α^n * Δ n v := by
  intro n
  induction n with
  | zero =>
    intro v
    simpa [hroot] using mul_le_mul_of_nonneg_left (T.weight_le_one 0 v) hΔ₀
  | succ n ih =>
    intro v
    calc
      Δ₀ * T.weight (n+1) v = p n v * (Δ₀ * T.weight n (T.parent n v)) := by
        rw [hstep]; ring
      _ ≤ p n v * (α^n * Δ n (T.parent n v)) :=
        mul_le_mul_of_nonneg_left (ih _) (hp n v)
      _ = α^n * (p n v * Δ n (T.parent n v)) := by ring
      _ ≤ α^n * (α * Δ (n+1) v) :=
        mul_le_mul_of_nonneg_left (hlin n v) (pow_nonneg hα n)
      _ = _ := by rw [pow_succ]; ring

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_VisualSynchronousPrefix
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
open Set Topology

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance visualSynchronousPrefixSetoid_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
theorem visual_synchronous_prefix (C : ℝ) (_hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ (r s : BasedRay D) (j : ℕ),
      boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) ≤ C*visualScale δ j →
      D.graph.dist (r.val j) (s.val j) ≤ B := by
  have hε := visualExponent_pos δ
  have hexp : Tendsto (fun n : ℕ => Real.exp (visualExponent δ*(n:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  obtain ⟨A,hA⟩ := (hexp.eventually (eventually_gt_atTop (2*C))).exists
  refine ⟨2*(A+(8*δ+6))+4*δ+2,fun r s j hj => ?_⟩
  have hc := (visualMetric_comparison D hδ r s).2
  have hp : (preDist (visualExponent δ) r s : ℝ) <
      Real.exp (visualExponent δ*(A:ℝ)-2*visualExponent δ*j) := by
    calc
      _ ≤ 2*boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) := hc
      _ ≤ 2*(C*visualScale δ j) := mul_le_mul_of_nonneg_left hj (by norm_num)
      _ < Real.exp (visualExponent δ*(A:ℝ))*visualScale δ j := by
        nlinarith only [mul_lt_mul_of_pos_right hA (visualScale_pos δ j)]
      _ = _ := by rw [visualScale,← Real.exp_add]; congr 1; push_cast; ring
  have hlim : Tendsto (fun n => (decay (visualExponent δ) r s n : ℝ)) atTop
      (𝓝 (preDist (visualExponent δ) r s : ℝ)) :=
    NNReal.continuous_coe.tendsto _ |>.comp
      (tendsto_decay D.connected hε.le r s)
  obtain ⟨n,hn,hdec⟩ := ((eventually_ge_atTop j).and (hlim.eventually_lt_const hp)).exists
  change Real.exp (-visualExponent δ*(product2 (G:=D.graph) 1 (r.val n) (s.val n):ℝ)) < _ at hdec
  have hprod : 2*j ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n)+A := by
    have he := Real.exp_lt_exp.mp hdec
    have he' : (2*j:ℕ) ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n)+A := by
      have hh : ((2*j:ℕ):ℝ) ≤ ((product2 (G:=D.graph) 1 (r.val n) (s.val n)+A:ℕ):ℝ) := by
        push_cast
        nlinarith only [he,hε]
      exact_mod_cast hh
    exact he'
  have hpref := (product2_prefix D.connected hδ r s hn).2
  have hr : D.graph.dist 1 (r.val j) = j := by
    simpa only [r.property.1,Nat.dist_zero_left] using r.property.2 0 j
  dsimp only [CayleyData.graph] at *
  have hv := vertex_close_to_ray D.connected hδ s (r.val j) n (A+(8*δ+6))
    (by simpa only [hr] using hn) (by rw [hr]; omega)
  simpa only [hr] using hv

theorem separated_ray_products {e : ℝ} (he : 0 < e) :
    ∃ C : ℕ, ∀ (r s : BasedRay D),
      e ≤ boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' s) →
      ∀ n, product2 (G:=D.graph) 1 (r.val n) (s.val n) ≤ C := by
  have hε := visualExponent_pos δ
  have ht : Tendsto (fun n : ℕ => Real.exp (-visualExponent δ*(n:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul,Function.comp_def] using tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  obtain ⟨C,hC⟩ := (ht.eventually_lt_const he).exists
  refine ⟨C,fun r s hsep n => ?_⟩
  have hc := (visualMetric_comparison D hδ r s).1
  have hd := preDist_le_decay (visualExponent δ) r s n
  have hd' : (preDist (visualExponent δ) r s : ℝ) ≤
      Real.exp (-visualExponent δ*(product2 (G:=D.graph) 1 (r.val n) (s.val n):ℝ)) := hd
  by_contra hn
  have hCN : (C:ℝ) ≤ product2 (G:=D.graph) 1 (r.val n) (s.val n) := by exact_mod_cast (lt_of_not_ge hn).le
  have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hCN (neg_nonpos.mpr hε.le))
  exact (not_lt_of_ge (hsep.trans (hc.trans hd'))) (hm.trans_lt hC)

theorem inverse_puncture_prefix {e : ℝ} (he : 0 < e) :
    ∃ B : ℕ, ∀ (r z : BasedRay D) (k : ℕ),
      e ≤ boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' z) →
      D.graph.dist (r.val k)⁻¹
        ((translateRay D ⟨δ,hδ⟩ (r.val k)⁻¹ z).val k) ≤ B := by
  obtain ⟨C,hC⟩ := separated_ray_products D hδ he
  refine ⟨2*(C+(8*δ+6))+4*δ+2,fun r z k hz => ?_⟩
  let g := (r.val k)⁻¹
  let p := translateRay D ⟨δ,hδ⟩ g z
  have hk : D.graph.dist 1 (r.val k) = k := by
    simpa only [r.property.1,Nat.dist_zero_left] using r.property.2 0 k
  have hg : D.graph.dist 1 g = k := by
    have hh := D.dist_mul_left g (r.val k) 1
    simpa [g,SimpleGraph.dist_comm,hk] using hh
  obtain ⟨n,hn,hbig⟩ := ((eventually_ge_atTop k).and
    (translated_mixed_product_large D hδ g z (2*D.graph.dist 1 g))).exists
  have hrepl := product2_replace_one D.connected hδ 1 g (g*z.val n) (p.val n) hbig
  have hpref := (product2_prefix D.connected hδ r z hn).1
  have hbound := hC r z hz n
  have hcomp := product2_complement D.connected 1 (r.val k) (z.val n)
  have hmul : product2 (G:=D.graph) 1 g (g*z.val n) =
      product2 (G:=D.graph) (r.val k) 1 (z.val n) := by
    have hh := product2_mul D g (r.val k) 1 (z.val n)
    simpa [g] using hh
  change product2 (G:=D.graph) (r.val k) 1 (z.val n) +
    product2 (G:=D.graph) 1 (r.val k) (z.val n) = 2*D.graph.dist 1 (r.val k) at hcomp
  rw [hk,← hmul] at hcomp
  dsimp only [CayleyData.graph] at *
  have hprod : 2*D.graph.dist 1 g ≤ product2 (G:=D.graph) 1 g (p.val n)+(C+(8*δ+6)) := by
    dsimp only [CayleyData.graph]
    rw [hg]
    omega
  have hh := vertex_close_to_ray D.connected hδ p g n (C+(8*δ+6)) (hg ▸ hn) hprod
  simpa only [hg] using hh

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

attribute [local instance] OAI.CannonRelease.visualSynchronousGraphBallDecidable
omit [TopologicalSpace G] [DiscreteTopology G] in
lemma uniform_graph_ball_card (B : ℕ) :
    ∃ N : ℕ, ∀ (x : G) (S : Finset G),
      (∀ y ∈ S, D.graph.dist x y ≤ B) → S.card ≤ N := by
  classical
  let T := (finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 B).toFinset
  refine ⟨T.card,fun x S hS => ?_⟩
  apply card_le_card_of_injOn (fun y => x⁻¹*y) ?_ (by intro a _ b _ hab; exact mul_left_cancel hab)
  intro y hy
  change x⁻¹*y ∈ (finite_graph_ball D.connected (finite_cayley_neighbors D.generators) 1 B).toFinset
  rw [Set.Finite.mem_toFinset]
  have hh := D.dist_mul_left x 1 (x⁻¹*y)
  simp only [mul_one,mul_inv_cancel_left] at hh
  change D.graph.dist 1 (x⁻¹*y) ≤ B
  rw [← hh]
  exact hS y hy

local instance visualSynchronousGraphBallSetoid_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
theorem vertex_assignment_multiplicity {H : ℝ} (hH : 0 < H) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D) (k : ℕ),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      ∀ v : G, (S.filter (fun i => (r i).val k = v)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  obtain ⟨N,hN⟩ := relative_packing_bound D hδ hH
  refine ⟨N,fun {ι} S r k hsep v => ?_⟩
  let T := S.filter (fun i => (r i).val k = v)
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi⟩ := hT
    let x : ι → Boundary D := fun j => Quotient.mk' (r j)
    have hinj : Set.InjOn x (T : Set ι) := by
      intro j hj j' hj' heq
      by_contra hne
      have hh := hsep j (mem_filter.mp hj).1 j' (mem_filter.mp hj').1 hne
      change H*visualScale δ k ≤ dist (x j) (x j') at hh
      rw [heq,dist_self] at hh
      exact (not_le_of_gt (mul_pos hH (visualScale_pos δ k))) hh
    have hh := hN (x i) (visualScale δ k) (visualScale_pos δ k)
      (by rw [visualScale]; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (visualExponent_pos δ).le) (Nat.cast_nonneg _)) (T.image x) (by
        intro y hy
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
        exact boundaryDist_le_of_prefix D hδ (r i) (r j)
          ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)) (by
        intro y hy y' hy' hne
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
        obtain ⟨j',hj',rfl⟩ := mem_image.mp hy'
        exact hsep j (mem_filter.mp hj).1 j' (mem_filter.mp hj').1
          (fun he => hne (congrArg x he)))
    rwa [card_image_of_injOn hinj] at hh
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

theorem puncture_ball_multiplicity {e H C : ℝ} (he : 0 < e) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D) (z : BasedRay D) (k : ℕ),
      (∀ i ∈ S, e ≤ boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' z)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      ∀ b : Boundary D, (S.filter (fun i => boundaryDist D hδ
        (boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z)) b ≤ C*visualScale δ k)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  obtain ⟨B,hB⟩ := inverse_puncture_prefix D hδ he
  obtain ⟨B',hB'⟩ := visual_synchronous_prefix D hδ (2*C) (by positivity)
  obtain ⟨Ng,hNg⟩ := uniform_graph_ball_card D (B+B')
  obtain ⟨Nv,hNv⟩ := vertex_assignment_multiplicity D hδ hH
  refine ⟨Nv*Ng,fun {ι} S r z k hsep hcent b => ?_⟩
  let p : ι → BasedRay D := fun i => translateRay D ⟨δ,hδ⟩ ((r i).val k)⁻¹ z
  let T := S.filter (fun i => boundaryDist D hδ (Quotient.mk' (p i)) b ≤ C*visualScale δ k)
  change T.card ≤ Nv*Ng
  by_cases hT : T.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hT
    have hnear (i : ι) (hi : i ∈ T) :
        D.graph.dist ((r i).val k)⁻¹ ((p i₀).val k) ≤ B+B' := by
      have h₁ := hB (r i) z k (hsep i (mem_filter.mp hi).1)
      have hpd : boundaryDist D hδ (Quotient.mk' (p i)) (Quotient.mk' (p i₀)) ≤
          (2*C)*visualScale δ k := by
        have hh := @dist_triangle (Boundary D) _ (Quotient.mk' (p i)) b (Quotient.mk' (p i₀))
        rw [@dist_comm (Boundary D) _ b (Quotient.mk' (p i₀))] at hh
        change boundaryDist D hδ (Quotient.mk' (p i)) (Quotient.mk' (p i₀)) ≤
          boundaryDist D hδ (Quotient.mk' (p i)) b + boundaryDist D hδ (Quotient.mk' (p i₀)) b at hh
        linarith only [hh,(mem_filter.mp hi).2,(mem_filter.mp hi₀).2]
      have h₂ := hB' (p i) (p i₀) k hpd
      have ht := @SimpleGraph.Connected.dist_triangle _ D.graph
        ((r i).val k)⁻¹ ((p i).val k) ((p i₀).val k) D.connected
      exact ht.trans (Nat.add_le_add h₁ h₂)
    have hcard := hNg ((p i₀).val k) (T.image (fun i => ((r i).val k)⁻¹)) (by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      rw [SimpleGraph.dist_comm]
      exact hnear i hi)
    have hfib : ∀ v ∈ T.image (fun i => ((r i).val k)⁻¹),
        (T.filter (fun i => ((r i).val k)⁻¹ = v)).card ≤ Nv := by
      intro v _
      have hh := hNv T r k (fun i hi j hj hij => hcent i (mem_filter.mp hi).1
        j (mem_filter.mp hj).1 hij) v⁻¹
      simpa only [inv_eq_iff_eq_inv] using hh
    exact (card_le_mul_card_image T Nv hfib).trans (Nat.mul_le_mul_left Nv hcard)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

end CannonRelease

namespace CannonGraph

open SimpleGraph CannonVisual

variable {V : Type*} {Γ : SimpleGraph V} {o : V}

lemma prefix_of_near_ray (hΓ : Γ.Connected) {δ : ℕ} (hδ : Thin Γ δ)
    (p : Ray Γ o) (v w : V) (k l B : ℕ) (hl : l ≤ k)
    (_hv : Γ.dist o v = k) (hw : Γ.dist o w = l)
    (hwv : Γ.dist w v = k-l) (hvp : Γ.dist v (p.val k) ≤ B) :
    Γ.dist w (p.val l) ≤ 2*B+4*δ+2 := by
  have hp : Γ.dist o (p.val k) = k := by
    simpa only [p.property.1,Nat.dist_zero_left] using p.property.2 0 k
  have ht := @Connected.dist_triangle _ Γ w v (p.val k) hΓ
  have hprod := product2_add_dist hΓ o w (p.val k)
  have hlarge : 2*Γ.dist o w ≤ product2 (G:=Γ) o w (p.val k)+B := by
    rw [hwv] at ht
    rw [hw,hp] at hprod
    rw [hw]
    omega
  have hh := vertex_close_to_ray hΓ hδ p w k B (by simpa only [hw] using hl) hlarge
  simpa only [hw] using hh

end CannonGraph

namespace CannonRelease

open CannonGraph CannonVisual Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

attribute [local instance] OAI.CannonRelease.visualSynchronousInverseRayDecidable
omit [TopologicalSpace G] [DiscreteTopology G] in
lemma inverse_ray_prefix (r : BasedRay D) {k l : ℕ} (hl : l ≤ k) :
    D.graph.dist 1 ((r.val k)⁻¹*r.val (k-l)) = l ∧
    D.graph.dist ((r.val k)⁻¹*r.val (k-l)) (r.val k)⁻¹ = k-l := by
  have h₁ := D.dist_mul_left (r.val k) 1 ((r.val k)⁻¹*r.val (k-l))
  have h₂ := D.dist_mul_left (r.val k) ((r.val k)⁻¹*r.val (k-l)) (r.val k)⁻¹
  simp only [mul_one,mul_inv_cancel_left,mul_inv_cancel] at h₁ h₂
  have hkk := r.property.2 k (k-l)
  have hk₀ := r.property.2 (k-l) 0
  rw [r.property.1,Nat.dist_zero_right] at hk₀
  dsimp only [CayleyData.graph] at h₁ h₂ hkk hk₀ ⊢
  constructor
  · rw [← h₁,hkk,Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _)]
    omega
  · rw [← h₂,hk₀]

attribute [local instance] OAI.CannonRelease.visualSynchronousInverseRaySetoid
theorem near_puncture_descendant_count {e H C : ℝ}
    (he : 0 < e) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ {ι : Type*} (S : Finset ι) (r : ι → BasedRay D)
      (z a b : BasedRay D) (k l : ℕ), l ≤ k →
      (∀ i ∈ S, e ≤ boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' z)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*visualScale δ k ≤
        boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' (r j))) →
      (∀ i ∈ S, boundaryDist D hδ (Quotient.mk' (r i)) (Quotient.mk' a) ≤
        C*visualScale δ (k-l)) →
      (∀ i ∈ S, boundaryDist D hδ
        (boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z))
        (Quotient.mk' b) ≤ visualScale δ l) →
      S.card ≤ N := by
  classical
  obtain ⟨B,hB⟩ := inverse_puncture_prefix D hδ he
  obtain ⟨B₁,hB₁⟩ := visual_synchronous_prefix D hδ 1 (by norm_num)
  obtain ⟨B₂,hB₂⟩ := visual_synchronous_prefix D hδ C hC
  obtain ⟨N₁,hN₁⟩ := uniform_graph_ball_card D (2*B+4*δ+2+B₁)
  obtain ⟨N₂,hN₂⟩ := uniform_graph_ball_card D B₂
  obtain ⟨Nv,hNv⟩ := vertex_assignment_multiplicity D hδ hH
  refine ⟨Nv*(N₁*N₂),fun {ι} S r z a b k l hl hsep hcent hanc hpunc => ?_⟩
  let u : ι → G := fun i => (r i).val (k-l)
  let w : ι → G := fun i => ((r i).val k)⁻¹*u i
  let p : ι → BasedRay D := fun i => translateRay D ⟨δ,hδ⟩ ((r i).val k)⁻¹ z
  have hw (i : ι) (hi : i ∈ S) :
      D.graph.dist (w i) (b.val l) ≤ 2*B+4*δ+2+B₁ := by
    have hg : D.graph.dist 1 ((r i).val k)⁻¹ = k := by
      have hh := D.dist_mul_left ((r i).val k) 1 ((r i).val k)⁻¹
      have hk := (r i).property.2 k 0
      rw [(r i).property.1,Nat.dist_zero_right] at hk
      simpa only [mul_one,mul_inv_cancel,hk] using hh.symm
    have hpre := inverse_ray_prefix D (r i) hl
    have hnear := hB (r i) z k (hsep i hi)
    have hh := prefix_of_near_ray D.connected hδ (p i) ((r i).val k)⁻¹ (w i)
      k l B hl hg hpre.1 hpre.2 hnear
    have hpi := hpunc i hi
    have heq : boundaryTranslate D ⟨δ,hδ⟩ ((r i).val k)⁻¹ (Quotient.mk' z) =
        Quotient.mk' (p i) := rfl
    rw [heq] at hpi
    have hsync := hB₁ (p i) b l (by simpa only [one_mul] using hpi)
    exact (@SimpleGraph.Connected.dist_triangle _ D.graph (w i) ((p i).val l) (b.val l)
      D.connected).trans (Nat.add_le_add hh hsync)
  have hu (i : ι) (hi : i ∈ S) : D.graph.dist (u i) (a.val (k-l)) ≤ B₂ :=
    hB₂ (r i) a (k-l) (hanc i hi)
  have hwcard : (S.image w).card ≤ N₁ := hN₁ (b.val l) (S.image w) (by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    rw [SimpleGraph.dist_comm]
    exact hw i hi)
  have hucard : (S.image u).card ≤ N₂ := hN₂ (a.val (k-l)) (S.image u) (by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    rw [SimpleGraph.dist_comm]
    exact hu i hi)
  let f : ι → G × G := fun i => (w i,u i)
  have hfcard : (S.image f).card ≤ N₁*N₂ := by
    have hsub : S.image f ⊆ (S.image w) ×ˢ (S.image u) := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩,mem_image.mpr ⟨i,hi,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (by rw [card_product]; exact Nat.mul_le_mul hwcard hucard)
  have hfib : ∀ y ∈ S.image f, (S.filter (fun i => f i = y)).card ≤ Nv := by
    intro y _
    apply (Finset.card_le_card (show S.filter (fun i => f i = y) ⊆
      S.filter (fun i => (r i).val k = y.2*y.1⁻¹) from ?_)).trans (hNv S r k hcent _)
    intro i hi
    obtain ⟨hi,heq⟩ := mem_filter.mp hi
    have hw := congrArg Prod.fst heq
    have hu := congrArg Prod.snd heq
    change w i = y.1 at hw
    change u i = y.2 at hu
    refine mem_filter.mpr ⟨hi,?_⟩
    rw [← hw,← hu]
    simp only [w,mul_inv_rev,inv_inv,mul_inv_cancel_left]
  exact (card_le_mul_card_image S Nv hfib).trans (Nat.mul_le_mul_left Nv hfcard)

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

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

namespace FiniteFlow

variable (T : FiniteFlow)

theorem conditional_weight {α : ℝ} (hα : 0 ≤ α)
    (hstep : ∀ n v, T.weight (n+1) v ≤ α*T.weight n (T.parent n v)) :
    ∀ n m v, T.weight (n+m) v ≤ α^m*T.weight n (T.ancestor n m v) := by
  intro n m
  induction m with
  | zero => intro v; simp [ancestor]
  | succ m ih =>
    intro v
    calc
      _ ≤ α*T.weight (n+m) (T.parent (n+m) v) := hstep _ _
      _ ≤ α*(α^m*T.weight n (T.ancestor n m (T.parent (n+m) v))) :=
        mul_le_mul_of_nonneg_left (ih _) hα
      _ = _ := by simp only [ancestor,pow_succ]; ring

end FiniteFlow

end CannonFlow

namespace CannonFlow.FiniteFlow

open Finset

variable (T : CannonFlow.FiniteFlow)

theorem descendant_displacement {X : Type*} [MetricSpace X]
    (center : (n : ℕ) → Fin (T.size n) → X) (r : ℕ → ℝ)
    (B C θ : ℝ) (hr : ∀ n, 0 ≤ r n) (hBC : B ≤ C*(1-θ))
    (hscale : ∀ n, r (n+1) = θ*r n)
    (hstep : ∀ n v, dist (center (n+1) v) (center n (T.parent n v)) ≤ B*r n) :
    ∀ n m v, dist (center (n+m) v) (center n (T.ancestor n m v)) ≤
      C*(r n-r (n+m)) := by
  intro n m
  induction m with
  | zero => intro v; simp [ancestor]
  | succ m ih =>
    intro v
    have hed : B*r (n+m) ≤ C*(r (n+m)-r (n+m+1)) := by
      have hh := mul_le_mul_of_nonneg_right hBC (hr (n+m))
      rw [hscale]
      nlinarith only [hh]
    calc
      _ ≤ dist (center (n+m+1) v) (center (n+m) (T.parent (n+m) v)) +
          dist (center (n+m) (T.parent (n+m) v))
            (center n (T.ancestor n m (T.parent (n+m) v))) := dist_triangle _ _ _
      _ ≤ B*r (n+m) + C*(r n-r (n+m)) := add_le_add (hstep _ _) (ih _)
      _ ≤ C*(r (n+m)-r (n+m+1)) + C*(r n-r (n+m)) := add_le_add hed le_rfl
      _ = _ := by ring_nf

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

end

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

theorem finite_pair_bound {X I P : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (pairs : Finset P)
    (pay : P → I) (B : P → Set X) (Δ weight : I → ℝ)
    (hm : ∀ p ∈ pairs, MeasurableSet (B p))
    {c A Pstar M : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hP : 0 ≤ Pstar)
    (hweight : ∀ p ∈ pairs, Pstar ≤ weight (pay p))
    (hgap : ∀ p ∈ pairs, A * weight (pay p) ≤ Δ (pay p))
    (hcost : ∀ p ∈ pairs, c * Δ (pay p)^2 ≤ μ.real (B p))
    (hmult : ∀ x, (pairs.filter (fun p => x ∈ B p)).card ≤ M) :
    (pairs.card : ℝ) * c * A^2 * Pstar^2 ≤ M * μ.real univ := by
  have hlocal : ∀ p ∈ pairs, c * A^2 * Pstar^2 ≤ μ.real (B p) := by
    intro p hp
    have h₁ := mul_le_mul_of_nonneg_left (hweight p hp) hA
    have h₂ := h₁.trans (hgap p hp)
    have h₃ : (A * Pstar)^2 ≤ Δ (pay p)^2 :=
      sq_le_sq₀ (mul_nonneg hA hP) (le_trans (mul_nonneg hA hP) h₂) |>.mpr h₂
    calc
      _ = c * (A * Pstar)^2 := by ring
      _ ≤ c * Δ (pay p)^2 := mul_le_mul_of_nonneg_left h₃ hc
      _ ≤ _ := hcost p hp
  calc
    _ = ∑ p ∈ pairs, c * A^2 * Pstar^2 := by simp; ring
    _ ≤ ∑ p ∈ pairs, μ.real (B p) := Finset.sum_le_sum hlocal
    _ ≤ _ := sum_measure_le_multiplicity μ pairs B hm hmult

lemma cost_comparison {N F c A Pstar M mass η k : ℝ}
    (hc : 0 ≤ c) (_hA : 0 ≤ A) (hP : 0 ≤ Pstar) (hη : 0 ≤ η)
    (hN : 0 ≤ N) (hk : 0 < k)
    (hfar : η * N^2 ≤ F) (hclass : 1 / k ≤ N * Pstar)
    (hbound : F * c * A^2 * Pstar^2 ≤ M * mass) :
    η * c * A^2 ≤ M * mass * k^2 := by
  have hh : (1 / k)^2 ≤ (N * Pstar)^2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hN hP)).mpr hclass
  have hlow : η * c * A^2 * (1 / k)^2 ≤ F * c * A^2 * Pstar^2 := by
    calc
      _ ≤ η * c * A^2 * (N * Pstar)^2 :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (η * N^2) * c * A^2 * Pstar^2 := by ring
      _ ≤ _ := by gcongr
  have h := mul_le_mul_of_nonneg_right (hlow.trans hbound) (sq_nonneg k)
  field_simp at h
  nlinarith

theorem not_frequently_exp_le_quadratic {c : ℝ} (hc : 0 < c)
    (C k₀ D : ℝ) :
    ¬ ∃ᶠ n : ℕ in atTop,
      Real.exp (c * n) ≤ C * (k₀ + D * n)^2 := by
  have h₀ := (isLittleO_pow_exp_pos_mul_atTop 0 hc).const_mul_left (C * k₀^2)
  have h₁ := (isLittleO_pow_exp_pos_mul_atTop 1 hc).const_mul_left (2*C*k₀*D)
  have h₂ := (isLittleO_pow_exp_pos_mul_atTop 2 hc).const_mul_left (C*D^2)
  have hpoly : (fun x : ℝ => C * (k₀ + D * x)^2) =o[atTop]
      (fun x => Real.exp (c * x)) := by
    have hsum := (h₀.add h₁).add h₂
    have heq : (fun x : ℝ => C * k₀^2 * x^0 + (2*C*k₀*D)*x^1 +
          (C*D^2)*x^2) = (fun x : ℝ => C * (k₀ + D*x)^2) := by
      funext x
      ring
    change (fun x : ℝ => C * k₀^2 * x^0 + (2*C*k₀*D)*x^1 +
      (C*D^2)*x^2) =o[atTop] (fun x => Real.exp (c*x)) at hsum
    rw [heq] at hsum
    exact hsum
  have hevent := hpoly.bound (show (0 : ℝ) < 1/2 by norm_num)
  have hevent' := tendsto_natCast_atTop_atTop.eventually hevent
  intro hfreq
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hevent').exists
  have hepos := Real.exp_pos (c * (n : ℝ))
  simp only [Real.norm_eq_abs, abs_of_pos hepos] at hn'
  have hle := le_abs_self (C * (k₀ + D * (n : ℝ))^2)
  linarith

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

lemma step_linear (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.step g i*S.len g (S.flow.parent g i) ≤ Real.exp (-ell*n)*S.len (g+1) i :=
  S.child_linear _ _

lemma step_nested (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.len (g+1) i ≤ S.len g (S.flow.parent g i) := S.child_length_le _ _

lemma weight_linear (g : ℕ) (i : Fin (S.flow.size g)) :
    S.root.length*S.flow.weight g i ≤ (Real.exp (-ell*n))^g*S.len g i :=
  S.flow.linear_transition_product S.step S.len S.root.length_pos.le (Real.exp_pos _).le
    S.root_length (fun g i => (S.step_pos g i).le) S.weight_step S.step_linear g i

lemma weight_conditional (g m : ℕ) (i : Fin (S.flow.size (g+m))) :
    S.flow.weight (g+m) i ≤ (Real.exp (-ell*n))^m*
      S.flow.weight g (S.flow.ancestor g m i) := by
  apply S.flow.conditional_weight (Real.exp_pos _).le
  intro j v
  have h := (S.step_linear j v).trans (mul_le_mul_of_nonneg_left (S.step_nested j v)
    (Real.exp_pos _).le)
  have hp : S.step j v ≤ Real.exp (-ell*n) :=
    (mul_le_mul_iff_left₀ (S.len_pos j (S.flow.parent j v))).mp h
  rw [S.weight_step]
  exact mul_le_mul_of_nonneg_right hp (S.flow.nonneg _ _)

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

lemma descendant_displacement (hθ : radius ell (160*(qdim+1)*n) < 1/4)
    (hB : 0 ≤ B+1) (g m : ℕ) (i : Fin (S.flow.size (g+m))) :
    dist (S.center (g+m) i) (S.center g (S.flow.ancestor g m i)) ≤ 2*(B+1)*S.scale g := by
  have h := S.flow.descendant_displacement S.center S.scale (B+1) (2*(B+1))
    (radius ell (160*(qdim+1)*n)) (fun g => (radius_pos _ _).le)
    (by nlinarith only [hθ,hB]) S.scale_succ S.center_step g m i
  have hp := mul_nonneg (by linarith only [hB] : 0 ≤ 2*(B+1)) (show 0 ≤ S.scale (g+m) from (radius_pos _ _).le)
  linarith only [h,hp]

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

lemma center_mem (hB : 0 ≤ B+1) (g : ℕ) (i : Fin (S.flow.size g)) :
    S.center g i ∈ closedBall x₀ ε := (S.state g i).center_mem hB

end CannonNode.SourceConstruction

end

section

section

section

namespace CannonMagnification

open Set Metric

lemma denominator_triangle {X : Type*} [MetricSpace X] (x y z : X) (R : ℝ) :
    denominator x R z ≤ denominator x R y+dist y z := by
  apply max_le
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right dist_nonneg)
  · exact (dist_triangle x y z).trans (add_le_add (le_max_right _ _) le_rfl)

theorem puncture_bounds {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x z₀ : X) (R C L d : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hL : 0 < L)
    (hd : 0 < d) (hRone : R ≤ 1) (hz₀ : d ≤ dist x z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1) (hexp : Expansion h x R C L) :
    (∀ y, dist (h y) (h z₀)*denominator x R y ≤ (C/d)*R) ∧
    (∀ y, denominator x R y ≤ d/2 →
      R ≤ (2*L/d)*dist (h y) (h z₀)*denominator x R y) := by
  constructor
  · intro y
    have hh := (hexp y z₀).1
    have hm : dist (h y) (h z₀)*max R (dist x y)*d ≤
        dist (h y) (h z₀)*max R (dist x y)*max R (dist x z₀) :=
      mul_le_mul_of_nonneg_left (hz₀.trans (le_max_right _ _)) (by positivity)
    have ht : C*R*dist y z₀ ≤ C*R :=
      (mul_le_mul_of_nonneg_left (hdiam y z₀) (mul_nonneg hC hR.le)).trans_eq (mul_one _)
    have hh' := hm.trans (hh.trans ht)
    calc
      _ ≤ C*R/d := (le_div_iff₀ hd).mpr hh'
      _ = _ := by ring
  · intro y hy
    have hxy : dist x y ≤ d/2 := (le_max_right _ _).trans hy
    have hdist : d/2 ≤ dist y z₀ := by linarith only [dist_triangle x y z₀,hz₀,hxy]
    have hh := (hexp y z₀).2
    have hmax : max R (dist x z₀) ≤ 1 := max_le hRone (hdiam _ _)
    have hm : L*dist (h y) (h z₀)*max R (dist x y)*max R (dist x z₀) ≤
        L*dist (h y) (h z₀)*max R (dist x y) :=
      (mul_le_mul_of_nonneg_left hmax (by positivity)).trans_eq (mul_one _)
    have hdR := mul_le_mul_of_nonneg_left hdist hR.le
    have hh' := hdR.trans (hh.trans hm)
    calc
      R ≤ 2*(L*dist (h y) (h z₀)*max R (dist x y))/d :=
        (le_div_iff₀ hd).mpr (by linarith only [hh'])
      _ = _ := by dsimp [denominator]; ring

theorem cost_ball_geometry {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x p p' : X) (R C L U V cutoff A B S t : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hL : 0 ≤ L) (hU : 0 < U) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 < S) (ht : 0 < t) (htone : t ≤ 1)
    (hexp : Expansion h x R C L)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (hlower : ∀ y, denominator x R y ≤ cutoff →
      R ≤ V*dist (h y) p*denominator x R y)
    (hscale : R = dist p' p*t)
    (hfar : 2*A*R ≤ dist p' p)
    (hlocal : U*t ≤ cutoff)
    (hcoef : 2*L*A*U^2 ≤ S)
    (hsmall : 2*V*B*S*t ≤ 1) :
    let z := h.symm p'
    let s := S*t^2
    h.symm '' closedBall p' (A*R) ⊆ closedBall z s ∧
    h '' closedBall z (B*s) ⊆ closedBall p' ((2*C*V^2*B*S)*R) ∧
    closedBall z (B*s) ⊆ closedBall x ((U+B*S)*t) := by
  dsimp only
  let z := h.symm p'
  let δ := dist p' p
  have hδ : 0 < δ := by
    change 0 < dist p' p
    nlinarith only [hscale,hR,ht,dist_nonneg (x:=p') (y:=p)]
  have hz : h z = p' := h.apply_symm_apply _
  have hDznon : 0 < denominator x R z := hR.trans_le (le_max_left _ _)
  have hDz : denominator x R z ≤ U*t := by
    have hh : δ*denominator x R z ≤ δ*(U*t) := by
      calc
        _ ≤ U*R := by simpa only [δ,hz] using hupper z
        _ = _ := by rw [hscale]; dsimp [δ]; ring
    exact (mul_le_mul_iff_right₀ hδ).mp hh
  have htDz : t ≤ V*denominator x R z := by
    have hh : δ*t ≤ δ*(V*denominator x R z) := by
      calc
        _ = R := hscale.symm
        _ ≤ V*dist (h z) p*denominator x R z := hlower z (hDz.trans hlocal)
        _ = _ := by rw [hz]; dsimp [δ]; ring
    exact (mul_le_mul_iff_right₀ hδ).mp hh
  have hrad : 2*(B*(S*t^2)) ≤ denominator x R z := by
    have hh := mul_le_mul_of_nonneg_right hsmall ht.le
    have hh' : V*(2*(B*(S*t^2))) ≤ V*denominator x R z := by
      calc
        _ ≤ t := by nlinarith only [hh]
        _ ≤ _ := htDz
    exact (mul_le_mul_iff_right₀ hV).mp hh'
  constructor
  · rintro y ⟨w,hw,rfl⟩
    let y := h.symm w
    have hy : h y = w := h.apply_symm_apply _
    have hwδ : δ/2 ≤ dist w p := by
      have hh := dist_triangle p' w p
      have hw' := mem_closedBall.mp hw
      rw [dist_comm w p'] at hw'
      dsimp [δ]
      linarith only [hh,hw',hfar]
    have hDy : denominator x R y ≤ 2*U*t := by
      have hDypos : 0 ≤ denominator x R y := hR.le.trans (le_max_left _ _)
      have hh : δ/2*denominator x R y ≤ U*(δ*t) := by
        calc
          _ ≤ dist w p*denominator x R y := mul_le_mul_of_nonneg_right hwδ hDypos
          _ ≤ U*R := by simpa only [hy] using hupper y
          _ = _ := by rw [hscale]
      apply (mul_le_mul_iff_right₀ hδ).mp
      nlinarith only [hh]
    have hh := (hexp y z).2
    change R*dist y z ≤ L*dist (h y) (h z)*denominator x R y*denominator x R z at hh
    rw [hy,hz] at hh
    have hw' := mem_closedBall.mp hw
    have hm : L*dist w p'*denominator x R y*denominator x R z ≤
        L*(A*R)*(2*U*t)*(U*t) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hw' hL
        · exact hDy
        · exact hR.le.trans (le_max_left _ _)
        · positivity
      · exact hDz
      · exact hDznon.le
      · positivity
    have hh' : R*dist y z ≤ R*(2*L*A*U^2*t^2) :=
      (hh.trans hm).trans_eq (by ring)
    have hdist := (mul_le_mul_iff_right₀ hR).mp hh'
    apply mem_closedBall.mpr
    exact hdist.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  constructor
  · rintro w ⟨y,hy,rfl⟩
    have hyz := mem_closedBall.mp hy
    have hDy : denominator x R z/2 ≤ denominator x R y := by
      have hh := denominator_triangle x y z R
      linarith only [hh,hyz,hrad]
    have htDy : t ≤ 2*V*denominator x R y := by
      have hh := mul_le_mul_of_nonneg_left hDy hV.le
      linarith only [hh,htDz]
    have htprod : t^2 ≤ 2*V^2*denominator x R y*denominator x R z := by
      calc
        t^2 = t*t := by ring
        _ ≤ (2*V*denominator x R y)*(V*denominator x R z) :=
          mul_le_mul htDy htDz ht.le (ht.le.trans htDy)
        _ = _ := by ring
    have hh := (hexp y z).1
    change dist (h y) (h z)*denominator x R y*denominator x R z ≤ C*R*dist y z at hh
    rw [hz] at hh
    have hdistnon := dist_nonneg (x:=h y) (y:=p')
    have hm := mul_le_mul_of_nonneg_left htprod hdistnon
    have hE := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 2*V^2)
    have hradE := mul_le_mul_of_nonneg_left hyz (by positivity : 0 ≤ 2*V^2*C*R)
    have hall : t^2*dist (h y) p' ≤ t^2*((2*C*V^2*B*S)*R) := by
      nlinarith only [hm,hE,hradE]
    exact mem_closedBall.mpr ((mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hall)
  · intro y hy
    have hyz := mem_closedBall.mp hy
    have hxy := dist_triangle x z y
    rw [dist_comm z y] at hxy
    have hxz : dist x z ≤ U*t := (le_max_right _ _).trans hDz
    have htsq : t^2 ≤ t := by nlinarith only [ht,htone]
    have hm := mul_le_mul_of_nonneg_left htsq (by positivity : 0 ≤ B*S)
    apply mem_closedBall.mpr
    rw [dist_comm]
    nlinarith only [hxy,hxz,hyz,hm]

end CannonMagnification

end

end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_AnnularPatternDistance
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
namespace CannonMagnification

open Set Metric

lemma annular_pattern_distance {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y z : X) (R θ C L a d P : ℝ)
    (hR : 0 < R) (hθ : 0 ≤ θ) (ha : 0 < a) (hC : 0 ≤ C)
    (hexp : Expansion h x R C L)
    (hy : a*R ≤ dist x y) (hz : a*R ≤ dist x z)
    (hyz : dist y z ≤ d*θ*R) (hcoef : C*d ≤ P*a^2) :
    dist (h y) (h z) ≤ P*θ := by
  have hprod : a^2*R^2 ≤ max R (dist x y)*max R (dist x z) := by
    calc
      _ = (a*R)*(a*R) := by ring
      _ ≤ _ := mul_le_mul (hy.trans (le_max_right _ _)) (hz.trans (le_max_right _ _))
        (mul_nonneg ha.le hR.le) (hR.le.trans (le_max_left _ _))
  have hh := (mul_le_mul_of_nonneg_left hprod (dist_nonneg (x := h y) (y := h z))).trans
    (by simpa only [mul_assoc] using (hexp y z).1)
  have hCdist := mul_le_mul_of_nonneg_left hyz (mul_nonneg hC hR.le)
  have hcoeff := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hθ (sq_nonneg R))
  apply (mul_le_mul_iff_left₀ (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hR))).mp
  nlinarith only [hh,hCdist,hcoeff]

lemma inverse_ball_criterion {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y z : X) (R C L d s : ℝ)
    (hR : 0 < R) (hL : 0 ≤ L) (hd : 0 < d) (hs : 0 ≤ s)
    (hexp : Expansion h x R C L)
    (hcoef : L*s*denominator x R y*(denominator x R y+d) < R*d)
    (hyz : dist (h y) (h z) ≤ s) : dist y z < d := by
  by_contra hh
  have hdd : d ≤ dist y z := le_of_not_gt hh
  have hD : 0 < denominator x R y := hR.trans_le (le_max_left _ _)
  have hDz : 0 ≤ denominator x R z := hR.le.trans (le_max_left _ _)
  have htri := denominator_triangle x y z R
  have hscale : denominator x R z*d ≤ (denominator x R y+d)*dist y z := by
    have hh := mul_le_mul_of_nonneg_right htri hd.le
    have hh' := mul_le_mul_of_nonneg_left hdd hD.le
    nlinarith only [hh,hh']
  have he := (hexp y z).2
  change R*dist y z ≤ L*dist (h y) (h z)*denominator x R y*denominator x R z at he
  have he' := mul_le_mul_of_nonneg_right he hd.le
  have hu := mul_le_mul_of_nonneg_left hyz hL
  have hu' := mul_le_mul_of_nonneg_right hu (mul_nonneg hD.le (mul_nonneg hDz hd.le))
  have hv := mul_le_mul_of_nonneg_left hscale (mul_nonneg (mul_nonneg hL hs) hD.le)
  have hc := mul_lt_mul_of_pos_right hcoef (hd.trans_le hdd)
  nlinarith only [he',hu',hv,hc]

lemma pattern_ball_containment {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y : X) (R θ C L B c p : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hL : 0 ≤ L) (hB : 1 ≤ B)
    (hc : 0 < c) (hp : 0 ≤ p) (hsmall : c*θ ≤ 1)
    (hexp : Expansion h x R C L) (hy : dist x y ≤ B*R)
    (hcoef : L*p*B*(B+1) < c) :
    closedBall (h y) (p*θ) ⊆ h '' ball y (c*θ*R) := by
  intro z hz
  refine ⟨h.symm z,?_,h.apply_symm_apply z⟩
  have hD : denominator x R y ≤ B*R := max_le (by nlinarith only [hB,hR]) hy
  have hDnon : 0 ≤ denominator x R y := hR.le.trans (le_max_left _ _)
  have hDplus : denominator x R y+c*θ*R ≤ (B+1)*R := by
    have hm := mul_le_mul_of_nonneg_right hsmall hR.le
    linarith only [hD,hm]
  have hco : L*(p*θ)*denominator x R y*(denominator x R y+c*θ*R) < R*(c*θ*R) := by
    have hmul : L*(p*θ)*denominator x R y*(denominator x R y+c*θ*R) ≤
        L*(p*θ)*(B*R)*((B+1)*R) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hD (by positivity)
      · exact hDplus
      · positivity
      · positivity
    have hh := mul_lt_mul_of_pos_right hcoef (mul_pos hθ (sq_pos_of_pos hR))
    nlinarith only [hmul,hh]
  have hh := inverse_ball_criterion h x y (h.symm z) R C L (c*θ*R) (p*θ)
    hR hL (by positivity) (by positivity) hexp hco (by
      rw [h.apply_symm_apply,dist_comm]
      exact mem_closedBall.mp hz)
  simpa only [mem_ball,dist_comm] using hh

lemma net_pattern_ball {X : Type*} [MetricSpace X] (c z : X) (e : ℝ)
    (he : 0 ≤ e) (hcz : dist c z ≤ e) :
    closedBall c (e/2) ⊆ closedBall z (3*e) ∧
    closedBall z (3*e) ⊆ closedBall c (10*e) := by
  constructor
  · intro w hw
    have hdist := dist_triangle w c z
    have hw' := mem_closedBall.mp hw
    exact mem_closedBall.mpr (by linarith only [hdist,hw',hcz,he])
  · intro w hw
    have hdist := dist_triangle w z c
    have hw' := mem_closedBall.mp hw
    rw [dist_comm z c] at hdist
    exact mem_closedBall.mpr (by linarith only [hdist,hw',hcz,he])

end CannonMagnification

end

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
section
namespace CannonNode

open Set Metric CannonMagnification

theorem good_candidate_pattern {X : Type*} [MetricSpace X] [ProperSpace X]
    {ι : Type*} [Fintype ι] (net : ι → X) (f : X → ℝ) (Ω : Set X)
    (h : X ≃ₜ X) (x : X) (y : Bool → X)
    (R θ A B c₀ cIn cPat CE LE gap δ : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hA : 2 < A) (hB : 1 ≤ B)
    (hc₀ : 0 < c₀) (_hcIn : 0 < cIn) (hcPat : 0 < cPat)
    (hCE : 0 ≤ CE) (hLE : 0 ≤ LE) (hsmall : c₀*θ ≤ 1)
    (hinner : cIn ≤ c₀) (hinner2 : 2 ≤ c₀)
    (hcoef₁ : CE*cIn ≤ (cPat/2)*(A-2)^2)
    (hcoef₂ : LE*(10*cPat)*B*(B+1) < c₀)
    (hexp : Expansion h x R CE LE)
    (hloc : ∀ s, (A-1)*R ≤ dist x (y s) ∧ dist x (y s) ≤ B*R)
    (hΩ : ∀ s, closedBall (y s) (c₀*θ*R) ⊆ Ω)
    (hf : ContinuousOn f Ω)
    (hnet : ∀ z, ∃ i, dist z (net i) ≤ cPat*θ)
    (hpaths : ∀ s u v, u ∈ closedBall (y s) (2*θ*R) →
      v ∈ closedBall (y s) (2*θ*R) →
      JoinedIn (ball (y s) (cIn*θ*R)) u v)
    (hgap : ∀ s, gap ≤ upper f (y s) (2*θ*R)-lower f (y s) (2*θ*R))
    (hsep : upper f (y false) (c₀*θ*R)+δ ≤ lower f (y true) (c₀*θ*R)) :
    ∃ pat : Bool → ι, ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall (net (pat s)) (3*cPat*θ)) ∧
      (∀ s, gap ≤ f (h.symm (v₁ s))-f (h.symm (v₀ s))) ∧
      (∀ s, closedBall (net (pat s)) (3*cPat*θ) ⊆ h '' ball (y s) (c₀*θ*R)) ∧
      ∀ z ∈ closedBall (net (pat false)) (3*cPat*θ),
        ∀ w ∈ closedBall (net (pat true)) (3*cPat*θ),
          f (h.symm z)+δ ≤ f (h.symm w) := by
  classical
  have hr : 0 < θ*R := mul_pos hθ hR
  have hinnerball (s : Bool) : closedBall (y s) (2*θ*R) ⊆ closedBall (y s) (c₀*θ*R) :=
    closedBall_subset_closedBall (by nlinarith only [hinner2,hr])
  have hfc (s : Bool) := hf.mono (hΩ s)
  have hext (s : Bool) := ball_extrema (by positivity : 0 ≤ 2*θ*R) ((hfc s).mono (hinnerball s))
  choose v hv hvval using fun s => (hext s).1
  choose w hw hwval using fun s => (hext s).2
  have hp (s : Bool) := hpaths s (v s) (w s) (hv s) (hw s)
  choose π hπ using hp
  choose idx hidx using fun s => hnet (h (y s))
  let γ : ∀ s, Path (h (v s)) (h (w s)) := fun s => (π s).map h.continuous
  have hsmall' : cIn*θ ≤ 1 := (mul_le_mul_of_nonneg_right hinner hθ.le).trans hsmall
  have himage (s : Bool) : range (γ s) ⊆ closedBall (h (y s)) (cPat*θ/2) := by
    rintro z ⟨t,rfl⟩
    have hyt : dist (y s) (π s t) ≤ cIn*θ*R := by
      have hh := hπ s t
      change dist (π s t) (y s) < cIn*θ*R at hh
      simpa only [dist_comm] using hh.le
    have hyt' := dist_triangle x (π s t) (y s)
    rw [dist_comm (π s t) (y s)] at hyt'
    have hlow : (A-2)*R ≤ dist x (π s t) := by
      have hm := mul_le_mul_of_nonneg_right hsmall' hR.le
      nlinarith only [(hloc s).1,hyt,hyt',hm]
    have hh := annular_pattern_distance h x (y s) (π s t) R θ CE LE (A-2) cIn (cPat/2)
      hR hθ.le (by linarith only [hA]) hCE hexp
      (by nlinarith only [(hloc s).1,hR]) hlow hyt hcoef₁
    change dist (h (π s t)) (h (y s)) ≤ cPat*θ/2
    rw [dist_comm]
    nlinarith only [hh]
  have hcont (s : Bool) : closedBall (h (y s)) (10*(cPat*θ)) ⊆ h '' ball (y s) (c₀*θ*R) := by
    simpa only [mul_assoc] using pattern_ball_containment h x (y s) R θ CE LE B c₀ (10*cPat)
      hR hθ hLE hB hc₀ (by positivity) hsmall hexp (hloc s).2 hcoef₂
  have hb (s : Bool) := net_pattern_ball (h (y s)) (net (idx s)) (cPat*θ)
    (mul_nonneg hcPat.le hθ.le) (hidx s)
  refine ⟨idx,fun s => h (v s),fun s => h (w s),γ,?_,?_,?_,?_⟩
  · intro s
    simpa only [mul_assoc] using (himage s).trans (hb s).1
  · intro s
    simp only [h.symm_apply_apply]
    rw [hvval s,hwval s]
    exact hgap s
  · intro s
    simpa only [mul_assoc] using (hb s).2.trans (hcont s)
  · intro z hz w hw'
    have hz' : h.symm z ∈ closedBall (y false) (c₀*θ*R) := by
      have hh := (hb false).2 (by simpa only [mul_assoc] using hz)
      obtain ⟨v,hv,hvz⟩ := hcont false hh
      rw [← hvz,h.symm_apply_apply]
      exact ball_subset_closedBall hv
    have hw' : h.symm w ∈ closedBall (y true) (c₀*θ*R) := by
      have hh := (hb true).2 (by simpa only [mul_assoc] using hw')
      obtain ⟨v,hv,hvw⟩ := hcont true hh
      rw [← hvw,h.symm_apply_apply]
      exact ball_subset_closedBall hv
    linarith only [(ball_range (hfc false) hz').2,hsep,(ball_range (hfc true) hw').1]

end CannonNode

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

lemma clip_difference_le {a b l u : ℝ} (hab : a ≤ b) (hlu : l ≤ u) :
    clip a b u-clip a b l ≤ u-l := by
  rw [clip_difference hab hlu]
  apply max_le (sub_nonneg.mpr hlu)
  linarith only [min_le_right b u, le_max_right a l]

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

theorem node_pattern {ι : Type*} [Fintype ι] (net : ι → X)
    (Ω : Set X) (hf : ContinuousOn f Ω) (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (L CE LE cPat : ℝ) (hL : 1 ≤ L) (hCE : 0 ≤ CE) (hLE : 0 ≤ LE)
    (hcPat : 0 < cPat) (hA : 2 < A) (hB : 0 ≤ B) (hc₀ : 2*L ≤ c₀)
    (hcoef₁ : CE*(2*L) ≤ (cPat/2)*(A-2)^2)
    (hcoef₂ : LE*(10*cPat)*(B+1)*(B+2) < c₀)
    (hsmall : (B+2)*ρ ≤ ε)
    (hnet : ∀ z, ∃ i, dist z (net i) ≤ cPat*radius ell (160*(qdim+1)*n))
    (hpaths : ∀ x u w : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist w x ≤ r →
      JoinedIn (ball x (L*r)) u w)
    (v : SourceNode f x₀ ε ell c₀ (B+1) S.kmin) (hv : S.good v)
    (h : X ≃ₜ X) (hexp : Expansion h v.center (radius ell v.depth) CE LE) :
    ∃ pat : Bool → ι, ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall (net (pat s)) (3*cPat*radius ell (160*(qdim+1)*n))) ∧
      (∀ s, S.κ*v.length ≤ f (h.symm (v₁ s))-f (h.symm (v₀ s))) ∧
      (∀ s, ∃ y ∈ S.Y v,
        closedBall (net (pat s)) (3*cPat*radius ell (160*(qdim+1)*n)) ⊆
          h '' ball y (c₀*radius ell (v.depth+160*(qdim+1)*n))) ∧
      ∀ z ∈ closedBall (net (pat false)) (3*cPat*radius ell (160*(qdim+1)*n)),
        ∀ w ∈ closedBall (net (pat true)) (3*cPat*radius ell (160*(qdim+1)*n)),
          f (h.symm z)+v.length/4 ≤ f (h.symm w) := by
  classical
  let θ := radius ell (160*(qdim+1)*n)
  let R := radius ell v.depth
  have hθ : 0 < θ := radius_pos _ _
  have hR : 0 < R := radius_pos _ _
  have hc₂ : 2 ≤ c₀ := (by linarith only [hL] : 2 ≤ 2*L).trans hc₀
  have hc : 0 < c₀ := by linarith only [hc₂]
  have hB' : 0 ≤ B+1 := by linarith only [hB]
  have hθsmall : c₀*θ ≤ 1 := S.pattern_small
  have hgeom (y : S.Y v) : (A-1)*R ≤ dist v.center y ∧ dist v.center y ≤ (B+1)*R := by
    simpa only [dist_comm] using S.Yloc v y y.property
  have hyΩ (y : S.Y v) : closedBall (y:X) (c₀*θ*R) ⊆ Ω := by
    intro z hz
    apply hloc
    rw [mem_closedBall] at hz ⊢
    have ht := dist_triangle z y v.center
    have ht' := dist_triangle z v.center x₀
    have hy := (S.Yloc v y y.property).2
    have hx := mem_closedBall.mp (v.center_mem hB')
    have hsm := mul_le_mul_of_nonneg_right hθsmall hR.le
    have hrho := mul_le_mul_of_nonneg_left (S.small v.depth v.lowerDepth)
      (by linarith only [hB] : 0 ≤ B+2)
    change (B+2)*R ≤ (B+2)*ρ at hrho
    linarith only [hz,ht,ht',hy,hx,hsm,hrho,hsmall]
  have hinner (y : S.Y v) : lower f (y:X) (2*θ*R) ≤ upper f y (2*θ*R) :=
    lower_le_upper (by positivity) ((hf.mono (hyΩ y)).mono
      (closedBall_subset_closedBall (by nlinarith only [hc₂,mul_pos hθ hR])))
  obtain ⟨i,j,hgi,hgj,hsep⟩ := hv
  simp only [radius_add] at hgi hgj hsep
  have hgi' : S.κ*v.length ≤ upper f (i:X) (2*θ*R)-lower f i (2*θ*R) := by
    apply hgi.trans
    simpa only [θ, R, mul_assoc] using clip_difference_le
      (show v.a ≤ v.a+(v.b-v.a)/4 by linarith only [v.ab]) (hinner i)
  have hgj' : S.κ*v.length ≤ upper f (j:X) (2*θ*R)-lower f j (2*θ*R) := by
    apply hgj.trans
    simpa only [θ, R, mul_assoc] using clip_difference_le
      (show v.a+3*(v.b-v.a)/4 ≤ v.b by linarith only [v.ab]) (hinner j)
  let y : Bool → X := fun s => if s then j else i
  have hy (s : Bool) : y s ∈ S.Y v := by cases s <;> exact Subtype.property _
  have hyloc (s : Bool) : (A-1)*R ≤ dist v.center (y s) ∧ dist v.center (y s) ≤ (B+1)*R := by
    cases s <;> exact hgeom _
  have hgap (s : Bool) : S.κ*v.length ≤ upper f (y s) (2*θ*R)-lower f (y s) (2*θ*R) := by
    cases s
    · exact hgi'
    · exact hgj'
  have hsep' : upper f (y false) (c₀*θ*R)+v.length/4 ≤ lower f (y true) (c₀*θ*R) := by
    simpa only [θ, R, y, Bool.false_eq_true, ↓reduceIte, SourceNode.length, mul_assoc] using hsep
  obtain ⟨pat,v₀,v₁,γ,hγ,hvar,hball,hrange⟩ := good_candidate_pattern net f Ω h v.center y
    R θ A (B+1) c₀ (2*L) cPat CE LE (S.κ*v.length) (v.length/4) hR hθ hA
    (by linarith only [hB]) hc (by linarith only [hL]) hcPat hCE hLE hθsmall
    hc₀ hc₂ hcoef₁ (by convert hcoef₂ using 1; ring) hexp hyloc
    (fun s => by cases s <;> exact hyΩ _) hf hnet
    (fun s u w hu hw => by
      simpa only [mul_assoc, mul_left_comm L 2] using
        hpaths (y s) u w (2*θ*R) (by positivity) (mem_closedBall.mp hu) (mem_closedBall.mp hw))
    hgap hsep'
  refine ⟨pat,v₀,v₁,γ,hγ,hvar,?_,hrange⟩
  intro s
  refine ⟨y s,hy s,?_⟩
  simpa only [θ, R, radius_add,mul_assoc] using hball s

end SourceConstruction

end CannonNode

end

section

open Set MeasureTheory
open scoped BigOperators

namespace CannonCrossEnergy

theorem weighted_interval_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      c ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    c * (b - a) ≤ ∑ i, w i * (U i - L i) := by
  have hint (l u v : ℝ) : Integrable ((Icc l u).indicator (fun _ : ℝ => v)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hle : (Icc a b).indicator (fun _ : ℝ => c) ≤
      fun t => ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t := by
    intro t
    by_cases ht : t ∈ Icc a b
    · simpa [Set.indicator_of_mem ht] using hcover t ht
    · rw [Set.indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => hw i) _)
  have hi := integral_mono (hint a b c)
    (integrable_finsetSum _ (fun i _ => hint (L i) (U i) (w i))) hle
  rw [integral_finsetSum _ (fun i _ => hint (L i) (U i) (w i))] at hi
  simpa only [integral_indicator_const _ measurableSet_Icc, Measure.real,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hLU _)), smul_eq_mul, mul_comm] using hi

end CannonCrossEnergy

namespace CannonCrossEnergyLocal

variable {X : Type*} [TopologicalSpace X]

open CannonCrossEnergy

lemma mem_rangeInterval {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) {x : X} (hx : x ∈ A) : f x ∈ rangeInterval f A := by
  have hc := hA.image_of_continuousOn hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hx),
    le_csSup hc.bddAbove (mem_image_of_mem f hx)⟩

lemma oscillation_nonneg {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) (hne : A.Nonempty) : 0 ≤ oscillation f A := by
  exact sub_nonneg.mpr (csInf_le_csSup (hne.image f)
    (hA.image_of_continuousOn hf).bddBelow (hA.image_of_continuousOn hf).bddAbove)

lemma rangeInterval_eq_image {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) (hne : A.Nonempty) (hcon : IsPreconnected A) :
    rangeInterval f A = f '' A := by
  apply le_antisymm
  · exact (hcon.image f hf).ordConnected.out
      ((hA.image_of_continuousOn hf).sInf_mem (hne.image f)) ((hA.image_of_continuousOn hf).sSup_mem (hne.image f))
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_rangeInterval hf hA hx

theorem level_continuum_cover {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (f w : X → ℝ)
    (S : Set X) (hCS : ∀ i, C i ⊆ S)
    (hf : ContinuousOn f S) (hw : ContinuousOn w S) (D : Set X) (hDS : D ⊆ S)
    (hD : IsCompact D) (hDne : D.Nonempty) (hDcon : IsPreconnected D)
    (hcover : ∀ x ∈ D, ∃ i, x ∈ C i) (t : ℝ) (hlevel : ∀ x ∈ D, f x = t) :
    oscillation w D ≤ ∑ i, (rangeInterval f (C i)).indicator
      (fun _ : ℝ => oscillation w (C i)) t := by
  classical
  let weights : ι → ℝ := fun i => if t ∈ rangeInterval f (C i) then 1 else 0
  have hweights : ∀ i, 0 ≤ weights i := by
    intro i
    dsimp [weights]
    split_ifs <;> norm_num
  have hrange : ∀ v ∈ rangeInterval w D,
      1 ≤ ∑ i, (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) v := by
    intro v hv
    rw [rangeInterval_eq_image (hw.mono hDS) hD hDne hDcon] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨i, hi⟩ := hcover x hx
    have hti : t ∈ rangeInterval f (C i) := by
      rw [← hlevel x hx]
      exact mem_rangeInterval (hf.mono (hCS i)) (hC i) hi
    have hwi : w x ∈ rangeInterval w (C i) := mem_rangeInterval (hw.mono (hCS i)) (hC i) hi
    calc
      1 = (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) (w x) := by
        simp [Set.indicator_of_mem hwi, weights, hti]
      _ ≤ ∑ j, (rangeInterval w (C j)).indicator (fun _ : ℝ => weights j) (w x) :=
        Finset.single_le_sum (f := fun j => (rangeInterval w (C j)).indicator
          (fun _ : ℝ => weights j) (w x)) (fun j _ => Set.indicator_nonneg
          (fun _ _ => hweights j) (w x)) (Finset.mem_univ i)
  have h := weighted_interval_cover
    (fun i => sInf (w '' C i)) (fun i => sSup (w '' C i)) weights
    (sInf (w '' D)) (sSup (w '' D)) 1
    (sub_nonneg.mp (oscillation_nonneg (hw.mono hDS) hD hDne))
    (fun i => sub_nonneg.mp (oscillation_nonneg (hw.mono (hCS i)) (hC i) (hne i)))
    hweights hrange
  simp only [one_mul] at h
  change oscillation w D ≤ _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : t ∈ rangeInterval f (C i)
  · simp [weights, ht, CannonCrossEnergy.oscillation]
  · simp [weights, ht]

theorem finite_cell_level_comparison {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (K : Set X)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ C i)
    (f w : X → ℝ) (S : Set X) (hKS : K ⊆ S) (hCS : ∀ i, C i ⊆ S)
    (hf : ContinuousOn f S) (hw : ContinuousOn w S)
    (a b b₀ : ℝ) (hab : a ≤ b)
    (hlevels : ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f x = t) ∧ b₀ ≤ oscillation w D) :
    b₀ * (b - a) ≤ ∑ i, oscillation f (C i) * oscillation w (C i) := by
  have hpoint : ∀ t ∈ Icc a b,
      b₀ ≤ ∑ i, (rangeInterval f (C i)).indicator
        (fun _ : ℝ => oscillation w (C i)) t := by
    intro t ht
    obtain ⟨D, hD, hDne, hDcon, hDK, hlevel, hwD⟩ := hlevels t ht
    exact hwD.trans (level_continuum_cover C hC hne f w S hCS hf hw D (hDK.trans hKS) hD hDne hDcon
      (fun x hx => hcover x (hDK hx)) t hlevel)
  have h := weighted_interval_cover
    (fun i => sInf (f '' C i)) (fun i => sSup (f '' C i))
    (fun i => oscillation w (C i)) a b b₀ hab
    (fun i => sub_nonneg.mp (oscillation_nonneg (hf.mono (hCS i)) (hC i) (hne i)))
    (fun i => oscillation_nonneg (hw.mono (hCS i)) (hC i) (hne i)) hpoint
  simpa only [CannonCrossEnergy.oscillation, mul_comm] using h

end CannonCrossEnergyLocal

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_ClopenNeighborhoodComponent
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
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonContinuum

lemma clopen_neighborhood_of_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X} (hU : IsOpen U)
    (hC : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let S := {s : Set X // IsClopen s ∧ x ∈ s}
  have hnull : Uᶜ ∩ ⋂ s : S, (s : Set X) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left_iff_subset.mpr hC)
  obtain ⟨T, hT⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : S => (s : Set X)) (fun s => s.property.1.isClosed)
    hnull
  refine ⟨⋂ s ∈ T, (s : Set X), isClopen_biInter_finset (fun s _ => s.property.1),
    mem_iInter₂.mpr (fun s _ => s.property.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp (Set.disjoint_iff_inter_eq_empty.mpr hT)

theorem component_meets_level {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (r : ℝ)
    (x : {z : X // r ≤ f z}) (hbelow : ∃ y : X, f y < r) :
    ∃ z ∈ connectedComponent x, f (z : X) = r := by
  let K : Set X := {z | r ≤ f z}
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  by_contra hn
  push Not at hn
  have hC : connectedComponent x ⊆ {z : K | r < f (z : X)} := by
    intro z hz
    exact lt_of_le_of_ne z.property (Ne.symm (hn z hz))
  obtain ⟨W, hW, hxW, hWU⟩ := clopen_neighborhood_of_component (X := K) x
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val)) hC
  let V : Set X := Subtype.val '' W
  have hVc : IsClosed V := hK.isClosedMap_subtype_val W hW.isClosed
  have hVo : IsOpen V := by
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW.isOpen
    have hV : V = O ∩ {z | r < f z} := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        exact ⟨by simpa only [← hOW, mem_preimage] using hz', hWU hz'⟩
      · rintro ⟨hzO, hzr⟩
        refine ⟨⟨z, show r ≤ f z from hzr.le⟩, ?_, rfl⟩
        simpa only [← hOW, mem_preimage] using hzO
    rw [hV]
    exact hO.inter (isOpen_lt continuous_const hf)
  have hVall : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ ⟨x, x, hxW, rfl⟩
  obtain ⟨y, hy⟩ := hbelow
  have hyV : y ∈ V := by rw [hVall]; trivial
  obtain ⟨z, hz, hzy⟩ := hyV
  have := z.property
  rw [hzy] at this
  exact (not_lt_of_ge this) hy

theorem stop_continuum {X : Type*} [MetricSpace X]
    {D : Set X} (hD : IsCompact D) (hconn : IsConnected D)
    {p x : X} {r : ℝ} (hx : x ∈ D) (hxr : r < dist x p)
    (hin : ∃ y ∈ D, dist y p < r) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C ⊆ D ∧ x ∈ C ∧
      (∃ z ∈ C, dist z p = r) ∧ ∀ z ∈ C, r ≤ dist z p := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let : PreconnectedSpace D := Subtype.preconnectedSpace hconn.isPreconnected
  let f : D → ℝ := fun z => dist (z : X) p
  have hf : Continuous f := continuous_subtype_val.dist continuous_const
  let K : Set D := {z | r ≤ f z}
  let xK : K := ⟨⟨x, hx⟩, hxr.le⟩
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hbelow : ∃ y : D, f y < r := by
    obtain ⟨y, hyD, hyr⟩ := hin
    exact ⟨⟨y, hyD⟩, hyr⟩
  obtain ⟨z, hz, hzr⟩ := component_meets_level f hf r xK hbelow
  let g : K → X := fun z => z.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  refine ⟨g '' connectedComponent xK, isClosed_connectedComponent.isCompact.image hg,
    isConnected_connectedComponent.image g hg.continuousOn, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact y.val.property
  · exact ⟨xK, mem_connectedComponent, rfl⟩
  · exact ⟨g z, ⟨z, hz, rfl⟩, hzr⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact y.property

end CannonContinuum

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_NoVanishingLocalMesh
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
open Set MeasureTheory
open scoped BigOperators

namespace CannonCrossEnergyLocal

open Set Metric Filter Topology CannonApprox CannonCrossEnergy

theorem no_vanishing_local_mesh {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (S : ℕ → Set X) (K : Set X)
    (hKS : ∀ᶠ n in atTop, K ⊆ S n)
    (hCS : ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (2*r n) ⊆ S n)
    (hf : ∀ᶠ n in atTop, ContinuousOn (f n) (S n))
    (hw : ∀ᶠ n in atTop, ContinuousOn (w n) (S n))
    (a b q : ℝ) (hab : a < b) (hq : 0 < q)
    (hlevels : ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f n x = t) ∧ q ≤ CannonCrossEnergy.oscillation (w n) D)
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n) K) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n) K) atTop (𝓝 0)) :
    False := by
  classical
  have he := hfe.mul hwe
  simp only [mul_zero] at he
  have hlow : (q*(b-a))^2 ≤ (0:ℝ) := by
    apply ge_of_tendsto he
    filter_upwards [hlevels,hf,hw,hKS,hCS] with n hn hfn hwn hKSn hCSn
    let α := {i : ι n // (ball (p n i) (2*r n) ∩ K).Nonempty}
    let C : α → Set X := fun i => closedBall (p n i.val) (2*r n)
    have hcover : ∀ x ∈ K, ∃ i : α, x ∈ C i := by
      intro x hx
      obtain ⟨i,hi⟩ := hpnet n x
      have hxi : x ∈ ball (p n i) (2*r n) := by
        rw [mem_ball,dist_comm]
        linarith [hr n]
      exact ⟨⟨i,⟨x,hxi,hx⟩⟩, ball_subset_closedBall hxi⟩
    have hsum := finite_cell_level_comparison C (fun _ => isCompact_closedBall _ _)
      (fun _ => nonempty_closedBall.mpr (mul_nonneg (by norm_num) (hr n).le)) K hcover (f n) (w n)
      (S n) hKSn (fun i => hCSn i.val i.property) hfn hwn a b q hab.le hn
    calc
      (q*(b-a))^2 ≤ (∑ i, CannonCrossEnergy.oscillation (f n) (C i)*
          CannonCrossEnergy.oscillation (w n) (C i))^2 :=
        pow_le_pow_left₀ (mul_nonneg hq.le (sub_nonneg.mpr hab.le)) hsum 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  exact (not_le_of_gt (sq_pos_of_pos (mul_pos hq (sub_pos.mpr hab)))) hlow

end CannonCrossEnergyLocal

open Set Topology

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_EscapingLevelEnergyObstruction
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
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonCrossEnergyLocal

open Set Metric Filter Topology CannonApprox CannonCrossEnergy CannonContinuum

theorem escaping_level_energy_obstruction {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (S : ℕ → Set X)
    (b c : X) (ρ ε : ℝ) (P : Set X)
    (hP : ∀ x ∈ P, ρ < dist x b)
    (a d q : ℝ) (had : a < d) (hq : 0 < q)
    (hKS : ∀ᶠ n in atTop, {z | ρ ≤ dist z b ∧ ε ≤ dist z c} ⊆ S n)
    (hCS : ∀ᶠ n in atTop, ∀ i,
      (ball (p n i) (2*r n) ∩ {z | ρ ≤ dist z b ∧ ε ≤ dist z c}).Nonempty →
      closedBall (p n i) (2*r n) ⊆ S n)
    (hf : ∀ᶠ n in atTop, ContinuousOn (f n) (S n))
    (hw : ∀ᶠ n in atTop, ContinuousOn (w n) (S n))
    (hgap : ∀ᶠ n in atTop, ∀ x ∈ P, ∀ z, dist z b = ρ →
      q ≤ |w n x-w n z|)
    (hlevels : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ P).Nonempty ∧
      (∀ x ∈ D, f n x = t) ∧ (∃ z ∈ D, dist z b < ρ) ∧
      ∀ z ∈ D, ε ≤ dist z c)
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0)) : False := by
  apply no_vanishing_local_mesh ι p r hr hpnet f w S _ hKS hCS hf hw a d q had hq _ hfe hwe
  filter_upwards [hlevels,hgap,hw,hKS] with n hn hgn hwn hKSn
  intro t ht
  obtain ⟨D,hD,hDconn,⟨x,hxD,hxP⟩,hfD,hin,havoid⟩ := hn t ht
  obtain ⟨C,hC,hCconn,hCD,hxC,⟨z,hzC,hzr⟩,hout⟩ :=
    stop_continuum hD hDconn hxD (hP x hxP) hin
  have hCK : C ⊆ {z | ρ ≤ dist z b ∧ ε ≤ dist z c} :=
    fun v hv => ⟨hout v hv,havoid v (hCD hv)⟩
  have hwC : ContinuousOn (w n) C := hwn.mono (hCK.trans hKSn)
  have hxx := mem_rangeInterval hwC hC hxC
  have hzz := mem_rangeInterval hwC hC hzC
  have habs : |w n x-w n z| ≤ CannonCrossEnergy.oscillation (w n) C := by
    apply abs_le.mpr
    rcases hxx with ⟨hxlo,hxhi⟩
    rcases hzz with ⟨hzlo,hzhi⟩
    constructor <;> dsimp [CannonCrossEnergy.oscillation] <;> linarith
  exact ⟨C,hC,hCconn.nonempty,hCconn.isPreconnected,hCK,
    fun v hv => hfD v (hCD hv),(hgn x hxP z hzr).trans habs⟩

end CannonCrossEnergyLocal

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_FarDiam
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
open Set MeasureTheory
open scoped BigOperators
open Set Topology
open Set Metric Filter Topology

namespace CannonMagnification

lemma exists_far_of_diam {X : Type*} [MetricSpace X] (A : Set X)
    (d : ℝ) (hd : 0 < d) (hdiam : d ≤ diam A) (x : X) :
    ∃ y ∈ A, d/3 ≤ dist x y := by
  by_contra hn
  push Not at hn
  have hh : diam A ≤ 2*d/3 := by
    apply diam_le_of_forall_dist_le (by positivity)
    intro y hy z hz
    have ht := dist_triangle y x z
    rw [dist_comm y x] at ht
    linarith [hn y hy,hn z hz]
  linarith

end CannonMagnification

end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_IntervalAvoidingShortRange
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
namespace CannonPairs

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal

lemma interval_avoiding_short_range {u v l h : ℝ} (huv : u < v)
    (hshort : h-l < (v-u)/4) :
    ∃ a d e : ℝ, u < a ∧ a < d ∧ d < v ∧ 0 < e ∧
      ∀ t ∈ Icc a d, ∀ z ∈ Icc l h, e ≤ |t-z| := by
  by_cases hl : u+(v-u)/4 < l
  · refine ⟨u+(v-u)/12,u+(v-u)/6,(v-u)/12,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht z hz
    have hh : (v-u)/12 ≤ z-t := by linarith only [hl,ht.2,hz.1]
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hl' := le_of_not_gt hl
    refine ⟨u+2*(v-u)/3,u+5*(v-u)/6,(v-u)/12,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht z hz
    exact (show (v-u)/12 ≤ t-z by linarith only [huv,hshort,hl',ht.1,hz.2]).trans
      (le_abs_self _)

lemma cells_into_puncture_exterior {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) (p : ∀ n, ι n → X) (r : ℕ → ℝ)
    (hrlim : Tendsto r atTop (𝓝 0)) (b c : X) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i,
      (ball (p n i) (2*r n) ∩ {z | ρ ≤ dist z b ∧ ε ≤ dist z c}).Nonempty →
      closedBall (p n i) (2*r n) ⊆ {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c} := by
  have ht : ∀ᶠ n in atTop, 4*r n < min ρ ε/2 := by
    have hh : Tendsto (fun n => 4*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => 4*r n) atTop (𝓝 (4*0)))
    exact hh.eventually_lt_const (div_pos (lt_min hρ hε) (by norm_num))
  filter_upwards [ht] with n hn
  intro i hi z hz
  obtain ⟨t,hti,htK⟩ := hi
  have htz := dist_triangle t (p n i) z
  have hti' := mem_ball.mp hti
  have hzi := mem_closedBall.mp hz
  rw [dist_comm (p n i) z] at htz
  have hbtri := dist_triangle t z b
  have hctri := dist_triangle t z c
  have hbmin := min_le_left ρ ε
  have hcmin := min_le_right ρ ε
  obtain ⟨htb,htc⟩ := htK
  constructor <;> linarith

theorem path_forces_opposite_oscillation {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (v₀ v₁ : X) (γ : Path v₀ v₁) (hvar : W v₀ < W v₁)
    (hP : ∀ x ∈ range γ, ρ < dist x b)
    (q : ℝ) (hq : 0 < q)
    (hgap : ∀ x ∈ range γ, ∀ z ∈ closedBall b ρ, q ≤ |V x-V z|)
    (hW : ContinuousOn W (closedBall c ε))
    (hflim : TendstoUniformlyOn f W atTop (closedBall c ε))
    (hwlimP : TendstoUniformlyOn w V atTop (range γ))
    (hwlimB : TendstoUniformlyOn w V atTop (closedBall b ρ))
    (hfcont : ∀ᶠ n in atTop,
      ContinuousOn (f n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hwcont : ∀ᶠ n in atTop,
      ContinuousOn (w n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hlevels : ∀ a d : ℝ, W v₀ < a → a < d → d < W v₁ →
      ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
        IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
        (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ) :
    (W v₁-W v₀)/4 ≤ CannonCrossEnergy.oscillation W (closedBall c ε) := by
  by_contra hn
  have hshort : sSup (W '' closedBall c ε)-sInf (W '' closedBall c ε) <
      (W v₁-W v₀)/4 := lt_of_not_ge hn
  obtain ⟨a,d,e,hva,had,hdv,he,hegap⟩ := interval_avoiding_short_range hvar hshort
  have hCc : IsCompact (closedBall c ε) := isClosed_closedBall.isCompact
  have havoid : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∀ z ∈ closedBall c ε, f n z ≠ t := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hflim e he] with n hn
    intro t ht z hz hzt
    have hwr := CannonCrossEnergyLocal.mem_rangeInterval hW hCc hz
    have hg := hegap t ht (W z) hwr
    have hh := hn z hz
    rw [Real.dist_eq,hzt,abs_sub_comm] at hh
    exact (not_lt_of_ge hg) hh
  have hwgap : ∀ᶠ n in atTop, ∀ x ∈ range γ, ∀ z, dist z b = ρ →
      q/2 ≤ |w n x-w n z| := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hwlimP (q/4) (by positivity),
      Metric.tendstoUniformlyOn_iff.mp hwlimB (q/4) (by positivity)] with n hnP hnB
    intro x hx z hz
    have hzB : z ∈ closedBall b ρ := mem_closedBall.mpr hz.le
    have hxerr := hnP x hx
    have hzerr := hnB z hzB
    rw [Real.dist_eq] at hxerr hzerr
    have hg := hgap x hx z hzB
    have ha := abs_sub_le (V x) (w n x) (V z)
    have hb := abs_sub_le (w n x) (w n z) (V z)
    rw [abs_sub_comm (w n z) (V z)] at hb
    linarith
  apply escaping_level_energy_obstruction ι p r hr hpnet f w
    (fun _ => {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c}) b c ρ ε (range γ) hP a d (q/2)
    had (by positivity) (Eventually.of_forall (by
      intro n z hz
      constructor <;> linarith [hz.1,hz.2]))
    (cells_into_puncture_exterior ι p r hrlim b c hρ hε) hfcont hwcont hwgap _ hfe hwe
  filter_upwards [hlevels a d hva had hdv,havoid] with n hn hnA
  intro t ht
  obtain ⟨D,hD,hDconn,hDP,hDlev,hDesc⟩ := hn t ht
  refine ⟨D,hD,hDconn,hDP,hDlev,hDesc,?_⟩
  intro z hz
  by_contra hnz
  exact hnA t ht z (mem_closedBall.mpr (lt_of_not_ge hnz).le) (hDlev z hz)

end CannonPairs

namespace CannonPairs

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal

lemma separated_paths_avoid_short_range {X : Type*} [TopologicalSpace X]
    (V : X → ℝ) (P₀ P₁ E : Set X) (hP₀ : IsCompact P₀) (hne : P₀.Nonempty)
    (hE : IsCompact E) (hVP : ContinuousOn V P₀) (hVE : ContinuousOn V E)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ P₀, ∀ y ∈ P₁, V x+δ ≤ V y)
    (hshort : CannonCrossEnergy.oscillation V E < δ/4) :
    (∀ x ∈ P₀, ∀ z ∈ E, δ/4 ≤ |V x-V z|) ∨
    (∀ x ∈ P₁, ∀ z ∈ E, δ/4 ≤ |V x-V z|) := by
  let u₀ := sSup (V '' P₀)
  have hbound₀ : ∀ x ∈ P₀, V x ≤ u₀ := by
    intro x hx
    exact le_csSup (hP₀.image_of_continuousOn hVP).bddAbove (mem_image_of_mem V hx)
  have hbound₁ : ∀ y ∈ P₁, u₀+δ ≤ V y := by
    intro y hy
    have hh : u₀ ≤ V y-δ := csSup_le (hne.image V) (by
      rintro _ ⟨x,hx,rfl⟩
      linarith only [hsep x hx y hy])
    linarith only [hh]
  by_cases hhi : sSup (V '' E) ≤ u₀+δ/2
  · right
    intro x hx z hz
    have hzx := (CannonCrossEnergyLocal.mem_rangeInterval hVE hE hz).2
    have hxx := hbound₁ x hx
    exact (show δ/4 ≤ V x-V z by linarith only [hhi,hzx,hxx,hδ]).trans (le_abs_self _)
  · left
    have hhi' := lt_of_not_ge hhi
    intro x hx z hz
    have hzx := (CannonCrossEnergyLocal.mem_rangeInterval hVE hE hz).1
    have hxx := hbound₀ x hx
    dsimp [CannonCrossEnergy.oscillation] at hshort
    have hh : δ/4 ≤ V z-V x := by linarith only [hhi',hzx,hxx,hshort]
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)

theorem two_path_pair_alternative {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (gap δ : ℝ) (hgap : 0 < gap) (hδ : 0 < δ)
    (hvar : ∀ s, gap ≤ W (v₁ s)-W (v₀ s))
    (hP : ∀ s, ∀ x ∈ range (γ s), ρ < dist x b)
    (hsep : ∀ x ∈ range (γ false), ∀ y ∈ range (γ true), V x+δ ≤ V y)
    (hVP : ContinuousOn V (range (γ false)))
    (hVE : ContinuousOn V (closedBall b ρ))
    (hW : ContinuousOn W (closedBall c ε))
    (hflim : TendstoUniformlyOn f W atTop (closedBall c ε))
    (hwlimP : ∀ s, TendstoUniformlyOn w V atTop (range (γ s)))
    (hwlimB : TendstoUniformlyOn w V atTop (closedBall b ρ))
    (hfcont : ∀ᶠ n in atTop,
      ContinuousOn (f n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hwcont : ∀ᶠ n in atTop,
      ContinuousOn (w n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hlevels : ∀ s, ∀ a d : ℝ, W (v₀ s) < a → a < d → d < W (v₁ s) →
      ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
        IsCompact D ∧ IsConnected D ∧ (D ∩ range (γ s)).Nonempty ∧
        (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ) :
    gap/4 ≤ CannonCrossEnergy.oscillation W (closedBall c ε) ∨
      δ/4 ≤ CannonCrossEnergy.oscillation V (closedBall b ρ) := by
  by_cases hv : δ/4 ≤ CannonCrossEnergy.oscillation V (closedBall b ρ)
  · exact Or.inr hv
  left
  have hor := separated_paths_avoid_short_range V (range (γ false)) (range (γ true))
    (closedBall b ρ) (isCompact_range (γ false).continuous) (range_nonempty _)
    isClosed_closedBall.isCompact hVP hVE δ hδ hsep (lt_of_not_ge hv)
  obtain ⟨s,hs⟩ : ∃ s : Bool, ∀ x ∈ range (γ s), ∀ z ∈ closedBall b ρ,
      δ/4 ≤ |V x-V z| := by
    rcases hor with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have hh := path_forces_opposite_oscillation ι p r hr hrlim hpnet f w W V b c ρ ε
    hρ hε (v₀ s) (v₁ s) (γ s) (by linarith only [hgap,hvar s]) (hP s) (δ/4)
    (by positivity) hs hW hflim (hwlimP s) hwlimB hfcont hwcont hfe hwe (hlevels s)
  linarith only [hh,hvar s]

end CannonPairs

end

namespace CannonPairs

open Set Metric Filter Topology CannonMagnification CannonApprox

lemma uniformly_on_preimage {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (H : ℕ → X → ℝ) (f : X → ℝ) (Ω T : Set X)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (hT : IsCompact T) (hTΩ : h.symm '' T ⊆ Ω) :
    TendstoUniformlyOn (fun n => H n ∘ h.symm) (f ∘ h.symm) atTop T :=
  ((hlim (h.symm '' T) (hT.image h.symm.continuous) hTΩ).comp h.symm).mono
    (fun _ hx => mem_image_of_mem _ hx)

lemma continuousOn_preimage {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X)
    (f : X → ℝ) (Ω T : Set X) (hf : ContinuousOn f Ω) (hTΩ : h.symm '' T ⊆ Ω) :
    ContinuousOn (f ∘ h.symm) T :=
  hf.comp h.symm.continuous.continuousOn (fun _ hx => hTΩ (mem_image_of_mem _ hx))

lemma puncture_exterior_domain {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R U A ε : ℝ) (Ω : Set X)
    (hR : 0 < R) (hA : 0 < A) (hroom : 2*U/A ≤ ε)
    (hΩ : closedBall x ε ⊆ Ω)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R) :
    h.symm '' {z | A*R/2 ≤ dist z p} ⊆ Ω := by
  rintro y ⟨z,hz,rfl⟩
  apply hΩ
  rw [mem_closedBall,dist_comm]
  have hD : 0 ≤ denominator x R (h.symm z) := hR.le.trans (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_right hz hD
  have hu := hupper (h.symm z)
  rw [h.apply_symm_apply] at hu
  have hd : denominator x R (h.symm z) ≤ 2*U/A := by
    apply (le_div_iff₀ hA).mpr
    have hh : R*(A*denominator x R (h.symm z)) ≤ R*(2*U) := by
      nlinarith only [hm,hu]
    simpa only [mul_comm A] using (mul_le_mul_iff_right₀ hR).mp hh
  exact (le_max_right _ _).trans (hd.trans hroom)

lemma pattern_puncture_distance {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R V B cutoff : ℝ)
    (hR : 0 < R) (hV : 0 < V) (hB : 1 ≤ B) (hsmall : B*R ≤ cutoff)
    (hlower : ∀ y, denominator x R y ≤ cutoff →
      R ≤ V*dist (h y) p*denominator x R y)
    (T : Set X) (hT : h.symm '' T ⊆ closedBall x (B*R)) :
    ∀ z ∈ T, 1/(V*B) ≤ dist z p := by
  intro z hz
  have hd := mem_closedBall.mp (hT (mem_image_of_mem _ hz))
  have hD : denominator x R (h.symm z) ≤ B*R := by
    apply max_le (by nlinarith only [hB,hR])
    simpa only [dist_comm] using hd
  have hh := hlower (h.symm z) (hD.trans hsmall)
  rw [h.apply_symm_apply] at hh
  have hm := mul_le_mul_of_nonneg_left hD (mul_nonneg hV.le (dist_nonneg (x:=z) (y:=p)))
  have hh' : R*1 ≤ R*(V*B*dist z p) := by nlinarith only [hh,hm]
  have hz' := (mul_le_mul_iff_right₀ hR).mp hh'
  exact (div_le_iff₀ (mul_pos hV (zero_lt_one.trans_le hB))).mpr (by nlinarith only [hz'])

lemma wide_image_enters {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R U A d : ℝ) (hR : 0 < R)
    (hd : 0 < d) (hA : 3*U/d < A)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (K : Set X) (hK : d ≤ diam K) :
    ∃ z ∈ h '' K, dist z p < A*R := by
  obtain ⟨y,hy,hyfar⟩ := exists_far_of_diam K d hd hK x
  have hm := mul_le_mul_of_nonneg_left (hyfar.trans (le_max_right R (dist x y)))
    (dist_nonneg (x:=h y) (y:=p))
  change dist (h y) p*(d/3) ≤ dist (h y) p*denominator x R y at hm
  have hh : dist (h y) p ≤ (3*U/d)*R := by
    apply (mul_le_mul_iff_left₀ (show 0 < d/3 by positivity)).mp
    calc
      _ ≤ U*R := hm.trans (hupper y)
      _ = ((3*U/d)*R)*(d/3) := by field_simp
  exact ⟨h y,mem_image_of_mem h hy,hh.trans_lt (mul_lt_mul_of_pos_right hA hR)⟩

theorem transformed_level_paths {X : Type*} [MetricSpace X] [CompactSpace X]
    (Ω : Set X) (H : ℕ → X → ℝ) (f : X → ℝ)
    (hfunit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (d : ℝ) (hd : 0 < d)
    (hlevels : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ d ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
      ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
        (K ∩ range γ).Nonempty)
    (h : X ≃ₜ X) (x p : X) (R U A : ℝ) (hR : 0 < R) (hA : 3*U/d < A)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (v₀ v₁ : X) (γ : Path v₀ v₁) (hγ : h.symm '' range γ ⊆ Ω)
    (a b : ℝ) (ha : f (h.symm v₀) < a) (_hab : a < b) (hb : b < f (h.symm v₁)) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
      (∀ y ∈ D, (H n ∘ h.symm) y=t) ∧ ∃ y ∈ D, dist y p < A*R := by
  let π : Path (h.symm v₀) (h.symm v₁) := γ.map h.symm.continuous
  have hπ : range π ⊆ Ω := by
    rintro y ⟨s,rfl⟩
    exact hγ (mem_image_of_mem _ (mem_range_self s))
  have huv₀ : 0 ≤ f (h.symm v₀) := (hfunit _ (hπ π.source_mem_range)).1
  have huv₁ : f (h.symm v₁) ≤ 1 := (hfunit _ (hπ π.target_mem_range)).2
  have hconv := hlim (range π) (isCompact_range π.continuous) hπ
  have ht₀ : ∀ᶠ n in atTop, H n (h.symm v₀) < a :=
    (hconv.tendsto_at π.source_mem_range).eventually_lt_const ha
  have ht₁ : ∀ᶠ n in atTop, b < H n (h.symm v₁) :=
    (hconv.tendsto_at π.target_mem_range).eventually_const_lt hb
  filter_upwards [ht₀,ht₁] with n hn₀ hn₁
  intro t ht
  have htt : t ∈ Ioo (0:ℝ) 1 := ⟨huv₀.trans_lt (ha.trans_le ht.1),ht.2.trans_lt (hb.trans_le huv₁)⟩
  obtain ⟨K,hK,hKc,hKd,hKt,hhit⟩ := hlevels n t htt
  obtain ⟨z,hz,⟨s,hs⟩⟩ := hhit _ _ π hπ (hn₀.trans_le ht.1) (ht.2.trans_lt hn₁)
  refine ⟨h '' K,hK.image h.continuous,hKc.image h h.continuous.continuousOn,?_,?_,
    wide_image_enters h x p R U A d hR hd hA hupper K hKd⟩
  · refine ⟨γ s,?_,mem_range_self s⟩
    refine ⟨z,hz,?_⟩
    rw [← hs]
    exact h.apply_symm_apply (γ s)
  · rintro y ⟨z,hz,rfl⟩
    simpa only [Function.comp_apply,h.symm_apply_apply] using hKt z hz

end CannonPairs

open Set Filter Metric Topology CannonMagnification CannonApprox

namespace CannonPairs

theorem fixed_source_pair {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (Ω : Set X) (H : ℕ → X → ℝ) (f : X → ℝ)
    (hf : ContinuousOn f Ω) (hH : ∀ n, ContinuousOn (H n) Ω)
    (hfunit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (d : ℝ) (hd : 0 < d)
    (hlevels : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ d ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
      ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
        (K ∩ range γ).Nonempty)
    (hi hj : X ≃ₜ X) (xi xj pi pj : X) (R U A ε : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hwide : 3*U/d < A)
    (hroom : 2*U/A ≤ ε) (hΩi : closedBall xi ε ⊆ Ω) (hΩj : closedBall xj ε ⊆ Ω)
    (hui : ∀ y, dist (hi y) pi*denominator xi R y ≤ U*R)
    (huj : ∀ y, dist (hj y) pj*denominator xj R y ≤ U*R)
    (hfar : 2*A*R ≤ dist pi pj)
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (hP : ∀ s z, z ∈ range (γ s) → A*R < dist z pi ∧ A*R < dist z pj)
    (gap δ : ℝ) (hgap : 0 < gap) (hδ : 0 < δ)
    (hvar : ∀ s, gap ≤ f (hi.symm (v₁ s))-f (hi.symm (v₀ s)))
    (hsep : ∀ x ∈ range (γ false), ∀ y ∈ range (γ true),
      f (hj.symm x)+δ ≤ f (hj.symm y))
    (hei : ∀ K : Set X, IsCompact K → hi.symm '' K ⊆ Ω →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (H n ∘ hi.symm) K) atTop (𝓝 0))
    (hej : ∀ K : Set X, IsCompact K → hj.symm '' K ⊆ Ω →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (H n ∘ hj.symm) K) atTop (𝓝 0)) :
    gap/4 ≤ CannonCrossEnergy.oscillation f (hi.symm '' closedBall pj (A*R)) ∨
      δ/4 ≤ CannonCrossEnergy.oscillation f (hj.symm '' closedBall pi (A*R)) := by
  have hρ : 0 < A*R := mul_pos hA hR
  have hDi := puncture_exterior_domain hi xi pi R U A ε Ω hR hA hroom hΩi hui
  have hDj := puncture_exterior_domain hj xj pj R U A ε Ω hR hA hroom hΩj huj
  have hbi : hi.symm '' closedBall pj (A*R) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDi
    intro z hz
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle pi z pj
    rw [dist_comm pi z] at htri
    change A*R/2 ≤ dist z pi
    linarith only [hfar,htri,hz',hρ]
  have hbj : hj.symm '' closedBall pi (A*R) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDj
    intro z hz
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle pi z pj
    rw [dist_comm pi z] at htri
    change A*R/2 ≤ dist z pj
    linarith only [hfar,htri,hz',hρ]
  have hpathi (s : Bool) : hi.symm '' range (γ s) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDi
    intro z hz
    change A*R/2 ≤ dist z pi
    linarith only [(hP s z hz).1,hρ]
  have hpathj (s : Bool) : hj.symm '' range (γ s) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDj
    intro z hz
    change A*R/2 ≤ dist z pj
    linarith only [(hP s z hz).2,hρ]
  let T : Set X := {z | A*R/2 ≤ dist z pi ∧ A*R/2 ≤ dist z pj}
  let K : Set X := {z | A*R ≤ dist z pi ∧ A*R ≤ dist z pj}
  have hTi : hi.symm '' T ⊆ Ω :=
    (image_mono (fun _ hz => hz.1)).trans hDi
  have hTj : hj.symm '' T ⊆ Ω :=
    (image_mono (fun _ hz => hz.2)).trans hDj
  have hKT : K ⊆ T := by
    intro z hz
    exact ⟨(by linarith only [hρ] : A*R/2 ≤ A*R).trans hz.1,
      (by linarith only [hρ] : A*R/2 ≤ A*R).trans hz.2⟩
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hh := two_path_pair_alternative ι p r hr hrlim hpnet
    (fun n => H n ∘ hi.symm) (fun n => H n ∘ hj.symm)
    (f ∘ hi.symm) (f ∘ hj.symm) pi pj (A*R) (A*R) hρ hρ v₀ v₁ γ gap δ
    hgap hδ hvar (fun s z hz => (hP s z hz).1) hsep
    (continuousOn_preimage hj f Ω _ hf (hpathj false))
    (continuousOn_preimage hj f Ω _ hf hbj)
    (continuousOn_preimage hi f Ω _ hf hbi)
    (uniformly_on_preimage hi H f Ω _ hlim isClosed_closedBall.isCompact hbi)
    (fun s => uniformly_on_preimage hj H f Ω _ hlim (isCompact_range (γ s).continuous) (hpathj s))
    (uniformly_on_preimage hj H f Ω _ hlim isClosed_closedBall.isCompact hbj)
    (Eventually.of_forall (fun n => continuousOn_preimage hi (H n) Ω T (hH n) hTi))
    (Eventually.of_forall (fun n => continuousOn_preimage hj (H n) Ω T (hH n) hTj))
    (hei K hK ((image_mono hKT).trans hTi))
    (hej K hK ((image_mono hKT).trans hTj))
    (fun s a b ha hab hb => transformed_level_paths Ω H f hfunit hlim d hd hlevels
      hi xi pi R U A hR hwide hui (v₀ s) (v₁ s) (γ s) (hpathi s) a b ha hab hb)
  simpa only [CannonCrossEnergy.oscillation, image_comp] using hh

end CannonPairs

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPatternSetup
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
namespace CannonApprox

open Set Metric Filter Topology CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.margins {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hL : 1 ≤ L) (_hCE : 0 ≤ CE) (hLE : 0 ≤ LE) :
    2 < F.A ∧ 0 ≤ F.B ∧ 0 < F.c₀ ∧ 2*L ≤ F.c₀ ∧
      CE*(2*L) ≤ (F.cPat/2)*(F.A-2)^2 ∧
      LE*(10*F.cPat)*(F.B+1)*(F.B+2) < F.c₀ ∧ 4*(F.B+1) < F.H := by
  have hc : 0 < F.c₀ := by linarith only [F.core,hL]
  have hA : 2 < F.A := by rw [F.inner]; nlinarith only [hc,hL]
  have hB : 0 ≤ F.B := by rw [F.outer]; linarith only [hA]
  have hpat : CE*(2*L) = (F.cPat/2)*(F.A-2)^2 := by
    rw [F.pattern]
    field_simp [ne_of_gt (sub_pos.mpr hA)]
  have hm : LE*(10*F.cPat)*(F.B+1)*(F.B+2) ≤ 12*F.cPat*(F.B+2)^2*LE := by
    have hb : 0 ≤ F.B+2 := by positivity
    have hnorm : LE*(10*F.cPat)*(F.B+1)*(F.B+2) =
        (10*(F.B+1))*((F.cPat*LE)*(F.B+2)) := by ring
    rw [hnorm]
    calc
      _ ≤ (12*(F.B+2))*((F.cPat*LE)*(F.B+2)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hB])
          (mul_nonneg (mul_nonneg F.pattern_pos.le hLE) hb)
      _ = _ := by ring
  exact ⟨hA,hB,hc,by linarith only [F.core],hpat.le,hm.trans_lt F.margin,
    (le_max_left _ _).trans_lt F.separation⟩

omit [CompactSpace X] in
lemma FlowSetup.center_puncture {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hB : 0 ≤ F.B+1) (g : ℕ) (i : Fin (F.S.flow.size g)) :
    F.ε ≤ dist (F.S.center g i) T.z₀ := by
  by_contra hn
  have hi := mem_closedBall.mp (F.S.center_mem hB g i)
  apply T.z₀not (F.local_domain ?_)
  rw [mem_closedBall]
  have ht := dist_triangle T.z₀ (F.S.center g i) T.x₀
  rw [dist_comm T.z₀ (F.S.center g i)] at ht
  linarith only [ht,hi,lt_of_not_ge hn]

theorem RecordData.pattern_pair (T : RecordData action ι p r)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (gi gj : Γ) (xi xj pi pj : X) (R U V A B cutoff ε : ℝ)
    (hR : 0 < R) (hV : 0 < V) (hA : 0 < A) (hB : 1 ≤ B)
    (hwide : 3*U/T.H_diameter < A) (hroom : 2*U/A ≤ ε)
    (hΩi : closedBall xi ε ⊆ T.Ω) (hΩj : closedBall xj ε ⊆ T.Ω)
    (hui : ∀ y, dist (action gi y) pi*denominator xi R y ≤ U*R)
    (huj : ∀ y, dist (action gj y) pj*denominator xj R y ≤ U*R)
    (hli : ∀ y, denominator xi R y ≤ cutoff →
      R ≤ V*dist (action gi y) pi*denominator xi R y)
    (hlj : ∀ y, denominator xj R y ≤ cutoff →
      R ≤ V*dist (action gj y) pj*denominator xj R y)
    (hsmall : B*R ≤ cutoff) (havoid : A*R < 1/(V*B)) (hfar : 2*A*R ≤ dist pi pj)
    (Pat : Bool → Set X)
    (hPati : ∀ s, (action gi).symm '' Pat s ⊆ closedBall xi (B*R))
    (hPatj : ∀ s, (action gj).symm '' Pat s ⊆ closedBall xj (B*R))
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (hγ : ∀ s, range (γ s) ⊆ Pat s)
    (κ li lj : ℝ) (hκ : 0 < κ) (hli_pos : 0 < li) (hlj_pos : 0 < lj)
    (hgap : ∀ s, κ*li ≤ T.f ((action gi).symm (v₁ s))-T.f ((action gi).symm (v₀ s)))
    (hsep : ∀ x ∈ Pat false, ∀ y ∈ Pat true,
      T.f ((action gj).symm x)+lj/4 ≤ T.f ((action gj).symm y)) :
    (min (κ/4) (1/16))*li ≤ CannonCrossEnergy.oscillation T.f
      ((action gi).symm '' closedBall pj (A*R)) ∨
    (min (κ/4) (1/16))*lj ≤ CannonCrossEnergy.oscillation T.f
      ((action gj).symm '' closedBall pi (A*R)) := by
  have hP : ∀ s z, z ∈ range (γ s) → A*R < dist z pi ∧ A*R < dist z pj := by
    intro s z hz
    exact ⟨havoid.trans_le (pattern_puncture_distance (action gi) xi pi R V B cutoff
      hR hV hB hsmall hli (Pat s) (hPati s) z (hγ s hz)),
      havoid.trans_le (pattern_puncture_distance (action gj) xj pj R V B cutoff
      hR hV hB hsmall hlj (Pat s) (hPatj s) z (hγ s hz))⟩
  have henergy (g : Γ) (K : Set X) (hK : IsCompact K) (hKΩ : (action g).symm '' K ⊆ T.Ω) :
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (T.H n ∘ (action g).symm) K) atTop (𝓝 0) := by
    apply T.energy g K hK _ 2 (by norm_num)
    intro z hz
    exact ⟨(action g).symm z,hKΩ (mem_image_of_mem _ hz),(action g).apply_symm_apply z⟩
  have hh := fixed_source_pair ι p r hr hrlim hpnet T.Ω T.H T.f T.continuous T.H_continuous
    T.unit T.H_limit T.H_diameter T.H_diameter_pos T.H_level
    (action gi) (action gj) xi xj pi pj R U A ε hR hA hwide hroom hΩi hΩj hui huj hfar
    v₀ v₁ γ hP (κ*li) (lj/4) (mul_pos hκ hli_pos) (by positivity) hgap
    (fun x hx y hy => hsep x (hγ false hx) y (hγ true hy)) (henergy gi) (henergy gj)
  rcases hh with hh | hh
  · left
    calc
      _ ≤ (κ/4)*li := mul_le_mul_of_nonneg_right (min_le_left _ _) hli_pos.le
      _ = (κ*li)/4 := by ring
      _ ≤ _ := hh
  · right
    calc
      _ ≤ (1/16)*lj := mul_le_mul_of_nonneg_right (min_le_right _ _) hlj_pos.le
      _ = (lj/4)/4 := by ring
      _ ≤ _ := hh

end CannonApprox

end

namespace CannonApprox

open Set Metric CannonNode CannonMagnification

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

theorem exists_flow_patterns (T : RecordData action ι p r) {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hL : 1 ≤ L) (hCE : 0 ≤ CE) (hLE : 0 ≤ LE)
    (hpaths : ∀ x u w : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist w x ≤ r →
      JoinedIn (ball x (L*r)) u w)
    (h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X)
    (hexp : ∀ g i, Expansion (h g i) (F.S.center g i) (F.S.scale g) CE LE) :
    Nonempty (FlowPatternSetup T F h) := by
  classical
  obtain ⟨hA,hB,hc,hcore,hcoef₁,hcoef₂,hH⟩ := F.margins hL hCE hLE
  obtain ⟨Z,_,hnet,_⟩ := CannonNet.exists_compact_net (X:=X)
    (F.cPat*radius ell (160*(Q+1)*F.n)) (mul_pos F.pattern_pos (radius_pos _ _))
  obtain ⟨z,hz,_⟩ := hnet T.x₀
  have hZ : Z.Nonempty := ⟨z,hz⟩
  let ballOf : (Bool → Z) → Bool → Set X := fun pat s =>
    closedBall (pat s : X) (3*F.cPat*radius ell (160*(Q+1)*F.n))
  let HasPattern (g : ℕ) (i : Fin (F.S.flow.size g)) (pat : Bool → Z) : Prop :=
    ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ ballOf pat s) ∧
      (∀ s, F.S.κ*F.S.len g i ≤ T.f ((h g i).symm (v₁ s))-T.f ((h g i).symm (v₀ s))) ∧
      (∀ s, (h g i).symm '' ballOf pat s ⊆ closedBall (F.S.center g i) ((F.B+2)*F.S.scale g)) ∧
      ∀ z ∈ ballOf pat false, ∀ w ∈ ballOf pat true,
        T.f ((h g i).symm z)+F.S.len g i/4 ≤ T.f ((h g i).symm w)
  have hp : ∀ g i, F.S.good (F.S.state g i) → ∃ pat, HasPattern g i pat := by
    intro g i hi
    have hexp' : Expansion (h g i) (F.S.state g i).center
        (radius ell (F.S.state g i).depth) CE LE := by
      rw [F.S.state_depth g i]
      exact hexp g i
    obtain ⟨pat,v₀,v₁,γ,hγ,hgap,hball,hsep⟩ := F.S.node_pattern (fun z : Z => (z:X))
      T.Ω T.continuous F.local_domain L CE LE F.cPat hL hCE hLE F.pattern_pos
      hA hB hcore hcoef₁ hcoef₂ F.small
      (fun x => by obtain ⟨z,hz,hd⟩ := hnet x; exact ⟨⟨z,hz⟩,hd⟩) hpaths
      (F.S.state g i) hi (h g i) hexp'
    refine ⟨pat,v₀,v₁,γ,hγ,hgap,?_,hsep⟩
    intro s y hy
    obtain ⟨w,hw,hball⟩ := hball s
    obtain ⟨v,hv,rfl⟩ := hy
    obtain ⟨u,hu,huv⟩ := hball hv
    rw [← huv,(h g i).symm_apply_apply]
    have hloc := (F.S.Yloc (F.S.state g i) w hw).2
    have hsm := mul_le_mul_of_nonneg_right F.S.pattern_small (radius_pos ell (F.S.state g i).depth).le
    have ht := dist_triangle u w (F.S.center g i)
    change dist u w < F.c₀*radius ell ((F.S.state g i).depth+160*(Q+1)*F.n) at hu
    rw [radius_add] at hu
    rw [mem_closedBall]
    rw [F.S.state_depth g i] at hu hloc hsm
    change F.c₀*radius ell (160*(Q+1)*F.n)*F.S.scale g ≤ 1*F.S.scale g at hsm
    change dist w (F.S.center g i) ≤ (F.B+1)*F.S.scale g at hloc
    change dist u w < F.c₀*(radius ell (160*(Q+1)*F.n)*F.S.scale g) at hu
    nlinarith only [ht,hu,hloc,hsm]
  let pat : ∀ g, Fin (F.S.flow.size g) → Bool → Z := fun g i =>
    if hi : F.S.good (F.S.state g i) then (hp g i hi).choose else fun _ => ⟨z,hz⟩
  refine ⟨⟨Z,hZ,pat,?_⟩⟩
  intro g i hi
  dsimp only [pat]
  rw [dite_eq_left hi]
  exact (hp g i hi).choose_spec

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_NearProbabilityBound
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
namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

theorem near_probability_bound {ι α : Type*} [Fintype α]
    (S : Finset ι) (ancestor : ι → α) (P : ι → ℝ) (W : α → ℝ)
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (hW : ∀ a, 0 ≤ W a)
    (hcount : ∀ a, (S.filter (fun i => ancestor i = a)).card ≤ N)
    (hweight : ∀ i ∈ S, P i ≤ c*W (ancestor i)) :
    ∑ i ∈ S, P i ≤ (N:ℝ)*c*∑ a, W a := by
  classical
  have heq : ∑ i ∈ S, c*W (ancestor i) =
      ∑ a, ((S.filter (fun i => ancestor i = a)).card : ℝ)*(c*W a) := by
    calc
      _ = ∑ i ∈ S, ∑ a : α, if ancestor i = a then c*W a else 0 := by
        apply sum_congr rfl
        intro i hi
        simp
      _ = ∑ a, ∑ i ∈ S.filter (fun i => ancestor i = a), c*W a := by
        rw [sum_comm]
        simp only [sum_filter]
      _ = _ := by simp only [sum_const,nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ S, c*W (ancestor i) := sum_le_sum hweight
    _ = _ := heq
    _ ≤ ∑ a, (N:ℝ)*(c*W a) := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount a) (mul_nonneg hc (hW a))
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro a _; ring

theorem far_pairs_card {ι : Type*} (S : Finset ι) (P : ι → ℝ)
    (near : ι → ι → Prop) (pstar ε : ℝ) (hpstar : 0 < pstar)
    (hlower : ∀ i ∈ S, pstar ≤ P i)
    (hnearmass : ∀ i ∈ S, ∑ j ∈ S.filter (near i), P j ≤ ε)
    (hsmall : 2*ε ≤ (S.card:ℝ)*pstar) :
    (S.card:ℝ)^2/2 ≤ (((S ×ˢ S).filter (fun p => ¬ near p.1 p.2)).card : ℝ) := by
  classical
  have hnear (i : ι) (hi : i ∈ S) :
      ((S.filter (near i)).card:ℝ)*pstar ≤ ε := by
    calc
      _ = ∑ j ∈ S.filter (near i), pstar := by simp
      _ ≤ ∑ j ∈ S.filter (near i), P j := sum_le_sum (fun j hj => hlower j (mem_filter.mp hj).1)
      _ ≤ ε := hnearmass i hi
  have hfar (i : ι) (hi : i ∈ S) :
      (S.card:ℝ)/2 ≤ ((S.filter (fun j => ¬ near i j)).card:ℝ) := by
    have heq := card_filter_add_card_filter_not (s:=S) (p:=near i)
    have heq' : ((S.filter (near i)).card:ℝ)+((S.filter (fun j => ¬ near i j)).card:ℝ) = S.card := by
      exact_mod_cast heq
    have hh := hnear i hi
    nlinarith only [hsmall,heq',hh,hpstar]
  have heq : (((S ×ˢ S).filter (fun p => ¬ near p.1 p.2)).card : ℝ) =
      ∑ i ∈ S, ((S.filter (fun j => ¬ near i j)).card : ℝ) := by
    simp only [card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,sum_filter,sum_product,
      Nat.cast_ite,Nat.cast_zero]
  calc
    _ = ∑ _i ∈ S, (S.card:ℝ)/2 := by simp; ring
    _ ≤ ∑ i ∈ S, ((S.filter (fun j => ¬ near i j)).card : ℝ) := sum_le_sum hfar
    _ = _ := heq.symm

theorem pair_orientation_fiber {ι : Type*} (S : Finset (ι × ι))
    (orient : ι × ι → ι × ι)
    (horient : ∀ p ∈ S, orient p = p ∨ orient p = p.swap)
    (q : ι × ι) :
    (S.filter (fun p => orient p = q)).card ≤ 2 := by
  classical
  have hsub : S.filter (fun p => orient p = q) ⊆ {q,q.swap} := by
    intro p hp
    obtain ⟨hp,heq⟩ := mem_filter.mp hp
    rcases horient p hp with h | h
    · have : p=q := h.symm.trans heq
      simp [this]
    · have : p=q.swap := by have hh := congrArg Prod.swap (h.symm.trans heq); simpa using hh
      simp [this]
  calc
    _ ≤ ( {q,q.swap} : Finset (ι × ι)).card := Finset.card_le_card hsub
    _ ≤ ({q.swap} : Finset (ι × ι)).card + 1 := card_insert_le _ _
    _ = 2 := by simp

end CannonPairs

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_DyadicBin
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
namespace CannonPairs

open Finset

attribute [local instance] Classical.propDecidable

lemma dyadic_bin {p : ℝ} (m : ℕ) (hp : (2:ℝ)^(-(m:ℤ)) ≤ p) (hp1 : p ≤ 1) :
    ∃ j : Fin (m+1), (2:ℝ)^(-((j.val+1:ℕ):ℤ)) ≤ p ∧
      p ≤ 2*(2:ℝ)^(-((j.val+1:ℕ):ℤ)) := by
  let S : Finset ℕ := (range (m+1)).filter (fun j => p ≤ (2:ℝ)^(-(j:ℤ)))
  have hS : S.Nonempty := ⟨0,by simp [S,hp1]⟩
  let j := S.max' hS
  have hjS : j ∈ S := max'_mem _ _
  have hjm : j ≤ m := by have := (mem_filter.mp hjS).1; simp only [mem_range] at this; omega
  have hjp : p ≤ (2:ℝ)^(-(j:ℤ)) := (mem_filter.mp hjS).2
  have hpow : (2:ℝ)^(-(j:ℤ)) = 2*(2:ℝ)^(-((j+1:ℕ):ℤ)) := by
    rw [Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ (by norm_num)]
    norm_num
    ring
  refine ⟨⟨j,by omega⟩,?_,by simpa only [hpow] using hjp⟩
  by_cases hj : j = m
  · simpa only [hj] using (le_trans (by
      rw [Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ (by norm_num)]
      norm_num) hp)
  · by_contra hn
    have hjnext : j+1 ∈ S := by
      simp only [S,mem_filter,mem_range]
      exact ⟨by omega,(lt_of_not_ge hn).le⟩
    have hh : j+1 ≤ j := le_max' S (j+1) hjnext
    omega

theorem probability_pattern_class {ι π : Type*} [Fintype ι] [Fintype π]
    [Nonempty π] (P : ι → ℝ) (pattern : ι → π) (good : ι → Prop)
    (m : ℕ) (mass : ℝ) (_hP : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (hmass : mass ≤ ∑ i ∈ univ.filter (fun i => good i ∧ (2:ℝ)^(-(m:ℤ)) ≤ P i), P i) :
    ∃ S : Finset ι, ∃ pat : π, ∃ Pstar : ℝ, 0 < Pstar ∧
      (∀ i ∈ S, good i ∧ pattern i = pat ∧ Pstar ≤ P i ∧ P i ≤ 2*Pstar) ∧
      mass/((Fintype.card π : ℝ)*(m+1)) ≤ ∑ i ∈ S, P i := by
  classical
  let eligible : Finset ι := univ.filter (fun i => good i ∧ (2:ℝ)^(-(m:ℤ)) ≤ P i)
  have hbin : ∀ i ∈ eligible, ∃ j : Fin (m+1), (2:ℝ)^(-((j.val+1:ℕ):ℤ)) ≤ P i ∧
      P i ≤ 2*(2:ℝ)^(-((j.val+1:ℕ):ℤ)) :=
    fun i hi => dyadic_bin m (mem_filter.mp hi).2.2 (hP1 i)
  let bin : ι → Fin (m+1) := fun i => if hi : i ∈ eligible then (hbin i hi).choose else 0
  let cls : π × Fin (m+1) → Finset ι := fun k => eligible.filter (fun i => (pattern i,bin i) = k)
  have hsum : ∑ k : π × Fin (m+1), ∑ i ∈ cls k, P i = ∑ i ∈ eligible, P i := by
    simp only [cls,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    simp
  have hcpos : 0 < (Fintype.card π : ℝ)*(m+1) :=
    mul_pos (by exact_mod_cast Fintype.card_pos) (by positivity)
  have hcls : ∃ k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1)) ≤ ∑ i ∈ cls k, P i := by
    by_contra hn
    have hlt : (∑ k : π × Fin (m+1), ∑ i ∈ cls k, P i) <
        ∑ _k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1)) :=
      sum_lt_sum_of_nonempty univ_nonempty (fun k _ => lt_of_not_ge (fun hk => hn ⟨k,hk⟩))
    have heq : (∑ _k : π × Fin (m+1), mass/((Fintype.card π : ℝ)*(m+1))) = mass := by
      simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Fintype.card_fin,
        Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      field_simp
    rw [hsum,heq] at hlt
    exact (not_lt_of_ge hmass) hlt
  obtain ⟨⟨pat,j⟩,hk⟩ := hcls
  refine ⟨cls (pat,j),pat,(2:ℝ)^(-((j.val+1:ℕ):ℤ)),zpow_pos (by norm_num) _,?_,hk⟩
  intro i hi
  obtain ⟨hei,heq⟩ := mem_filter.mp hi
  have hbini : bin i = j := congrArg Prod.snd heq
  have hselect := (hbin i hei).choose_spec
  have hbinEq : bin i = (hbin i hei).choose := dite_eq_left hei
  rw [← hbinEq,hbini] at hselect
  exact ⟨(mem_filter.mp hei).2.1,congrArg Prod.fst heq,hselect⟩

lemma discarded_weight_bound {ι : Type*} [Fintype ι] (P : ι → ℝ)
    (good : ι → Prop) (threshold mass : ℝ) (ht : 0 ≤ threshold)
    (hmass : mass ≤ ∑ i ∈ Finset.univ.filter good, P i) :
    mass-(Fintype.card ι : ℝ)*threshold ≤
      ∑ i ∈ Finset.univ.filter (fun i => good i ∧ threshold ≤ P i), P i := by
  classical
  have hh : ∑ i ∈ Finset.univ.filter good, P i ≤
      (∑ i ∈ Finset.univ.filter (fun i => good i ∧ threshold ≤ P i), P i)+
        (Fintype.card ι : ℝ)*threshold := by
    calc
      _ ≤ ∑ i : ι, ((if good i ∧ threshold ≤ P i then P i else 0)+threshold) := by
        rw [sum_filter]
        apply sum_le_sum
        intro i _
        by_cases hg : good i <;> by_cases hi : threshold ≤ P i <;>
          simp only [hg,hi,and_self,and_true,and_false,ite_true,ite_false,zero_add]
        · exact le_add_of_nonneg_right ht
        · exact (lt_of_not_ge hi).le
        · exact ht
        · exact ht
      _ = _ := by rw [sum_add_distrib,← sum_filter]; simp
  linarith only [hmass,hh]

end CannonPairs

end

namespace CannonPairs

open Finset Filter Topology

attribute [local instance] Classical.propDecidable

theorem eventually_probability_class {ι : ℕ → Type*} [∀ g, Fintype (ι g)]
    {π : Type*} [Fintype π] [Nonempty π]
    (P : ∀ g, ι g → ℝ) (pat : ∀ g, ι g → π) (good : ∀ g, ι g → Prop)
    (depth : ℕ → ℕ) (hdepth : Tendsto depth atTop atTop)
    (C a : ℝ) (_hC : 0 ≤ C)
    (hcard : ∀ g, (Fintype.card (ι g) : ℝ) ≤ C*Real.exp (a*depth g))
    (hP : ∀ g i, 0 ≤ P g i) (hP1 : ∀ g i, P g i ≤ 1) :
    ∃ J : ℕ, ∀ᶠ g in atTop,
      (1/2:ℝ) ≤ ∑ i ∈ univ.filter (good g), P g i →
      ∃ S : Finset (ι g), ∃ v : π, ∃ pstar : ℝ, 0 < pstar ∧
        (∀ i ∈ S, good g i ∧ pat g i=v ∧ pstar ≤ P g i ∧ P g i ≤ 2*pstar) ∧
        1/(6*(Fintype.card π : ℝ)*((J*depth g:ℕ)+1)) ≤ (S.card:ℝ)*pstar := by
  classical
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (Real.exp a) (by norm_num : (1:ℝ)<2)
  let q := Real.exp a/(2:ℝ)^J
  have hq : 0 ≤ q := (div_pos (Real.exp_pos _) (by positivity)).le
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr hJ
  have hlim : Tendsto (fun g => C*q^(depth g)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).comp hdepth).const_mul C
    simpa only [mul_zero,Function.comp_def] using hh
  have hevent := hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/6))
  refine ⟨J,hevent.mono ?_⟩
  intro g hg hgood
  let th : ℝ := (2:ℝ)^(-((J*depth g:ℕ):ℤ))
  have hth : 0 ≤ th := (zpow_pos (by norm_num) _).le
  have hdisc : (Fintype.card (ι g) : ℝ)*th ≤ 1/6 := by
    calc
      _ ≤ (C*Real.exp (a*depth g))*th := mul_le_mul_of_nonneg_right (hcard g) hth
      _ = C*q^(depth g) := by
        dsimp [th,q]
        rw [zpow_neg, zpow_mul, zpow_natCast, zpow_natCast]
        rw [mul_comm a, Real.exp_nat_mul, div_pow]
        ring
      _ ≤ _ := hg.le
  have hmass : (1/3:ℝ) ≤ ∑ i ∈ univ.filter (fun i => good g i ∧ th ≤ P g i), P g i := by
    have hh := discarded_weight_bound (P g) (good g) th (1/2) hth hgood
    linarith only [hh,hdisc]
  obtain ⟨S,v,pstar,hp,hclass,hm⟩ := probability_pattern_class (P g) (pat g) (good g)
    (J*depth g) (1/3) (hP g) (hP1 g) hmass
  refine ⟨S,v,pstar,hp,hclass,?_⟩
  have hupper : (∑ i ∈ S, P g i) ≤ (S.card:ℝ)*(2*pstar) := by
    calc
      _ ≤ ∑ _i ∈ S, 2*pstar := sum_le_sum (fun i hi => (hclass i hi).2.2.2)
      _ = _ := by simp
  have hc : 0 < (Fintype.card π : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : 0 < ((J*depth g:ℕ):ℝ)+1 := by positivity
  have heq : (1/3:ℝ)/((Fintype.card π:ℝ)*((J*depth g:ℕ)+1)) =
      2*(1/(6*(Fintype.card π:ℝ)*((J*depth g:ℕ)+1))) := by
    field_simp
    norm_num
  rw [heq] at hm
  linarith only [hm,hupper]

end CannonPairs

end

section

namespace CannonPairs

open Filter Topology

lemma division_difference_tendsto {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun g : ℕ => g-g/q) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2*N)] with g hg
  have hm := Nat.mul_div_le g q
  have h2 : 2*(g/q) ≤ g := by nlinarith
  omega

theorem division_geometric_tail {q : ℕ} (hq : 0 < q) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (k D : ℝ) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    Tendsto (fun g : ℕ => (k+D*g)*r^(g/q)) atTop (𝓝 0) := by
  have hm := Nat.tendsto_div_const_atTop (ne_of_gt hq)
  have h₀ := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).comp hm
  have h₁ := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp hm
  have hlim : Tendsto (fun g : ℕ => (k+D*(q:ℝ))*r^(g/q)+
      (D*(q:ℝ))*((g/q:ℕ):ℝ)*r^(g/q)) atTop (𝓝 0) := by
    have hh := (h₀.const_mul (k+D*(q:ℝ))).add (h₁.const_mul (D*(q:ℝ)))
    simpa only [mul_zero,add_zero,Function.comp_def,mul_assoc] using hh
  apply squeeze_zero (fun g => mul_nonneg (by positivity) (pow_nonneg hr _))
    (fun g => ?_) hlim
  have hgn : g < q*(g/q+1) := Nat.lt_mul_div_succ g hq
  have hg : (g:ℝ) ≤ (q:ℝ)*((g/q:ℕ)+1) := by exact_mod_cast hgn.le
  calc
    _ ≤ (k+D*((q:ℝ)*((g/q:ℕ)+1)))*r^(g/q) := by gcongr
    _ = _ := by ring

lemma division_exp_tail {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c)
    (k D : ℝ) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    Tendsto (fun g : ℕ => (k+D*g)*Real.exp (-c)^ (g/q)) atTop (𝓝 0) :=
  division_geometric_tail hq (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; linarith only [hc]) k D hk hD

lemma depth_difference_tendsto {q D : ℕ} (hq : 2 ≤ q) (hD : 0 < D) (k : ℕ) :
    Tendsto (fun g : ℕ => k+D*g-D*(g/q)) atTop atTop := by
  have hm := division_difference_tendsto hq
  apply tendsto_atTop.2
  intro N
  filter_upwards [hm.eventually (eventually_ge_atTop N)] with g hg
  have hgm := Nat.div_le_self g q
  have hmul := Nat.mul_le_mul_left D hgm
  have hge : g-g/q ≤ D*(g-g/q) := Nat.le_mul_of_pos_left _ hD
  rw [Nat.mul_sub_left_distrib] at hge
  omega

lemma pair_split_exponent (Q n g : ℕ) (_hQ : 0 < Q) :
    Q*(160*(Q+1)*n*(g/(160*Q*(Q+1)))) ≤ n*g := by
  have hh := Nat.mul_div_le g (160*Q*(Q+1))
  have hh' := Nat.mul_le_mul_left n hh
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma pair_split_ratio (Q : ℕ) (hQ : 0 < Q) : 2 ≤ 160*Q*(Q+1) := by
  nlinarith

lemma pair_overlap_exponential {ell : ℝ} (hell : 0 ≤ ell)
    (Q n g : ℕ) (hQ : 0 < Q) :
    Real.exp ((Q:ℝ)*ell*(160*(Q+1)*n*(g/(160*Q*(Q+1))):ℕ)) ≤
      Real.exp (ell*n*g) := by
  apply Real.exp_le_exp.mpr
  have hn : ((Q*(160*(Q+1)*n*(g/(160*Q*(Q+1)))):ℕ):ℝ) ≤ ((n*g:ℕ):ℝ) :=
    by exact_mod_cast pair_split_exponent Q n g hQ
  have hh := mul_le_mul_of_nonneg_left hn hell
  push_cast at hh ⊢
  nlinarith only [hh]

end CannonPairs

end

namespace CannonApprox

open Set Metric Finset Filter Topology CannonNode CannonPacking CannonPairs

attribute [local instance] Classical.propDecidable

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.depth_tendsto {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) :
    Tendsto (fun g : ℕ => F.S.kmin+160*(Q+1)*F.n*g) atTop atTop := by
  apply tendsto_atTop_mono (f:=fun g : ℕ => g)
  · intro g
    have hh := Nat.le_mul_of_pos_left g (by have := F.npos; positivity : 0 < 160*(Q+1)*F.n)
    omega
  · exact tendsto_id

omit [CompactSpace X] in
theorem FlowSetup.card_exponential {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      (Fintype.card (Fin (F.S.flow.size g)):ℝ) ≤
        C*Real.exp (((Q:ℝ)*ell)*(F.S.kmin+160*(Q+1)*F.n*g:ℕ)) := by
  classical
  have hHp : 0 < F.H := by linarith only [hB,hH]
  let b := min F.H 1
  have hb : 0 < b := lt_min hHp zero_lt_one
  refine ⟨CP*(b⁻¹)^Q,by positivity,fun g => ?_⟩
  have hr1 : F.S.scale g ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell) (Nat.cast_nonneg _)
  have hs : 0 < b*F.S.scale g := mul_pos hb (radius_pos _ _)
  have hs1 : b*F.S.scale g ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right F.H 1) (radius_pos _ _).le).trans
      (by simpa only [one_mul] using hr1)
  have hh := indexed_packing Q CP hpack (F.S.center g) univ T.x₀ 1 (b*F.S.scale g)
    hs hs1 le_rfl (fun i _ => hdiam _ _) (fun i _ j _ hij =>
      (mul_le_mul_of_nonneg_right (min_le_left F.H 1) (radius_pos _ _).le).trans
        (F.S.centers_separated F.decay hB hH g i j hij))
  have heq : (1/(b*F.S.scale g))^Q = b⁻¹^Q *
      Real.exp (((Q:ℝ)*ell)*(F.S.kmin+160*(Q+1)*F.n*g:ℕ)) := by
    rw [one_div,mul_inv_rev,mul_comm,mul_pow]
    rw [CannonNode.SourceConstruction.scale,radius,← Real.exp_neg,neg_mul,neg_neg]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [heq] at hh
  simpa only [card_univ,mul_assoc] using hh

omit [CompactSpace X] in
theorem FlowSetup.pattern_class {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    {h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X} (P : FlowPatternSetup T F h) :
    ∃ J : ℕ, ∀ᶠ g in atTop, (1/2:ℝ) ≤ F.S.flow.goodMass g →
      ∃ S : Finset (Fin (F.S.flow.size g)), ∃ v : Bool → P.net, ∃ pstar : ℝ, 0 < pstar ∧
        (∀ i ∈ S, F.S.good (F.S.state g i) ∧ P.pat g i=v ∧
          pstar ≤ F.S.flow.weight g i ∧ F.S.flow.weight g i ≤ 2*pstar) ∧
        1/(6*(Fintype.card (Bool → P.net):ℝ)*((J*(F.S.kmin+160*(Q+1)*F.n*g):ℕ)+1)) ≤
          (S.card:ℝ)*pstar := by
  classical
  let _ : Nonempty P.net := ⟨⟨P.net_nonempty.choose,P.net_nonempty.choose_spec⟩⟩
  obtain ⟨C,hC,hcard⟩ := F.card_exponential hell hB hH CP hCP hpack hdiam
  obtain ⟨J,hJ⟩ := eventually_probability_class F.S.flow.weight P.pat
    (fun g i => F.S.good (F.S.state g i)) (fun g => F.S.kmin+160*(Q+1)*F.n*g)
    F.depth_tendsto C ((Q:ℝ)*ell) hC hcard F.S.flow.nonneg F.S.flow.weight_le_one
  refine ⟨J,hJ.mono fun g hg hgood => hg ?_⟩
  change (1/2:ℝ) ≤ ∑ i ∈ (univ : Finset (Fin (F.S.rule.generation F.S.root g).size)).filter
    (fun i => F.S.good ((F.S.rule.generation F.S.root g).state i)), F.S.rule.weights F.S.root g i
  rw [Finset.sum_filter]
  change (1/2:ℝ) ≤ ∑ i : Fin (F.S.rule.generation F.S.root g).size,
    F.S.rule.weights F.S.root g i * if F.S.good ((F.S.rule.generation F.S.root g).state i) then 1 else 0 at hgood
  simpa only [mul_ite,mul_one,mul_zero] using hgood

end CannonApprox

end

section

section

namespace CannonPairs

open Finset Set Metric CannonPacking

attribute [local instance] Classical.propDecidable

theorem ordered_cost_real_multiplicity {X ι : Type*} (S : Finset ι)
    (P : Finset (ι × ι)) (B : ι × ι → Set X) (A : ι → Set X) (K : ℝ) (M : ℕ)
    (hP : P ⊆ S ×ˢ S) (hsource : ∀ p ∈ P, B p ⊆ A p.1)
    (hfirst : ∀ x, ((S.filter (fun i => x ∈ A i)).card:ℝ) ≤ K)
    (hsecond : ∀ i ∈ S, ∀ x,
      (S.filter (fun j => (i,j) ∈ P ∧ x ∈ B (i,j))).card ≤ M) :
    ∀ x, ((P.filter (fun p => x ∈ B p)).card:ℝ) ≤ K*M := by
  classical
  intro x
  let T := P.filter (fun p => x ∈ B p)
  have him : T.image Prod.fst ⊆ S.filter (fun i => x ∈ A i) := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    obtain ⟨hp,hx⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_product.mp (hP hp)).1,hsource p hp hx⟩
  have hfib (i : ι) (hi : i ∈ T.image Prod.fst) :
      (T.filter (fun p => p.1=i)).card ≤ M := by
    have hiS := (mem_filter.mp (him hi)).1
    apply le_trans (card_le_card_of_injOn Prod.snd (t:=S.filter
      (fun j => (i,j) ∈ P ∧ x ∈ B (i,j))) ?_ ?_) (hsecond i hiS x)
    · intro p hp
      obtain ⟨hp,heq⟩ := mem_filter.mp hp
      obtain ⟨hp,hx⟩ := mem_filter.mp hp
      apply mem_filter.mpr
      refine ⟨(mem_product.mp (hP hp)).2,?_,?_⟩
      · simpa only [← heq,Prod.mk.eta] using hp
      · simpa only [← heq,Prod.mk.eta] using hx
    · intro p hp q hq heq
      apply Prod.ext
      · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
      · exact heq
  have hh : (T.card:ℝ) ≤ (M:ℝ)*((T.image Prod.fst).card:ℝ) := by
    exact_mod_cast card_le_mul_card_image T M hfib
  calc
    _ ≤ (M:ℝ)*((T.image Prod.fst).card:ℝ) := hh
    _ ≤ (M:ℝ)*((S.filter (fun i => x ∈ A i)).card:ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card him) (Nat.cast_nonneg _)
    _ ≤ (M:ℝ)*K := mul_le_mul_of_nonneg_left (hfirst x) (Nat.cast_nonneg _)
    _ = K*M := mul_comm _ _

theorem oriented_cost_real_multiplicity {X ι : Type*}
    (P : Finset (ι × ι)) (B : ι × ι → Set X) (orient : ι × ι → ι × ι) (K : ℝ)
    (horient : ∀ p ∈ P, orient p=p ∨ orient p=p.swap)
    (hmap : ∀ p ∈ P, orient p ∈ P)
    (hcount : ∀ x, ((P.filter (fun p => x ∈ B p)).card:ℝ) ≤ K) :
    ∀ x, ((P.filter (fun p => x ∈ B (orient p))).card:ℝ) ≤ 2*K := by
  classical
  intro x
  let T := P.filter (fun p => x ∈ B (orient p))
  have hfib (p : ι × ι) : (T.filter (fun q => orient q=p)).card ≤ 2 :=
    pair_orientation_fiber T orient (fun q hq => horient q (mem_filter.mp hq).1) p
  have him : T.image orient ⊆ P.filter (fun p => x ∈ B p) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨hq,hx⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hmap q hq,hx⟩
  have hh : (T.card:ℝ) ≤ 2*((P.filter (fun p => x ∈ B p)).card:ℝ) := by
    exact_mod_cast (card_le_mul_card_image T 2 (fun p _ => hfib p)).trans
      (Nat.mul_le_mul_left 2 (card_le_card him))
  exact hh.trans (mul_le_mul_of_nonneg_left (hcount x) (by norm_num))

theorem geometric_cost_multiplicity {X ι : Type*} [MetricSpace X]
    (Q : ℕ) (CP H R d Csrc Cimg : ℝ) (hpack : PolynomialPacking (X:=X) Q CP)
    (hH : 0 < H) (hR : 0 < R) (hd : 0 < d) (hCs : H ≤ Csrc)
    (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (P : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (B : ι × ι → Set X) (M : ℕ) (hP : P ⊆ S ×ˢ S)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hsource : ∀ ij ∈ P, B ij ⊆ closedBall (x ij.1) (Csrc*R/d))
    (himage : ∀ ij ∈ P, h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M) :
    ∀ z, ((P.filter (fun ij => z ∈ B ij)).card:ℝ) ≤
      CP*(Csrc/H/d)^Q*M := by
  classical
  apply ordered_cost_real_multiplicity S P B (fun i => closedBall (x i) (Csrc*R/d))
    (CP*(Csrc/H/d)^Q) M hP hsource
  · intro z
    have hh := indexed_packing Q CP hpack x
      (S.filter (fun i => z ∈ closedBall (x i) (Csrc*R/d))) z (Csrc*R/d) (H*R)
      (mul_pos hH hR) ?_ hsmall
      (fun i hi => by simpa only [mem_closedBall] using (mem_filter.mp hi).2)
      (fun i hi j hj hne => hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne)
    · convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      field_simp
    · apply (le_div_iff₀ hd).mpr
      calc (H*R)*d ≤ H*R := by nlinarith only [hd1,mul_pos hH hR]
           _ ≤ Csrc*R := mul_le_mul_of_nonneg_right hCs hR.le
  · intro i hi z
    apply (card_le_card ?_).trans (hpunctures (h i z))
    intro j hj
    obtain ⟨hj,hij,hz⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨hj,?_⟩
    have hh := mem_closedBall.mp (himage (i,j) hij (mem_image_of_mem _ hz))
    simpa only [dist_comm] using hh

end CannonPairs

end

namespace CannonPairs

open Set Metric Finset MeasureTheory CannonPacking CannonPairCost

attribute [local instance] Classical.propDecidable

theorem geometric_pair_comparison {X ι : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : FiniteMeasure X) (Q : ℕ) (CP H R d Csrc Cimg : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hH : 0 < H) (hR : 0 < R)
    (hd : 0 < d) (hCs : H ≤ Csrc) (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (pairs : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (B : ι × ι → Set X) (M : ℕ)
    (hP : pairs ⊆ S ×ˢ S) (hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hm : ∀ ij ∈ pairs, MeasurableSet (B ij))
    (hsource : ∀ ij ∈ pairs, B ij ⊆ closedBall (x ij.1) (Csrc*R/d))
    (himage : ∀ ij ∈ pairs, h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M)
    (Δ weight : ι → ℝ) (c A pstar k : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hpstar : 0 ≤ pstar) (hk : 0 < k)
    (hweight : ∀ i ∈ S, pstar ≤ weight i)
    (hgap : ∀ i ∈ S, A*weight i ≤ Δ i)
    (hcost : ∀ ij ∈ pairs, c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) ∨
      c*(Δ ij.2)^2 ≤ (ν (B ij.swap):ℝ))
    (hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ))
    (hclass : 1/k ≤ (S.card:ℝ)*pstar) :
    (1/2:ℝ)*c*A^2 ≤ (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ)*k^2 := by
  classical
  let orient : ι × ι → ι × ι := fun ij =>
    if c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) then ij else ij.swap
  have horient (ij : ι × ι) (_hij : ij ∈ pairs) : orient ij=ij ∨ orient ij=ij.swap := by
    dsimp only [orient]
    split_ifs <;> simp
  have hmap (ij : ι × ι) (hij : ij ∈ pairs) : orient ij ∈ pairs := by
    rcases horient ij hij with hh | hh
    · simpa only [hh] using hij
    · simpa only [hh] using hswap ij hij
  have hpay (ij : ι × ι) (hij : ij ∈ pairs) :
      c*(Δ (orient ij).1)^2 ≤ (ν (B (orient ij)):ℝ) := by
    dsimp only [orient]
    split_ifs with hh
    · exact hh
    · exact (hcost ij hij).resolve_left hh
  have hmult := geometric_cost_multiplicity Q CP H R d Csrc Cimg hpack hH hR hd hCs hd1
    hsmall S pairs x p h B M hP hsep hsource himage hpunctures
  have hmult' := oriented_cost_real_multiplicity pairs B orient (CP*(Csrc/H/d)^Q*M)
    horient hmap hmult
  have hb : (pairs.card:ℝ)*c*A^2*pstar^2 ≤
      (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ) := by
    have hh := finite_pair_bound (ν:Measure X) pairs (fun ij => (orient ij).1)
      (fun ij => B (orient ij)) Δ weight (fun ij hij => hm _ (hmap ij hij)) hc hA hpstar
      (fun ij hij => hweight _ (mem_product.mp (hP (hmap ij hij))).1)
      (fun ij hij => hgap _ (mem_product.mp (hP (hmap ij hij))).1)
      (fun ij hij => hpay ij hij)
      hmult'
    exact hh
  apply cost_comparison hc hA hpstar (by norm_num : (0:ℝ)≤1/2)
    (Nat.cast_nonneg _) hk ?_ hclass hb
  nlinarith only [hfar]

end CannonPairs

namespace CannonPairs

open Set Metric Finset MeasureTheory CannonPacking CannonPairCost

attribute [local instance] Classical.propDecidable

theorem charged_pair_comparison {X ι : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : FiniteMeasure X) (Q : ℕ) (CP H R d Csrc Cimg : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hH : 0 < H) (hR : 0 < R)
    (hd : 0 < d) (hCs : H ≤ Csrc) (hd1 : d ≤ 1) (hsmall : Csrc*R/d ≤ 1)
    (S : Finset ι) (pairs : Finset (ι × ι)) (x p : ι → X) (h : ι → X ≃ₜ X)
    (M : ℕ) (hP : pairs ⊆ S ×ˢ S) (hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*R ≤ dist (x i) (x j))
    (hpunctures : ∀ b, (S.filter (fun j => dist (p j) b ≤ Cimg*R)).card ≤ M)
    (Δ weight : ι → ℝ) (c A pstar k : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hpstar : 0 ≤ pstar) (hk : 0 < k)
    (hweight : ∀ i ∈ S, pstar ≤ weight i)
    (hgap : ∀ i ∈ S, A*weight i ≤ Δ i)
    (paid : ι × ι → Prop) (hpaid : ∀ ij ∈ pairs, paid ij ∨ paid ij.swap)
    (hcharge : ∀ ij ∈ pairs, paid ij → ∃ B : Set X, MeasurableSet B ∧
      c*(Δ ij.1)^2 ≤ (ν B:ℝ) ∧ B ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ⊆ closedBall (p ij.2) (Cimg*R))
    (hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ))
    (hclass : 1/k ≤ (S.card:ℝ)*pstar) :
    (1/2:ℝ)*c*A^2 ≤ (2*(CP*(Csrc/H/d)^Q*M))*(ν univ:ℝ)*k^2 := by
  classical
  let eligible := pairs.filter paid
  have he (ij : ι × ι) (hij : ij ∈ eligible) : ∃ B : Set X, MeasurableSet B ∧
      c*(Δ ij.1)^2 ≤ (ν B:ℝ) ∧ B ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ⊆ closedBall (p ij.2) (Cimg*R) :=
    hcharge ij (mem_filter.mp hij).1 (mem_filter.mp hij).2
  let B : ι × ι → Set X := fun ij => if hij : ij ∈ eligible then (he ij hij).choose else ∅
  have hdata (ij : ι × ι) (hij : ij ∈ eligible) : MeasurableSet (B ij) ∧
      c*(Δ ij.1)^2 ≤ (ν (B ij):ℝ) ∧ B ij ⊆ closedBall (x ij.1) (Csrc*R/d) ∧
      h ij.1 '' B ij ⊆ closedBall (p ij.2) (Cimg*R) := by
    dsimp only [B]
    rw [dite_eq_left hij]
    exact (he ij hij).choose_spec
  apply geometric_pair_comparison ν Q CP H R d Csrc Cimg hpack hH hR hd hCs hd1 hsmall
    S pairs x p h B M hP hswap hsep ?_ ?_ ?_ hpunctures Δ weight c A pstar k
    hc hA hpstar hk hweight hgap ?_ hfar hclass
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).1
    · simp only [B,dite_eq_right hij,MeasurableSet.empty]
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).2.2.1
    · simp only [B,dite_eq_right hij,Set.empty_subset]
  · intro ij _
    by_cases hij : ij ∈ eligible
    · exact (hdata ij hij).2.2.2
    · simp only [B,dite_eq_right hij,Set.image_empty,Set.empty_subset]
  · intro ij hij
    rcases hpaid ij hij with hh | hh
    · exact Or.inl (hdata ij (mem_filter.mpr ⟨hij,hh⟩)).2.1
    · exact Or.inr (hdata ij.swap (mem_filter.mpr ⟨hswap ij hij,hh⟩)).2.1

end CannonPairs

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_CirclePacking_SplitRadiusRatioTendsto
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
namespace CannonPairs

open Filter Topology CannonNode

lemma split_radius_ratio_tendsto (Q n k : ℕ) (hQ : 0 < Q) (hn : 0 < n)
    {ell : ℝ} (hell : 0 < ell) :
    Tendsto (fun g : ℕ => radius ell (k+160*(Q+1)*n*g) /
      radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1))))) atTop (𝓝 0) := by
  have ht := (radius_tendsto hell).comp
    (depth_difference_tendsto (pair_split_ratio Q hQ) (by positivity : 0 < 160*(Q+1)*n) k)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  have hm : 160*(Q+1)*n*(g/(160*Q*(Q+1))) ≤ k+160*(Q+1)*n*g :=
    (Nat.mul_le_mul_left _ (Nat.div_le_self _ _)).trans (Nat.le_add_left _ _)
  simp only [Function.comp_def,radius,← Real.exp_sub,Nat.cast_sub hm]
  congr 1
  ring

lemma eventually_near_class_threshold {q : ℕ} (hq : 0 < q)
    {ell : ℝ} (hell : 0 < ell) (n : ℕ) (hn : 0 < n)
    (N K J k D : ℝ) (hK : 0 < K) (hJ : 0 ≤ J) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    ∀ᶠ g : ℕ in atTop, 2*N*Real.exp (-ell*n)^(g/q) ≤
      1/(K*(J*(k+D*g)+1)) := by
  have hc : 0 < ell*n := mul_pos hell (Nat.cast_pos.mpr hn)
  have ht := (division_exp_tail hq hc (J*k+1) (J*D) (by positivity) (by positivity)).const_mul (2*N*K)
  have ht' : Tendsto (fun g : ℕ => (2*N*Real.exp (-ell*n)^(g/q))*(K*(J*(k+D*g)+1)))
      atTop (𝓝 0) := by
    convert ht using 1 <;> try simp only [mul_zero]
    funext g
    rw [neg_mul]
    ring
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with g hg
  exact (le_div_iff₀ (mul_pos hK (by positivity : 0 < J*(k+D*g)+1))).mpr hg

lemma radius_inverse_pow (ell : ℝ) (k Q : ℕ) :
    (radius ell k)⁻¹^Q = Real.exp ((Q:ℝ)*ell*k) := by
  rw [radius,← Real.exp_neg,← Real.exp_nat_mul]
  congr 1
  ring

theorem pair_cost_exponential_bound (Q n g : ℕ) (hQ : 0 < Q)
    {ell c lam CP Cs H mass k : ℝ} (hell : 0 ≤ ell)
    (hc : 0 < c) (hlam : 0 < lam) (hCP : 0 ≤ CP) (hCs : 0 ≤ Cs)
    (hH : 0 < H) (hmass : 0 ≤ mass) (M : ℕ)
    (hcost : (1/2:ℝ)*c*(lam*Real.exp (ell*n*g))^2 ≤
      (2*(CP*(Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q*M))*mass*k^2) :
    Real.exp ((ell*n)*g) ≤
      ((2*CP*(Cs/H)^Q*M*mass)/(c*lam^2/2))*k^2 := by
  let e := Real.exp (ell*n*g)
  have he : 0 < e := Real.exp_pos _
  have hover : (Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q ≤
      (Cs/H)^Q*e := by
    rw [div_eq_mul_inv,mul_pow,radius_inverse_pow]
    exact mul_le_mul_of_nonneg_left (pair_overlap_exponential hell Q n g hQ) (by positivity)
  have hh : (c*lam^2/2)*e^2 ≤ (2*CP*(Cs/H)^Q*M*mass)*e*k^2 := by
    calc _ = (1/2:ℝ)*c*(lam*e)^2 := by ring
         _ ≤ (2*(CP*(Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q*M))*mass*k^2 := hcost
         _ ≤ (2*(CP*((Cs/H)^Q*e)*M))*mass*k^2 := by gcongr
         _ = _ := by ring
  have hh' : ((c*lam^2/2)*e)*e ≤ ((2*CP*(Cs/H)^Q*M*mass)*k^2)*e := by
    nlinarith only [hh]
  have hc' : 0 < c*lam^2/2 := div_pos (mul_pos hc (sq_pos_of_pos hlam)) (by norm_num)
  have hh'' := (mul_le_mul_iff_left₀ he).mp hh'
  calc _ = e := rfl
       _ ≤ ((2*CP*(Cs/H)^Q*M*mass)*k^2)/(c*lam^2/2) :=
         (le_div_iff₀ hc').mpr (by simpa only [mul_comm] using hh'')
       _ = _ := by ring

end CannonPairs

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPaid
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
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPairs CannonPacking Finset

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] [BorelSpace X] in
theorem FlowSetup.no_pair_data {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 < ell) (hQ : 0 < Q)
    (hB : 0 ≤ F.B+1) (hH : 4*(F.B+1) < F.H)
    (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X:=X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (c Cs Ci τ : ℝ) (hc : 0 < c) (hCs : 0 < Cs) (hτ : 0 < τ)
    (hHCs : F.H ≤ Cs) (hCsτ : Cs*τ ≤ 1)
    (N M : ℕ)
    (hmulti : ∀ g b, ((univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (action (gi g i) T.z₀) b ≤ Ci*F.S.scale g)).card ≤ M)
    (hnear : ∀ g b, ∑ i ∈ (univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (action (gi g i) T.z₀) b ≤ radius ell (160*(Q+1)*F.n*(g/(160*Q*(Q+1))))),
      F.S.flow.weight g i ≤ (N:ℝ)*Real.exp (-ell*F.n)^(g/(160*Q*(Q+1))))
    (hcost : ∀ g i j, F.S.good (F.S.state g i) → F.S.good (F.S.state g j) → P.pat g i=P.pat g j →
      ∀ d : ℝ, 0 < d → d ≤ 1 → F.S.scale g/d ≤ τ →
      d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀) →
        FlowPaid F gi c Cs Ci d g i j ∨ FlowPaid F gi c Cs Ci d g j i) : False := by
  classical
  have hHpos : 0 < F.H := by linarith only [hB,hH]
  let _ : Nonempty P.net := ⟨⟨P.net_nonempty.choose,P.net_nonempty.choose_spec⟩⟩
  obtain ⟨J,hJ⟩ := F.pattern_class hell.le hB hH CP hCP hpack hdiam P
  let K : ℝ := 6*(Fintype.card (Bool → P.net):ℝ)
  have hK : 0 < K := mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)
  let D := 160*(Q+1)*F.n
  let q := 160*Q*(Q+1)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 2) (pair_split_ratio Q hQ)
  let kval (g : ℕ) : ℝ := K*((J:ℝ)*(F.S.kmin+(D:ℝ)*g)+1)
  have hkval (g : ℕ) : 0 < kval g := mul_pos hK (by dsimp only [D]; positivity)
  have hsmall : ∀ᶠ g : ℕ in atTop,
      F.S.scale g/radius ell (D*(g/q)) ≤ τ :=
    (split_radius_ratio_tendsto Q F.n F.S.kmin hQ F.npos hell).eventually (eventually_le_nhds hτ)
  have hnearSmall : ∀ᶠ g : ℕ in atTop,
      2*(N:ℝ)*Real.exp (-ell*F.n)^(g/q) ≤ 1/kval g :=
    eventually_near_class_threshold hq hell F.n F.npos (N:ℝ) K J F.S.kmin D hK
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let C := (2*CP*(Cs/F.H)^Q*M*(T.ν univ:ℝ))/(c*F.S.root.length^2/2)
  have hfreq : ∃ᶠ g : ℕ in atTop, (1/2:ℝ) ≤ F.S.flow.goodMass g :=
    frequently_atTop.mpr F.good
  apply CannonPairCost.not_frequently_exp_le_quadratic
    (mul_pos hell (Nat.cast_pos.mpr F.npos)) C (K*((J:ℝ)*F.S.kmin+1)) (K*J*D)
  apply (hfreq.and_eventually (hJ.and (hsmall.and hnearSmall))).mono
  intro g hg
  obtain ⟨S,v,pstar,hpstar,hclass,hsize⟩ := hg.2.1 hg.1
  have hsize' : 1/kval g ≤ (S.card:ℝ)*pstar := by
    convert hsize using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [kval,K,D]
    push_cast
    ring
  let d := radius ell (D*(g/q))
  have hd : 0 < d := radius_pos _ _
  have hd1 : d ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell.le) (Nat.cast_nonneg _))
  let near (i j : Fin (F.S.flow.size g)) : Prop :=
    dist (action (gi g j) T.z₀) (action (gi g i) T.z₀) ≤ d
  let pairs := (S ×ˢ S).filter (fun ij => ¬ near ij.1 ij.2)
  have hfar : (S.card:ℝ)^2/2 ≤ (pairs.card:ℝ) := by
    apply far_pairs_card S (F.S.flow.weight g) near pstar
      ((N:ℝ)*Real.exp (-ell*F.n)^(g/q)) hpstar (fun i hi => (hclass i hi).2.2.1)
    · intro i _
      apply le_trans ?_ (hnear g (action (gi g i) T.z₀))
      apply sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => F.S.flow.nonneg g j)
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
    · have hh := hg.2.2.2.trans hsize'
      nlinarith only [hh]
  have hP : pairs ⊆ S ×ˢ S := filter_subset _ _
  have hswap : ∀ ij ∈ pairs, ij.swap ∈ pairs := by
    intro ij hij
    obtain ⟨hm,hn⟩ := mem_filter.mp hij
    obtain ⟨hi,hj⟩ := mem_product.mp hm
    apply mem_filter.mpr ⟨mem_product.mpr ⟨hj,hi⟩,?_⟩
    simpa only [near,Prod.fst_swap,Prod.snd_swap,dist_comm] using hn
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → F.H*F.S.scale g ≤
      dist (F.S.center g i) (F.S.center g j) :=
    fun i _ j _ hij => F.S.centers_separated F.decay hB hH g i j hij
  have hmultS (b : X) : (S.filter (fun j => dist (action (gi g j) T.z₀) b ≤ Ci*F.S.scale g)).card ≤ M :=
    (Finset.card_le_card (filter_subset_filter _ (subset_univ S))).trans (hmulti g b)
  have hpaid (ij : Fin (F.S.flow.size g) × Fin (F.S.flow.size g)) (hij : ij ∈ pairs) :
      FlowPaid F gi c Cs Ci d g ij.1 ij.2 ∨ FlowPaid F gi c Cs Ci d g ij.2 ij.1 := by
    obtain ⟨hm,hn⟩ := mem_filter.mp hij
    obtain ⟨hi,hj⟩ := mem_product.mp hm
    apply hcost g ij.1 ij.2 (hclass _ hi).1 (hclass _ hj).1
      ((hclass _ hi).2.1.trans (hclass _ hj).2.1.symm) d hd hd1 hg.2.2.1
    simpa only [near,not_le,dist_comm] using hn
  have hgap (i : Fin (F.S.flow.size g)) (_hi : i ∈ S) :
      (F.S.root.length*Real.exp (ell*F.n*g))*F.S.flow.weight g i ≤ F.S.len g i := by
    have heq : Real.exp (ell*F.n*g)*(Real.exp (-ell*F.n))^g=1 := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      convert Real.exp_zero using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    calc _ = Real.exp (ell*F.n*g)*(F.S.root.length*F.S.flow.weight g i) := by ring
         _ ≤ Real.exp (ell*F.n*g)*((Real.exp (-ell*F.n))^g*F.S.len g i) :=
           mul_le_mul_of_nonneg_left (F.S.weight_linear g i) (Real.exp_pos _).le
         _ = _ := by rw [← mul_assoc,heq,one_mul]
  have hscaleSmall : Cs*F.S.scale g/d ≤ 1 := by
    calc _ = Cs*(F.S.scale g/d) := by ring
         _ ≤ Cs*τ := mul_le_mul_of_nonneg_left hg.2.2.1 hCs.le
         _ ≤ 1 := hCsτ
  have hcomparison := charged_pair_comparison T.ν Q CP F.H (F.S.scale g) d Cs Ci hpack
    hHpos (radius_pos _ _) hd hHCs hd1 hscaleSmall S pairs (F.S.center g)
    (fun i => action (gi g i) T.z₀) (fun i => action (gi g i)) M hP hswap hsep hmultS
    (F.S.len g) (F.S.flow.weight g) c (F.S.root.length*Real.exp (ell*F.n*g)) pstar (kval g)
    hc.le (mul_pos F.S.root.length_pos (Real.exp_pos _)).le hpstar.le (hkval g)
    (fun i hi => (hclass i hi).2.2.1) hgap (fun ij => FlowPaid F gi c Cs Ci d g ij.1 ij.2)
    hpaid (fun _ _ hh => hh) hfar hsize'
  have hbound := pair_cost_exponential_bound Q F.n g hQ hell.le hc F.S.root.length_pos
    hCP hCs.le hHpos (by positivity : 0 ≤ (T.ν univ:ℝ)) M hcomparison
  convert hbound using 1
  · dsimp only [C,kval]
    congr 2
    ring

end CannonApprox

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_FlowPuncture
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
namespace CannonRelease

open CannonGraph CannonVisual CannonApprox CannonNode CannonPairs Set Metric Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {p : ∀ n, ι n → Boundary D} {r : ℕ → ℝ}

attribute [local instance] OAI.CannonRelease.flowPunctureMeasurableSpace
lemma flow_scale_visual :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q), ∀ g : ℕ,
    F.S.scale g=visualScale δ (F.S.kmin+160*(Q+1)*F.n*g) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F g
  dsimp [CannonNode.SourceConstruction.scale,CannonNode.radius,CannonVisual.visualScale]
  congr 1
  push_cast
  ring

lemma flow_center_z₀ :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → ∀ (g : ℕ) (i : Fin (F.S.flow.size g)),
    F.ε ≤ dist (F.S.center g i) T.z₀ := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB g i
  by_contra hn
  have hi := mem_closedBall.mp (F.S.center_mem hB g i)
  apply T.z₀not (F.local_domain ?_)
  rw [mem_closedBall]
  have ht := dist_triangle T.z₀ (F.S.center g i) T.x₀
  rw [dist_comm T.z₀ (F.S.center g i)] at ht
  linarith only [ht,hi,lt_of_not_ge hn]

local instance flowPunctureSetoid_rcc2e4e_1 : Setoid (BasedRay D) := raySetoid D
theorem flow_puncture_multiplicity :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → 4*(F.B+1) < F.H → ∀ C : ℝ, 0 ≤ C →
    ∃ N : ℕ, ∀ g b, ((univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (flowPuncture D hδ T F g i) b ≤ C*F.S.scale g)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB hH C hC
  have hep (g : ℕ) (i : Fin (F.S.flow.size g)) : flowPuncture D hδ T F g i =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D (F.S.center g i)).val
        (F.S.kmin+160*(Q+1)*F.n*g))⁻¹ T.z₀ := rfl
  have hdistance (x y : Boundary D) : dist x y=boundaryDist D hδ x y := rfl
  have hHp : 0 < F.H := by linarith only [hB,hH]
  obtain ⟨N,hN⟩ := puncture_ball_multiplicity D hδ F.εpos hHp hC
  refine ⟨N,fun g b => ?_⟩
  have hh := hN (univ : Finset (Fin (F.S.flow.size g)))
    (fun i => boundaryBasedRay D (F.S.center g i)) (boundaryBasedRay D T.z₀)
    (F.S.kmin+160*(Q+1)*F.n*g)
    (fun i _ => by simpa only [boundaryBasedRay_rep] using flow_center_z₀ D hδ T F hB g i)
    (fun i _ j _ hij => by simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F g]
      using F.S.centers_separated F.decay hB hH g i j hij) b
  simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F g,hep,hdistance] using hh

theorem flow_near_probability :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → 4*(F.B+1) < F.H →
    ∃ N : ℕ, ∀ g m (b : Boundary D),
      ∑ i ∈ (univ : Finset (Fin (F.S.flow.size (g+m)))).filter
        (fun i => dist (flowPuncture D hδ T F (g+m) i) b ≤ visualScale δ (160*(Q+1)*F.n*m)),
        F.S.flow.weight (g+m) i ≤ (N:ℝ)*(Real.exp (-(2*visualExponent δ)*F.n))^m := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB hH
  have hep (g : ℕ) (i : Fin (F.S.flow.size g)) : flowPuncture D hδ T F g i =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D (F.S.center g i)).val
        (F.S.kmin+160*(Q+1)*F.n*g))⁻¹ T.z₀ := rfl
  have hdistance (x y : Boundary D) : dist x y=boundaryDist D hδ x y := rfl
  have hHp : 0 < F.H := by linarith only [hB,hH]
  obtain ⟨N,hN⟩ := near_puncture_descendant_count D hδ F.εpos hHp (by positivity : 0 ≤ 2*(F.B+1))
  refine ⟨N,fun g m b => ?_⟩
  let S := (univ : Finset (Fin (F.S.flow.size (g+m)))).filter
    (fun i => dist (flowPuncture D hδ T F (g+m) i) b ≤ visualScale δ (160*(Q+1)*F.n*m))
  have hcount (a : Fin (F.S.flow.size g)) :
      (S.filter (fun i => F.S.flow.ancestor g m i=a)).card ≤ N := by
    let V := S.filter (fun i => F.S.flow.ancestor g m i=a)
    have hd : F.S.kmin+160*(Q+1)*F.n*(g+m)-160*(Q+1)*F.n*m =
        F.S.kmin+160*(Q+1)*F.n*g := by simp only [Nat.mul_add]; omega
    apply hN V (fun i => boundaryBasedRay D (F.S.center (g+m) i))
      (boundaryBasedRay D T.z₀) (boundaryBasedRay D (F.S.center g a)) (boundaryBasedRay D b)
      (F.S.kmin+160*(Q+1)*F.n*(g+m)) (160*(Q+1)*F.n*m) (by simp only [Nat.mul_add]; omega)
    · intro i _
      simpa only [boundaryBasedRay_rep] using flow_center_z₀ D hδ T F hB (g+m) i
    · intro i _ j _ hij
      simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F (g+m)]
        using F.S.centers_separated F.decay hB hH (g+m) i j hij
    · intro i hi
      have hia := (mem_filter.mp hi).2
      have hx := F.S.descendant_displacement F.decay hB g m i
      rw [hia,flow_scale_visual D hδ T F g] at hx
      simpa only [boundaryBasedRay_rep,hd] using hx
    · intro i hi
      have hip := (mem_filter.mp (mem_filter.mp hi).1).2
      simpa only [boundaryBasedRay_rep,hep,hdistance] using hip
  have hh := near_probability_bound S (F.S.flow.ancestor g m) (F.S.flow.weight (g+m))
    (F.S.flow.weight g) N ((Real.exp (-(2*visualExponent δ)*F.n))^m)
    (pow_nonneg (Real.exp_pos _).le _) (F.S.flow.nonneg g) (fun a => by
      convert hcount a using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext i
      simp only [mem_filter])
    (fun i _ => F.S.weight_conditional g m i)
  simpa only [F.S.flow.total_mass,mul_one] using hh

end CannonRelease

end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_OscillationMonoRange
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
open Set Filter Topology TopologicalSpace Metric

namespace CannonCrossEnergy

lemma oscillation_mono_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {S : Set X} {T : Set Y}
    (hS : S.Nonempty) (hT₁ : BddAbove (g '' T)) (hT₂ : BddBelow (g '' T))
    (hsub : f '' S ⊆ g '' T) :
    0 ≤ oscillation f S ∧ oscillation f S ≤ oscillation g T := by
  have hne := hS.image f
  exact ⟨sub_nonneg.mpr (csInf_le_csSup hne (hT₂.mono hsub) (hT₁.mono hsub)),
    sub_le_sub (csSup_le_csSup hT₁ hne hsub) (csInf_le_csInf hT₂ hne hsub)⟩

end CannonCrossEnergy

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_CenterNeighborhood
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
namespace CannonApprox

open Set Metric Filter Topology CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.center_neighborhood {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hB : 0 ≤ F.B+1) (g : ℕ) (i : Fin (F.S.flow.size g)) :
    closedBall (F.S.center g i) F.ε ⊆ T.Ω := by
  intro y hy
  apply F.local_domain
  have hx := mem_closedBall.mp (F.S.center_mem hB g i)
  rw [mem_closedBall] at hy ⊢
  linarith only [dist_triangle y (F.S.center g i) T.x₀,hy,hx]

theorem FlowPatternSetup.paid_alternative (T : RecordData action ι p r)
    {ell L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T ell L CE LE Q)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (hB : 0 ≤ F.B) (U V A cutoff : ℝ) (hV : 0 < V) (hA : 0 < A)
    (hwide : 3*U/T.H_diameter < A) (hroom : 2*U/A ≤ F.ε)
    (g : ℕ) (i j : Fin (F.S.flow.size g))
    (hi : F.S.good (F.S.state g i)) (hj : F.S.good (F.S.state g j))
    (hpat : P.pat g i=P.pat g j)
    (hui : ∀ y, dist (action (gi g i) y) (action (gi g i) T.z₀)*
      denominator (F.S.center g i) (F.S.scale g) y ≤ U*F.S.scale g)
    (huj : ∀ y, dist (action (gi g j) y) (action (gi g j) T.z₀)*
      denominator (F.S.center g j) (F.S.scale g) y ≤ U*F.S.scale g)
    (hli : ∀ y, denominator (F.S.center g i) (F.S.scale g) y ≤ cutoff →
      F.S.scale g ≤ V*dist (action (gi g i) y) (action (gi g i) T.z₀)*
        denominator (F.S.center g i) (F.S.scale g) y)
    (hlj : ∀ y, denominator (F.S.center g j) (F.S.scale g) y ≤ cutoff →
      F.S.scale g ≤ V*dist (action (gi g j) y) (action (gi g j) T.z₀)*
        denominator (F.S.center g j) (F.S.scale g) y)
    (hsmall : (F.B+2)*F.S.scale g ≤ cutoff)
    (havoid : A*F.S.scale g < 1/(V*(F.B+2)))
    (hfar : 2*A*F.S.scale g ≤ dist (action (gi g i) T.z₀) (action (gi g j) T.z₀)) :
    (min (F.S.κ/4) (1/16))*F.S.len g i ≤ CannonCrossEnergy.oscillation T.f
      ((action (gi g i)).symm '' closedBall (action (gi g j) T.z₀) (A*F.S.scale g)) ∨
    (min (F.S.κ/4) (1/16))*F.S.len g j ≤ CannonCrossEnergy.oscillation T.f
      ((action (gi g j)).symm '' closedBall (action (gi g i) T.z₀) (A*F.S.scale g)) := by
  obtain ⟨v₀,v₁,γ,hγ,hgap,hball,hsep⟩ := P.data g i hi
  obtain ⟨w₀,w₁,γ',hγ',hgap',hball',hsep'⟩ := P.data g j hj
  apply T.pattern_pair hr hrlim hpnet (gi g i) (gi g j) (F.S.center g i) (F.S.center g j)
    (action (gi g i) T.z₀) (action (gi g j) T.z₀) (F.S.scale g) U V A (F.B+2) cutoff F.ε
    (radius_pos _ _) hV hA (by linarith only [hB]) hwide hroom
    (F.center_neighborhood (by linarith only [hB]) g i)
    (F.center_neighborhood (by linarith only [hB]) g j)
    hui huj hli hlj hsmall havoid hfar
    (fun s => closedBall (P.pat g i s : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)))
    hball (by intro s; simpa only [hpat] using hball' s)
    v₀ v₁ γ hγ F.S.κ (F.S.len g i) (F.S.len g j) F.S.κpos
    (F.S.len_pos g i) (F.S.len_pos g j) hgap
  simpa only [hpat] using hsep'

end CannonApprox

end

section

namespace CannonPairs

open Set Metric CannonMagnification CannonCrossEnergy MeasureTheory

theorem exists_cost_measure_threshold {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (Ω : Set X) (f : X → ℝ) (ν : FiniteMeasure X) (E B ε C L U V cutoff A S : ℝ)
    (x₀ : X) (hε : 0 < ε) (hB : 0 < B) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hU : 0 < U) (hV : 0 < V)
    (hcut : 0 < cutoff) (hA : 0 < A) (hS : 0 < S) (hcoef : 2*L*A*U^2 ≤ S)
    (hf : ContinuousOn f Ω) (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (hmeasure : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ x ∈ K,
        closedBall x s ⊆ Ω ∧ (oscillation f (closedBall x s))^2 ≤ E*(ν (closedBall x (B*s)) : ℝ)) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (h : X ≃ₜ X) (x p p' : X) (R t lam : ℝ),
      x ∈ closedBall x₀ ε → 0 < R → 0 < t → t ≤ t₀ →
      Expansion h x R C L →
      (∀ y, dist (h y) p*denominator x R y ≤ U*R) →
      (∀ y, denominator x R y ≤ cutoff → R ≤ V*dist (h y) p*denominator x R y) →
      R=dist p' p*t → 2*A*R ≤ dist p' p → 0 ≤ lam →
      lam ≤ oscillation f (h.symm '' closedBall p' (A*R)) →
      lam^2/(E+1) ≤ (ν (closedBall (h.symm p') (B*(S*t^2))) : ℝ) ∧
      h '' closedBall (h.symm p') (B*(S*t^2)) ⊆ closedBall p' ((2*C*V^2*B*S)*R) ∧
      closedBall (h.symm p') (B*(S*t^2)) ⊆ closedBall x ((U+B*S)*t) := by
  have hKΩ : closedBall x₀ (3*ε/2) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith only [hε])).trans hloc
  obtain ⟨s₀,hs₀,hbound⟩ := hmeasure _ isClosed_closedBall.isCompact hKΩ
  let t₀ := min 1 (min (s₀/S) (min (ε/(2*U)) (min (cutoff/U) (1/(2*V*B*S)))))
  have ht₀ : 0 < t₀ := lt_min zero_lt_one (lt_min (div_pos hs₀ hS)
    (lt_min (div_pos hε (by positivity)) (lt_min (div_pos hcut hU) (by positivity))))
  refine ⟨t₀,ht₀,?_⟩
  intro h x p p' R t lam hx hR ht htt hexp hu hl hscale hfar hlam hosc
  have ht1 : t ≤ 1 := htt.trans (min_le_left _ _)
  have hts : t ≤ s₀/S := htt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hte : t ≤ ε/(2*U) := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have htc : t ≤ cutoff/U := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have htb : t ≤ 1/(2*V*B*S) := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hlocal : U*t ≤ cutoff := by simpa only [mul_comm] using (le_div_iff₀ hU).mp htc
  have hsmall : 2*V*B*S*t ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2*V*B*S)).mp htb
  have hgeom := cost_ball_geometry h x p p' R C L U V cutoff A B S t hR hC hL hU hV hA hB hS
    ht ht1 hexp hu hl hscale hfar hlocal hcoef hsmall
  have hd : 0 < dist p' p := by
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) dist_nonneg
    rw [heq,zero_mul] at hscale
    exact (ne_of_gt hR) hscale
  have hzx : dist (h.symm p') x ≤ U*t := by
    have hh := hu (h.symm p')
    rw [h.apply_symm_apply] at hh
    nth_rewrite 2 [hscale] at hh
    have hh' : denominator x R (h.symm p') ≤ U*t :=
      (mul_le_mul_iff_right₀ hd).mp (by nlinarith only [hh])
    rw [dist_comm]
    exact (le_max_right _ _).trans hh'
  have hUt : U*t ≤ ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*U)).mp hte
    linarith only [hh]
  have hzK : h.symm p' ∈ closedBall x₀ (3*ε/2) := by
    rw [mem_closedBall] at hx ⊢
    linarith only [dist_triangle (h.symm p') x x₀,hzx,hUt,hx]
  have hs : 0 < S*t^2 := mul_pos hS (sq_pos_of_pos ht)
  have hss : S*t^2 ≤ s₀ := by
    have hh := (le_div_iff₀ hS).mp hts
    have hsq : t^2 ≤ t := by nlinarith only [ht,ht1]
    nlinarith only [hh,mul_le_mul_of_nonneg_left hsq hS.le]
  obtain ⟨hball,hmeas⟩ := hbound _ hs hss _ hzK
  have hb := (isCompact_closedBall (h.symm p') (S*t^2)).image_of_continuousOn (hf.mono hball)
  have hsub : f '' (h.symm '' closedBall p' (A*R)) ⊆ f '' closedBall (h.symm p') (S*t^2) :=
    image_mono hgeom.1
  have hne : (h.symm '' closedBall p' (A*R)).Nonempty :=
    (nonempty_closedBall.mpr (mul_pos hA hR).le).image h.symm
  have hosc' := hosc.trans (oscillation_mono_range hne hb.bddAbove hb.bddBelow hsub).2
  have hsq := (pow_le_pow_left₀ hlam hosc' 2).trans hmeas
  refine ⟨(div_le_iff₀ (by linarith only [hE] : 0 < E+1)).mpr ?_,hgeom.2⟩
  have hn : 0 ≤ (ν (closedBall (h.symm p') (B*(S*t^2))) : ℝ) := NNReal.coe_nonneg _
  nlinarith only [hsq,hn]

end CannonPairs

end

namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

theorem FlowPatternSetup.cost_data {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell) (hL : 1 ≤ L)
    (hCE : 0 < CE) (hLE : 0 < LE) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (hexp : ∀ g i, Expansion (action (gi g i)) (F.S.center g i) (F.S.scale g) CE LE)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n) :
    ∃ c Cs Ci τ : ℝ, 0 < c ∧ 0 < Cs ∧ 0 < Ci ∧ 0 < τ ∧ F.H ≤ Cs ∧ Cs*τ ≤ 1 ∧
      ∀ g i j, F.S.good (F.S.state g i) → F.S.good (F.S.state g j) → P.pat g i=P.pat g j →
      ∀ d : ℝ, 0 < d → d ≤ 1 → F.S.scale g/d ≤ τ →
      d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀) →
        FlowPaid F gi c Cs Ci d g i j ∨ FlowPaid F gi c Cs Ci d g j i := by
  obtain ⟨_,hB,_,_,_,_,hH⟩ := F.margins hL hCE.le hLE.le
  have hB0 : 0 ≤ F.B := by linarith only [hB]
  have hB1 : 0 ≤ F.B+1 := by linarith only [hB]
  have hB2 : 0 < F.B+2 := by linarith only [hB]
  let U := CE/F.ε
  let V := 2*LE/F.ε
  have hU : 0 < U := div_pos hCE F.εpos
  have hV : 0 < V := div_pos (by positivity) F.εpos
  let A := 1+3*U/T.H_diameter+2*U/F.ε
  have hAA : 0 ≤ 3*U/T.H_diameter := (div_pos (by positivity) T.H_diameter_pos).le
  have hAB : 0 ≤ 2*U/F.ε := (div_pos (by positivity) F.εpos).le
  have hA : 0 < A := by dsimp only [A]; linarith only [hAA,hAB]
  have hwide : 3*U/T.H_diameter < A := by dsimp only [A]; linarith only [hAB]
  have hroom : 2*U/A ≤ F.ε := by
    apply (div_le_iff₀ hA).mpr
    have hh : 2*U/F.ε ≤ A := by dsimp only [A]; linarith only [hAA]
    have hh' := (div_le_iff₀ F.εpos).mp hh
    linarith only [hh']
  let Scoef := 1+2*LE*A*U^2
  have hS : 0 < Scoef := by dsimp only [Scoef]; positivity
  have hcoef : 2*LE*A*U^2 ≤ Scoef := le_add_of_nonneg_left zero_le_one
  obtain ⟨t₀,ht₀,hcost⟩ := exists_cost_measure_threshold T.Ω T.f T.ν T.E T.Cμ F.ε
    CE LE U V (F.ε/2) A Scoef T.x₀ F.εpos T.Cμ_pos T.E_nonneg hCE.le hLE.le hU hV
    (by have := F.εpos; positivity) hA hS hcoef T.continuous F.local_domain T.measure_bound
  let Cs := max F.H (U+T.Cμ*Scoef)
  let Ci := 2*CE*V^2*T.Cμ*Scoef
  have hCμ := T.Cμ_pos
  have hCs : 0 < Cs := (by positivity : 0 < U+T.Cμ*Scoef).trans_le (le_max_right _ _)
  have hCi : 0 < Ci := by dsimp only [Ci]; positivity
  let τ := min t₀ (min (F.ε/(2*(F.B+2)))
    (min (1/(2*A*V*(F.B+2))) (min (1/(2*A)) (1/Cs))))
  have hτ : 0 < τ := lt_min ht₀ (lt_min (div_pos F.εpos (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have τ₀ : τ ≤ t₀ := min_le_left _ _
  have τ₁ : τ ≤ F.ε/(2*(F.B+2)) := (min_le_right _ _).trans (min_le_left _ _)
  have τ₂ : τ ≤ 1/(2*A*V*(F.B+2)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have τ₃ : τ ≤ 1/(2*A) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have τ₄ : τ ≤ 1/Cs := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let cp := min (F.S.κ/4) (1/16)
  have hcp : 0 < cp := lt_min (div_pos F.S.κpos (by norm_num)) (by norm_num)
  let c := cp^2/(T.E+1)
  have hEn : 0 < T.E+1 := by linarith only [T.E_nonneg]
  refine ⟨c,Cs,Ci,τ,div_pos (sq_pos_of_pos hcp) hEn,hCs,hCi,hτ,le_max_left _ _,?_,?_⟩
  · have hh := (le_div_iff₀ hCs).mp τ₄
    exact (mul_comm Cs τ).le.trans hh
  intro g i j hi hj hpat d hd hd1 hsmall hfar
  have hR : 0 < F.S.scale g := radius_pos _ _
  have hR1 : F.S.scale g ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell) (Nat.cast_nonneg _))
  have hRratio : F.S.scale g ≤ F.S.scale g/d :=
    (le_div_iff₀ hd).mpr ((mul_le_mul_of_nonneg_left hd1 hR.le).trans_eq (mul_one _))
  have hRτ := hRratio.trans hsmall
  have hbounds (v : Fin (F.S.flow.size g)) := puncture_bounds (action (gi g v))
    (F.S.center g v) T.z₀ (F.S.scale g) CE LE F.ε hR hCE.le hLE F.εpos hR1
    (F.center_puncture hB1 g v) hdiam (hexp g v)
  have hsmall' : (F.B+2)*F.S.scale g ≤ F.ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(F.B+2))).mp (hRτ.trans τ₁)
    linarith only [hh]
  have havoid : A*F.S.scale g < 1/(V*(F.B+2)) := by
    apply (lt_div_iff₀ (mul_pos hV hB2)).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A*V*(F.B+2))).mp (hRτ.trans τ₂)
    nlinarith only [hh]
  have hfar' : 2*A*F.S.scale g ≤ d := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp (hsmall.trans τ₃)
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    field_simp at hh'
    nlinarith only [hh']
  have hpaid := P.paid_alternative T F gi hr hrlim hpnet hB0 U V A (F.ε/2) hV hA
    hwide hroom g i j hi hj hpat (hbounds i).1 (hbounds j).1 (hbounds i).2
    (hbounds j).2 hsmall' havoid (hfar'.trans hfar.le)
  have hcharge (i j : Fin (F.S.flow.size g))
      (hfj : d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀))
      (hpay : cp*F.S.len g i ≤ CannonCrossEnergy.oscillation T.f
        ((action (gi g i)).symm '' closedBall (action (gi g j) T.z₀) (A*F.S.scale g))) :
      FlowPaid F gi c Cs Ci d g i j := by
    let δij := dist (action (gi g j) T.z₀) (action (gi g i) T.z₀)
    have hdi : d ≤ δij := by simpa only [δij,dist_comm] using hfj.le
    have hδ : 0 < δij := hd.trans_le hdi
    let t := F.S.scale g/δij
    have ht : 0 < t := div_pos hR hδ
    have htt : t ≤ F.S.scale g/d := div_le_div_of_nonneg_left hR.le hd hdi
    have hscale : F.S.scale g=δij*t := by dsimp only [t]; field_simp
    have hlam : 0 ≤ cp*F.S.len g i := (mul_pos hcp (F.S.len_pos g i)).le
    obtain ⟨hm,him,hsrc⟩ := hcost (action (gi g i)) (F.S.center g i)
      (action (gi g i) T.z₀) (action (gi g j) T.z₀) (F.S.scale g) t (cp*F.S.len g i)
      (F.S.center_mem hB1 g i) hR ht (htt.trans (hsmall.trans τ₀))
      (hexp g i) (hbounds i).1 (hbounds i).2 hscale (hfar'.trans hdi) hlam hpay
    refine ⟨closedBall ((action (gi g i)).symm (action (gi g j) T.z₀)) (T.Cμ*(Scoef*t^2)),
      measurableSet_closedBall,?_,?_,him⟩
    · convert hm using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [c]
      ring
    · apply hsrc.trans (closedBall_subset_closedBall ?_)
      calc (U+T.Cμ*Scoef)*t ≤ Cs*t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
           _ ≤ Cs*(F.S.scale g/d) := mul_le_mul_of_nonneg_left htt hCs.le
           _ = Cs*F.S.scale g/d := by ring
  rcases hpaid with hp | hp
  · exact Or.inl (hcharge i j hfar hp)
  · exact Or.inr (hcharge j i (by simpa only [dist_comm] using hfar) hp)

end CannonApprox

end

namespace CannonRelease
open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox
open CannonNode CannonAnnular Set Metric Filter Topology Finset MeasureTheory

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_no_record_flow_oai :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let ell := 2*visualExponent δ
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D) (r : ℕ → ℝ),
    (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n x, ∃ i, dist (p n i) x ≤ r n) →
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      (Q : ℕ), 0 < Q → ∀ CP : ℝ, 0 ≤ CP → PolynomialPacking (X:=Boundary D) Q CP →
    ∀ L : ℝ, 1 ≤ L →
      (∀ x u w : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist w x ≤ s →
        JoinedIn (ball x (L*s)) u w) →
    FlowSetup T ell L CE LE Q → False := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  dsimp only
  intro ι hι p r hr hrlim hpnet T Q hQ CP hCP hpack L hL hpaths F
  let ell := 2*visualExponent δ
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hell : 0 < ell := mul_pos (by norm_num) (visualExponent_pos δ)
  have hCE : 0 < CE := by dsimp [CE]; positivity
  have hLE : 0 < LE := by dsimp [LE]; positivity
  let gi (g : ℕ) (i : Fin (F.S.flow.size g)) :=
    ((boundaryBasedRay D (F.S.center g i)).val (F.S.kmin+160*(Q+1)*F.n*g))⁻¹
  have hexp (g : ℕ) (i : Fin (F.S.flow.size g)) :
      Expansion (boundaryHomeomorph D ⟨δ,hδ⟩ (gi g i)) (F.S.center g i) (F.S.scale g) CE LE := by
    simpa only [CannonNode.radius_eq_power, boundaryExpansion, gi, CE, LE] using
      boundaryExpansion_formula D hδ (F.S.center g i) (F.S.kmin+160*(Q+1)*F.n*g)
  have hdiam (x y : Boundary D) : dist x y ≤ 1 := boundaryDist_le_one D hδ x y
  obtain ⟨P⟩ := exists_flow_patterns T F hL hCE.le hLE.le hpaths
    (fun g i => boundaryHomeomorph D ⟨δ,hδ⟩ (gi g i)) hexp
  obtain ⟨c,Cs,Ci,τ,hc,hCs,hCi,hτ,hHCs,hCsτ,hcost⟩ :=
    P.cost_data F hell.le hL hCE hLE hdiam gi hexp hr hrlim hpnet
  obtain ⟨_,hB,_,_,_,_,hH⟩ := F.margins hL hCE.le hLE.le
  have hB1 : 0 ≤ F.B+1 := by linarith only [hB]
  obtain ⟨M,hM⟩ := flow_puncture_multiplicity D hδ T F hB1 hH Ci hCi.le
  obtain ⟨N,hN⟩ := flow_near_probability D hδ T F hB1 hH
  apply F.no_pair_data hell hQ hB1 hH CP hCP hpack hdiam gi P c Cs Ci τ hc hCs hτ
    hHCs hCsτ N M hM ?_ hcost
  intro g b
  let m := g/(160*Q*(Q+1))
  have hsum : g-m+m=g := Nat.sub_add_cancel (Nat.div_le_self _ _)
  have hh := hN (g-m) m b
  rw [hsum] at hh
  have hscale (k : ℕ) : visualScale δ k=radius ell k := by
    dsimp only [visualScale,radius,ell]
    congr 1
    push_cast
    ring
  simpa only [hscale, flowPuncture, boundaryExpansion, gi, ell, m, id_eq] using hh

end CannonRelease

end
end
end
end

end OAI
end

theorem solution.{v, u_1} : type_of% @OAI.CannonRelease.boundary_no_record_flow_oai.{v, u_1} := @OAI.CannonRelease.boundary_no_record_flow_oai.{v, u_1}
