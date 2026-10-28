-- Prove2me | solution 1 for OAI.CannonRelease.boundary_holder_scalar_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:05:20.079322+00:00
-- url     : https://prove2.me/submissions/dcfe0988-95c3-4c7a-8063-054c3b6fbd73

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
end OAICompat434

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

local instance instSetoidBasedRay_2_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_3_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_10_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_12_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_27_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_29_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_31_rbf13aa_1 : Setoid (BasedRay D) := raySetoid D
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

section

section

open Set Metric Filter Topology

namespace CannonMagnification

theorem preimage_distance_bound {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z₀ z : X) (r C L e d : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (he : 0 < e) (hd : 0 < d)
    (hexp : Expansion h x r C L)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hz₀ : d ≤ dist x z₀) (hz : e ≤ dist z (h z₀)) :
    dist x (h.symm z) ≤ (C/(e*d))*r := by
  have hh := (hexp (h.symm z) z₀).1
  rw [h.apply_symm_apply] at hh
  have h₁ : e*dist x (h.symm z)*d ≤
      dist z (h z₀)*max r (dist x (h.symm z))*max r (dist x z₀) := by
    apply mul_le_mul
    · exact mul_le_mul hz (le_max_right _ _) dist_nonneg (dist_nonneg)
    · exact hz₀.trans (le_max_right _ _)
    · exact hd.le
    · positivity
  have h₂ : C*r*dist (h.symm z) z₀ ≤ C*r := by
    exact (mul_le_mul_of_nonneg_left (hdiam _ _) (mul_nonneg hC hr.le)).trans_eq (mul_one _)
  have hh' := h₁.trans (hh.trans h₂)
  have hh'' : dist x (h.symm z) ≤ (C*r)/(e*d) := by
    apply (le_div_iff₀ (mul_pos he hd)).mpr
    calc
      dist x (h.symm z)*(e*d) = e*dist x (h.symm z)*d := by ring
      _ ≤ C*r := hh'
  exact hh''.trans_eq (by ring)

theorem inverse_lipschitz_on_preimages {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z w : X) (r C L B : ℝ)
    (hr : 0 < r) (hL : 0 ≤ L) (hexp : Expansion h x r C L)
    (hz : dist x (h.symm z) ≤ B*r) (hw : dist x (h.symm w) ≤ B*r) :
    dist (h.symm z) (h.symm w) ≤ (L*(max 1 B)^2)*r*dist z w := by
  have hb : 0 ≤ max 1 B := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hmax (v : X) (hv : dist x v ≤ B*r) : max r (dist x v) ≤ max 1 B*r := by
    apply max_le
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) B) hr.le
    · exact hv.trans (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) B) hr.le)
  have hh := (hexp (h.symm z) (h.symm w)).2
  rw [h.apply_symm_apply,h.apply_symm_apply] at hh
  have hprod : L*dist z w*max r (dist x (h.symm z))*max r (dist x (h.symm w)) ≤
      L*dist z w*(max 1 B*r)*(max 1 B*r) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hmax _ hz) (mul_nonneg hL dist_nonneg)
    · exact hmax _ hw
    · exact hr.le.trans (le_max_left _ _)
    · positivity
  have hh' : r*dist (h.symm z) (h.symm w) ≤ r*((L*(max 1 B)^2)*r*dist z w) :=
    (hh.trans hprod).trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ hr).mp hh'

theorem image_ball_avoids_puncture {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z₀ y : X) (r C L d : ℝ)
    (hr : 0 < r) (hL : 0 < L) (_hd : 0 < d) (hrd : r ≤ d/2)
    (hexp : Expansion h x r C L) (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hz₀ : d ≤ dist x z₀) (hy : dist x y ≤ r) :
    d/(2*L) ≤ dist (h y) (h z₀) := by
  have hdone : d ≤ 1 := hz₀.trans (hdiam _ _)
  have hrone : r ≤ 1 := by linarith
  have hfar : d/2 ≤ dist y z₀ := by
    have hh := dist_triangle x y z₀
    linarith
  have hh := (hexp y z₀).2
  rw [max_eq_left hy] at hh
  have hmax : max r (dist x z₀) ≤ 1 := max_le hrone (hdiam _ _)
  have hbound : L*dist (h y) (h z₀)*r*max r (dist x z₀) ≤
      L*dist (h y) (h z₀)*r := by
    exact (mul_le_mul_of_nonneg_left hmax (by positivity)).trans_eq (mul_one _)
  have heq : dist y z₀ ≤ L*dist (h y) (h z₀) := by
    have hh' : r*dist y z₀ ≤ r*(L*dist (h y) (h z₀)) :=
      (hh.trans hbound).trans_eq (by ring)
    exact (mul_le_mul_iff_right₀ hr).mp hh'
  apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
  nlinarith

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

namespace CannonCrossEnergy

variable {X : Type*} [TopologicalSpace X]

lemma mem_rangeInterval {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) {x : X} (hx : x ∈ A) : f x ∈ rangeInterval f A := by
  have hc := hA.image hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hx),
    le_csSup hc.bddAbove (mem_image_of_mem f hx)⟩

lemma oscillation_nonneg {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) (hne : A.Nonempty) : 0 ≤ oscillation f A := by
  exact sub_nonneg.mpr (csInf_le_csSup (hne.image f)
    (hA.image hf).bddBelow (hA.image hf).bddAbove)

lemma rangeInterval_eq_image {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) (hne : A.Nonempty) (hcon : IsPreconnected A) :
    rangeInterval f A = f '' A := by
  apply le_antisymm
  · exact (hcon.image f hf.continuousOn).ordConnected.out
      ((hA.image hf).sInf_mem (hne.image f)) ((hA.image hf).sSup_mem (hne.image f))
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_rangeInterval hf hA hx

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
-- module Solutions.OAIQ046_CN.Cannon_Flows_WeightedOscillation
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
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology

namespace CannonMagnification

lemma exists_tail_maximum (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (ht : Tendsto f atTop (𝓝 0)) (n : ℕ) :
    ∃ k, n ≤ k ∧ ∀ l, k ≤ l → f l ≤ f k := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (hf n)))
  let B := max N (n+1)
  have hnB : n ∈ Finset.Ico n B := by simp only [Finset.mem_Ico]; exact ⟨le_rfl,(Nat.lt_succ_self n).trans_le (le_max_right _ _)⟩
  obtain ⟨k,hk,hmax⟩ := (Finset.Ico n B).exists_max_image f ⟨n,hnB⟩
  have hnk : n ≤ k := (Finset.mem_Ico.mp hk).1
  refine ⟨k,hnk,?_⟩
  intro l hkl
  by_cases hl : l < B
  · exact hmax l (Finset.mem_Ico.mpr ⟨hnk.trans hkl,hl⟩)
  · exact (hN l ((le_max_left N (n+1)).trans (le_of_not_gt hl))).le.trans (hmax n hnB)

theorem exists_tail_records (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (ht : Tendsto f atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i l, k i ≤ l → f l ≤ f (k i) := by
  choose next hn hnext using exists_tail_maximum f hf ht
  let k : ℕ → ℕ := fun j => Nat.rec (next 0) (fun _ n => next (n+1)) j
  refine ⟨k,strictMono_nat_of_lt_succ (fun i => ?_),?_⟩
  · exact (Nat.lt_succ_self (k i)).trans_le (hn (k i+1))
  · intro i l hl
    cases i with
    | zero => exact hnext 0 l hl
    | succ i => exact hnext (k i+1) l hl

theorem weighted_tail_records (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (b : ℝ) (hb : 0 < b)
    (ht : Tendsto (fun n => A n*b^n) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i j, A (k i+j) ≤ (b^j)⁻¹*A (k i) := by
  obtain ⟨k,hk,htail⟩ := exists_tail_records (fun n => A n*b^n)
    (fun n => mul_pos (hA n) (pow_pos hb n)) ht
  refine ⟨k,hk,?_⟩
  intro i j
  have hh := htail i (k i+j) (Nat.le_add_right _ _)
  rw [pow_add] at hh
  have hdiv : A (k i+j)*b^j ≤ A (k i) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hb (k i))).mp
    nlinarith [hh]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (pow_pos hb j)).mpr hdiv

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking
open Set Metric Filter Topology

lemma oscillation_le_of_pairwise {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A)
    (hne : A.Nonempty) (B : ℝ) (hpair : ∀ x ∈ A, ∀ y ∈ A, f x-f y ≤ B) :
    oscillation f A ≤ B := by
  obtain ⟨x,hx,hfx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,hfy⟩ := (hA.image hf).sInf_mem (hne.image f)
  simpa only [CannonCrossEnergy.oscillation,← hfx,← hfy] using hpair x hx y hy

theorem connected_oscillation_cover {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : X → ℝ) (hf : Continuous f) (P : Set X) (hP : IsCompact P)
    (hconn : IsConnected P) (A : ι → Set X) (hA : ∀ i, IsCompact (A i))
    (hne : ∀ i, (A i).Nonempty) (hcover : ∀ x ∈ P, ∃ i, x ∈ A i) :
    oscillation f P ≤ ∑ i, oscillation f (A i) := by
  classical
  have hcov : ∀ t ∈ rangeInterval f P,
      (1 : ℝ) ≤ ∑ i, (rangeInterval f (A i)).indicator (fun _ : ℝ => (1 : ℝ)) t := by
    intro t ht
    rw [rangeInterval_eq_image hf hP hconn.1 hconn.2] at ht
    obtain ⟨x,hx,rfl⟩ := ht
    obtain ⟨i,hi⟩ := hcover x hx
    have ht := mem_rangeInterval hf (hA i) hi
    calc
      (1 : ℝ) = (rangeInterval f (A i)).indicator (fun _ : ℝ => (1 : ℝ)) (f x) := by simp [ht]
      _ ≤ _ := Finset.single_le_sum
        (f := fun j : ι => (rangeInterval f (A j)).indicator (fun _ : ℝ => (1 : ℝ)) (f x))
        (fun j _ => Set.indicator_nonneg (by intro; norm_num) _) (Finset.mem_univ i)
  have hh := weighted_interval_cover (fun i => sInf (f '' A i))
    (fun i => sSup (f '' A i)) (fun _ => 1) (sInf (f '' P)) (sSup (f '' P)) 1
    (sub_nonneg.mp (oscillation_nonneg hf hP hconn.1))
    (fun i => sub_nonneg.mp (oscillation_nonneg hf (hA i) (hne i)))
    (fun _ => by norm_num) hcov
  simpa only [one_mul,CannonCrossEnergy.oscillation] using hh

lemma weightedOscillation_bounds {X : Type*} [MetricSpace X] [CompactSpace X]
    (f w : X → ℝ) (hf : Continuous f) (O : Set X) (hO : O.Nonempty)
    (hw : ∀ x ∈ O, w x ∈ Icc (0:ℝ) 1) (r : ℝ) (hr : 0 ≤ r)
    (B : ℝ) (_hB : 0 ≤ B) (hbound : ∀ x ∈ O, oscillation f (closedBall x r) ≤ B) :
    0 ≤ weightedOscillation f w O r ∧ weightedOscillation f w O r ≤ B ∧
      ∀ x ∈ O, w x*oscillation f (closedBall x r) ≤ weightedOscillation f w O r := by
  have hpoint (x : X) (hx : x ∈ O) : w x*oscillation f (closedBall x r) ≤ B := by
    have hh := oscillation_nonneg hf (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩
    calc
      w x*oscillation f (closedBall x r) ≤ 1*B :=
        mul_le_mul (hw x hx).2 (hbound x hx) hh (by norm_num)
      _ = B := one_mul _
  have hBdd : BddAbove ((fun x => w x*oscillation f (closedBall x r)) '' O) :=
    ⟨B,by rintro _ ⟨x,hx,rfl⟩; exact hpoint x hx⟩
  have hne := hO.image (fun x => w x*oscillation f (closedBall x r))
  have hle (x : X) (hx : x ∈ O) : w x*oscillation f (closedBall x r) ≤ weightedOscillation f w O r :=
    le_csSup hBdd (mem_image_of_mem _ hx)
  refine ⟨?_,csSup_le hne (by rintro _ ⟨x,hx,rfl⟩; exact hpoint x hx),hle⟩
  obtain ⟨x,hx⟩ := hO
  exact (mul_nonneg (hw x hx).1
    (oscillation_nonneg hf (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩)).trans (hle x hx)

theorem weightedOscillation_lower {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f w : X → ℝ) (hf : Continuous f) (O P : Set X)
    (hP : IsCompact P) (hconn : IsConnected P) (hPO : P ⊆ O)
    (hw : ∀ x ∈ O, w x ∈ Icc (0:ℝ) 1)
    (v : ℝ) (_hv : 0 < v) (hvary : v ≤ oscillation f P)
    (η : ℝ) (hη : 0 < η) (hwP : ∀ x ∈ P, η ≤ w x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B) :
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      (η*v/(max CP 1))*r^Q ≤ weightedOscillation f w O r := by
  classical
  intro r hr hr1
  obtain ⟨T,hTP,hsep,hnet⟩ := CannonNet.exists_finite_separated_net P hP.totallyBounded r hr
  have hO : O.Nonempty := hconn.1.mono hPO
  obtain ⟨hA0,hAB,hA⟩ := weightedOscillation_bounds f w hf O hO hw r hr.le B hB
    (fun x hx => hbound x hx r hr.le)
  have hoc := connected_oscillation_cover f hf P hP hconn
    (fun i : T => closedBall (i : X) r) (fun _ => isCompact_closedBall _ _)
    (fun i => ⟨i.val,mem_closedBall_self hr.le⟩) (fun x hx => by
      obtain ⟨y,hy,hxy⟩ := hnet x hx
      exact ⟨⟨y,hy⟩,mem_closedBall.mpr hxy⟩)
  obtain ⟨p,hp⟩ := hconn.1
  have hcard₀ := hpack p 1 r hr hr1 le_rfl T (fun y _ => hdiam p y) hsep
  have hcard : (Fintype.card T : ℝ) ≤ (max CP 1)*(1/r)^Q := by
    simpa only [Fintype.card_coe] using hcard₀.trans
      (mul_le_mul_of_nonneg_right (le_max_left CP 1) (by positivity))
  have hseed : η*v ≤ (max CP 1)*(1/r)^Q*weightedOscillation f w O r := by
    calc
      η*v ≤ η*oscillation f P := mul_le_mul_of_nonneg_left hvary hη.le
      _ ≤ η*∑ i : T, oscillation f (closedBall (i : X) r) := mul_le_mul_of_nonneg_left hoc hη.le
      _ = ∑ i : T, η*oscillation f (closedBall (i : X) r) := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : T, weightedOscillation f w O r := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_right (hwP i.val (hTP i.property))
          (oscillation_nonneg hf (isCompact_closedBall _ _) ⟨i.val,mem_closedBall_self hr.le⟩)).trans
            (hA i.val (hPO (hTP i.property)))
      _ = (Fintype.card T : ℝ)*weightedOscillation f w O r := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hA0
  have hpow : 0 < r^Q := pow_pos hr Q
  have hh := mul_le_mul_of_nonneg_right hseed hpow.le
  have heq : (max CP 1)*(1/r)^Q*weightedOscillation f w O r*r^Q =
      (max CP 1)*weightedOscillation f w O r := by
    rw [div_pow,one_pow]
    field_simp
  rw [heq] at hh
  have hCP : 0 < max CP 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hh' : (η*v*r^Q)/(max CP 1) ≤ weightedOscillation f w O r :=
    (div_le_iff₀ hCP).mpr (by nlinarith [hh])
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy Set Metric Filter Topology

lemma infDist_compl_weight {X : Type*} [MetricSpace X]
    (O : Set X) (hO : IsOpen O) (hne : Oᶜ.Nonempty)
    (hdiam : ∀ x y : X, dist x y ≤ 1) (q : ℕ) :
    ∀ x ∈ O, 0 < infDist x Oᶜ ^ (q+1) ∧ infDist x Oᶜ ^ (q+1) ≤ 1 := by
  intro x hx
  have hd : 0 < infDist x Oᶜ := (hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa)
  have hd1 : infDist x Oᶜ ≤ 1 := by
    obtain ⟨y,hy⟩ := hne
    exact (infDist_le_dist_of_mem hy).trans (hdiam x y)
  exact ⟨pow_pos hd _,pow_le_one₀ hd.le hd1⟩

lemma infDist_compl_compact_lower {X : Type*} [MetricSpace X]
    (O P : Set X) (hO : IsOpen O) (hne : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPe : P.Nonempty) (hPO : P ⊆ O) (q : ℕ) :
    ∃ η > 0, ∀ x ∈ P, η ≤ infDist x Oᶜ ^ (q+1) := by
  obtain ⟨x,hx,hmin⟩ := hP.exists_isMinOn hPe ((continuous_infDist_pt Oᶜ).pow (q+1)).continuousOn
  refine ⟨_,pow_pos ((hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hPO hx)) _,hmin⟩

theorem weighted_centers_escape (q : ℕ) (r δ A : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hδ : ∀ i, 0 ≤ δ i)
    (hrt : Tendsto r atTop (𝓝 0)) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ i, c*(r i)^q ≤ A i)
    (hselected : ∀ i, A i ≤ 2*(δ i)^(q+1)*B) :
    Tendsto (fun i => δ i/r i) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro L
  let T : ℝ := max L 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have ht : Tendsto (fun i => 2*B*T^(q+1)*r i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrt.const_mul (2*B*T^(q+1))
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with i hi
  have hlarge : T < δ i/r i := by
    by_contra hn
    have hδT : δ i ≤ T*r i := (div_le_iff₀ (hr i)).mp (le_of_not_gt hn)
    have hp := pow_le_pow_left₀ (hδ i) hδT (q+1)
    have hh : c*(r i)^q ≤ (2*B*T^(q+1)*r i)*(r i)^q := by
      calc
        c*(r i)^q ≤ A i := hlower i
        _ ≤ 2*(δ i)^(q+1)*B := hselected i
        _ ≤ 2*(T*r i)^(q+1)*B := by nlinarith [hp]
        _ = _ := by rw [mul_pow,pow_succ (r i)]; ring
    have hh' := (mul_le_mul_iff_left₀ (pow_pos (hr i) q)).mp hh
    exact (not_le_of_gt hi) hh'
  exact (le_max_left L 1).trans hlarge.le

theorem select_weighted_magnifications {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O)
    (hOe : O.Nonempty) (hOc : Oᶜ.Nonempty)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (q : ℕ) (a : ℝ) (ha : 1 < a) (β b : ℝ)
    (hβ : 0 < β) (hb : 1 < b) (hβb : β*b < 1)
    (c C B : ℝ) (hc : 0 < c) (_hC : 0 ≤ C) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B)
    (hlower : ∀ n : ℕ, c*((a^n)⁻¹)^q ≤
      weightedOscillation f (fun x => infDist x Oᶜ ^ (q+1)) O ((a^n)⁻¹))
    (hupper : ∀ n : ℕ,
      weightedOscillation f (fun x => infDist x Oᶜ ^ (q+1)) O ((a^n)⁻¹) ≤ C*β^n) :
    ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ), StrictMono k ∧
      (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      (∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) ∧
      (∀ i j y, y ∈ O →
        infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
          (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop := by
  classical
  let w : X → ℝ := fun x => infDist x Oᶜ ^ (q+1)
  let A : ℕ → ℝ := fun n => weightedOscillation f w O ((a^n)⁻¹)
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hr (n : ℕ) : 0 < (a^n)⁻¹ := inv_pos.mpr (pow_pos ha0 n)
  have hw (x : X) (hx : x ∈ O) : 0 < w x ∧ w x ≤ 1 := infDist_compl_weight O hO hOc hdiam q x hx
  have hAbounds (n : ℕ) := weightedOscillation_bounds f w hf O hOe
    (fun x hx => ⟨(hw x hx).1.le,(hw x hx).2⟩) _ (hr n).le B hB
      (fun x hx => hbound x hx _ (hr n).le)
  have hApos (n : ℕ) : 0 < A n := (mul_pos hc (pow_pos (hr n) q)).trans_le (hlower n)
  have ht : Tendsto (fun n => A n*b^n) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hβ (zero_lt_one.trans hb)).le hβb
    have ht' : Tendsto (fun n : ℕ => C*(β*b)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hp.const_mul C
    apply squeeze_zero (fun n => (mul_pos (hApos n) (pow_pos (zero_lt_one.trans hb) n)).le) _ ht'
    intro n
    simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_right (hupper n)
      (pow_nonneg (zero_lt_one.trans hb).le n)
  obtain ⟨k,hk,htail⟩ := weighted_tail_records A hApos b (zero_lt_one.trans hb) ht
  have hchoose (i : ℕ) : ∃ x ∈ O, A (k i)/2 < w x*oscillation f (closedBall x ((a^(k i))⁻¹)) := by
    obtain ⟨v,⟨x,hx,hv⟩,hval⟩ := exists_lt_of_lt_csSup
      (s := (fun x => w x*oscillation f (closedBall x ((a^(k i))⁻¹))) '' O)
      (hOe.image _) (show A (k i)/2 < A (k i) by linarith [hApos (k i)])
    exact ⟨x,hx,by simpa only [← hv] using hval⟩
  choose x hx hsel using hchoose
  let σ : ℕ → ℝ := fun i => A (k i)/w (x i)
  have hσ (i : ℕ) : 0 < σ i := div_pos (hApos _) (hw _ (hx i)).1
  have hσeq (i : ℕ) : σ i*w (x i) = A (k i) := div_mul_cancel₀ _ (ne_of_gt (hw _ (hx i)).1)
  refine ⟨k,x,σ,hk,(fun i => ⟨hx i,hσ i⟩),?_,?_,?_⟩
  · intro i
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_lt_iff₀ (hw _ (hx i)).1).mpr
    nlinarith [hsel i]
  · intro i j y hy
    have hh := (hAbounds (k i+j)).2.2 y hy
    have hh' := hh.trans (htail i j)
    change w y*oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤ (b^j)⁻¹*σ i*w (x i)
    simpa only [mul_assoc,hσeq i] using hh'
  · refine weighted_centers_escape q (fun i => (a^(k i))⁻¹) (fun i => infDist (x i) Oᶜ)
      (fun i => A (k i)) (fun i => hr (k i)) (fun _ => infDist_nonneg)
      ?_ c B hc hB (fun i => hlower (k i)) ?_
    · simpa only [inv_pow,Function.comp_def] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
    · intro i
      have hh := hbound (x i) (hx i) _ (hr (k i)).le
      have hh' := mul_le_mul_of_nonneg_left hh (hw _ (hx i)).1.le
      change A (k i) ≤ 2*w (x i)*B
      nlinarith [hsel i,hh']

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma inverse_geometric_near {a s : ℝ} (ha : 1 < a) (l₀ : ℕ) (hs : 0 < s)
    (hsmall : s ≤ (a^l₀)⁻¹) :
    ∃ l : ℕ, l₀ ≤ l ∧ s ≤ (a^l)⁻¹ ∧ (a^l)⁻¹ < a*s := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hsone : s ≤ 1 := hsmall.trans (inv_le_one_of_one_le₀ (one_le_pow₀ ha.le))
  obtain ⟨l,hl₁,hl₂⟩ := exists_nat_pow_near_of_lt_one hs hsone
    (inv_pos.mpr hap) (inv_lt_one_of_one_lt₀ ha)
  have hl₀ : l₀ ≤ l := by
    by_contra hn
    have hle : l+1 ≤ l₀ := by omega
    have hh := pow_le_pow_of_le_one (inv_nonneg.mpr hap.le)
      (inv_lt_one_of_one_lt₀ ha).le hle
    rw [inv_pow,inv_pow] at hh
    rw [inv_pow] at hl₁
    exact (hl₁.trans_le (hsmall.trans hh)).false
  refine ⟨l,hl₀,by simpa only [inv_pow] using hl₂,?_⟩
  have hh := mul_lt_mul_of_pos_right hl₁ hap
  rw [pow_succ,inv_pow] at hh
  simpa only [mul_assoc,inv_mul_cancel₀ hap.ne',mul_one,mul_comm s a] using hh

lemma reciprocal_pow_log {a lam : ℝ} (ha : 1 < a) (hlam : 0 < lam) (l : ℕ) :
    ((a^l)⁻¹) ^ (Real.log lam / Real.log a) = (lam^l)⁻¹ := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hlog : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (inv_pos.mpr (pow_pos hap l)) _)
    (inv_pos.mpr (pow_pos hlam l))
  rw [Real.log_rpow (inv_pos.mpr (pow_pos hap l)),Real.log_inv,Real.log_inv,
    Real.log_pow,Real.log_pow]
  field_simp

lemma abs_sub_le_oscillation {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) : |f x-f y| ≤ oscillation f A := by
  have hx' := mem_rangeInterval hf hA hx
  have hy' := mem_rangeInterval hf hA hy
  change sInf (f '' A) ≤ f x ∧ f x ≤ sSup (f '' A) at hx'
  change sInf (f '' A) ≤ f y ∧ f y ≤ sSup (f '' A) at hy'
  change |f x-f y| ≤ sSup (f '' A)-sInf (f '' A)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma infDist_comparable {X : Type*} [MetricSpace X]
    (O : Set X) {x y : X} (hx : 0 < infDist x Oᶜ)
    (hxy : dist x y ≤ infDist x Oᶜ/2) :
    y ∈ O ∧ infDist x Oᶜ ≤ 2*infDist y Oᶜ := by
  have hy := notMem_of_dist_lt_infDist (s := Oᶜ) (lt_of_le_of_lt hxy (by linarith))
  have hh := infDist_le_infDist_add_dist (x := x) (y := y) (s := Oᶜ)
  exact ⟨by simpa using hy,by linarith⟩

theorem normalized_local_oscillation {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (_hf : Continuous f) (O : Set X) (q : ℕ)
    (x y : X) (r σ t : ℝ) (_hr : 0 ≤ r) (hσ : 0 < σ) (ht : 0 ≤ t)
    (hx : 0 < infDist x Oᶜ) (hxy : dist x y ≤ infDist x Oᶜ/2)
    (hrec : ∀ y ∈ O, infDist y Oᶜ^(q+1)*oscillation f (closedBall y r) ≤
      t*σ*infDist x Oᶜ^(q+1)) :
    oscillation f (closedBall y r)/σ ≤ 2^(q+1)*t := by
  obtain ⟨hy,hδ⟩ := infDist_comparable O hx hxy
  have hδy : 0 < infDist y Oᶜ := by linarith
  have hp := pow_le_pow_left₀ infDist_nonneg hδ (q+1)
  rw [mul_pow] at hp
  have hc := (hrec y hy).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg ht hσ.le))
  apply (div_le_iff₀ hσ).mpr
  have hh : infDist y Oᶜ^(q+1)*oscillation f (closedBall y r) ≤
      infDist y Oᶜ^(q+1)*(2^(q+1)*t*σ) := hc.trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ (pow_pos hδy (q+1))).mp hh

theorem bounded_connected_variation {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (f : X → ℝ) (hf : Continuous f) (P : Set X) (hP : IsCompact P)
    (hconn : IsConnected P) (x : X) (r D σ A : ℝ)
    (hr : 0 < r) (hD : 1 ≤ D) (hDr : D*r ≤ 1) (hσ : 0 < σ) (hA : 0 ≤ A)
    (hball : ∀ y ∈ P, dist x y ≤ D*r)
    (hlocal : ∀ y ∈ P, oscillation f (closedBall y r)/σ ≤ A) :
    oscillation f P/σ ≤ CP*D^q*A := by
  classical
  obtain ⟨T,hTP,hsep,hnet⟩ := CannonNet.exists_finite_separated_net P hP.totallyBounded r hr
  have hoc := connected_oscillation_cover f hf P hP hconn
    (fun i : T => closedBall (i : X) r) (fun _ => isCompact_closedBall _ _)
    (fun i => ⟨i.val,mem_closedBall_self hr.le⟩) (fun y hy => by
      obtain ⟨z,hz,hyz⟩ := hnet y hy
      exact ⟨⟨z,hz⟩,mem_closedBall.mpr hyz⟩)
  have hcard : (Fintype.card T : ℝ) ≤ CP*D^q := by
    have hh := hpack x (D*r) r hr (by nlinarith) hDr T
      (fun y hy => hball y (hTP hy)) hsep
    simpa only [Fintype.card_coe,mul_div_cancel_right₀ D hr.ne'] using hh
  calc
    oscillation f P/σ ≤ (∑ i : T, oscillation f (closedBall (i : X) r))/σ :=
      div_le_div_of_nonneg_right hoc hσ.le
    _ = ∑ i : T, oscillation f (closedBall (i : X) r)/σ := Finset.sum_div _ _ _
    _ ≤ ∑ _i : T, A := Finset.sum_le_sum (fun i _ => hlocal i.val (hTP i.property))
    _ = (Fintype.card T : ℝ)*A := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hA

theorem holder_of_geometric_bounds (a b D C t V : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hD : 0 < D) (hC : 0 ≤ C) (ht : 0 < t)
    (hsmall : D*t ≤ 1)
    (hdiscrete : ∀ j : ℕ, D*t ≤ (a^j)⁻¹ → V ≤ C*(b^j)⁻¹) :
    V ≤ (C*(a*D)^(Real.log b/Real.log a))*t^(Real.log b/Real.log a) := by
  have hα : 0 < Real.log b/Real.log a := div_pos (Real.log_pos hb) (Real.log_pos ha)
  obtain ⟨j,_hj,hj₁,hj₂⟩ := inverse_geometric_near ha 0 (mul_pos hD ht) (by simpa using hsmall)
  have hh := hdiscrete j hj₁
  rw [← reciprocal_pow_log ha (zero_lt_one.trans hb) j] at hh
  apply hh.trans
  have hp := Real.rpow_le_rpow
    (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans ha).le j)) hj₂.le hα.le
  apply (mul_le_mul_of_nonneg_left hp hC).trans_eq
  rw [show a*(D*t) = (a*D)*t by ring,Real.mul_rpow (by positivity) ht.le]
  ring

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma normalized_dist {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (h : X ≃ₜ X) (x : X) (σ : ℝ) (hσ : 0 < σ) (z w : X) :
    dist (normalized f h x σ z) (normalized f h x σ w) =
      |f (h.symm z)-f (h.symm w)|/σ := by
  have hh : normalized f h x σ z-normalized f h x σ w =
      (f (h.symm z)-f (h.symm w))/σ := by unfold normalized; ring
  rw [Real.dist_eq,hh,abs_div,abs_of_pos hσ]

lemma compact_puncture_separation {X : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) (p : ℕ → X) (b : X) (hb : b ∉ K)
    (hp : Tendsto p atTop (𝓝 b)) :
    ∃ e > 0, ∀ᶠ n in atTop, ∀ z ∈ K, e ≤ dist z (p n) := by
  rcases K.eq_empty_or_nonempty with hKe | hKe
  · exact ⟨1,zero_lt_one,Eventually.of_forall (by simp [hKe])⟩
  have hd : 0 < infDist b K := (hK.isClosed.notMem_iff_infDist_pos hKe).mp hb
  refine ⟨infDist b K/2,by positivity,?_⟩
  filter_upwards [hp.eventually (ball_mem_nhds b (half_pos hd))] with n hn z hz
  have hz' := infDist_le_dist_of_mem (x := b) hz
  have ht := dist_triangle b (p n) z
  rw [dist_comm b z] at hz'
  rw [dist_comm b (p n),dist_comm (p n) z,dist_comm b z] at ht
  have hn' := mem_ball.mp hn
  linarith

theorem normalized_bounds_at_scale {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (f : X → ℝ) (hf : Continuous f) (O : Set X)
    (L B D r a b σ : ℝ) (hL : 1 ≤ L) (hB : 1 ≤ B) (_hD : 0 < D)
    (hr : 0 < r) (ha : 1 < a) (hb : 1 < b) (hσ : 0 < σ)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (h : X ≃ₜ X) (x : X) (K : Set X)
    (hx : 0 < infDist x Oᶜ) (hdeep : 2*(L*B)*r ≤ infDist x Oᶜ)
    (hsmall : (L*B)*r ≤ 1)
    (hpre : ∀ z ∈ K, dist x (h.symm z) ≤ B*r)
    (hlip : ∀ z ∈ K, ∀ w ∈ K, dist (h.symm z) (h.symm w) ≤ D*r*dist z w)
    (hrec : ∀ j : ℕ, ∀ y ∈ O,
      infDist y Oᶜ^(q+1)*oscillation f (closedBall y (r*(a^j)⁻¹)) ≤
        (b^j)⁻¹*σ*infDist x Oᶜ^(q+1)) :
    (∀ z ∈ K, |normalized f h x σ z| ≤ CP*(L*B)^q*2^(q+1)) ∧
    (∀ z ∈ K, ∀ w ∈ K, ∀ j : ℕ, D*dist z w ≤ (a^j)⁻¹ →
      dist (normalized f h x σ z) (normalized f h x σ w) ≤ 2^(q+1)*(b^j)⁻¹) := by
  have hR : 1 ≤ L*B := one_le_mul_of_one_le_of_one_le hL hB
  have hBr : 0 < B*r := mul_pos (zero_lt_one.trans_le hB) hr
  have hBR : B*r ≤ (L*B)*r := by nlinarith
  have hcenter (y : X) (hy : dist x y ≤ (L*B)*r) : dist x y ≤ infDist x Oᶜ/2 := by linarith
  have hlocal (j : ℕ) (y : X) (hy : dist x y ≤ (L*B)*r) :
      oscillation f (closedBall y (r*(a^j)⁻¹))/σ ≤ 2^(q+1)*(b^j)⁻¹ :=
    normalized_local_oscillation f hf O q x y _ σ _
      (mul_nonneg hr.le (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans ha).le j))) hσ
      (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hb).le j)) hx (hcenter y hy) (hrec j)
  constructor
  · intro z hz
    obtain ⟨γ,hγ⟩ := hpaths x x (h.symm z) (B*r) hBr (by simp; exact hBr.le) (hpre z hz)
    have hP : IsCompact (range γ) := isCompact_range γ.continuous
    have hconn : IsConnected (range γ) := isConnected_range γ.continuous
    have hh := bounded_connected_variation q CP hpack f hf (range γ) hP hconn x r (L*B) σ (2^(q+1))
      hr hR hsmall hσ (by positivity) (by
        rintro y ⟨t,rfl⟩
        exact (hγ t).le.trans_eq (by ring)) (by
        rintro y ⟨t,rfl⟩
        simpa only [pow_zero,inv_one,mul_one] using hlocal 0 (γ t) ((hγ t).le.trans_eq (by ring)))
    have hvar := abs_sub_le_oscillation f hf (range γ) hP
      (show h.symm z ∈ range γ from ⟨1,γ.target⟩) (show x ∈ range γ from ⟨0,γ.source⟩)
    unfold normalized
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_div_of_nonneg_right hvar hσ.le).trans hh
  · intro z hz w hw j hj
    have hd : dist (h.symm w) (h.symm z) ≤ r*(a^j)⁻¹ := by
      rw [dist_comm]
      calc
        dist (h.symm z) (h.symm w) ≤ D*r*dist z w := hlip z hz w hw
        _ ≤ r*(a^j)⁻¹ := by nlinarith [mul_le_mul_of_nonneg_left hj hr.le]
    have hc := hlocal j (h.symm z) ((hpre z hz).trans hBR)
    have hvar := abs_sub_le_oscillation f hf (closedBall (h.symm z) (r*(a^j)⁻¹))
      (isCompact_closedBall _ _) (mem_closedBall_self (by positivity)) (mem_closedBall.mpr hd)
    rw [normalized_dist f h x σ hσ]
    exact (div_le_div_of_nonneg_right hvar hσ.le).trans hc

theorem global_holder_of_discrete {X : Type*} [MetricSpace X]
    (F : X → ℝ) (K : Set X) (a b D M C : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hD : 0 < D) (_hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ K, |F z| ≤ M)
    (hdiscrete : ∀ z ∈ K, ∀ w ∈ K, ∀ j : ℕ, D*dist z w ≤ (a^j)⁻¹ →
      dist (F z) (F w) ≤ C*(b^j)⁻¹) :
    ∀ z ∈ K, ∀ w ∈ K,
      dist (F z) (F w) ≤
        max (C*(a*D)^(Real.log b/Real.log a)) (2*M*D^(Real.log b/Real.log a)) *
          (dist z w)^(Real.log b/Real.log a) := by
  intro z hz w hw
  let α := Real.log b/Real.log a
  have hα : 0 < α := div_pos (Real.log_pos hb) (Real.log_pos ha)
  by_cases heq : z = w
  · subst w
    have hαne : Real.log b/Real.log a ≠ 0 := hα.ne'
    simp only [dist_self,Real.zero_rpow hαne,mul_zero,le_refl]
  have ht : 0 < dist z w := dist_pos.mpr heq
  by_cases hsmall : D*dist z w ≤ 1
  · exact (holder_of_geometric_bounds a b D C (dist z w) (dist (F z) (F w))
      ha hb hD hC ht hsmall (hdiscrete z hz w hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  · have hp : 1 ≤ D^α*(dist z w)^α := by
      rw [← Real.mul_rpow hD.le ht.le]
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1)
        (le_of_not_ge hsmall) hα.le
    have hdist : dist (F z) (F w) ≤ 2*M := by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hbound z hz,hbound w hw])
    calc
      dist (F z) (F w) ≤ 2*M := hdist
      _ ≤ (2*M*D^α)*(dist z w)^α := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

theorem expansion_record_tails {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (Lp a b CE LE d : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hb : 1 < b)
    (hCE : 0 ≤ CE) (hLE : 0 < LE) (hd : 0 < d)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (k : ℕ → ℕ) (hk : StrictMono k) (x : ℕ → X) (σ : ℕ → ℝ)
    (hx : ∀ i, x i ∈ O) (hσ : ∀ i, 0 < σ i)
    (h : ℕ → X ≃ₜ X) (z₀ pLim : X)
    (hsep : ∀ i, d ≤ dist (x i) z₀)
    (hexp : ∀ i, Expansion (h i) (x i) ((a^(k i))⁻¹) CE LE)
    (hp : Tendsto (fun i => h i z₀) atTop (𝓝 pLim))
    (hescape : Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop)
    (hrec : ∀ i j y, y ∈ O →
      infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
        (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) :
    ∀ K : Set X, IsCompact K → pLim ∉ K → ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
      ∀ᶠ i in atTop,
        (∀ z ∈ K, (h i).symm z ∈ O) ∧
        (∀ z ∈ K, |normalized f (h i) (x i) (σ i) z| ≤ M) ∧
        (∀ z ∈ K, ∀ w ∈ K,
          dist (normalized f (h i) (x i) (σ i) z) (normalized f (h i) (x i) (σ i) w) ≤
            H*(dist z w)^(Real.log b/Real.log a)) := by
  intro K hK hKp
  obtain ⟨e,he,hep⟩ := compact_puncture_separation K hK (fun i => h i z₀) pLim hKp hp
  let B := max 1 (CE/(e*d))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let R := Lp*B
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hLp hB
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hBR : B ≤ R := by dsimp [R]; nlinarith
  let D := LE*B^2
  have hD : 0 < D := mul_pos hLE (pow_pos hB0 2)
  let M := CP*R^q*2^(q+1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let H := max (2^(q+1)*(a*D)^(Real.log b/Real.log a))
    (2*M*D^(Real.log b/Real.log a))
  have hH : 0 ≤ H := (show 0 ≤ 2^(q+1)*(a*D)^(Real.log b/Real.log a) by positivity).trans
    (le_max_left _ _)
  have hr (i : ℕ) : 0 < (a^(k i))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hrt : Tendsto (fun i => (a^(k i))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hsmall : ∀ᶠ i in atTop, R*(a^(k i))⁻¹ ≤ 1 := by
    have ht : Tendsto (fun i => R*(a^(k i))⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrt.const_mul R
    exact (ht.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hn => hn.le)
  refine ⟨M,H,hM,hH,?_⟩
  filter_upwards [hep,hsmall,hescape.eventually (eventually_ge_atTop (2*R))] with i hi hsmall hdeep
  have hδx : 0 < infDist (x i) Oᶜ :=
    (hO.isClosed_compl.notMem_iff_infDist_pos hOc).mp (by simpa using hx i)
  have hdeep' : 2*R*(a^(k i))⁻¹ ≤ infDist (x i) Oᶜ := (le_div_iff₀ (hr i)).mp hdeep
  have hpre (z : X) (hz : z ∈ K) : dist (x i) ((h i).symm z) ≤ B*(a^(k i))⁻¹ := by
    exact (preimage_distance_bound (h i) (x i) z₀ z _ CE LE e d (hr i) hCE he hd
      (hexp i) hdiam (hsep i) (hi z hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hr i).le)
  have hlip (z : X) (hz : z ∈ K) (w : X) (hw : w ∈ K) :
      dist ((h i).symm z) ((h i).symm w) ≤ D*(a^(k i))⁻¹*dist z w := by
    have hh := inverse_lipschitz_on_preimages (h i) (x i) z w _ CE LE B (hr i) hLE.le
      (hexp i) (hpre z hz) (hpre w hw)
    simpa only [max_eq_right hB] using hh
  have hrec' (j : ℕ) (y : X) (hy : y ∈ O) :
      infDist y Oᶜ^(q+1)*oscillation f (closedBall y ((a^(k i))⁻¹*(a^j)⁻¹)) ≤
        (b^j)⁻¹*σ i*infDist (x i) Oᶜ^(q+1) := by
    simpa only [pow_add,mul_inv_rev,mul_comm] using hrec i j y hy
  obtain ⟨hbound,hdiscrete⟩ := normalized_bounds_at_scale q CP hpack f hf O
    Lp B D ((a^(k i))⁻¹) a b (σ i) hLp hB hD (hr i) ha hb (hσ i)
    hpaths (h i) (x i) K hδx hdeep' hsmall hpre hlip hrec'
  refine ⟨fun z hz => ?_,hbound,?_⟩
  · exact (infDist_comparable O hδx (by
      have hh := hpre z hz
      have hh' := mul_le_mul_of_nonneg_right hBR (hr i).le
      linarith)).1
  · exact global_holder_of_discrete (normalized f (h i) (x i) (σ i)) K
      a b D M (2^(q+1)) ha hb hD hM (by positivity) hbound hdiscrete

end CannonMagnification

open Set Filter Topology Metric

end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_Domain
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
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric

namespace CannonMagnification

lemma all_bound_of_eventual (v : ℕ → ℝ) (B : ℝ)
    (h : ∀ᶠ n in atTop, |v n| ≤ B) : ∃ D ≥ 0, ∀ n, |v n| ≤ D := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨C,hC⟩ := ((Finset.range N).finite_toSet.image (fun n => |v n|)).bddAbove
  refine ⟨max 0 (max C B),le_max_left _ _,fun n => ?_⟩
  by_cases hn : n < N
  · exact (hC (mem_image_of_mem _ (by simpa using hn))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hN n (le_of_not_gt hn)).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma equicontinuous_of_eventual_holder {X : Type*} [MetricSpace X]
    [LocallyCompactSpace X] (f : ℕ → C(X,ℝ)) (α : ℝ) (hα : 0 < α)
    (hlocal : ∀ K : Set X, IsCompact K → ∃ C ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ C*(dist x y)^α) :
    Equicontinuous (fun n x => f n x) := by
  intro x
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  obtain ⟨K,hK,hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨C,_hC,hC⟩ := hlocal K hK
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  have hfinite : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N, dist (f n x) (f n y) < ε := by
    apply (eventually_all_finset _).mpr
    intro n _hn
    simpa only [Metric.mem_ball,dist_comm] using
      (f n).continuous.continuousAt.eventually (ball_mem_nhds (f n x) hε)
  have ht : Tendsto (fun y => C*(dist x y)^α) (𝓝 x) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const hα.le).comp ((continuous_const : Continuous (fun _ : X => x)).dist continuous_id)
    have ht' : Tendsto (fun y => C*(dist x y)^α) (𝓝 x) (𝓝 (C*(dist x x)^α)) :=
      (hc.const_mul C).tendsto x
    simpa only [dist_self,Real.zero_rpow (ne_of_gt hα),mul_zero] using ht'
  filter_upwards [hfinite,hKx,ht.eventually (gt_mem_nhds hε)] with y hfin hy hnear n
  by_cases hn : n < N
  · exact hfin n (by simpa using hn)
  · exact (hN n (le_of_not_gt hn) x (mem_of_mem_nhds hKx) y hy).trans_lt hnear

theorem locally_bounded_holder_subsequence {X : Type*} [MetricSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X]
    (f : ℕ → C(X,ℝ)) (α : ℝ) (hα : 0 < α)
    (hlocal : ∀ K : Set X, IsCompact K → ∃ C ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ C*(dist x y)^α)
    (hb : ∀ x, ∃ B, ∀ᶠ n in atTop, |f n x| ≤ B) :
    ∃ F : C(X,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 F) ∧
      ∀ K : Set X, IsCompact K → ∃ C ≥ 0,
        ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ C*(dist x y)^α := by
  classical
  have heq := equicontinuous_of_eventual_holder f α hα hlocal
  have hball (x : X) : ∃ B ≥ 0, ∀ n, |f n x| ≤ B := by
    obtain ⟨B,hB⟩ := hb x
    exact all_bound_of_eventual (fun n => f n x) B hB
  have : T2Space (UniformOnFun X ℝ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X,ℝ) => (g : X → ℝ)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have hindex : ∀ g : range f, ∃ n, f n = g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range f => (g.val : X → ℝ)) := by
        convert heq' using 1
        all_goals try with_reducible_and_instances rfl
        funext g x
        exact congrArg (fun h : C(X,ℝ) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _hK x _hx
      obtain ⟨B,_hB,hB⟩ := hball x
      refine ⟨Icc (-B) B,isCompact_Icc,?_⟩
      rintro g ⟨n,rfl⟩
      exact abs_le.mp (hB n)
  obtain ⟨F,_hF,φ,hφ,ht⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨F,φ,hφ,ht,fun K hK => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hlocal K hK
  refine ⟨C,hC,fun x hx y hy => ?_⟩
  apply le_of_tendsto (((continuous_eval_const x).tendsto F |>.comp ht).dist
    ((continuous_eval_const y).tendsto F |>.comp ht))
  exact (hφ.tendsto_atTop.eventually hbound).mono (fun n hn => hn x hx y hy)

end CannonMagnification

namespace CannonMagnification

open Set Metric Filter Topology

theorem punctured_nonconstant_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : ℕ → C(X,ℝ)) (p : X) (α : ℝ) (hα : 0 < α)
    (htails : ∀ K : Set X, IsCompact K → p ∉ K → ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
      ∀ᶠ n in atTop, (∀ x ∈ K, |f n x| ≤ M) ∧
        (∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ H*(dist x y)^α))
    (e v : ℝ) (he : 0 < e) (hv : 0 < v)
    (hvariation : ∀ᶠ n in atTop, ∃ x y : X, e ≤ dist x p ∧ e ≤ dist y p ∧
      v ≤ dist (f n x) (f n y)) :
    ∃ F : C(({p}ᶜ : Set X),ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n : ℕ => (f (φ n)).comp ⟨Subtype.val,continuous_subtype_val⟩) atTop (𝓝 F) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ H*(dist x y)^α) ∧
      (∃ x y, F x ≠ F y) := by
  classical
  let Y := ({p}ᶜ : Set X)
  let : LocallyCompactSpace Y := isClosed_singleton.isOpen_compl.locallyCompactSpace
  let g : ℕ → C(Y,ℝ) := fun n => (f n).comp ⟨Subtype.val,continuous_subtype_val⟩
  have hlocal (K : Set Y) (hK : IsCompact K) : ∃ H ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (g n x) (g n y) ≤ H*(dist x y)^α := by
    have hKn : p ∉ Subtype.val '' K := by
      rintro ⟨x,_hx,hx⟩
      exact x.property (by simpa only [mem_singleton_iff] using hx)
    obtain ⟨M,H,_hM,hH,h⟩ := htails _ (hK.image continuous_subtype_val) hKn
    refine ⟨H,hH,h.mono (fun n hn x hx y hy => ?_)⟩
    exact hn.2 x (mem_image_of_mem _ hx) y (mem_image_of_mem _ hy)
  have hb (x : Y) : ∃ M, ∀ᶠ n in atTop, |g n x| ≤ M := by
    have hxn : p ∉ ({x.val} : Set X) := by simpa only [mem_singleton_iff] using Ne.symm (show x.val ≠ p from x.property)
    obtain ⟨M,H,_hM,_hH,h⟩ := htails _ isCompact_singleton hxn
    exact ⟨M,h.mono (fun n hn => hn.1 _ (mem_singleton _))⟩
  obtain ⟨F,φ,hφ,ht,hholder⟩ := locally_bounded_holder_subsequence g α hα hlocal hb
  refine ⟨F,φ,hφ,ht,hholder,?_⟩
  by_contra hnc
  push Not at hnc
  let K : Set X := {x | e ≤ dist x p}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hKY : K ⊆ Y := by
    intro x hx
    change x ≠ p
    intro hxp
    have hh : e ≤ dist x p := hx
    rw [hxp,dist_self] at hh
    exact (not_le_of_gt he) hh
  let L : Set Y := Subtype.val ⁻¹' K
  have hL : IsCompact L := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' L = K := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩; exact hz
      · intro hx; exact ⟨⟨x,hKY hx⟩,hx,rfl⟩
    rwa [heq]
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht L hL
  have hclose := Metric.tendstoUniformlyOn_iff.mp hu (v/3) (by positivity)
  obtain ⟨n,hn,hv'⟩ := (hclose.and (hφ.tendsto_atTop.eventually hvariation)).exists
  obtain ⟨x,y,hx,hy,hxy⟩ := hv'
  let x' : Y := ⟨x,hKY hx⟩
  let y' : Y := ⟨y,hKY hy⟩
  have hxx := hn x' hx
  have hyy := hn y' hy
  have hdist := dist_triangle (g (φ n) x') (F x') (g (φ n) y')
  rw [hnc x' y'] at hdist
  have hg : dist (f (φ n) x) (f (φ n) y) < 2*(v/3) := by
    change dist (g (φ n) x') (g (φ n) y') < _
    have heq : dist (g (φ n) x') (F y') = dist (F x') (g (φ n) x') := by rw [hnc x' y',dist_comm]
    rw [heq] at hdist
    simp only [Function.comp_apply] at hxx hyy
    linarith
  linarith

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma oscillation_attained {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ u ∈ A, ∃ v ∈ A, |f u-f v| = oscillation f A := by
  obtain ⟨u,hu,hfu⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨v,hv,hfv⟩ := (hA.image hf).sInf_mem (hne.image f)
  refine ⟨u,hu,v,hv,?_⟩
  rw [hfu,hfv]
  exact abs_of_nonneg (oscillation_nonneg hf hA hne)

theorem expansion_record_limit {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (Lp a b CE LE d : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hb : 1 < b)
    (hCE : 0 ≤ CE) (hLE : 0 < LE) (hd : 0 < d)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (k : ℕ → ℕ) (hk : StrictMono k) (x : ℕ → X) (σ : ℕ → ℝ)
    (hx : ∀ i, x i ∈ O) (hσ : ∀ i, 0 < σ i)
    (h : ℕ → X ≃ₜ X) (z₀ pLim : X)
    (hsep : ∀ i, d ≤ dist (x i) z₀)
    (hexp : ∀ i, Expansion (h i) (x i) ((a^(k i))⁻¹) CE LE)
    (hp : Tendsto (fun i => h i z₀) atTop (𝓝 pLim))
    (hescape : Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop)
    (hrec : ∀ i j y, y ∈ O →
      infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
        (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1))
    (hvar : ∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) :
    ∃ F : C(({pLim}ᶜ : Set X),ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n : ℕ => (⟨normalized f (h (φ n)) (x (φ n)) (σ (φ n)),
        continuous_normalized f hf _ _ _⟩ : C(X,ℝ)).comp ⟨Subtype.val,continuous_subtype_val⟩)
          atTop (𝓝 F) ∧
      (∀ K : Set ({pLim}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  let fn : ℕ → C(X,ℝ) := fun i => ⟨normalized f (h i) (x i) (σ i),continuous_normalized f hf _ _ _⟩
  have ht := expansion_record_tails q CP hCP hpack hdiam f hf O hO hOc Lp a b CE LE d
    hLp ha hb hCE hLE hd hpaths k hk x σ hx hσ h z₀ pLim hsep hexp hp hescape hrec
  let e := d/(4*LE)
  have he : 0 < e := div_pos hd (by positivity)
  have hrt : Tendsto (fun i => (a^(k i))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hvariation : ∀ᶠ i in atTop, ∃ z w : X, e ≤ dist z pLim ∧ e ≤ dist w pLim ∧
      (1:ℝ)/2 ≤ dist (fn i z) (fn i w) := by
    filter_upwards [hrt.eventually (gt_mem_nhds (half_pos hd)),hp.eventually (ball_mem_nhds pLim he)] with i hi hpi
    have hr : 0 < (a^(k i))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
    have hball : (closedBall (x i) ((a^(k i))⁻¹)).Nonempty := ⟨x i,mem_closedBall_self hr.le⟩
    obtain ⟨u,hu,v,hv,huv⟩ := oscillation_attained f hf _ (isCompact_closedBall _ _) hball
    have haway (y : X) (hy : y ∈ closedBall (x i) ((a^(k i))⁻¹)) : e ≤ dist (h i y) pLim := by
      have hh := image_ball_avoids_puncture (h i) (x i) z₀ y _ CE LE d hr hLE hd hi.le
        (hexp i) hdiam (hsep i) (by simpa only [mem_closedBall,dist_comm] using hy)
      have htri := dist_triangle (h i y) pLim (h i z₀)
      have hnear : dist pLim (h i z₀) < e := by simpa only [mem_ball,dist_comm] using hpi
      have hfract : d/(2*LE) = 2*e := by dsimp [e]; ring
      rw [hfract] at hh
      linarith
    refine ⟨h i u,h i v,haway u hu,haway v hv,?_⟩
    change (1:ℝ)/2 ≤ dist (normalized f (h i) (x i) (σ i) (h i u))
      (normalized f (h i) (x i) (σ i) (h i v))
    rw [normalized_dist f (h i) (x i) (σ i) (hσ i), (h i).symm_apply_apply,(h i).symm_apply_apply,huv]
    apply (le_div_iff₀ (hσ i)).mpr
    linarith [hvar i]
  apply punctured_nonconstant_subsequence fn pLim _ (div_pos (Real.log_pos hb) (Real.log_pos ha))
    (fun K hK hKp => ?_) e (1/2) he (by norm_num) hvariation
  obtain ⟨M,H,hM,hH,hest⟩ := ht K hK hKp
  exact ⟨M,H,hM,hH,hest.mono (fun _ hn => hn.2)⟩

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma continuous_oscillation_bound {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) : ∃ B ≥ 0, ∀ A : Set X, IsCompact A → A.Nonempty →
      oscillation f A ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_univ.image hf.abs).bddAbove
  refine ⟨2*max B 0,by positivity,fun A hA hne => ?_⟩
  apply oscillation_le_of_pairwise f hf A hA hne
  intro x hx y hy
  have hx' : |f x| ≤ max B 0 := (hB (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)
  have hy' : |f y| ≤ max B 0 := (hB (mem_image_of_mem _ (mem_univ y))).trans (le_max_left _ _)
  exact (le_abs_self _).trans ((abs_sub _ _).trans (by linarith))

lemma upper_geometric_of_eventual (A : ℕ → ℝ) (β C : ℝ) (hβ : 0 < β)
    (hA : ∀ᶠ n in atTop, A n ≤ C*β^n) : ∃ D ≥ 0, ∀ n, A n ≤ D*β^n := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hA
  obtain ⟨B,hB⟩ := ((Finset.range N).finite_toSet.image (fun n => A n/β^n)).bddAbove
  refine ⟨max 0 (max B C),le_max_left _ _,fun n => ?_⟩
  by_cases hn : n < N
  · apply (div_le_iff₀ (pow_pos hβ n)).mp
    exact (hB (mem_image_of_mem _ (by simpa using hn))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hN n (le_of_not_gt hn)).trans
      (mul_le_mul_of_nonneg_right ((le_max_right B C).trans (le_max_right _ _)) (pow_pos hβ n).le)

theorem holder_weighted_records {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O P : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O)
    (hvary : 0 < oscillation f P)
    (a α s C : ℝ) (ha : 1 < a) (hα : 0 < α) (hs : 0 < s) (hC : 0 ≤ C)
    (hholder : ∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
      |f y-f z| ≤ C*(dist y z)^α) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ), StrictMono k ∧
      (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      (∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) ∧
      (∀ i j y, y ∈ O →
        infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
          (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop := by
  let w := fun x => infDist x Oᶜ ^ (q+1)
  let A := fun n : ℕ => weightedOscillation f w O ((a^n)⁻¹)
  let β := (a⁻¹)^α
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hβ : 0 < β := Real.rpow_pos_of_pos (inv_pos.mpr ha0) _
  have hβ1 : β < 1 := Real.rpow_lt_one (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha) hα
  have hβi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
  obtain ⟨b,hb,hbi⟩ := exists_between hβi
  have hβb : β*b < 1 := by
    have hh := (lt_div_iff₀ hβ).mp (show b < 1/β by simpa only [one_div] using hbi)
    nlinarith
  obtain ⟨B,hB,hBbound⟩ := continuous_oscillation_bound f hf
  have hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B := by
    intro x _hx r hr
    exact hBbound _ (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩
  have hw (x : X) (hx : x ∈ O) : w x ∈ Icc (0:ℝ) 1 :=
    ⟨(infDist_compl_weight O hO hOc hdiam q x hx).1.le,(infDist_compl_weight O hO hOc hdiam q x hx).2⟩
  obtain ⟨η,hη,hwP⟩ := infDist_compl_compact_lower O P hO hOc hP hPcon.1 hPO q
  have hlower : ∀ n : ℕ, (η*oscillation f P/(max CP 1))*((a^n)⁻¹)^q ≤ A n := by
    intro n
    apply weightedOscillation_lower q CP hpack hdiam f w hf O P hP hPcon hPO hw
      _ hvary le_rfl η hη hwP B hB hbound _ (inv_pos.mpr (pow_pos ha0 _))
    exact inv_le_one_of_one_le₀ (one_le_pow₀ ha.le)
  have hrt : Tendsto (fun n : ℕ => (a^n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha)
  have hupper : ∀ᶠ n in atTop, A n ≤ (C*2^α)*β^n := by
    filter_upwards [hrt.eventually (gt_mem_nhds hs)] with n hn
    have hr : 0 < (a^n)⁻¹ := inv_pos.mpr (pow_pos ha0 _)
    have hosc (x : X) (hx : x ∈ O) : oscillation f (closedBall x ((a^n)⁻¹)) ≤ C*(2*(a^n)⁻¹)^α := by
      apply oscillation_le_of_pairwise f hf _ (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr.le⟩
      intro y hy z hz
      have hy' : y ∈ closedBall x s := closedBall_subset_closedBall hn.le hy
      have hz' : z ∈ closedBall x s := closedBall_subset_closedBall hn.le hz
      have hdist : dist y z ≤ 2*(a^n)⁻¹ := by
        have ht := dist_triangle y x z
        have hy'' := mem_closedBall.mp hy
        have hz'' := mem_closedBall.mp hz
        rw [dist_comm x z] at ht
        linarith
      exact (le_abs_self _).trans ((hholder x hx y hy' z hz').trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hdist hα.le) hC))
    have hA := (weightedOscillation_bounds f w hf O (hPcon.1.mono hPO) hw _ hr.le
      (C*(2*(a^n)⁻¹)^α) (by positivity) hosc).2.1
    have heq : (C*2^α)*β^n = C*(2*(a^n)⁻¹)^α := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr.le,← inv_pow]
      rw [← Real.rpow_pow_comm (inv_pos.mpr ha0).le]
      dsimp [β]
      ring
    exact hA.trans_eq heq.symm
  obtain ⟨D,hD,hDupper⟩ := upper_geometric_of_eventual A β (C*2^α) hβ hupper
  refine ⟨b,hb,?_⟩
  exact select_weighted_magnifications f hf O hO (hPcon.1.mono hPO) hOc hdiam q a ha β b
    hβ hb hβb (η*oscillation f P/(max CP 1)) D B (by positivity) hD hB hbound hlower hDupper

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

theorem holder_magnification_global {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O P : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O) (hvary : 0 < oscillation f P)
    (Lp a CE LE : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hCE : 0 ≤ CE) (hLE : 0 < LE)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (expand : X → ℕ → X ≃ₜ X)
    (hexpand : ∀ x k, Expansion (expand x k) x ((a^k)⁻¹) CE LE)
    (α s C : ℝ) (hα : 0 < α) (hs : 0 < s) (hC : 0 ≤ C)
    (hholder : ∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
      |f y-f z| ≤ C*(dist y z)^α)
    (z₀ : X) (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ O, d ≤ dist x z₀) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ) (p : X)
      (F : C(({p}ᶜ : Set X),ℝ)), StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => expand (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set X, IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (expand (x i) (k i)).symm z ∈ O) ∧
      Tendsto (fun i : ℕ => (⟨normalized f (expand (x i) (k i)) (x i) (σ i),
        continuous_normalized f hf _ _ _⟩ : C(X,ℝ)).comp ⟨Subtype.val,continuous_subtype_val⟩)
          atTop (𝓝 F) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  obtain ⟨b,hb,k,x,σ,hk,hx,hvar,hrec,hescape⟩ := holder_weighted_records q CP hpack hdiam
    f hf O P hO hOc hP hPcon hPO hvary a α s C ha hα hs hC hholder
  obtain ⟨p,_hp,ψ,hψ,hpt⟩ := (isCompact_univ : IsCompact (univ : Set X)).tendsto_subseq
    (fun i => mem_univ (expand (x i) (k i) z₀))
  let k' := k ∘ ψ
  let x' := x ∘ ψ
  let σ' := σ ∘ ψ
  let h' := fun i => expand (x' i) (k' i)
  have hhproj : ∀ i, Expansion (h' i) (x' i) ((a^(k' i))⁻¹) CE LE := fun i => hexpand _ _
  obtain ⟨F,φ,hφ,ht,hFholder,hFvar⟩ := expansion_record_limit q CP hCP hpack hdiam f hf O hO hOc
    Lp a b CE LE d hLp ha hb hCE hLE hd hpaths k' (hk.comp hψ) x' σ'
    (fun i => (hx (ψ i)).1) (fun i => (hx (ψ i)).2) h' z₀ p
    (fun i => hsep _ (hx (ψ i)).1) hhproj hpt (hescape.comp hψ.tendsto_atTop)
    (fun i j y hy => hrec (ψ i) j y hy) (fun i => hvar (ψ i))
  refine ⟨b,hb,k' ∘ φ,x' ∘ φ,σ' ∘ φ,p,F,(hk.comp hψ).comp hφ,
    (fun i => hx (ψ (φ i))),hpt.comp hφ.tendsto_atTop,
    (hescape.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop,?_,ht,hFholder,hFvar⟩
  intro K hK hKp
  obtain ⟨M,H,_hM,_hH,hest⟩ := expansion_record_tails q CP hCP hpack hdiam f hf O hO hOc
    Lp a b CE LE d hLp ha hb hCE hLE hd hpaths k' (hk.comp hψ) x' σ'
    (fun i => (hx (ψ i)).1) (fun i => (hx (ψ i)).2) h' z₀ p
    (fun i => hsep _ (hx (ψ i)).1) hhproj hpt (hescape.comp hψ.tendsto_atTop)
    (fun i j y hy => hrec (ψ i) j y hy) K hK hKp
  exact (hφ.tendsto_atTop.eventually hest).mono (fun _ hn => hn.1)

end CannonMagnification

open Set Metric Topology

namespace CannonMagnification

theorem local_holder_extension {X : Type*} [MetricSpace X] [CompactSpace X]
    (Ω O : Set X) (hΩ : IsOpen Ω) (hOΩ : closure O ⊆ Ω)
    (f : C(Ω,ℝ)) (α : ℝ)
    (hholder : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) :
    ∃ g : C(X,ℝ), ∃ s C : ℝ, 0 < s ∧ 0 ≤ C ∧
      (∀ x ∈ O, ∀ hx : x ∈ Ω, g x = f ⟨x,hx⟩) ∧
      (∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
        |g y-g z| ≤ C*(dist y z)^α) := by
  obtain ⟨s,hs,hsΩ⟩ := isClosed_closure.isCompact.exists_cthickening_subset_open hΩ hOΩ
  let K := cthickening s (closure O)
  have hK : IsClosed K := isClosed_cthickening
  let fK : C(K,ℝ) := f.comp ⟨fun x => ⟨x.val,hsΩ x.property⟩,continuous_subtype_val.subtype_mk _⟩
  obtain ⟨g,hg⟩ := fK.exists_extension' hK.isClosedEmbedding_subtypeVal
  have hagree (x : X) (hx : x ∈ K) : g x = f ⟨x,hsΩ hx⟩ := by
    exact congrFun hg ⟨x,hx⟩
  obtain ⟨C,hC,hH⟩ := hholder K hK.isCompact hsΩ
  refine ⟨g,s,C,hs,hC,?_,?_⟩
  · intro x hx hxΩ
    have hxK : x ∈ K := self_subset_cthickening _ (subset_closure hx)
    exact hagree x hxK
  · intro x hx y hy z hz
    have hyK : y ∈ K := closedBall_subset_cthickening (subset_closure hx) s hy
    have hzK : z ∈ K := closedBall_subset_cthickening (subset_closure hx) s hz
    rw [hagree y hyK,hagree z hzK]
    exact hH ⟨y,hsΩ hyK⟩ ⟨z,hsΩ hzK⟩ hyK hzK

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma onDomain_eq {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (f : C(Ω,ℝ)) (x : X) (hx : x ∈ Ω) : onDomain f x = f ⟨x,hx⟩ := by simp only [onDomain,dite_eq_left hx]

theorem local_holder_magnification {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (Ω O P : Set X) (hΩ : IsOpen Ω) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hOΩ : closure O ⊆ Ω) (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O)
    (f : C(Ω,ℝ)) (hvary : ∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v)
    (Lp a CE LE : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hCE : 0 ≤ CE) (hLE : 0 < LE)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (expand : X → ℕ → X ≃ₜ X)
    (hexpand : ∀ x k, Expansion (expand x k) x ((a^k)⁻¹) CE LE)
    (α : ℝ) (hα : 0 < α)
    (hholder : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α)
    (z₀ : X) (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ O, d ≤ dist x z₀) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ) (p : X)
      (F : C(({p}ᶜ : Set X),ℝ)), StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => expand (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set X, IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (expand (x i) (k i)).symm z ∈ Ω) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K →
        TendstoUniformlyOn (fun i z => normalized (onDomain f) (expand (x i) (k i))
          (x i) (σ i) z.val) F atTop K) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  obtain ⟨g,s,C,hs,hC,hagree,hH⟩ := local_holder_extension Ω O hΩ hOΩ f α hholder
  have hOΩ' : O ⊆ Ω := subset_closure.trans hOΩ
  have hgeq (x : X) (hx : x ∈ O) : g x = onDomain f x := by
    rw [onDomain_eq f x (hOΩ' hx)]
    exact hagree x hx (hOΩ' hx)
  have hgvar : 0 < oscillation g P := by
    obtain ⟨u,hu,v,hv,huv⟩ := hvary
    have hne : g u ≠ g v := by simpa only [hgeq u (hPO hu),hgeq v (hPO hv)] using huv
    exact (abs_pos.mpr (sub_ne_zero.mpr hne)).trans_le (abs_sub_le_oscillation g g.continuous P hP hu hv)
  obtain ⟨b,hb,k,x,σ,p,F,hk,hx,hp,he,hpre,ht,hF,hvar⟩ := holder_magnification_global
    q CP hCP hpack hdiam g g.continuous O P hO hOc hP hPcon hPO hgvar
    Lp a CE LE hLp ha hCE hLE hpaths expand hexpand α s C hα hs hC hH z₀ d hd hsep
  refine ⟨b,hb,k,x,σ,p,F,hk,hx,hp,he,?_,?_,hF,hvar⟩
  · intro K hK hKp
    exact (hpre K hK hKp).mono (fun i hi z hz => hOΩ' (hi z hz))
  · intro K hK
    have hKp : p ∉ Subtype.val '' K := by
      rintro ⟨z,_hz,hz⟩
      exact z.property (by simpa only [mem_singleton_iff] using hz)
    have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht K hK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε,
      hpre (Subtype.val '' K) (hK.image continuous_subtype_val) hKp] with i hi hpi z hz
    have heq : normalized (onDomain f) (expand (x i) (k i)) (x i) (σ i) z.val =
        normalized g (expand (x i) (k i)) (x i) (σ i) z.val := by
      unfold normalized
      rw [hgeq _ (hpi _ (mem_image_of_mem _ hz)),hgeq _ (hx i).1]
    rw [heq]
    exact hi z hz

end CannonMagnification

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_holder_magnification (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∀ (Ω O P : Set (Boundary D)), IsOpen Ω → IsOpen O → Oᶜ.Nonempty →
    closure O ⊆ Ω → IsCompact P → IsConnected P → P ⊆ O →
    ∀ f : C(Ω,ℝ), (∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v) →
    ∀ α : ℝ, 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) →
    ∀ (z₀ : Boundary D) (d : ℝ), 0 < d → (∀ x ∈ O, d ≤ dist x z₀) →
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → Boundary D) (σ : ℕ → ℝ) (p : Boundary D)
      (F : C(({p}ᶜ : Set (Boundary D)),ℝ)),
      StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => boundaryExpansion D hδ (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((Real.exp (2*visualExponent δ)^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set (Boundary D), IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (boundaryExpansion D hδ (x i) (k i)).symm z ∈ Ω) ∧
      (∀ K : Set ({p}ᶜ : Set (Boundary D)), IsCompact K →
        TendstoUniformlyOn (fun i z => normalized (onDomain f) (boundaryExpansion D hδ (x i) (k i))
          (x i) (σ i) z.val) F atTop K) ∧
      (∀ K : Set ({p}ᶜ : Set (Boundary D)), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤
          H*(dist z w)^(Real.log b/Real.log (Real.exp (2*visualExponent δ)))) ∧
      (∃ z w, F z ≠ F w) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro Ω O P hΩ hO hOc hOΩ hP hPcon hPO f hvary α hα hholder z₀ d hd hsep
  obtain ⟨q,CP,_hq,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨Lp,hLp,hpaths⟩ := boundary_controlled_paths D hδ φ
  exact local_holder_magnification q CP hCP.le hpack (boundaryDist_le_one D hδ)
    Ω O P hΩ hO hOc hOΩ hP hPcon hPO f hvary Lp
    (Real.exp (2*visualExponent δ))
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) hLp
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ)))
    (by positivity) (by positivity) hpaths (boundaryExpansion D hδ)
    (boundaryExpansion_formula D hδ) α hα hholder z₀ d hd hsep

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Flows_ContinuousDomain
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonMagnification

open Set Metric Filter Topology

lemma continuousOn_onDomain {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (f : C(Ω,ℝ)) : ContinuousOn (onDomain f) Ω := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact onDomain_eq f x.val x.property

lemma uniform_onDomain {X : Type*} [MetricSpace X] {Ω : Set X}
    (f : ℕ → X → ℝ) (F : C(Ω,ℝ))
    (hlim : ∀ K : Set Ω, IsCompact K →
      TendstoUniformlyOn (fun i z => f i z.val) F atTop K)
    (K : Set X) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn f (onDomain F) atTop K := by
  let K' : Set Ω := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (by simpa only [Subtype.range_coe] using hKΩ)
  intro u hu
  filter_upwards [hlim K' hK' u hu] with i hi
  intro z hz
  simpa only [onDomain_eq F z (hKΩ hz)] using hi ⟨z,hKΩ hz⟩ hz

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_ThinQuadrilateral
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology

namespace CannonGraph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma thin_quadrilateral (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {a b c d : V} (p : G.Walk a b) (q : G.Walk b c)
    (r : G.Walk c d) (s : G.Walk d a)
    (hp : p.length = G.dist a b) (hq : q.length = G.dist b c)
    (hr : r.length = G.dist c d) (hs : s.length = G.dist d a)
    {x : V} (hx : x ∈ p.support) :
    ∃ y ∈ q.support ++ r.support ++ s.support, G.dist x y ≤ 2*δ := by
  obtain ⟨t,ht⟩ := hG.exists_walk_length_eq_dist b d
  obtain ⟨y,hy,hxy⟩ := hthin a b d p t s hp ht hs x hx
  rcases List.mem_append.mp hy with hy | hy
  · have htr : t.reverse.length = G.dist d b := by
      simpa [SimpleGraph.dist_comm] using ht
    obtain ⟨z,hz,hyz⟩ := hthin d b c t.reverse q r htr hq hr y (by simpa using hy)
    refine ⟨z, ?_, ?_⟩
    · exact List.mem_append_left _ hz
    · have := @Connected.dist_triangle _ G x y z hG
      omega
  · exact ⟨y, List.mem_append_right _ hy, by omega⟩

theorem asymptotic_rays_asynchronous (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C)
    {n : ℕ} (hn : G.dist (r 0) (s 0) + 2*δ < n) :
    ∃ m : ℕ, G.dist (r n) (s m) ≤ 2*δ ∧
      m ≤ n + G.dist (r 0) (s 0) + 2*δ ∧
      n ≤ m + G.dist (r 0) (s 0) + 2*δ := by
  obtain ⟨C,hC⟩ := hbounded
  let N := n+C+2*δ+1
  have hnN : n ≤ N := by dsimp [N]; omega
  let p := raySegment r hr N
  let q := raySegment s hs N
  obtain ⟨u,hu⟩ := hG.exists_walk_length_eq_dist (r N) (s N)
  obtain ⟨v,hv⟩ := hG.exists_walk_length_eq_dist (s 0) (r 0)
  have hp : p.length = G.dist (r 0) (r N) := by simp [p,hr,Nat.dist]
  have hq : q.reverse.length = G.dist (s N) (s 0) := by simp [q,hs,Nat.dist]
  have hrn : r n ∈ p.support := by
    rw [← raySegment_getVert r hr hnN]
    exact Walk.getVert_mem_support _ _
  obtain ⟨y,hy,hd⟩ := thin_quadrilateral hG hthin p u q.reverse v hp hu hq hv hrn
  rcases List.mem_append.mp hy with hy | hy
  · rcases List.mem_append.mp hy with hy | hy
    · have hNy : G.dist (r N) y ≤ C := by
        have he := of_mem_geodesic hG u hu hy
        have hCN := hC N
        omega
      have htri := @Connected.dist_triangle _ G (r N) y (r n) hG
      rw [SimpleGraph.dist_comm (u := y) (v := r n), hr] at htri
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hnN] at htri
      have hN : N = n+C+2*δ+1 := rfl
      omega
    · have hyq : y ∈ q.support := by simpa using hy
      obtain ⟨m,hm,hmb⟩ := Walk.mem_support_iff_exists_getVert.mp hyq
      have hmN : m ≤ N := by simpa [q] using hmb
      have hym : y = s m := by
        rw [← hm]
        exact raySegment_getVert s hs hmN
      rw [hym] at hd
      refine ⟨m,hd,?_,?_⟩
      · have ht₁ := @Connected.dist_triangle _ G (s 0) (r 0) (r n) hG
        have ht₂ := @Connected.dist_triangle _ G (s 0) (r n) (s m) hG
        rw [SimpleGraph.dist_comm (u := s 0) (v := r 0), hr] at ht₁
        rw [hs] at ht₂
        simp only [Nat.dist_zero_left] at ht₁ ht₂
        omega
      · have ht₁ := @Connected.dist_triangle _ G (r 0) (s 0) (s m) hG
        have ht₂ := @Connected.dist_triangle _ G (r 0) (s m) (r n) hG
        rw [hs] at ht₁
        rw [hr, SimpleGraph.dist_comm (u := s m) (v := r n)] at ht₂
        simp only [Nat.dist_zero_left] at ht₁ ht₂
        omega
  · have hy₀ : G.dist y (r 0) ≤ G.dist (r 0) (s 0) := by
      have he := of_mem_geodesic hG v hv hy
      rw [SimpleGraph.dist_comm (u := s 0) (v := r 0)] at he
      omega
    have ht := @Connected.dist_triangle _ G (r n) y (r 0) hG
    rw [hr] at ht
    simp only [Nat.dist_zero_right] at ht
    omega

end CannonGraph

namespace CannonGraph

open SimpleGraph

variable {H : Type*} [Group H] {G : SimpleGraph H}

theorem asymptotic_translate_card_bound (hG : G.Connected)
    (hleft : ∀ a x y : H, G.dist (a*x) (a*y) = G.dist x y)
    {δ : ℕ} (hthin : Thin G δ) (r : ℕ → H) (hr₀ : r 0 = 1)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (B : Finset H) (hB : ∀ x, G.dist 1 x ≤ 2*δ → x ∈ B)
    (F : Finset H) (t : ℕ)
    (ht : ∀ q ∈ F, G.dist 1 q ≤ t)
    (hfix : ∀ q ∈ F, ∃ C : ℕ, ∀ n, G.dist (q*r n) (r n) ≤ C) :
    F.card ≤ (2*t+4*δ+2) * B.card := by
  classical
  let n := t+2*δ+1
  have hnear : ∀ q : {q // q ∈ F}, ∃ m : ℕ,
      G.dist (q.val*r n) (r m) ≤ 2*δ ∧ m < 2*t+4*δ+2 := by
    intro q
    have hqr : ∀ i j, G.dist (q.val*r i) (q.val*r j) = Nat.dist i j := by
      intro i j
      rw [hleft,hr]
    have hd₀ : G.dist (q.val*r 0) (r 0) = G.dist 1 q.val := by
      rw [hr₀,mul_one,SimpleGraph.dist_comm]
    have hqn : G.dist (q.val*r 0) (r 0) + 2*δ < n := by
      rw [hd₀]
      have := ht q.val q.property
      dsimp [n]
      omega
    obtain ⟨m,hm,hm₁,_⟩ := asymptotic_rays_asynchronous hG hthin
      (fun k => q.val*r k) r hqr hr (hfix q.val q.property) hqn
    refine ⟨m,hm,?_⟩
    rw [hd₀] at hm₁
    have := ht q.val q.property
    dsimp [n] at hm₁
    omega
  choose m hm using hnear
  have hmem : ∀ q : {q // q ∈ F}, (r (m q))⁻¹ * (q.val*r n) ∈ B := by
    intro q
    apply hB
    have he := hleft (r (m q)) 1 ((r (m q))⁻¹ * (q.val*r n))
    simp only [mul_one,mul_inv_cancel_left] at he
    rw [← he, SimpleGraph.dist_comm]
    exact (hm q).1
  let f : {q // q ∈ F} → Fin (2*t+4*δ+2) × {x // x ∈ B} := fun q =>
    (⟨m q,(hm q).2⟩, ⟨(r (m q))⁻¹ * (q.val*r n),hmem q⟩)
  have hf : Function.Injective f := by
    intro q q' he
    have hm' : m q = m q' := congrArg (fun p => p.1.val) he
    have hx : (r (m q))⁻¹ * (q.val*r n) = (r (m q'))⁻¹ * (q'.val*r n) :=
      congrArg (fun p => p.2.val) he
    rw [hm'] at hx
    exact Subtype.ext (mul_right_cancel (mul_left_cancel hx))
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

end CannonGraph

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Words
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

attribute [local instance] OAI.CannonRelease.boundaryStabilizerWordsSetoid
theorem boundary_stabilizer_linear (b : Boundary D) :
    ∃ C : ℕ, ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, boundaryTranslate D hthin g b = b) →
      (∀ g ∈ F, D.graph.dist 1 g ≤ t) → F.card ≤ C*(t+1) := by
  classical
  obtain ⟨δ,hδ⟩ := hthin
  let B := (CannonGraph.finite_graph_ball D.connected
    (CannonGraph.finite_cayley_neighbors D.generators) 1 (2*δ)).toFinset
  refine ⟨(4*δ+2)*B.card, ?_⟩
  induction b using Quotient.inductionOn with
  | h r =>
    intro F t hF ht
    have hfix : ∀ q ∈ F, ∃ C : ℕ, ∀ n, D.graph.dist (q*r.val n) (r.val n) ≤ C := by
      intro q hq
      have he : Quotient.mk' (translateRay D ⟨δ,hδ⟩ q r) = (Quotient.mk' r : Boundary D) :=
        hF q hq
      have he' : Asymptotic D (translateRay D ⟨δ,hδ⟩ q r).val r.val := Quotient.exact he
      exact Asymptotic.trans D (Asymptotic.symm D (translateRay_spec D ⟨δ,hδ⟩ q r)) he'
    have hcard := CannonGraph.asymptotic_translate_card_bound D.connected
      D.dist_mul_left hδ r.val r.property.1 r.property.2 B
      (fun x hx => by simpa [B] using hx) F t ht hfix
    calc
      F.card ≤ (2*t+4*δ+2)*B.card := hcard
      _ ≤ ((4*δ+2)*(t+1))*B.card := Nat.mul_le_mul_right _ (by nlinarith)
      _ = ((4*δ+2)*B.card)*(t+1) := by ring

end CannonRelease

namespace CannonStabilizer

open Set

private lemma words_preserve {G X : Type*} [Group G] [DecidableEq G]
    [MulAction G X] (a b : G) (T : Set X)
    (ha : ∀ x ∈ T, a • x ∈ T) (hb : ∀ x ∈ T, b • x ∈ T) :
    ∀ n g, g ∈ words a b n → ∀ x ∈ T, g • x ∈ T := by
  intro n
  induction n with
  | zero =>
    intro g hg x hx
    have : g = 1 := by simpa [words] using hg
    simpa [this] using hx
  | succ n ih =>
    intro g hg x hx
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
      simpa only [mul_smul] using ha (v • x) (ih v hv x hx)
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
      simpa only [mul_smul] using hb (v • x) (ih v hv x hx)

private lemma words_card {G X : Type*} [Group G] [DecidableEq G]
    [MulAction G X] (a b : G) (T U V : Set X) (hne : T.Nonempty)
    (hUT : U ⊆ T) (hVT : V ⊆ T) (hdis : Disjoint U V)
    (ha : ∀ x ∈ T, a • x ∈ U) (hb : ∀ x ∈ T, b • x ∈ V) :
    ∀ n, (words a b n).card = 2^n := by
  have hap : ∀ x ∈ T, a • x ∈ T := fun x hx => hUT (ha x hx)
  have hbp : ∀ x ∈ T, b • x ∈ T := fun x hx => hVT (hb x hx)
  intro n
  induction n with
  | zero => simp [words]
  | succ n ih =>
    have hd : Disjoint ((words a b n).image (a*·)) ((words a b n).image (b*·)) := by
      apply Finset.disjoint_left.mpr
      intro g hga hgb
      obtain ⟨u,hu,he₁⟩ := Finset.mem_image.mp hga
      obtain ⟨v,hv,he₂⟩ := Finset.mem_image.mp hgb
      obtain ⟨x,hx⟩ := hne
      have ha' : g • x ∈ U := by
        rw [← he₁,mul_smul]
        exact ha _ (words_preserve a b T hap hbp n u hu x hx)
      have hb' : g • x ∈ V := by
        rw [← he₂,mul_smul]
        exact hb _ (words_preserve a b T hap hbp n v hv x hx)
      exact Set.disjoint_left.mp hdis ha' hb'
    rw [words,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun x y h => mul_left_cancel h),
      Finset.card_image_of_injective _ (fun x y h => mul_left_cancel h),ih,pow_succ]
    omega

private lemma words_mem {G : Type*} [Group G] [DecidableEq G]
    (E : Subgroup G) (a b : G) (ha : a ∈ E) (hb : b ∈ E) :
    ∀ n g, g ∈ words a b n → g ∈ E := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := Finset.mem_singleton.mp hg
    subst g
    exact E.one_mem
  | succ n ih =>
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      exact E.mul_mem ha (ih u hu)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      exact E.mul_mem hb (ih u hu)

private lemma words_length {G : Type*} [Group G] [DecidableEq G]
    (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h) (a b : G) :
    ∀ n g, g ∈ words a b n → len g ≤ n * (len a + len b) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := by simpa [words] using hg
    simp [this,h₁]
  | succ n ih =>
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      have := ih u hu
      have := hsub a u
      rw [Nat.succ_mul]
      omega
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hg
      have := ih u hu
      have := hsub b u
      rw [Nat.succ_mul]
      omega

lemma exists_exponential_gt_linear (C L : ℕ) : ∃ n : ℕ, C*(n*L+1) < 2^n := by
  let k := C*(L+1)+1
  refine ⟨2*k, ?_⟩
  have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  have hk : C*L+1 ≤ k := by dsimp [k]; nlinarith
  have hC : C ≤ k := by dsimp [k]; nlinarith
  have hm := Nat.mul_le_mul_left (2*k) hk
  have hkpos : 0 < k := by dsimp [k]; positivity
  nlinarith

theorem no_disjoint_contractions {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h)
    (C : ℕ) (hlinear : ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, g ∈ E) → (∀ g ∈ F, len g ≤ t) → F.card ≤ C*(t+1))
    (a b : G) (haE : a ∈ E) (hbE : b ∈ E)
    (T U V : Set X) (hne : T.Nonempty) (hUT : U ⊆ T) (hVT : V ⊆ T)
    (hdis : Disjoint U V) (ha : ∀ x ∈ T, a • x ∈ U)
    (hb : ∀ x ∈ T, b • x ∈ V) : False := by
  classical
  obtain ⟨n,hn⟩ := exists_exponential_gt_linear C (len a+len b)
  have hc := hlinear (words a b n) (n*(len a+len b))
    (words_mem E a b haE hbE n) (words_length len h₁ hsub a b n)
  rw [words_card a b T U V hne hUT hVT hdis ha hb n] at hc
  omega

theorem contracting_direction_unique {G X : Type*} [Group G] [MulAction G X]
    [MetricSpace X] (E : Subgroup G) (len : G → ℕ) (h₁ : len 1 = 0)
    (hsub : ∀ g h, len (g*h) ≤ len g + len h)
    (C : ℕ) (hlinear : ∀ (F : Finset G) (t : ℕ),
      (∀ g ∈ F, g ∈ E) → (∀ g ∈ F, len g ≤ t) → F.card ≤ C*(t+1))
    {b x y : X} (hxb : x ≠ b) (hyb : y ≠ b)
    (hx : ContractingDirection E b x) (hy : ContractingDirection E b y) : x = y := by
  by_contra hxy
  let r := min (dist x y) (min (dist x b) (dist y b)) / 3
  have hr : 0 < r := div_pos (lt_min (dist_pos.mpr hxy)
    (lt_min (dist_pos.mpr hxb) (dist_pos.mpr hyb))) (by norm_num)
  have hxy' : r+r ≤ dist x y := by
    have := min_le_left (dist x y) (min (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  have hxb' : r+r ≤ dist x b := by
    have := (min_le_right (dist x y) (min (dist x b) (dist y b))).trans
      (min_le_left (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  have hyb' : r+r ≤ dist y b := by
    have := (min_le_right (dist x y) (min (dist x b) (dist y b))).trans
      (min_le_right (dist x b) (dist y b))
    dsimp [r] at *
    linarith
  obtain ⟨g,hg,hgc⟩ := hx (Metric.ball x r) Metric.isOpen_ball
    (Metric.mem_ball_self hr) (Metric.ball b r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨h,hh,hhc⟩ := hy (Metric.ball y r) Metric.isOpen_ball
    (Metric.mem_ball_self hr) (Metric.ball b r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hUT : Metric.ball x r ⊆ (Metric.ball b r)ᶜ :=
    (Metric.ball_disjoint_ball hxb').subset_compl_right
  have hVT : Metric.ball y r ⊆ (Metric.ball b r)ᶜ :=
    (Metric.ball_disjoint_ball hyb').subset_compl_right
  exact no_disjoint_contractions E len h₁ hsub C hlinear g h hg hh
    (Metric.ball b r)ᶜ (Metric.ball x r) (Metric.ball y r)
    ⟨x,hUT (Metric.mem_ball_self hr)⟩ hUT hVT
    (Metric.ball_disjoint_ball hxy') (fun z hz => hgc hz) (fun z hz => hhc hz)

end CannonStabilizer

namespace CannonStabilizer

open CannonMagnification

theorem contracting_direction_of_fixed_puncture
    {G X : Type*} [Group G] [MetricSpace X]
    (ρ : G →* (X ≃ₜ X)) (b y : X) (v₀ : G) (v : ℕ → G)
    (x : ℕ → X) (r : ℕ → ℝ) (C L : ℝ)
    (hdiam : ∀ z w : X, dist z w ≤ 1)
    (hC : 0 ≤ C) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hxlim : Tendsto x atTop (𝓝 y)) (hyb : y ≠ b)
    (hexp : ∀ i, Expansion (ρ ((v i)⁻¹)) (x i) (r i) C L)
    (hp : ∀ i, ρ ((v i)⁻¹) b = ρ (v₀⁻¹) b) :
    let _ : MulAction G X := homAction ρ
    ContractingDirection (MulAction.stabilizer G b) b y := by
  let _ : MulAction G X := homAction ρ
  dsimp only [ContractingDirection]
  intro U hU hyU V hV hbV
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU y hyU
  let p := ρ (v₀⁻¹) b
  have h₀ : ρ v₀ p = b := by
    dsimp [p]
    change ((ρ v₀)*(ρ (v₀⁻¹))) b = b
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  have hpre : IsOpen ((ρ v₀) ⁻¹' V) := hV.preimage (ρ v₀).continuous
  obtain ⟨e,he,hepre⟩ := Metric.isOpen_iff.mp hpre p (by simpa [h₀] using hbV)
  have hsep : ∀ z ∉ V, e ≤ dist (ρ (v₀⁻¹) z) p := by
    intro z hz
    by_contra hez
    have hmem := hepre (show ρ (v₀⁻¹) z ∈ ball p e by exact lt_of_not_ge hez)
    have hid : ρ v₀ (ρ (v₀⁻¹) z) = z := by
      change ((ρ v₀)*(ρ (v₀⁻¹))) z = z
      rw [← map_mul,mul_inv_cancel,map_one]
      rfl
    exact hz (by simpa only [Set.mem_preimage,hid] using hmem)
  let d := dist y b / 2
  have hd : 0 < d := div_pos (dist_pos.mpr hyb) (by norm_num)
  have hdlim : Tendsto (fun i => dist (x i) b) atTop (𝓝 (dist y b)) :=
    hxlim.dist tendsto_const_nhds
  have hdlate : ∀ᶠ i in atTop, d ≤ dist (x i) b :=
    (hdlim.eventually (eventually_gt_nhds (show d < dist y b by dsimp [d]; linarith [dist_pos.mpr hyb]))).mono
      (fun _ hi => hi.le)
  have hxlate : ∀ᶠ i in atTop, dist (x i) y < ε/2 :=
    hxlim.eventually (Metric.ball_mem_nhds y (by positivity))
  have hrlim' : Tendsto (fun i => (C/(e*d))*r i) atTop (𝓝 0) := by
    simpa using hrlim.const_mul (C/(e*d))
  have hrlate : ∀ᶠ i in atTop, (C/(e*d))*r i < ε/2 :=
    hrlim'.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨i,hiD,hiX,hiR⟩ := (hdlate.and (hxlate.and hrlate)).exists
  refine ⟨v i * v₀⁻¹, ?_, ?_⟩
  · change ρ (v i * v₀⁻¹) b = b
    rw [map_mul]
    change ρ (v i) (ρ (v₀⁻¹) b) = b
    rw [← hp i]
    change ((ρ (v i))*(ρ ((v i)⁻¹))) b = b
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  · intro z hz
    apply hεU
    have hnear := preimage_distance_bound (ρ ((v i)⁻¹)) (x i) b
      (ρ (v₀⁻¹) z) (r i) C L e d (hr i) hC he hd (hexp i) hdiam hiD
      (by rw [hp i]; exact hsep z hz)
    have hinv : (ρ ((v i)⁻¹)).symm (ρ (v₀⁻¹) z) = ρ (v i * v₀⁻¹) z := by
      rw [map_inv,map_mul]
      rfl
    rw [hinv] at hnear
    change dist (ρ (v i * v₀⁻¹) z) y < ε
    have ht := dist_triangle (ρ (v i * v₀⁻¹) z) (x i) y
    rw [dist_comm (ρ (v i * v₀⁻¹) z) (x i)] at ht
    linarith

end CannonStabilizer

namespace CannonStabilizer

open CannonMagnification

theorem puncture_fibers_finite {G X : Type*} [Group G] [MetricSpace X]
    (ρ : G →* (X ≃ₜ X)) (b : X) (v : ℕ → G) (x : ℕ → X) (r : ℕ → ℝ)
    (C L : ℝ) (hdiam : ∀ z w : X, dist z w ≤ 1)
    (hC : 0 ≤ C) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ i, Expansion (ρ ((v i)⁻¹)) (x i) (r i) C L)
    (K : Set X) (hK : IsCompact K) (hxK : ∀ i, x i ∈ K) (hbK : b ∉ K)
    (hgood : let _ : MulAction G X := homAction ρ
      ∀ y ∈ K, ¬ ContractingDirection (MulAction.stabilizer G b) b y) :
    ∀ p : X, {i | ρ ((v i)⁻¹) b = p}.Finite := by
  let _ : MulAction G X := homAction ρ
  intro p
  by_contra hfin
  have hinf : Set.Infinite {i | ρ ((v i)⁻¹) b = p} := hfin
  obtain ⟨s,hs,hsp⟩ := extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hinf)
  obtain ⟨y,hy,t,ht,hyLim⟩ := hK.tendsto_subseq (fun i => hxK (s i))
  have hp : ∀ i, ρ ((v (s (t i)))⁻¹) b = ρ ((v (s (t 0)))⁻¹) b :=
    fun i => (hsp (t i)).trans (hsp (t 0)).symm
  have hyb : y ≠ b := fun h => hbK (h ▸ hy)
  have hc := contracting_direction_of_fixed_puncture ρ b y (v (s (t 0)))
    (fun i => v (s (t i))) (fun i => x (s (t i))) (fun i => r (s (t i)))
    C L hdiam hC (fun i => hr (s (t i)))
    (hrlim.comp (hs.comp ht).tendsto_atTop) hyLim hyb (fun i => hexp (s (t i))) hp
  exact hgood y hy hc

theorem injective_subsequence_of_finite_fibers {X : Type*} (p : ℕ → X)
    (hfib : ∀ x : X, {i | p i = x}.Finite) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ Function.Injective (p ∘ s) := by
  classical
  have hRange : (range p).Infinite := by
    intro hfin
    have hU : (univ : Set ℕ).Finite := Set.Finite.of_finite_fibers p
      (by simpa using hfin) (by intro x _; exact (hfib x).subset (by intro i hi; exact hi.2))
    exact Set.infinite_univ hU
  let e := hRange.natEmbedding (range p)
  have hp : ∀ i : ℕ, ∃ n : ℕ, p n = (e i).val := fun i => (e i).property
  choose f hf using hp
  have hpf : Function.Injective (p ∘ f) := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    exact (hf i).symm.trans (h.trans (hf j))
  have hfij : Function.Injective f := fun i j h => hpf (congrArg p h)
  obtain ⟨s,hs,hfs⟩ := strictMono_subseq_of_tendsto_atTop hfij.nat_tendsto_atTop
  exact ⟨f ∘ s,hfs,hpf.comp hs.injective⟩

end CannonStabilizer

open Set unitInterval

namespace CannonVariation

open Filter Topology Metric

theorem path_meets_variation {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    {x y : X} (p : Path x y) (hxy : F x ≠ F y) :
    ∃ z ∈ range p, NonconstantAt F z := by
  by_contra h
  push Not at h
  have hlc : IsLocallyConstant (fun t : I => F (p t)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro t
    have ht : ∀ᶠ z in 𝓝 (p t), F z = F (p t) := not_not.mp (h (p t) (mem_range_self t))
    exact p.continuous.continuousAt.tendsto.eventually ht
  have he := hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (0 : I)) (mem_univ (1 : I))
  exact hxy (by simpa using he)

lemma nonconstantAt_normalize {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    (A sig : ℝ) (hsig : sig ≠ 0) (x : X) :
    NonconstantAt (fun z => (F z - A) / sig) x ↔ NonconstantAt F x := by
  simp only [NonconstantAt, div_left_inj' hsig, sub_left_inj]

theorem value_subpath {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    {x y : X} (p : Path x y) (hF : ContinuousOn F (range p))
    (a b : ℝ) (hab : a < b) (hxa : F x ≤ a) (hby : b ≤ F y) :
    ∃ v w : X, ∃ q : Path v w, range q ⊆ range p ∧ F v = a ∧ F w = b ∧
      ∀ z ∈ range q, F z ∈ Icc a b := by
  have hc : Continuous (fun t => F (p t)) := hF.comp_continuous p.continuous (fun t => mem_range_self t)
  obtain ⟨s,t,hst,hs,ht,hbt⟩ := CannonAnnular.radial_subinterval
    (fun t => F (p t)) hc a b hab (by simpa using hxa) (by simpa using hby)
  refine ⟨p s,p t,p.subpath s t,?_,hs,ht,?_⟩
  · rw [Path.range_subpath_of_le _ _ _ hst.le]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le _ _ _ hst.le] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    exact hbt u hu

end CannonVariation

end
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
-- module Solutions.OAIQ046_CN.Cannon_Flows_NormalizedComparison
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonSecondMagnification

open Filter Topology Metric CannonVariation

theorem impossible_nonconstant_limit {X : Type*} [MetricSpace X]
    (F : ℕ → X → ℝ) (p : ℕ → X) (b : X) (W : X → ℝ)
    (hp : Tendsto p atTop (𝓝 b)) (hinj : Function.Injective p)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hlim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn F W atTop K)
    (hcomp : ∀ i j, p i ≠ p j → ∀ x, x ≠ p i → x ≠ p j →
      NonconstantAt (F i) x → F j x = F j (p i))
    {v w : X} (q : Path v w) (hqb : b ∉ range q) (hvar : W v < W w) : False := by
  let d := (W w - W v) / 5
  have hd : 0 < d := div_pos (sub_pos.mpr hvar) (by norm_num)
  have hWr : ContinuousOn W (range q) := hW.mono (by
    intro x hx hxb
    exact hqb (hxb ▸ hx))
  obtain ⟨v₁,w₁,q₁,hq₁,hv₁,hw₁,hW₁⟩ := value_subpath W q hWr
    (W v + d) (W v + 2*d) (by linarith) (by linarith) (by dsimp [d]; linarith)
  obtain ⟨v₂,w₂,q₂,hq₂,hv₂,hw₂,hW₂⟩ := value_subpath W q hWr
    (W v + 3*d) (W v + 4*d) (by linarith) (by linarith) (by dsimp [d]; linarith)
  let K := range q₁ ∪ range q₂
  have hK : IsCompact K := (isCompact_range q₁.continuous).union (isCompact_range q₂.continuous)
  have hbK : b ∉ K := by
    rintro (hb | hb)
    · exact hqb (hq₁ hb)
    · exact hqb (hq₂ hb)
  have havoid : ∀ᶠ n in atTop, p n ∉ K := hp.eventually (hK.isClosed.isOpen_compl.mem_nhds hbK)
  have he : ∀ᶠ n in atTop, ∀ z ∈ K, |W z - F n z| < d/4 := by
    simpa only [Real.dist_eq] using (Metric.tendstoUniformlyOn_iff.mp (hlim K hK hbK) (d/4) (by positivity))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (havoid.and he)
  let i := N
  let j := N+1
  have hi := hN i le_rfl
  have hj := hN j (Nat.le_succ N)
  have hv₁K : v₁ ∈ K := Or.inl (q₁.source_mem_range)
  have hw₁K : w₁ ∈ K := Or.inl (q₁.target_mem_range)
  have hv₂K : v₂ ∈ K := Or.inr (q₂.source_mem_range)
  have hw₂K : w₂ ∈ K := Or.inr (q₂.target_mem_range)
  have hi₁ : F i v₁ < F i w₁ := by
    have ha := (abs_lt.mp (hi.2 v₁ hv₁K))
    have hb := (abs_lt.mp (hi.2 w₁ hw₁K))
    rw [hv₁] at ha
    rw [hw₁] at hb
    linarith
  have hi₂ : F i v₂ < F i w₂ := by
    have ha := (abs_lt.mp (hi.2 v₂ hv₂K))
    have hb := (abs_lt.mp (hi.2 w₂ hw₂K))
    rw [hv₂] at ha
    rw [hw₂] at hb
    linarith
  obtain ⟨z₁,hz₁,hz₁var⟩ := path_meets_variation (F i) q₁ hi₁.ne
  obtain ⟨z₂,hz₂,hz₂var⟩ := path_meets_variation (F i) q₂ hi₂.ne
  have hz₁K : z₁ ∈ K := Or.inl hz₁
  have hz₂K : z₂ ∈ K := Or.inr hz₂
  have hpi : p i ≠ p j := fun h => (Nat.ne_add_one N) (hinj h)
  have he₁ := hcomp i j hpi z₁ (fun h => hi.1 (h ▸ hz₁K)) (fun h => hj.1 (h ▸ hz₁K)) hz₁var
  have he₂ := hcomp i j hpi z₂ (fun h => hi.1 (h ▸ hz₂K)) (fun h => hj.1 (h ▸ hz₂K)) hz₂var
  have heq : F j z₁ = F j z₂ := he₁.trans he₂.symm
  have hb₁ := (hW₁ z₁ hz₁).2
  have hb₂ := (hW₂ z₂ hz₂).1
  have ha := abs_lt.mp (hj.2 z₁ hz₁K)
  have hb := abs_lt.mp (hj.2 z₂ hz₂K)
  linarith

end CannonSecondMagnification

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_IntervalAvoiding
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonVariation

open Set Metric Filter Topology

lemma exists_interval_avoiding {u v : ℝ} (huv : u < v) (z : ℝ) :
    ∃ a d ε : ℝ, u < a ∧ a < d ∧ d < v ∧ 0 < ε ∧
      ∀ t ∈ Icc a d, ε ≤ |t-z| := by
  by_cases hz : z ≤ (u+v)/2
  · refine ⟨(u+3*v)/4,(u+7*v)/8,(v-u)/4,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.1]
  · have hz' : (u+v)/2 ≤ z := (lt_of_not_ge hz).le
    refine ⟨(7*u+v)/8,(3*u+v)/4,(v-u)/4,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.2]

theorem variation_region_avoiding {X : Type*} [MetricSpace X]
    (W : X → ℝ) (b c : X) (hW : ContinuousOn W ({b}ᶜ : Set X))
    {v w : X} (q : Path v w) (hqb : b ∉ range q) (hvar : W v < W w) :
    ∃ O P : Set X, IsOpen O ∧ Oᶜ.Nonempty ∧ IsCompact P ∧ IsConnected P ∧
      P ⊆ O ∧ closure O ⊆ ({b}ᶜ : Set X) ∧ c ∉ closure O ∧
      (∃ u ∈ P, ∃ v ∈ P, W u ≠ W v) ∧
      ∃ d : ℝ, 0 < d ∧ ∀ x ∈ O, d ≤ dist x b := by
  obtain ⟨a,d,ε,hva,had,hdw,hε,havoid⟩ := exists_interval_avoiding hvar (W c)
  have hWr : ContinuousOn W (range q) := hW.mono (by
    intro x hx hxb
    exact hqb (hxb ▸ hx))
  obtain ⟨u,z,p,hpq,hu,hz,hslab⟩ := value_subpath W q hWr a d had hva.le hdw.le
  let P := range p
  have hP : IsCompact P := isCompact_range p.continuous
  have hbP : b ∉ P := fun h => hqb (hpq h)
  have hcP : c ∉ P := by
    intro hc
    have he := havoid (W c) (hslab c hc)
    simp only [sub_self,abs_zero] at he
    linarith
  let U : Set X := {b}ᶜ ∩ {c}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl
  have hPU : P ⊆ U := by
    intro x hx
    exact ⟨fun h => hbP (h ▸ hx),fun h => hcP (h ▸ hx)⟩
  obtain ⟨O,hO,hPO,hOU⟩ := hP.exists_isOpen_closure_subset
    (hU.mem_nhdsSet.mpr hPU)
  have hbO : b ∉ closure O := fun h => (hOU h).1 rfl
  have hOne : (closure O).Nonempty := ⟨u,subset_closure (hPO p.source_mem_range)⟩
  have hdpos : 0 < infDist b (closure O) :=
    isClosed_closure.notMem_iff_infDist_pos hOne |>.mp hbO
  refine ⟨O,P,hO,⟨b,fun h => hbO (subset_closure h)⟩,hP,
    (isConnected_range p.continuous),hPO,(fun x hx => (hOU hx).1),
    (fun h => (hOU h).2 rfl),⟨u,p.source_mem_range,z,p.target_mem_range,?_⟩,
    infDist b (closure O),hdpos,?_⟩
  · rw [hu,hz]
    exact had.ne
  · intro x hx
    exact (infDist_le_dist_of_mem (subset_closure hx)).trans_eq (dist_comm b x)

end CannonVariation

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_OrderedVariationPath
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonVariation

open Set

lemma ordered_variation_path {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (hΩ : IsPathConnected Ω) (W : X → ℝ)
    (hvar : ∃ v ∈ Ω, ∃ w ∈ Ω, W v ≠ W w) :
    ∃ v w : X, ∃ q : Path v w, range q ⊆ Ω ∧ W v < W w := by
  obtain ⟨v,hv,w,hw,hvw⟩ := hvar
  have hj := hΩ.joinedIn v hv w hw
  rcases lt_or_gt_of_ne hvw with hlt | hgt
  · exact ⟨v,w,hj.somePath,by rintro x ⟨t,rfl⟩; exact hj.somePath_mem t,hlt⟩
  · exact ⟨w,v,hj.symm.somePath,by rintro x ⟨t,rfl⟩; exact hj.symm.somePath_mem t,hgt⟩

end CannonVariation

end
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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryPuncturedPathConnected
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
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonStabilizer CannonVariation Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

omit [DiscreteTopology G] in
lemma boundary_punctured_pathConnected (φ : Boundary D ≃ₜ SphereTwo) (p : Boundary D) :
    IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
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

theorem boundary_second_magnification_obstruction (φ : Boundary D ≃ₜ SphereTwo)
    (b : Boundary D) :
    let _ := visualMetricSpace D hδ
    ∀ (W : C(({b}ᶜ : Set (Boundary D)),ℝ)) (α : ℝ), 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ ({b}ᶜ : Set (Boundary D)) → ∃ C ≥ 0,
      ∀ x y : ({b}ᶜ : Set (Boundary D)), x.val ∈ K → y.val ∈ K →
        |W x-W y| ≤ C*(dist x y)^α) →
    (∃ z w, W z ≠ W w) →
    (∀ s t : G, boundaryTranslate D ⟨δ,hδ⟩ s b ≠ boundaryTranslate D ⟨δ,hδ⟩ t b →
      ∀ z, z ≠ boundaryTranslate D ⟨δ,hδ⟩ s b → z ≠ boundaryTranslate D ⟨δ,hδ⟩ t b →
        NonconstantAt (fun z => onDomain W (boundaryTranslate D ⟨δ,hδ⟩ s⁻¹ z)) z →
        onDomain W (boundaryTranslate D ⟨δ,hδ⟩ t⁻¹ z) =
          onDomain W (boundaryTranslate D ⟨δ,hδ⟩ t⁻¹ (boundaryTranslate D ⟨δ,hδ⟩ s b))) → False := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro W α hα hholder hvar hcomp
  let ρ := boundaryAction D ⟨δ,hδ⟩
  let _ : MulAction G (Boundary D) := homAction ρ
  let E := MulAction.stabilizer G b
  obtain ⟨CG,hCG⟩ := boundary_stabilizer_linear D ⟨δ,hδ⟩ b
  have hlin : ∀ (F : Finset G) (t : ℕ), (∀ g ∈ F, g ∈ E) →
      (∀ g ∈ F, D.graph.dist 1 g ≤ t) → F.card ≤ CG*(t+1) := by
    intro F t hF ht
    exact hCG F t hF ht
  have hsub (g h : G) : D.graph.dist 1 (g*h) ≤ D.graph.dist 1 g + D.graph.dist 1 h := by
    calc
      _ ≤ D.graph.dist 1 g + D.graph.dist g (g*h) := D.connected.dist_triangle
      _ = _ := by rw [show D.graph.dist g (g*h) = D.graph.dist 1 h from
        by simpa only [mul_one] using D.dist_mul_left g 1 h]
  have hexcept : ∃ c : Boundary D, ∀ y, y ≠ b → ContractingDirection E b y → y = c := by
    by_cases he : ∃ c, c ≠ b ∧ ContractingDirection E b c
    · obtain ⟨c,hcb,hc⟩ := he
      refine ⟨c,fun y hy hdir => ?_⟩
      exact contracting_direction_unique E (D.graph.dist 1) (by simp) hsub CG hlin hy hcb hdir hc
    · refine ⟨b,fun y hy hdir => ?_⟩
      exact (he ⟨y,hy,hdir⟩).elim
  obtain ⟨c,hc⟩ := hexcept
  have hW : ContinuousOn (onDomain W) ({b}ᶜ : Set (Boundary D)) := continuousOn_onDomain W
  have hvar' : ∃ v ∈ ({b}ᶜ : Set (Boundary D)), ∃ w ∈ ({b}ᶜ : Set (Boundary D)),
      onDomain W v ≠ onDomain W w := by
    obtain ⟨v,w,hvw⟩ := hvar
    exact ⟨v.val,v.property,w.val,w.property,by simpa only [onDomain_eq _ _ v.property,onDomain_eq _ _ w.property] using hvw⟩
  obtain ⟨v₀,w₀,q,hq,hqw⟩ := ordered_variation_path _ (boundary_punctured_pathConnected D φ b)
    (onDomain W) hvar'
  have hbq : b ∉ range q := fun h => hq h rfl
  obtain ⟨O,P,hO,hOc,hP,hPc,hPO,hOb,hcO,hPv,d,hd,hdb⟩ :=
    variation_region_avoiding (onDomain W) b c hW q hbq hqw
  have hgood : ∀ y ∈ closure O, ¬ ContractingDirection E b y := by
    intro y hy hdir
    have hyb : y ≠ b := hOb hy
    exact hcO ((hc y hyb hdir) ▸ hy)
  obtain ⟨β,hβ,k,x,sig,p,F,hk,hx,hp,_hescape,_hdom,hFlim,_hFholder,hFvar⟩ :=
    boundary_holder_magnification D hδ φ {b}ᶜ O P isClosed_singleton.isOpen_compl hO hOc hOb
      hP hPc hPO W hPv α hα hholder b d hd hdb
  let v : ℕ → G := fun i => (boundaryBasedRay D (x i)).val (k i)
  let r : ℕ → ℝ := fun i => (Real.exp (2*visualExponent δ)^(k i))⁻¹
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have ha : 1 < Real.exp (2*visualExponent δ) :=
    Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  have hr : ∀ i, 0 < r i := fun i => by dsimp [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := by
    simpa only [r,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hfib := puncture_fibers_finite ρ b v x r CE LE (boundaryDist_le_one D hδ)
    (by dsimp [CE]; positivity) hr hrlim
    (fun i => boundaryExpansion_formula D hδ (x i) (k i)) (closure O) isClosed_closure.isCompact
    (fun i => subset_closure (hx i).1) (fun h => hOb h rfl) hgood
  obtain ⟨s,hs,hinj⟩ := injective_subsequence_of_finite_fibers (fun i => ρ ((v i)⁻¹) b) hfib
  let H : ℕ → Boundary D → ℝ := fun i =>
    normalized (onDomain W) (boundaryExpansion D hδ (x (s i)) (k (s i))) (x (s i)) (sig (s i))
  have hHcomp : ∀ i j, ρ ((v (s i))⁻¹) b ≠ ρ ((v (s j))⁻¹) b →
      ∀ z, z ≠ ρ ((v (s i))⁻¹) b → z ≠ ρ ((v (s j))⁻¹) b →
        NonconstantAt (H i) z → H j z = H j (ρ ((v (s i))⁻¹) b) := by
    intro i j hij z hzi hzj hz
    apply congrArg (fun a : ℝ => a / sig (s j))
    apply sub_left_inj.mpr
    exact hcomp ((v (s i))⁻¹) ((v (s j))⁻¹) hij z hzi hzj
      ((nonconstantAt_normalize _ _ _ (hx (s i)).2.ne' z).mp hz)
  have hHlim : ∀ K : Set (Boundary D), IsCompact K → p ∉ K →
      TendstoUniformlyOn H (onDomain F) atTop K := by
    intro K hK hpK
    have hh := uniform_onDomain
      (fun i => normalized (onDomain W) (boundaryExpansion D hδ (x i) (k i)) (x i) (sig i))
      F hFlim K hK (by intro z hz hzp; exact hpK (hzp ▸ hz))
    intro u hu
    exact hs.tendsto_atTop.eventually (hh u hu)
  have hFvar' : ∃ v ∈ ({p}ᶜ : Set (Boundary D)), ∃ w ∈ ({p}ᶜ : Set (Boundary D)),
      onDomain F v ≠ onDomain F w := by
    obtain ⟨v,w,hvw⟩ := hFvar
    exact ⟨v.val,v.property,w.val,w.property,by simpa only [onDomain_eq _ _ v.property,onDomain_eq _ _ w.property] using hvw⟩
  obtain ⟨v₁,w₁,q₁,hq₁,hq₁w⟩ := ordered_variation_path _ (boundary_punctured_pathConnected D φ p)
    (onDomain F) hFvar'
  exact CannonSecondMagnification.impossible_nonconstant_limit H
    (fun i => ρ ((v (s i))⁻¹) b) p (onDomain F) (hp.comp hs.tendsto_atTop) hinj
    (continuousOn_onDomain F) hHlim hHcomp q₁ (fun h => hq₁ h rfl) hq₁w

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_MeshEnergy
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

namespace CannonApprox

open Set Metric CannonCrossEnergy

lemma meshEnergy_nonneg {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) :
    0 ≤ meshEnergy p r J F K := by
  classical
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end CannonApprox

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_MeshEnergySumFilter
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

namespace CannonApprox

attribute [local instance] Classical.propDecidable

open Set Metric CannonCrossEnergy

lemma meshEnergy_eq_sum_filter {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) :
    meshEnergy p r J F K = ∑ i ∈ Finset.univ.filter
      (fun i => (ball (p i) (2*r) ∩ K).Nonempty),
      (oscillation F (closedBall (p i) (J*r)))^2 := by
  classical
  simpa only [meshEnergy, Finset.subtype_univ] using (Finset.sum_subtype_eq_sum_filter
    (s := Finset.univ) (p := fun i => (ball (p i) (2*r) ∩ K).Nonempty)
    (f := fun i => (oscillation F (closedBall (p i) (J*r)))^2))

lemma meshEnergy_mono_set {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) {K L : Set X} (hKL : K ⊆ L) :
    meshEnergy p r J F K ≤ meshEnergy p r J F L := by
  classical
  rw [meshEnergy_eq_sum_filter,meshEnergy_eq_sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact hi.mono (inter_subset_inter_right _ hKL)
  · intro i _ _
    exact sq_nonneg _

lemma oscillation_mono_of_bounded {X : Type*} (f : X → ℝ)
    (hhi : BddAbove (range f)) (hlo : BddBelow (range f))
    {A B : Set X} (hA : A.Nonempty) (hAB : A ⊆ B) :
    0 ≤ oscillation f A ∧ oscillation f A ≤ oscillation f B := by
  have hAn := hA.image f
  have hhiA := hhi.mono (image_subset_range f A)
  have hloA := hlo.mono (image_subset_range f A)
  have hhiB := hhi.mono (image_subset_range f B)
  have hloB := hlo.mono (image_subset_range f B)
  exact ⟨sub_nonneg.mpr (csInf_le_csSup hAn hloA hhiA),
    sub_le_sub (csSup_le_csSup hhiB hAn (image_mono hAB))
      (csInf_le_csInf hloB hAn (image_mono hAB))⟩

lemma meshEnergy_mono_radius {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r : ℝ) (hr : 0 ≤ r) (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (K : Set X) {J T : ℝ} (hJ : 0 ≤ J) (hJT : J ≤ T) :
    meshEnergy p r J F K ≤ meshEnergy p r T F K := by
  classical
  apply Finset.sum_le_sum
  intro i _
  have hh := oscillation_mono_of_bounded F hhi hlo
    (nonempty_closedBall.mpr (mul_nonneg hJ hr) :
      (closedBall (p i.val) (J*r)).Nonempty)
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hJT hr))
  exact pow_le_pow_left₀ hh.1 hh.2 2

end CannonApprox

end
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
-- module Solutions.OAIQ046_CN.Cannon_Energy_AffineRangeBounded
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

namespace CannonApprox

open Set Metric Filter Topology CannonCrossEnergy

lemma affine_range_bounded {X : Type*} (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) :
    BddAbove (range (fun x => (F x-c)/σ)) ∧ BddBelow (range (fun x => (F x-c)/σ)) := by
  obtain ⟨A,hA⟩ := hhi
  obtain ⟨B,hB⟩ := hlo
  constructor
  · refine ⟨(A-c)/σ,?_⟩
    rintro _ ⟨x,rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hA (mem_range_self x)) c) hσ.le
  · refine ⟨(B-c)/σ,?_⟩
    rintro _ ⟨x,rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hB (mem_range_self x)) c) hσ.le

lemma oscillation_affine_le {X : Type*} (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) (A : Set X) (hA : A.Nonempty) :
    0 ≤ oscillation (fun x => (F x-c)/σ) A ∧
      oscillation (fun x => (F x-c)/σ) A ≤ oscillation F A/σ := by
  have hbounded := affine_range_bounded F hhi hlo c σ hσ
  refine ⟨(oscillation_mono_of_bounded _ hbounded.1 hbounded.2 hA Subset.rfl).1,?_⟩
  have hupper : sSup ((fun x => (F x-c)/σ) '' A) ≤ (sSup (F '' A)-c)/σ := by
    apply csSup_le (hA.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (le_csSup (hhi.mono (image_subset_range F A)) (mem_image_of_mem F hx)) c) hσ.le
  have hlower : (sInf (F '' A)-c)/σ ≤ sInf ((fun x => (F x-c)/σ) '' A) := by
    apply le_csInf (hA.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (csInf_le (hlo.mono (image_subset_range F A)) (mem_image_of_mem F hx)) c) hσ.le
  calc
    _ ≤ (sSup (F '' A)-c)/σ - (sInf (F '' A)-c)/σ := sub_le_sub hupper hlower
    _ = _ := by unfold CannonCrossEnergy.oscillation; ring

lemma meshEnergy_affine_le {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (hr : 0 ≤ r) (hJ : 0 ≤ J)
    (F : X → ℝ) (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) (K : Set X) :
    meshEnergy p r J (fun x => (F x-c)/σ) K ≤ (σ⁻¹)^2*meshEnergy p r J F K := by
  classical
  unfold meshEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := oscillation_affine_le F hhi hlo c σ hσ
    (closedBall (p i.val) (J*r)) (nonempty_closedBall.mpr (mul_nonneg hJ hr))
  calc
    _ ≤ (oscillation F (closedBall (p i.val) (J*r))/σ)^2 := pow_le_pow_left₀ hh.1 hh.2 2
    _ = _ := by ring

lemma meshEnergy_affine_tendsto {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (J : ℝ) (hJ : 0 ≤ J)
    (F : ℕ → X → ℝ) (hF : ∀ n, BddAbove (range (F n)) ∧ BddBelow (range (F n)))
    (c σ : ℝ) (hσ : 0 < σ) (K : Set X)
    (hE : Tendsto (fun n => meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0)) :
    Tendsto (fun n => meshEnergy (p n) (r n) J (fun x => (F n x-c)/σ) K) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => (σ⁻¹)^2*meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hE :
      Tendsto (fun n => (σ⁻¹)^2*meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 ((σ⁻¹)^2*0)))
  exact squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _))
    (Eventually.of_forall (fun n => meshEnergy_affine_le (p n) (r n) J (hr n) hJ
      (F n) (hF n).1 (hF n).2 c σ hσ K)) ht

lemma uniformly_affine {X : Type*} (F : ℕ → X → ℝ) (f : X → ℝ) (K : Set X)
    (hf : TendstoUniformlyOn F f atTop K) (c σ : ℝ) (hσ : 0 < σ) :
    TendstoUniformlyOn (fun n x => (F n x-c)/σ) (fun x => (f x-c)/σ) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (ε*σ) (mul_pos hε hσ)] with n hn
  intro x hx
  have hdist : dist ((f x-c)/σ) ((F n x-c)/σ) = dist (f x) (F n x)/σ := by
    rw [Real.dist_eq,Real.dist_eq,show (f x-c)/σ-(F n x-c)/σ = (f x-F n x)/σ by ring,
      abs_div,abs_of_pos hσ]
  rw [hdist]
  exact (div_lt_iff₀ hσ).mpr (hn x hx)

end CannonApprox

end
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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_RadialCellEnergy
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

namespace CannonTransfer
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

end CannonTransfer

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_MeshTransportBound
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

namespace CannonApprox

open Set Metric CannonCrossEnergy CannonPacking CannonTransfer

theorem exists_mesh_transport_bound {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP H B : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hH : 0 < H) (hB : 0 < B)
    (g : X ≃ₜ X)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y) :
    ∃ N : ℕ, ∀ (ι : Type*) [Fintype ι] (p : ι → X) (r J : ℝ),
      0 < r → 0 ≤ J → max H 1*r ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ x, ∃ i, dist (p i) x ≤ r) →
      ∀ (F : X → ℝ), BddAbove (range F) → BddBelow (range F) →
      ∀ K L : Set X,
      (∀ i, (ball (p i) (2*r) ∩ K).Nonempty →
        ∀ j, dist (p j) (g.symm (p i)) ≤ r → p j ∈ L) →
      meshEnergy p r J (F ∘ g.symm) K ≤ (N:ℝ)*meshEnergy p r (B*J+1) F L := by
  classical
  obtain ⟨N,hN⟩ := exists_overlap_bound Q CP H 1 hpack hCP hH (by norm_num)
  refine ⟨N,?_⟩
  intro ι hι p r J hr hJ hscale hpsep hpnet F hFhi hFlo K L hnear
  let α := {i : ι // (ball (p i) (2*r) ∩ K).Nonempty}
  let β := {j : ι // (ball (p j) (2*r) ∩ L).Nonempty}
  choose q hq using fun i : α => hpnet (g.symm (p i.val))
  have hqL (i : α) : p (q i) ∈ L := hnear i.val i.property (q i) (hq i)
  let σ : α → β := fun i => ⟨q i,⟨p (q i), by simp [hr],hqL i⟩⟩
  let w : β → ℝ := fun j => oscillation F (closedBall (p j.val) ((B*J+1)*r))
  have hosci (i : α) :
      (oscillation (F ∘ g.symm) (closedBall (p i.val) (J*r)))^2 ≤ (w (σ i))^2 := by
    have hsub : g.symm '' closedBall (p i.val) (J*r) ⊆
        closedBall (p (q i)) ((B*J+1)*r) := by
      rintro z ⟨y,hy,rfl⟩
      apply mem_closedBall.mpr
      have hd := dist_triangle (g.symm y) (g.symm (p i.val)) (p (q i))
      have h₁ := hginv y (p i.val)
      have h₂ := mul_le_mul_of_nonneg_left (mem_closedBall.mp hy) hB.le
      have h₃ : dist (g.symm (p i.val)) (p (q i)) ≤ r := by
        simpa only [dist_comm] using hq i
      nlinarith
    have hh := oscillation_mono_of_bounded F hFhi hFlo
      ((nonempty_closedBall.mpr (mul_nonneg hJ hr.le) :
        (closedBall (p i.val) (J*r)).Nonempty).image g.symm) hsub
    have heq : oscillation F (g.symm '' closedBall (p i.val) (J*r)) =
        oscillation (F ∘ g.symm) (closedBall (p i.val) (J*r)) := by
      simp only [CannonCrossEnergy.oscillation,image_image,Function.comp_def]
    rw [heq] at hh
    exact pow_le_pow_left₀ hh.1 hh.2 2
  have hcol (j : β) : (Finset.univ.filter (fun i : α => j ∈ ({σ i} : Finset β))).card ≤ N := by
    have hh := hN (fun i : α => p i.val) Finset.univ (g (p j.val)) r hr hscale (by
      intro i _ k _ hik
      simpa only [one_mul] using hpsep i.val k.val (fun heq => hik (Subtype.ext heq)))
    apply (Finset.card_le_card (s := Finset.univ.filter (fun i : α => j ∈ ({σ i} : Finset β))) ?_).trans hh
    intro i hi
    obtain ⟨_,hi⟩ := Finset.mem_filter.mp hi
    have heq : j = σ i := Finset.mem_singleton.mp hi
    have hqj : dist (p j.val) (g.symm (p i.val)) ≤ r := by
      rw [heq]
      exact hq i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
    calc
      dist (g (p j.val)) (p i.val) = dist (g (p j.val)) (g (g.symm (p i.val))) := by simp
      _ ≤ H*dist (p j.val) (g.symm (p i.val)) := hg _ _
      _ ≤ H*r := mul_le_mul_of_nonneg_left hqj hH.le
  have he := overlap_energy (fun i : α => ({σ i} : Finset β)) w 1 N (by simp) hcol
  simp only [Finset.sum_singleton,Nat.cast_one,one_mul] at he
  exact (Finset.sum_le_sum (fun i _ => hosci i)).trans he

end CannonApprox

namespace CannonApprox

open Set Metric Filter Topology CannonPacking

theorem transported_mesh_energy_tendsto {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP H B : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hH : 0 < H) (hB : 0 < B) (g : X ≃ₜ X)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (F : ℕ → X → ℝ) (hF : ∀ n, BddAbove (range (F n)) ∧ BddBelow (range (F n)))
    (b : X)
    (hE : ∀ L : Set X, IsCompact L → b ∉ L → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (F n) L) atTop (𝓝 0))
    (K : Set X) (hK : IsCompact K) (hbK : g b ∉ K) (J : ℝ) (hJ : 0 < J) :
    Tendsto (fun n => meshEnergy (p n) (r n) J (F n ∘ g.symm) K) atTop (𝓝 0) := by
  classical
  by_cases hKn : K.Nonempty
  · let K₀ := g.symm '' K
    have hK₀ : IsCompact K₀ := hK.image g.symm.continuous
    obtain ⟨x,hx,hmin⟩ := hK₀.exists_isMinOn (hKn.image g.symm)
      (continuous_id.dist continuous_const).continuousOn
    have hxb : x ≠ b := by
      intro hxb
      obtain ⟨y,hy,heq⟩ := hx
      have heq' : y = g b := by simpa only [g.apply_symm_apply] using congrArg g (heq.trans hxb)
      exact hbK (heq' ▸ hy)
    have hd : 0 < dist x b := dist_pos.mpr hxb
    let L : Set X := {y | dist x b/2 ≤ dist y b}
    have hL : IsCompact L := (isClosed_le continuous_const
      (continuous_id.dist continuous_const)).isCompact
    have hbL : b ∉ L := by change ¬ dist x b/2 ≤ dist b b; rw [dist_self]; linarith
    obtain ⟨N,hN⟩ := exists_mesh_transport_bound Q CP H B hpack hCP hH hB g hg hginv
    have ht₁ : ∀ᶠ n in atTop, (1+2*B)*r n < dist x b/2 := by
      have hh : Tendsto (fun n => (1+2*B)*r n) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
          Tendsto (fun n => (1+2*B)*r n) atTop (𝓝 ((1+2*B)*0)))
      exact hh.eventually_lt_const (by positivity)
    have ht₂ : ∀ᶠ n in atTop, max H 1*r n ≤ 1 := by
      have hh : Tendsto (fun n => max H 1*r n) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
          Tendsto (fun n => max H 1*r n) atTop (𝓝 (max H 1*0)))
      exact (hh.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
    have hbound : ∀ᶠ n in atTop,
        meshEnergy (p n) (r n) J (F n ∘ g.symm) K ≤
          (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L := by
      filter_upwards [ht₁,ht₂] with n hn₁ hn₂
      apply hN (ι n) (p n) (r n) J (hr n) hJ.le hn₂ (hpsep n) (hpnet n)
        (F n) (hF n).1 (hF n).2 K L
      intro i hi j hj
      obtain ⟨y,hy,hyK⟩ := hi
      have hymem : g.symm y ∈ K₀ := mem_image_of_mem _ hyK
      have hdy : dist x b ≤ dist (g.symm y) b := hmin hymem
      have hyball : dist (p n i) y < 2*r n := by simpa only [mem_ball,dist_comm] using hy
      have hdist := dist_triangle (p n j) (g.symm (p n i)) (g.symm y)
      have hginvy := hginv (p n i) y
      have hmul := mul_lt_mul_of_pos_left hyball hB
      have hdj := dist_triangle (g.symm y) (p n j) b
      rw [dist_comm (g.symm y) (p n j)] at hdj
      change dist x b/2 ≤ dist (p n j) b
      nlinarith
    have hlim : Tendsto (fun n => (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul (hE L hL hbL (B*J+1) (by positivity)) :
        Tendsto (fun n => (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L)
          atTop (𝓝 ((N:ℝ)*0)))
    exact squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _)) hbound hlim
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKn
    simp [hKempty,meshEnergy_eq_sum_filter]

end CannonApprox

open Set Metric Filter Topology

end
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

theorem wide_level_images_escape {X : Type*} [MetricSpace X]
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (r : ℕ → ℝ)
    (C L d d₀ : ℝ) (hC : 0 ≤ C) (hd : 0 < d) (hd₀ : 0 < d₀)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (r n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b)) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, ∀ A : Set X,
      d ≤ diam A → ∃ y ∈ (h n) '' A, dist y b < ρ := by
  intro ρ hρ
  have ht : Tendsto (fun n => C*r n/((d/3)*d₀)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using
      ((tendsto_const_nhds.mul hrlim).div_const ((d/3)*d₀))
  have hp : Tendsto (fun n => dist (h n z₀) b) atTop (𝓝 0) := by
    simpa only [dist_self] using hb.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b))
  have hsum : Tendsto (fun n => C*r n/((d/3)*d₀)+dist (h n z₀) b) atTop (𝓝 0) := by
    simpa only [add_zero] using ht.add hp
  filter_upwards [hsum.eventually_lt_const hρ] with n hn
  intro A hA
  obtain ⟨y,hy,hyfar⟩ := exists_far_of_diam A d hd hA (x n)
  refine ⟨h n y,mem_image_of_mem _ hy,?_⟩
  have hm : dist (h n y) (h n z₀)*((d/3)*d₀) ≤ C*r n := by
    calc
      _ = dist (h n y) (h n z₀)*(d/3)*d₀ := by ring
      _ ≤ dist (h n y) (h n z₀)*max (r n) (dist (x n) y)*
          max (r n) (dist (x n) z₀) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hyfar.trans (le_max_right _ _)) dist_nonneg
        · exact (hz₀ n).trans (le_max_right _ _)
        · exact hd₀.le
        · positivity
      _ ≤ C*r n*dist y z₀ := (hexp n y z₀).1
      _ ≤ C*r n := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hdiam y z₀) (mul_nonneg hC (hr n).le)
  have hynear : dist (h n y) (h n z₀) ≤ C*r n/((d/3)*d₀) := (le_div_iff₀ (mul_pos (div_pos hd (by norm_num)) hd₀)).mpr hm
  exact (dist_triangle (h n y) (h n z₀) b).trans_lt
    ((add_le_add hynear (le_refl (dist (h n z₀) b))).trans_lt hn)

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_EscapingLevelsAlong
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

namespace CannonVariation

open Set Metric Filter Topology

theorem exists_variation_path {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (F : X → ℝ) (x : X) (hx : NonconstantAt F x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ v w : X, ∃ γ : Path v w, range γ ⊆ U ∧ F v < F w := by
  classical
  let V := pathComponentIn U x
  have hVo : IsOpen V := hU.pathComponentIn x
  have hxV : x ∈ V := mem_pathComponentIn_self hxU
  have hy : ∃ y ∈ V, F y ≠ F x := by
    by_contra h
    push Not at h
    exact hx (Filter.mem_of_superset (hVo.mem_nhds hxV) h)
  obtain ⟨y,hyV,hyF⟩ := hy
  have hxy : JoinedIn U x y := hyV
  rcases lt_or_gt_of_ne hyF with hlt | hgt
  · exact ⟨y,x,hxy.symm.somePath,by
      rintro _ ⟨t,rfl⟩
      exact hxy.symm.somePath_mem t,hlt⟩
  · exact ⟨x,y,hxy.somePath,by
      rintro _ ⟨t,rfl⟩
      exact hxy.somePath_mem t,hgt⟩

end CannonVariation

namespace CannonComparison

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal CannonVariation

theorem comparison_across_punctures {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X) (hbc : b ≠ c)
    (hW : ContinuousOn W ({b}ᶜ : Set X)) (hV : ContinuousOn V ({c}ᶜ : Set X))
    (hfcont : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hwcont : ∀ K : Set X, IsCompact K → c ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (w n) K)
    (hflim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn f W atTop K)
    (hwlim : ∀ K : Set X, IsCompact K → c ∉ K → TendstoUniformlyOn w V atTop K)
    (hfe : ∀ K : Set X, IsCompact K → b ∉ K →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n) K) atTop (𝓝 0))
    (hwe : ∀ K : Set X, IsCompact K → c ∉ K →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n) K) atTop (𝓝 0))
    (hlevels : EscapingLevelsAlong f W b)
    (x : X) (hxb : x ≠ b) (hxc : x ≠ c) (hx : NonconstantAt W x) : V x = V b := by
  classical
  by_contra hneq
  let η := |V x-V b|/8
  have hη : 0 < η := div_pos (abs_pos.mpr (sub_ne_zero.mpr hneq)) (by norm_num)
  have hVx : ContinuousAt V x := hV.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hxc)
  obtain ⟨δx,hδx,hδxV⟩ := Metric.continuousAt_iff.mp hVx η hη
  let U : Set X := ball x δx ∩ {b}ᶜ ∩ {c}ᶜ
  have hU : IsOpen U := (isOpen_ball.inter isClosed_singleton.isOpen_compl).inter
    isClosed_singleton.isOpen_compl
  obtain ⟨v₀,v₁,γ,hγU,hγvar⟩ := exists_variation_path W x hx U hU ⟨⟨mem_ball_self hδx,hxb⟩,hxc⟩
  let P : Set X := range γ
  have hP : IsCompact P := isCompact_range γ.continuous
  have hbP : b ∉ P := fun h => (hγU h).1.2 rfl
  have hcP : c ∉ P := fun h => (hγU h).2 rfl
  have hPV : ∀ y ∈ P, 4*η ≤ |V y-V b| := by
    intro y hy
    have hxy := hδxV (hγU hy).1.1
    rw [Real.dist_eq] at hxy
    have hh := abs_sub_le (V x) (V y) (V b)
    rw [abs_sub_comm (V x) (V y)] at hh
    have ha := abs_nonneg (V x-V b)
    dsimp [η] at hxy ⊢
    linarith
  obtain ⟨a,d,e,hva,had,hdv,he,hegap⟩ := exists_interval_avoiding hγvar (W c)
  have hWc : ContinuousAt W c := hW.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hbc.symm)
  obtain ⟨δc,hδc,hδcW⟩ := Metric.continuousAt_iff.mp hWc (e/4) (by positivity)
  let ε := min (δc/2) (dist c b/4)
  have hε : 0 < ε := lt_min (by positivity) (div_pos (dist_pos.mpr hbc.symm) (by norm_num))
  have hεδ : ε < δc := (min_le_left _ _).trans_lt (by linarith)
  have hεdist : ε < dist c b := (min_le_right _ _).trans_lt (by have := dist_pos.mpr hbc.symm; linarith)
  let Cc : Set X := closedBall c ε
  have hCc : IsCompact Cc := isClosed_closedBall.isCompact
  have hbCc : b ∉ Cc := by
    intro h
    have hh := mem_closedBall.mp h
    rw [dist_comm] at hh
    exact (not_le_of_gt hεdist) hh
  have hcW : ∀ z ∈ Cc, |W z-W c| < e/4 := by
    intro z hz
    exact hδcW ((mem_closedBall.mp hz).trans_lt hεδ)
  have hcFn : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∀ z ∈ Cc, f n z ≠ t := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hflim Cc hCc hbCc) (e/4) (by positivity)] with n hn
    intro t ht z hz hzt
    have hh := hn z hz
    rw [Real.dist_eq,hzt,abs_sub_comm] at hh
    have hh' := abs_sub_le t (W z) (W c)
    have hg := hegap t ht
    have hwz := hcW z hz
    linarith
  obtain ⟨y,hyP,hymin⟩ := hP.exists_isMinOn (range_nonempty _) (continuous_id.dist continuous_const).continuousOn
  have hyb : y ≠ b := fun h => hbP (h ▸ hyP)
  have hydist : 0 < dist y b := dist_pos.mpr hyb
  have hVb : ContinuousAt V b := hV.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hbc)
  obtain ⟨δb,hδb,hδbV⟩ := Metric.continuousAt_iff.mp hVb η hη
  let ρ := min (δb/2) (min (dist b c/4) (dist y b/2))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min
    (div_pos (dist_pos.mpr hbc) (by norm_num)) (by positivity))
  have hρδ : ρ < δb := (min_le_left _ _).trans_lt (by linarith)
  have hρdist : ρ < dist b c := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (by have := dist_pos.mpr hbc; linarith)
  have hρP : ∀ z ∈ P, ρ < dist z b := by
    intro z hz
    have hρy : ρ < dist y b := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
    exact hρy.trans_le (hymin hz)
  let Cb : Set X := closedBall b ρ
  have hCb : IsCompact Cb := isClosed_closedBall.isCompact
  have hcCb : c ∉ Cb := by
    intro h
    have hh := mem_closedBall.mp h
    rw [dist_comm] at hh
    exact (not_le_of_gt hρdist) hh
  have hbV : ∀ z ∈ Cb, |V z-V b| < η := by
    intro z hz
    exact hδbV ((mem_closedBall.mp hz).trans_lt hρδ)
  have hgap : ∀ᶠ n in atTop, ∀ z ∈ P, ∀ t, dist t b = ρ → η ≤ |w n z-w n t| := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hwlim P hP hcP) η hη,
      Metric.tendstoUniformlyOn_iff.mp (hwlim Cb hCb hcCb) η hη] with n hnP hnB
    intro z hz t ht
    have htB : t ∈ Cb := mem_closedBall.mpr ht.le
    have he₁ := hnP z hz
    have he₂ := hnB t htB
    rw [Real.dist_eq] at he₁ he₂
    have he₃ := hbV t htB
    have he₄ := hPV z hz
    have ha₁ := abs_sub_le (V z) (w n z) (V b)
    have ha₂ := abs_sub_le (w n t) (V t) (V b)
    rw [abs_sub_comm (w n t) (V t)] at ha₂
    have ha₃ := abs_sub_le (w n z) (w n t) (V b)
    linarith
  let K : Set X := {z | ρ ≤ dist z b ∧ ε ≤ dist z c}
  let L : Set X := {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c}
  have hK : IsCompact K := ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le continuous_const (continuous_id.dist continuous_const))).isCompact
  have hL : IsCompact L := ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le continuous_const (continuous_id.dist continuous_const))).isCompact
  have hbK : b ∉ K := by rintro ⟨h,_⟩; simp only [dist_self] at h; linarith
  have hcK : c ∉ K := by rintro ⟨_,h⟩; simp only [dist_self] at h; linarith
  have hbL : b ∉ L := by rintro ⟨h,_⟩; simp only [dist_self] at h; linarith
  have hcL : c ∉ L := by rintro ⟨_,h⟩; simp only [dist_self] at h; linarith
  have hKL : K ⊆ L := by rintro z ⟨h₁,h₂⟩; constructor <;> linarith
  have hCS : ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (2*r n) ⊆ L := by
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
  apply escaping_level_energy_obstruction ι p r hr hpnet f w (fun _ => L) b c ρ ε P hρP a d η had hη
    (Eventually.of_forall (fun _ => hKL)) hCS (hfcont L hL hbL) (hwcont L hL hcL) hgap _
    (hfe K hK hbK) (hwe K hK hcK)
  filter_upwards [hlevels v₀ v₁ γ a d ρ (fun z hz => (hγU hz).1.2) hva had hdv hρ,hcFn] with n hn hnC
  intro t ht
  obtain ⟨D,hD,hDconn,hDP,hDlev,hDesc⟩ := hn t ht
  refine ⟨D,hD,hDconn,hDP,hDlev,hDesc,?_⟩
  intro z hz
  by_contra hnz
  have hzC : z ∈ Cc := mem_closedBall.mpr (lt_of_not_ge hnz).le
  exact hnC t ht z hzC (hDlev z hz)

end CannonComparison

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Exhaustion
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

namespace CannonDiagonal

open Set Metric Filter Topology CannonApprox

lemma select_strictMono_of_eventually (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j (φ j) := by
  classical
  choose m hm using fun j => eventually_atTop.mp (hP j)
  let φ : ℕ → ℕ := fun j => Nat.rec (m 0) (fun k x => max (x+1) (m (k+1))) j
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ (fun j =>
    (Nat.lt_succ_self (φ j)).trans_le (Nat.le_max_left _ _))
  refine ⟨φ,hφ,fun j => hm j (φ j) ?_⟩
  cases j with
  | zero => exact le_rfl
  | succ j => exact Nat.le_max_right _ _

lemma exhaustion_isCompact {X : Type*} [MetricSpace X] [CompactSpace X]
    (b : X) (j : ℕ) : IsCompact (exhaustion b j) :=
  (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact

lemma not_mem_exhaustion {X : Type*} [MetricSpace X] (b : X) (j : ℕ) :
    b ∉ exhaustion b j := by
  simp only [exhaustion,mem_ofPred_eq,dist_self,not_le]
  positivity

lemma compact_eventually_subset_exhaustion {X : Type*} [MetricSpace X]
    (b : X) {K : Set X} (hK : IsCompact K) (hb : b ∉ K) :
    ∀ᶠ j in atTop, K ⊆ exhaustion b j := by
  by_cases hKn : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hKn (continuous_id.dist continuous_const).continuousOn
    have hpos : 0 < dist x b := dist_pos.mpr (fun h => hb (h ▸ hx))
    have ht : ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) < dist x b :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hpos
    filter_upwards [ht] with j hj
    intro y hy
    exact hj.le.trans (hmin hy)
  · simp only [not_nonempty_iff_eq_empty] at hKn
    simp [hKn]

lemma enlarged_cells_eventually_subset {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) (p : ∀ n, ι n → X) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (J : ℝ)
    {K S : Set X} (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (J*r n) ⊆ S := by
  obtain ⟨δ,hδ,hδS⟩ := hK.exists_thickening_subset_open hS hKS
  have ht : Tendsto (fun n => (J+2)*r n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hr :
      Tendsto (fun n => (J+2)*r n) atTop (𝓝 ((J+2)*0)))
  filter_upwards [ht.eventually_lt_const hδ] with n hn
  intro i hi z hz
  obtain ⟨x,hxi,hxK⟩ := hi
  apply hδS
  refine mem_thickening_iff.mpr ⟨x,hxK,?_⟩
  have hzx := dist_triangle z (p n i) x
  have hxball : dist (p n i) x < 2*r n := by
    simpa only [mem_ball,dist_comm] using hxi
  have hzball : dist z (p n i) ≤ J*r n := mem_closedBall.mp hz
  linarith

theorem common_mesh_diagonal {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (b : X) (S : ℕ → Set X) (hS : ∀ i, IsOpen (S i))
    (F : ℕ → X → ℝ) (W : X → ℝ) (G : ℕ → ℕ → X → ℝ)
    (hF : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn F W atTop K)
    (hdom : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ i in atTop, K ⊆ S i)
    (hG : ∀ i K, IsCompact K → K ⊆ S i →
      TendstoUniformlyOn (G i) (F i) atTop K)
    (hGbounded : ∀ i n, BddAbove (range (G i n)) ∧ BddBelow (range (G i n)))
    (hE : ∀ i K, IsCompact K → K ⊆ S i → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (G i n) K) atTop (𝓝 0)) :
    ∃ α N : ℕ → ℕ, StrictMono α ∧ StrictMono N ∧
      (∀ K : Set X, IsCompact K → b ∉ K →
        TendstoUniformlyOn (fun j => G (α j) (N j)) W atTop K) ∧
      (∀ K : Set X, IsCompact K → b ∉ K → ∀ J : ℝ, 0 < J →
        Tendsto (fun j => meshEnergy (p (N j)) (r (N j)) J (G (α j) (N j)) K)
          atTop (𝓝 0) ∧
        ∀ᶠ j in atTop, ∀ i, (ball (p (N j) i) (2*r (N j)) ∩ K).Nonempty →
          closedBall (p (N j) i) (J*r (N j)) ⊆ S (α j)) := by
  classical
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K : ℕ → Set X := exhaustion b
  have hK : ∀ j, IsCompact (K j) := exhaustion_isCompact b
  have hbK : ∀ j, b ∉ K j := not_mem_exhaustion b
  obtain ⟨α,hα,hαspec⟩ := select_strictMono_of_eventually
    (fun j i => K j ⊆ S i ∧ ∀ x ∈ K j, dist (W x) (F i x) < ε j) (by
      intro j
      exact (hdom _ (hK j) (hbK j)).and
        (Metric.tendstoUniformlyOn_iff.mp (hF _ (hK j) (hbK j)) _ (hε j)))
  obtain ⟨N,hN,hNspec⟩ := select_strictMono_of_eventually
    (fun j n => (∀ x ∈ K j, dist (F (α j) x) (G (α j) n x) < ε j) ∧
      meshEnergy (p n) (r n) ((j:ℝ)+1) (G (α j) n) (K j) < ε j ∧
      ∀ i, (ball (p n i) (2*r n) ∩ K j).Nonempty →
        closedBall (p n i) (((j:ℝ)+1)*r n) ⊆ S (α j)) (by
      intro j
      exact (Metric.tendstoUniformlyOn_iff.mp
          (hG (α j) _ (hK j) (hαspec j).1) _ (hε j)).and
        (((hE (α j) _ (hK j) (hαspec j).1 ((j:ℝ)+1) (by positivity)).eventually_lt_const
          (hε j)).and (enlarged_cells_eventually_subset ι p r hrlim _ (hK j)
          (hS (α j)) (hαspec j).1)))
  refine ⟨α,N,hα,hN,?_,?_⟩
  · intro T hT hbT
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    have ht : ∀ᶠ j in atTop, 2*ε j < η := by
      have hh : Tendsto (fun j => 2*ε j) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hεlim :
          Tendsto (fun j => 2*ε j) atTop (𝓝 (2*0)))
      exact hh.eventually_lt_const hη
    filter_upwards [compact_eventually_subset_exhaustion b hT hbT,ht] with j hj hjη
    intro x hx
    exact (dist_triangle (W x) (F (α j) x) (G (α j) (N j) x)).trans_lt
      ((add_lt_add ((hαspec j).2 x (hj hx)) ((hNspec j).1 x (hj hx))).trans_le
        (by linarith))
  · intro T hT hbT J hJ
    have htJ : ∀ᶠ j : ℕ in atTop, J ≤ (j:ℝ)+1 := by
      obtain ⟨m,hm⟩ := exists_nat_ge J
      filter_upwards [eventually_ge_atTop m] with j hj
      have hh : (m:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
      linarith
    have hsmall : ∀ᶠ j in atTop,
        meshEnergy (p (N j)) (r (N j)) J (G (α j) (N j)) T ≤ ε j := by
      filter_upwards [compact_eventually_subset_exhaustion b hT hbT,htJ] with j hj hjJ
      exact (meshEnergy_mono_set _ _ _ _ hj).trans
        ((meshEnergy_mono_radius _ _ (hr (N j)).le _ (hGbounded _ _).1
          (hGbounded _ _).2 _ hJ.le hjJ).trans (hNspec j).2.1.le)
    refine ⟨squeeze_zero' (Eventually.of_forall (fun j => meshEnergy_nonneg _ _ _ _ _))
      hsmall hεlim,?_⟩
    filter_upwards [compact_eventually_subset_exhaustion b hT hbT,htJ] with j hj hjJ
    intro i hi
    exact (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hjJ (hr (N j)).le)).trans
      ((hNspec j).2.2 i (hi.mono (inter_subset_inter_right _ hj)))

end CannonDiagonal

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_NormalizedLevelsEscape
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

namespace CannonComparison

open Set Metric Filter Topology CannonMagnification

theorem normalized_levels_escape {X : Type*} [MetricSpace X]
    (H : ℕ → X → ℝ) (Ω : Set X)
    (hH : ∀ n y, y ∈ Ω → H n y ∈ Icc (0:ℝ) 1)
    (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : X, ∀ γ : Path v w, range γ ⊆ Ω → H n v < τ → τ < H n w →
          (A ∩ range γ).Nonempty)
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (r : ℕ → ℝ)
    (C L d₀ : ℝ) (hC : 0 ≤ C) (hd₀ : 0 < d₀)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (r n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b))
    (c σ : ℕ → ℝ) (hσ : ∀ n, 0 < σ n) (W : X → ℝ)
    (hpre : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ n in atTop, (h n).symm '' K ⊆ Ω)
    (hlim : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn (fun n z => (H n ((h n).symm z)-c n)/σ n) W atTop K) :
    EscapingLevelsAlong (fun n z => (H n ((h n).symm z)-c n)/σ n) W b := by
  intro v w γ a d ρ hγ hva had hdw hρ
  have hP : IsCompact (range γ) := isCompact_range γ.continuous
  have hbP : b ∉ range γ := fun h => by simpa using hγ h
  have hvP : v ∈ range γ := ⟨0,γ.source⟩
  have hwP : w ∈ range γ := ⟨1,γ.target⟩
  have hvl : Tendsto (fun n => (H n ((h n).symm v)-c n)/σ n) atTop (𝓝 (W v)) :=
    (hlim _ hP hbP).tendsto_at hvP
  have hwl : Tendsto (fun n => (H n ((h n).symm w)-c n)/σ n) atTop (𝓝 (W w)) :=
    (hlim _ hP hbP).tendsto_at hwP
  filter_upwards [hvl.eventually_lt_const hva,hwl.eventually_const_lt hdw,hpre _ hP hbP,
    wide_level_images_escape h x z₀ b r C L d₁ d₀ hC hd₁ hd₀ hr hrlim hexp hz₀ hdiam hb ρ hρ]
    with n hnv hnw hnpre hnesc
  intro t ht
  let τ := c n+σ n*t
  have hvτ : H n ((h n).symm v) < τ := by
    have hh := (div_lt_iff₀ (hσ n)).mp (hnv.trans_le ht.1)
    dsimp [τ]; nlinarith
  have hτw : τ < H n ((h n).symm w) := by
    have hh := (lt_div_iff₀ (hσ n)).mp (ht.2.trans_lt hnw)
    dsimp [τ]; nlinarith
  have hτ : τ ∈ Ioo (0:ℝ) 1 :=
    ⟨(hH n _ (hnpre (mem_image_of_mem _ hvP))).1.trans_lt hvτ,
      hτw.trans_le (hH n _ (hnpre (mem_image_of_mem _ hwP))).2⟩
  obtain ⟨A,hA,hAconn,hAd,hAlev,hAhit⟩ := hlevels n τ hτ
  let γ' := γ.map (h n).symm.continuous
  have hγ' : range γ' ⊆ Ω := by
    rintro _ ⟨s,rfl⟩
    exact hnpre (mem_image_of_mem _ (mem_range_self s))
  obtain ⟨y,hyA,s,hs⟩ := hAhit _ _ γ' hγ' hvτ hτw
  refine ⟨(h n) '' A,hA.image (h n).continuous,
    hAconn.image _ (h n).continuous.continuousOn,?_,?_,hnesc A hAd⟩
  · refine ⟨h n y,mem_image_of_mem _ hyA,s,?_⟩
    have hh : (h n).symm (γ s) = y := hs
    exact ((h n).apply_symm_apply (γ s)).symm.trans (congrArg (h n) hh)
  · rintro z ⟨y,hy,rfl⟩
    rw [(h n).symm_apply_apply,hAlev y hy]
    apply (div_eq_iff (ne_of_gt (hσ n))).mpr
    dsimp [τ]
    ring

end CannonComparison

end
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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_UniformlyImage
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

namespace CannonComparison

open Set Metric Filter Topology CannonPacking CannonApprox CannonVariation CannonDiagonal

lemma uniformly_on_image {X Y : Type*} (g : Y → X) (F : ℕ → X → ℝ)
    (W : X → ℝ) (K : Set Y) (h : TendstoUniformlyOn F W atTop (g '' K)) :
    TendstoUniformlyOn (fun n => F n ∘ g) (W ∘ g) atTop K :=
  (h.comp g).mono (fun _ hx => mem_image_of_mem _ hx)

theorem fixed_transform_comparison {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f : ℕ → X → ℝ) (W : X → ℝ) (b : X)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hfbounded : ∀ n, BddAbove (range (f n)) ∧ BddBelow (range (f n)))
    (hfcont : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hflim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn f W atTop K)
    (hfe : ∀ K : Set X, IsCompact K → b ∉ K → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (f n) K) atTop (𝓝 0))
    (hlevels : EscapingLevelsAlong f W b)
    (g : X ≃ₜ X) (H B : ℝ) (hH : 0 < H) (hB : 0 < B)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (hgb : g b ≠ b) (z : X) (hzb : z ≠ b) (hzgb : z ≠ g b)
    (hz : NonconstantAt W z) : W (g.symm z) = W (g.symm b) := by
  have hpre (K : Set X) (hbK : g b ∉ K) : b ∉ g.symm '' K := by
    rintro ⟨y,hy,heq⟩
    have heq' : y = g b := by simpa only [g.apply_symm_apply] using congrArg g heq
    exact hbK (heq' ▸ hy)
  have hV : ContinuousOn (W ∘ g.symm) ({g b}ᶜ : Set X) := by
    apply hW.comp g.symm.continuous.continuousOn
    intro y hy heq
    change y ≠ g b at hy
    exact hy (by simpa only [g.apply_symm_apply] using congrArg g heq)
  have hwcont : ∀ K : Set X, IsCompact K → g b ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (f n ∘ g.symm) K := by
    intro K hK hbK
    filter_upwards [hfcont (g.symm '' K) (hK.image g.symm.continuous) (hpre K hbK)] with n hn
    exact hn.comp g.symm.continuous.continuousOn (fun y hy => mem_image_of_mem _ hy)
  exact comparison_across_punctures ι p r hr hrlim hpnet f (fun n => f n ∘ g.symm)
    W (W ∘ g.symm) b (g b) hgb.symm hW hV hfcont hwcont hflim
    (fun K hK hbK => uniformly_on_image g.symm f W K
      (hflim _ (hK.image g.symm.continuous) (hpre K hbK)))
    (fun K hK hbK => hfe K hK hbK 2 (by norm_num))
    (fun K hK hbK => transported_mesh_energy_tendsto Q CP H B hpack hCP hH hB g hg hginv
      ι p r hr hrlim hpsep hpnet f hfbounded b hfe K hK hbK 2 (by norm_num))
    hlevels z hzb hzgb hz

end CannonComparison

namespace CannonComparison

open Set Metric Filter Topology CannonPacking CannonApprox CannonVariation CannonDiagonal CannonMagnification

theorem magnified_transform_comparison {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n y, ∃ i, dist (p n i) y ≤ r n)
    (Ω : Set X) (hΩ : IsOpen Ω) (U : X → ℝ) (H : ℕ → X → ℝ)
    (hHrange : ∀ n y, H n y ∈ Icc (0:ℝ) 1)
    (hHcont : ∀ n, ContinuousOn (H n) Ω)
    (hHlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H U atTop K)
    (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : X, ∀ γ : Path v w, range γ ⊆ Ω → H n v < τ → τ < H n w →
          (A ∩ range γ).Nonempty)
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (q : ℕ → ℝ)
    (C L d₀ : ℝ) (hC : 0 ≤ C) (hd₀ : 0 < d₀)
    (hq : ∀ n, 0 < q n) (hqlim : Tendsto q atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (q n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀) (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b))
    (c sig : ℕ → ℝ) (hsig : ∀ n, 0 < sig n) (W : X → ℝ)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hpre : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ n in atTop, (h n).symm '' K ⊆ Ω)
    (hFlim : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn (fun n z => (U ((h n).symm z)-c n)/sig n) W atTop K)
    (hE : ∀ i K, IsCompact K → K ⊆ (h i) '' Ω → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (H n ∘ (h i).symm) K) atTop (𝓝 0)) :
    ∀ (g : X ≃ₜ X) (A B : ℝ), 0 < A → 0 < B →
      (∀ y z, dist (g y) (g z) ≤ A*dist y z) →
      (∀ y z, dist (g.symm y) (g.symm z) ≤ B*dist y z) →
      g b ≠ b → ∀ z, z ≠ b → z ≠ g b → NonconstantAt W z →
        W (g.symm z) = W (g.symm b) := by
  let S : ℕ → Set X := fun i => h i '' Ω
  let F : ℕ → X → ℝ := fun i z => (U ((h i).symm z)-c i)/sig i
  let G : ℕ → ℕ → X → ℝ := fun i n z => (H n ((h i).symm z)-c i)/sig i
  have hHbounded (n : ℕ) : BddAbove (range (H n)) ∧ BddBelow (range (H n)) := by
    constructor
    · exact ⟨1,by rintro _ ⟨z,rfl⟩; exact (hHrange n z).2⟩
    · exact ⟨0,by rintro _ ⟨z,rfl⟩; exact (hHrange n z).1⟩
  have hcompbounded (i n : ℕ) : BddAbove (range (H n ∘ (h i).symm)) ∧
      BddBelow (range (H n ∘ (h i).symm)) :=
    ⟨(hHbounded n).1.range_comp_right _,(hHbounded n).2.range_comp_right _⟩
  have hGbounded (i n : ℕ) : BddAbove (range (G i n)) ∧ BddBelow (range (G i n)) :=
    affine_range_bounded _ (hcompbounded i n).1 (hcompbounded i n).2 (c i) (sig i) (hsig i)
  have hpreimage (i : ℕ) (K : Set X) (hK : K ⊆ S i) : (h i).symm '' K ⊆ Ω := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,rfl⟩ := hK hz
    simpa only [(h i).symm_apply_apply] using hw
  have hdom : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ i in atTop, K ⊆ S i := by
    intro K hK hbK
    filter_upwards [hpre K hK hbK] with i hi
    intro z hz
    exact ⟨(h i).symm z,hi (mem_image_of_mem _ hz),(h i).apply_symm_apply z⟩
  have hG : ∀ i K, IsCompact K → K ⊆ S i → TendstoUniformlyOn (G i) (F i) atTop K := by
    intro i K hK hKS
    exact uniformly_affine _ _ K
      (uniformly_on_image (h i).symm H U K
        (hHlim _ (hK.image (h i).symm.continuous) (hpreimage i K hKS)))
      (c i) (sig i) (hsig i)
  have hGE : ∀ i K, IsCompact K → K ⊆ S i → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (G i n) K) atTop (𝓝 0) := by
    intro i K hK hKS J hJ
    exact meshEnergy_affine_tendsto ι p r (fun n => (hr n).le) J hJ.le
      (fun n => H n ∘ (h i).symm) (hcompbounded i) (c i) (sig i) (hsig i) K (hE i K hK hKS J hJ)
  obtain ⟨α,N,hα,hN,hlim,henergy⟩ := common_mesh_diagonal ι p r hr hrlim b S
    (fun i => (h i).isOpenMap _ hΩ) F W G hFlim hdom hG hGbounded hGE
  have hpre' : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ j in atTop, (h (α j)).symm '' K ⊆ Ω := by
    intro K hK hbK
    exact hα.tendsto_atTop.eventually (hpre K hK hbK)
  have hcont' : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ j in atTop, ContinuousOn (G (α j) (N j)) K := by
    intro K hK hbK
    filter_upwards [hpre' K hK hbK] with j hj
    exact ((hHcont (N j)).comp (h (α j)).symm.continuous.continuousOn
      (fun z hz => hj (mem_image_of_mem _ hz))).sub continuousOn_const |>.div_const _
  have hlevels' : EscapingLevelsAlong (fun j => G (α j) (N j)) W b :=
    normalized_levels_escape (fun j => H (N j)) Ω (fun j y _ => hHrange (N j) y)
      d₁ hd₁ (fun j => hlevels (N j)) (fun j => h (α j)) (x ∘ α) z₀ b (q ∘ α)
      C L d₀ hC hd₀ (fun j => hq (α j)) (hqlim.comp hα.tendsto_atTop)
      (fun j => hexp (α j)) (fun j => hz₀ (α j)) hdiam (hb.comp hα.tendsto_atTop)
      (c ∘ α) (sig ∘ α) (fun j => hsig (α j)) W hpre' hlim
  intro g A B hA hB hg hginv hgb z hzb hzgb hz
  exact fixed_transform_comparison Q CP hpack hCP (fun j => ι (N j))
    (fun j => p (N j)) (r ∘ N) (fun j => hr (N j)) (hrlim.comp hN.tendsto_atTop)
    (fun j => hpsep (N j)) (fun j => hpnet (N j)) (fun j => G (α j) (N j)) W b hW
    (fun j => hGbounded (α j) (N j)) hcont' hlim
    (fun K hK hbK J hJ => (henergy K hK hbK J hJ).1) hlevels'
    g A B hA hB hg hginv hgb z hzb hzgb hz

end CannonComparison

namespace CannonComparison

open Set Filter Topology CannonVariation

lemma nonconstantAt_pullback {X : Type*} [TopologicalSpace X] (F : X → ℝ)
    (s : X ≃ₜ X) (z : X) (hz : NonconstantAt (F ∘ s) z) : NonconstantAt F (s z) := by
  intro he
  apply hz
  exact s.continuous.continuousAt.tendsto.eventually he

theorem all_two_transform_comparison {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (W : X → ℝ) (b : X)
    (hc : ∀ g : G, ρ g b ≠ b → ∀ z, z ≠ b → z ≠ ρ g b → NonconstantAt W z →
      W (ρ g⁻¹ z) = W (ρ g⁻¹ b)) :
    ∀ s t : G, ρ s b ≠ ρ t b → ∀ z, z ≠ ρ s b → z ≠ ρ t b →
      NonconstantAt (fun z => W (ρ s⁻¹ z)) z → W (ρ t⁻¹ z) = W (ρ t⁻¹ (ρ s b)) := by
  intro s t hst z hzs hzt hz
  have hsimp (u : X) : ρ s⁻¹ (ρ s u) = u := by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
  have hsimp' (u : X) : ρ s (ρ s⁻¹ u) = u := by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.apply_symm_apply]
  have hgb : ρ (s⁻¹*t) b ≠ b := by
    intro he
    apply hst
    have hh := congrArg (ρ s) he
    simpa only [map_mul,Homeomorph.mul_apply,hsimp'] using hh.symm
  have hzb : ρ s⁻¹ z ≠ b := by
    intro he
    apply hzs
    simpa only [hsimp'] using congrArg (ρ s) he
  have hzg : ρ s⁻¹ z ≠ ρ (s⁻¹*t) b := by
    intro he
    apply hzt
    have hh := congrArg (ρ s) he
    simpa only [map_mul,Homeomorph.mul_apply,hsimp'] using hh
  have hnc := nonconstantAt_pullback W (ρ s⁻¹) z hz
  have hh := hc (s⁻¹*t) hgb (ρ s⁻¹ z) hzb hzg hnc
  simpa only [mul_inv_rev,inv_inv,map_mul,Homeomorph.mul_apply,hsimp'] using hh

end CannonComparison

end

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonVariation CannonComparison
open CannonPacking CannonApprox CannonCrossEnergy CannonCrossEnergyLocal Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_holder_scalar_impossible_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D)
    (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j)) →
    (∀ n y, ∃ i, dist (p n i) y ≤ r n) →
    ∀ (Ω O P : Set (Boundary D)), IsOpen Ω → IsOpen O → Oᶜ.Nonempty →
    closure O ⊆ Ω → IsCompact P → IsConnected P → P ⊆ O →
    ∀ f : C(Ω,ℝ), (∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v) →
    ∀ α : ℝ, 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) →
    ∀ (z₀ : Boundary D) (d₀ : ℝ), 0 < d₀ → (∀ x ∈ O, d₀ ≤ dist x z₀) →
    ∀ H : ℕ → Boundary D → ℝ,
    (∀ n y, H n y ∈ Icc (0:ℝ) 1) → (∀ n, ContinuousOn (H n) Ω) →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn H (onDomain f) atTop K) →
    ∀ d₁ : ℝ, 0 < d₁ →
    (∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set (Boundary D), IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : Boundary D, ∀ γ : Path v w, range γ ⊆ Ω →
          H n v < τ → τ < H n w → (A ∩ range γ).Nonempty) →
    (∀ g : G, ∀ K, IsCompact K → K ⊆ boundaryHomeomorph D ⟨δ,hδ⟩ g '' Ω →
      ∀ J : ℝ, 0 < J → Tendsto
        (fun n => meshEnergy (p n) (r n) J
          (H n ∘ (boundaryHomeomorph D ⟨δ,hδ⟩ g).symm) K) atTop (𝓝 0)) → False := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro ι hι p r hr hrlim hpsep hpnet Ω O P hΩ hO hOc hOΩ hP hPc hPO
    f hv α hα hholder z₀ d₀ hd₀ hsep H hHrange hHcont hHlim d₁ hd₁ hlevels hE
  obtain ⟨β,hβ,k,x,sig,b,W,hk,hx,hb,_hescape,hpre,hFlim,hWholder,hWvar⟩ :=
    boundary_holder_magnification D hδ φ Ω O P hΩ hO hOc hOΩ hP hPc hPO
      f hv α hα hholder z₀ d₀ hd₀ hsep
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let q : ℕ → ℝ := fun i => (a^(k i))⁻¹
  have hq : ∀ i, 0 < q i := fun i => by dsimp [q,a]; positivity
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  obtain ⟨Q,CP,_hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  have hlim : ∀ K : Set (Boundary D), IsCompact K → b ∉ K →
      TendstoUniformlyOn
        (fun i z => (onDomain f ((boundaryExpansion D hδ (x i) (k i)).symm z)-onDomain f (x i))/sig i)
        (onDomain W) atTop K := by
    intro K hK hbK
    exact uniform_onDomain _ W hFlim K hK (by intro z hz hzb; exact hbK (hzb ▸ hz))
  have hcomp := magnified_transform_comparison Q CP hpack hCP.le ι p r hr hrlim hpsep hpnet
    Ω hΩ (onDomain f) H hHrange hHcont hHlim d₁ hd₁ hlevels
    (fun i => boundaryExpansion D hδ (x i) (k i)) x z₀ b q
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) d₀ (by positivity) hd₀
    hq hqlim (fun i => boundaryExpansion_formula D hδ (x i) (k i))
    (fun i => hsep (x i) (hx i).1) (boundaryDist_le_one D hδ) hb
    (fun i => onDomain f (x i)) sig (fun i => (hx i).2) (onDomain W)
    (continuousOn_onDomain W)
    (fun K hK hbK => by
      filter_upwards [hpre K hK hbK] with i hi
      rintro z ⟨y,hy,rfl⟩
      exact hi y hy) hlim
    (fun i K hK hKS J hJ => hE ((boundaryBasedRay D (x i)).val (k i))⁻¹ K hK hKS J hJ)
  have hall := all_two_transform_comparison (boundaryAction D ⟨δ,hδ⟩) (onDomain W) b (by
    intro g hgb z hzb hzgb hz
    exact hcomp (boundaryHomeomorph D ⟨δ,hδ⟩ g)
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g+4*δ):ℕ)))
      (2*Real.exp (visualExponent δ * (2*(3*D.graph.dist 1 g⁻¹+4*δ):ℕ)))
      (by positivity) (by positivity) (boundaryTranslate_lipschitz_bound D hδ g)
      (boundaryTranslate_lipschitz_bound D hδ g⁻¹) hgb z hzb hzgb hz)
  apply boundary_second_magnification_obstruction D hδ φ b W
    (Real.log β/Real.log a) (div_pos (Real.log_pos hβ) (Real.log_pos ha)) ?_ hWvar hall
  intro K hK hKb
  let K' : Set ({b}ᶜ : Set (Boundary D)) := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (by simpa only [Subtype.range_coe] using hKb)
  obtain ⟨C,hC,hCh⟩ := hWholder K' hK'
  refine ⟨C,hC,?_⟩
  intro z w hz hw
  simpa only [Real.dist_eq] using hCh z hz w hw

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

theorem solution.{v, u_1} : type_of% @OAI.CannonRelease.boundary_holder_scalar_impossible_oai.{v, u_1} := @OAI.CannonRelease.boundary_holder_scalar_impossible_oai.{v, u_1}
