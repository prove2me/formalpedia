-- Prove2me | solution 1 for OAI.CannonRelease.boundary_modulus_subexponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:05:21.485988+00:00
-- url     : https://prove2.me/submissions/84e52235-729a-4556-b394-845e13785f9a

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonRelease_boundary_holder_scalar_impossible
import Theorems.Thm_OAI_CannonRelease_boundary_record_scalar_limit

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

local instance instSetoidBasedRay_2_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_3_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_10_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_12_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_27_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_29_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_31_rf55b5c_1 : Setoid (BasedRay D) := raySetoid D
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

theorem interval_energy_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Ioo a b,
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    (b - a)^2 ≤ (∑ i, (w i)^2) * (∑ i, (U i - L i)^2) := by
  have h := weighted_open_interval_cover L U w a b 1 hab hLU hw hcover
  simp only [one_mul] at h
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hab) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => U i - L i))

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

theorem annular_energy_transfer {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (R : α → Finset β) (S : α → Finset γ) (ω : β → ℝ) (ρ : γ → ℝ)
    (L U : α → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hω : ∀ j, 0 ≤ ω j) (_hρ : ∀ j, 0 ≤ ρ j) (hLU : ∀ i, L i ≤ U i)
    (hlocal : ∀ i, U i - L i ≤ ∑ j ∈ S i, ρ j)
    (kr kc lr lc : ℕ)
    (hRrow : ∀ i, (R i).card ≤ kr)
    (hRcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc)
    (hSrow : ∀ i, (S i).card ≤ lr)
    (hScol : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ lc)
    (hcover : ∀ t ∈ Ioo a b,
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => ∑ j ∈ R i, ω j) t) :
    (b-a)^2 ≤ ((kr:ℝ)*kc*lr*lc) * (∑ j, (ω j)^2) * (∑ j, (ρ j)^2) := by
  have henergy := interval_energy_cover L U (fun i => ∑ j ∈ R i, ω j) a b hab hLU
    (fun i => Finset.sum_nonneg (fun j _ => hω j)) hcover
  have hωE := overlap_energy R ω kr kc hRrow hRcol
  have hρE : (∑ i, (U i-L i)^2) ≤ (lr:ℝ)*lc*(∑ j, (ρ j)^2) := by
    apply le_trans _ (overlap_energy S ρ lr lc hSrow hScol)
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (sub_nonneg.mpr (hLU i)) (hlocal i) 2)
  have hmul := mul_le_mul hωE hρE
    (Finset.sum_nonneg (fun i _ => sq_nonneg (U i-L i))) (by positivity)
  calc
    _ ≤ ((kr:ℝ)*kc*(∑ j, (ω j)^2)) * ((lr:ℝ)*lc*(∑ j, (ρ j)^2)) := henergy.trans hmul
    _ = _ := by ring

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

theorem interval_cover_of_charging {α β : Type*} [Fintype α] [Fintype β]
    (R : α → Finset β) (w : β → ℝ) (L U : α → ℝ)
    (hw : ∀ j, 0 ≤ w j) (t : ℝ) (B : Finset β)
    (hB : 1 ≤ ∑ j ∈ B, w j)
    (hcharge : ∀ j ∈ B, ∃ i, t ∈ Icc (L i) (U i) ∧ j ∈ R i) :
    1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => ∑ j ∈ R i, w j) t := by
  classical
  let A := Finset.univ.filter (fun i => t ∈ Icc (L i) (U i))
  have hh := finite_charge_cover A B R w hw (by
    intro j hj
    obtain ⟨i, hit, hij⟩ := hcharge j hj
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, hij⟩)
  apply hB.trans (hh.trans_eq _)
  simp only [A, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t ∈ Icc (L i) (U i) <;> simp [hi]

end CannonAnnular

namespace CannonAnnular

theorem annular_net_charge {X Y α : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (q : α → X) (h : X → Y) (f : X → ℝ) (L U : α → ℝ)
    (x y z : X) (ξ : Y) (R r C t : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2) (hC : 0 ≤ C)
    (hy : R ≤ dist y x ∧ dist y x ≤ 2*R)
    (hnet : ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u x ≤ 3*R → dist v x ≤ 3*R →
      dist (h u) (h v) ≤ C / R * dist u v)
    (hξ : dist ξ (h y) ≤ 2 * (r / R))
    (hz : dist z y ≤ r / 4) (hf : f z = t)
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i)) :
    ∃ i, R/2 ≤ dist (q i) x ∧ dist (q i) x ≤ 3*R ∧
      t ∈ Icc (L i) (U i) ∧ dist ξ (h (q i)) ≤ (C+2)*(r/R) := by
  obtain ⟨i, hi⟩ := hnet
  have hqu : dist (q i) x ≤ 3*R := (dist_triangle (q i) y x).trans (by linarith [hy.2])
  have hql : R/2 ≤ dist (q i) x := by
    have hh := dist_triangle y (q i) x
    rw [dist_comm y (q i)] at hh
    linarith [hy.1]
  refine ⟨i, hql, hqu, ?_, ?_⟩
  · rw [← hf]
    apply hrange
    have hh := dist_triangle z y (q i)
    rw [dist_comm y (q i)] at hh
    linarith
  · have hqy : dist (h (q i)) (h y) ≤ C/R*r := by
      exact (hzoom _ _ hqu (by linarith [hy.2])).trans
        (mul_le_mul_of_nonneg_left hi (div_nonneg hC hR.le))
    have hh := dist_triangle ξ (h y) (h (q i))
    rw [dist_comm (h y) (h (q i))] at hh
    calc
      _ ≤ 2*(r/R) + C/R*r := hh.trans (add_le_add hξ hqy)
      _ = _ := by ring

theorem charged_center_in_annulus {X : Type*} [PseudoMetricSpace X]
    (x q p : X) (R d : ℝ) (hR : 0 ≤ R)
    (hq : R/2 ≤ dist q x ∧ dist q x ≤ 3*R)
    (hpq : dist p q ≤ d) (hd : d ≤ R/4) :
    R/4 ≤ dist p x ∧ dist p x ≤ 4*R := by
  constructor
  · have hh := dist_triangle q p x
    rw [dist_comm q p] at hh
    linarith [hq.1]
  · have hh := dist_triangle p q x
    linarith [hq.2]

end CannonAnnular

end

end

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

theorem annular_interval_cover {X Y α β : Type*} [MetricSpace X] [MetricSpace Y]
    [LocallyPathConnectedSpace X] [Fintype α] [Fintype β]
    (q : α → X) (ξ : β → Y) (h : X → Y) (hh : Continuous h)
    (f : X → ℝ) (L U : α → ℝ) (o : X) (R r C d₀ a b : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R/2) (hC : 0 ≤ C)
    (hnet : ∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
      dist (h u) (h v) ≤ C/R * dist u v)
    (hlarge : ∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
      R ≤ dist u v → d₀ ≤ dist (h u) (h v))
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/R) d₀ ω)
    (Clevel : ℝ → Set X)
    (hlevel : ∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
      4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
      ∀ z ∈ Clevel t, f z = t) :
    ∀ t ∈ Ioo a b, 1 ≤ ∑ i,
      (Icc (L i) (U i)).indicator
        (fun _ : ℝ => ∑ j ∈ Finset.univ.filter
          (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R)), ω j) t := by
  classical
  intro t ht
  obtain ⟨hc, hd, ⟨x, hx, hxr⟩, hf⟩ := hlevel t ht
  obtain ⟨y, hy, hyr⟩ := exists_outer_point o R hR.le hd
  let V : Set X := ⋃ z ∈ Clevel t, ball z (r/4)
  have hV : IsOpen V := isOpen_iUnion (fun z => isOpen_iUnion (fun _ => isOpen_ball))
  have hCV : Clevel t ⊆ V := by
    intro z hz
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, by simp [hr]⟩⟩
  obtain ⟨u, v, p, hpV, hu, hv, huv, hp⟩ := annular_path_near_continuum
    o R (2*R) (by linarith) (Clevel t) V hc hV hCV hx hy (by linarith) hyr
  let p' : Path (h u) (h v) := p.map hh
  have hmacro : d₀ ≤ diam (Set.range p') := by
    have hsep := hlarge u v (by linarith) hv.le (by linarith)
    apply hsep.trans
    exact dist_le_diam_of_mem (isCompact_range p'.continuous).isBounded
      ⟨0, p'.source⟩ ⟨1, p'.target⟩
  have hadm := hω.2 (h u) (h v) p' hmacro
  apply interval_cover_of_charging _ ω L U hω.1 t (pathCellIndices ξ (r/R) p') hadm
  intro j hj
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hj).2
  change dist (h (p s)) (ξ j) < 2*(r/R) at hs
  have hsV := hpV (Set.mem_range_self s)
  obtain ⟨z, hz⟩ := mem_iUnion.mp hsV
  obtain ⟨hzC, hzs⟩ := mem_iUnion.mp hz
  have hnear : dist z (p s) ≤ r/4 := by
    rw [mem_ball, dist_comm] at hzs
    exact hzs.le
  obtain ⟨i, _, _, hit, hij⟩ := annular_net_charge q h f L U o (p s) z (ξ j)
    R r C t hR hr.le hrR hC (hp s) (hnet (p s) (hp s).1 (hp s).2)
    hzoom (by simpa only [dist_comm] using hs.le) hnear (hf z hzC) hrange
  exact ⟨i, hit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩

end CannonAnnular

namespace CannonAnnular

open Metric

theorem annular_comparison {X Y α β γ : Type*} [MetricSpace X] [MetricSpace Y]
    [LocallyPathConnectedSpace X] [Fintype α] [Fintype β] [Fintype γ]
    (q : α → X) (ξ : β → Y) (p : γ → X) (h : X → Y) (hh : Continuous h)
    (f : X → ℝ) (L U : α → ℝ) (o : X) (R r C d d₀ a b : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R/2) (hC : 0 ≤ C)
    (hd : d ≤ R/4) (hab : a ≤ b) (hLU : ∀ i, L i ≤ U i)
    (hq : ∀ i, R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R)
    (hnet : ∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
      dist (h u) (h v) ≤ C/R * dist u v)
    (hlarge : ∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
      R ≤ dist u v → d₀ ≤ dist (h u) (h v))
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i))
    (ω : β → ℝ) (hω : MacroscopicAdmissible ξ (r/R) d₀ ω)
    (ρ : γ → ℝ) (hρ : ∀ j, 0 ≤ ρ j)
    (hlocal : ∀ i, U i - L i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ d), ρ j)
    (Clevel : ℝ → Set X)
    (hlevel : ∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
      4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
      ∀ z ∈ Clevel t, f z = t)
    (kr kc lr lc : ℕ)
    (hTrow : ∀ i, (Finset.univ.filter
      (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))).card ≤ kr)
    (hTcol : ∀ j, (Finset.univ.filter
      (fun i => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))).card ≤ kc)
    (hSrow : ∀ i, (Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ d)).card ≤ lr)
    (hScol : ∀ j, (Finset.univ.filter
      (fun i => dist (p j) (q i) ≤ d)).card ≤ lc) :
    (b-a)^2 ≤ ((kr:ℝ)*kc*lr*lc) * (∑ j, (ω j)^2) *
      (∑ j ∈ Finset.univ.filter
        (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  let T (i : α) := Finset.univ.filter
    (fun j => dist (ξ j) (h (q i)) ≤ (C+2)*(r/R))
  let S (i : α) := Finset.univ.filter (fun j => dist (p j) (q i) ≤ d)
  let A := Finset.univ.filter
    (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R)
  let w (j : γ) := if j ∈ A then ρ j else 0
  have hn : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    split_ifs
    · exact hρ j
    · exact le_rfl
  have hloc : ∀ i, U i - L i ≤ ∑ j ∈ S i, w j := by
    intro i
    apply (hlocal i).trans_eq
    apply Finset.sum_congr rfl
    intro j hj
    have hja : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      charged_center_in_annulus o (q i) (p j) R d hR.le (hq i)
        (Finset.mem_filter.mp hj).2 hd⟩
    simp [w, hja]
  have hcover := annular_interval_cover q ξ h hh f L U o R r C d₀ a b
    hR hr hrR hC hnet hzoom hlarge hrange ω hω Clevel hlevel
  have henergy := annular_energy_transfer T S ω w L U a b hab hω.1 hn hLU
    hloc kr kc lr lc hTrow (by simpa [T] using hTcol)
    hSrow (by simpa [S] using hScol) hcover
  have hwE : (∑ j, (w j)^2) = ∑ j ∈ A, (ρ j)^2 := by
    simp [w]
  rw [hwE] at henergy
  exact henergy

end CannonAnnular

open Set Metric

namespace CannonAnnular

open CannonPacking Metric

theorem exists_packed_annular_constant {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (Q : ℕ) (CP C c A : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 < A) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
      (q : α → X) (ξ : β → X) (p : γ → X) (h : X → X), Continuous h →
      ∀ (f : X → ℝ) (L U : α → ℝ) (o : X) (R r d₀ a b : ℝ),
      0 < R → 0 < r → r ≤ R/2 → A*r ≤ R/4 →
      max (C+2) (max c 1)*(r/R) ≤ 1 → max A 1*r ≤ 1 →
      a ≤ b → (∀ i, L i ≤ U i) →
      (∀ i, R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → r/R ≤ dist (ξ i) (ξ j)) →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ y, R ≤ dist y o → dist y o ≤ 2*R → ∃ i, dist (q i) y ≤ r) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        dist (h u) (h v) ≤ C/R * dist u v) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        c/R * dist u v ≤ dist (h u) (h v)) →
      (∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
        R ≤ dist u v → d₀ ≤ dist (h u) (h v)) →
      (∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i)) →
      ∀ (ω : β → ℝ), MacroscopicAdmissible ξ (r/R) d₀ ω →
      ∀ (ρ : γ → ℝ), (∀ j, 0 ≤ ρ j) →
      (∀ i, U i-L i ≤ ∑ j ∈ Finset.univ.filter
        (fun j => dist (p j) (q i) ≤ A*r), ρ j) →
      ∀ (Clevel : ℝ → Set X),
      (∀ t ∈ Ioo a b, IsPreconnected (Clevel t) ∧
        4*R < diam (Clevel t) ∧ (∃ x ∈ Clevel t, dist x o ≤ R/2) ∧
        ∀ z ∈ Clevel t, f z = t) →
      (b-a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  have hC2 : 0 < C+2 := by linarith
  obtain ⟨kr, hkr⟩ := exists_overlap_bound Q CP (C+2) 1 hpack hCP hC2 zero_lt_one
  obtain ⟨kc, hkc⟩ := exists_overlap_bound Q CP (C+2) c hpack hCP hC2 hc
  obtain ⟨lr, hlr⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  obtain ⟨lc, hlc⟩ := exists_overlap_bound Q CP A 1 hpack hCP hA zero_lt_one
  refine ⟨(kr:ℝ)*kc*lr*lc, by positivity, ?_⟩
  intro α β γ _ _ _ q ξ p h hh f L U o R r d₀ a b hR hr hrR hAr
    hscaleT hscaleS hab hLU hq hqsep hξsep hpsep hnet hzoom hlow hlarge
    hrange ω hω ρ hρ hlocal Clevel hlevel
  have hrdiv : 0 < r/R := div_pos hr hR
  have hscale1 : max (C+2) 1*(r/R) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_right ..)) hrdiv.le).trans hscaleT
  have hscalec : max (C+2) c*(r/R) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (max_le_max le_rfl (le_max_left ..)) hrdiv.le).trans hscaleT
  have hrow (i : α) := hkr (ι := β) ξ Finset.univ (h (q i)) (r/R) hrdiv hscale1
    (by simpa using hξsep)
  have himsep (i j : α) (hne : i ≠ j) : c*(r/R) ≤ dist (h (q i)) (h (q j)) := by
    calc
      c*(r/R) = c/R*r := by ring
      _ ≤ c/R*dist (q i) (q j) :=
        mul_le_mul_of_nonneg_left (hqsep i j hne) (div_nonneg hc.le hR.le)
      _ ≤ dist (h (q i)) (h (q j)) := hlow _ _ (hq i).2 (hq j).2
  have hcol (j : β) := hkc (ι := α) (fun i => h (q i)) Finset.univ (ξ j) (r/R)
    hrdiv hscalec (by simpa using himsep)
  have hsrow (i : α) := hlr (ι := γ) p Finset.univ (q i) r hr hscaleS
    (by simpa using hpsep)
  have hscol (j : γ) := hlc (ι := α) q Finset.univ (p j) r hr hscaleS
    (by simpa using hqsep)
  exact annular_comparison q ξ p h hh f L U o R r C (A*r) d₀ a b
    hR hr hrR hC hAr hab hLU hq hnet hzoom hlarge hrange ω hω ρ hρ hlocal
    Clevel hlevel kr kc lr lc
    (by simpa only [dist_comm] using hrow) hcol
    (by simpa only [one_mul, dist_comm] using hsrow) hscol

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

end

end
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

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

lemma boundary_smallball_expansion :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ o : Boundary D, ∀ l : ℕ, ∃ h : Boundary D → Boundary D, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ CE/(a^l)⁻¹*dist u v ∧
        (1/(LE*3^2))/(a^l)⁻¹*dist u v ≤ dist (h u) (h v) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro o l
  refine ⟨boundaryExpansion D hδ o l,(boundaryExpansion D hδ o l).continuous,?_⟩
  intro u v hu hv
  apply expansion_ball_bounds (boundaryExpansion D hδ o l) o _ _ _ 3
    (by positivity) (by positivity) (by norm_num) (boundaryExpansion_formula D hδ o l) u v hu hv

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_Square
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonLevel.instPathConnectedSpaceSquare
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
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonPlanar

lemma continuous_clampSquare : Continuous clampSquare :=
  (continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd)

lemma clampSquare_coe (z : Square) : clampSquare (z.1, z.2) = z := by
  ext <;> simp [clampSquare, projIcc_of_mem, z.1.property, z.2.property]

theorem square_root {g : Square → ℂ} (hg : Continuous g) (h0 : ∀ z, g z ≠ 0) :
    ∃ f : Square → ℂ, Continuous f ∧ ∀ z, f z ^ 2 = g z := by
  let G : ℝ × ℝ → ℂ := g ∘ clampSquare
  have hG : Continuous G := hg.comp continuous_clampSquare
  have huc : IsSimplyConnected (univ : Set (ℝ × ℝ)) := by
    let : ContractibleSpace (univ : Set (ℝ × ℝ)) :=
      (convex_univ : Convex ℝ (univ : Set (ℝ × ℝ))).contractibleSpace univ_nonempty
    change SimplyConnectedSpace (univ : Set (ℝ × ℝ))
    infer_instance
  obtain ⟨f, hf, hp⟩ := Complex.exists_continuousOn_pow_eq huc isOpen_univ
    hG.continuousOn (by rintro ⟨z, _, hz⟩; exact h0 _ hz) (n := 2) (by decide)
  refine ⟨fun z => f (z.1, z.2), (continuousOn_univ.mp hf).comp ?_, ?_⟩
  · exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  · intro z
    simpa [G, Function.comp_def, clampSquare_coe] using hp (z.1, z.2)

lemma positive_everywhere {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) {x : X}
    (hx : 0 < f x) : ∀ y, 0 < f y := by
  intro y
  by_contra hn
  have hy : f y ≤ 0 := le_of_not_gt hn
  obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value
    (mem_univ y) (mem_univ x) hf.continuousOn ⟨hy, hx.le⟩
  exact h0 z hz

lemma squared_parts {g f : Square → ℂ} (hp : ∀ z, f z ^ 2 = g z) (z : Square) :
    (f z).re ^ 2 - (f z).im ^ 2 = (g z).re ∧
      2 * (f z).re * (f z).im = (g z).im := by
  have hr := congrArg Complex.re (hp z)
  have hi := congrArg Complex.im (hp z)
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  constructor <;> nlinarith

theorem square_zero {g : Square → ℂ} (hg : Continuous g)
    (hL : ∀ t, (g (0, t)).re ≤ 0) (hR : ∀ t, 0 ≤ (g (1, t)).re)
    (hB : ∀ s, (g (s, 0)).im ≤ 0) (hT : ∀ s, 0 ≤ (g (s, 1)).im) :
    ∃ z, g z = 0 := by
  by_contra hn
  have h0 : ∀ z, g z ≠ 0 := by simpa only [not_exists] using hn
  obtain ⟨f, hf, hp⟩ := square_root hg h0
  have fnz : ∀ z, (f z).re ≠ 0 ∨ (f z).im ≠ 0 := by
    intro z
    by_contra hz
    simp only [not_or, not_not] at hz
    have : f z = 0 := Complex.ext hz.1 hz.2
    exact h0 z (by rw [← hp z, this]; simp)
  have hright : ∀ t, (f (1, t)).re ≠ 0 := by
    intro t ht
    have he := (squared_parts hp (1, t)).1
    have h := hR t
    have hi : (f (1, t)).im = 0 := by nlinarith [sq_nonneg (f (1, t)).im]
    exact (fnz (1, t)).elim (fun hh => hh ht) (fun hh => hh hi)
  have hleft : ∀ t, (f (0, t)).im ≠ 0 := by
    intro t ht
    have he := (squared_parts hp (0, t)).1
    have h := hL t
    have hr : (f (0, t)).re = 0 := by nlinarith [sq_nonneg (f (0, t)).re]
    exact (fnz (0, t)).elim (fun hh => hh hr) (fun hh => hh ht)
  have hbottom : ∀ s, (f (s, 0)).re - (f (s, 0)).im ≠ 0 := by
    intro s hs
    have he := (squared_parts hp (s, 0)).2
    have h := hB s
    have hr : (f (s, 0)).re = 0 := by nlinarith [sq_nonneg (f (s, 0)).re]
    have hi : (f (s, 0)).im = 0 := by linarith
    exact (fnz (s, 0)).elim (fun hh => hh hr) (fun hh => hh hi)
  have htop : ∀ s, (f (s, 1)).re + (f (s, 1)).im ≠ 0 := by
    intro s hs
    have he := (squared_parts hp (s, 1)).2
    have h := hT s
    have hr : (f (s, 1)).re = 0 := by nlinarith [sq_nonneg (f (s, 1)).re]
    have hi : (f (s, 1)).im = 0 := by linarith
    exact (fnz (s, 1)).elim (fun hh => hh hr) (fun hh => hh hi)
  have impossible : ∀ f : Square → ℂ, Continuous f →
      (∀ z, f z ^ 2 = g z) →
      (∀ t, (f (1,t)).re ≠ 0) → (∀ t, (f (0,t)).im ≠ 0) →
      (∀ s, (f (s,0)).re - (f (s,0)).im ≠ 0) →
      (∀ s, (f (s,1)).re + (f (s,1)).im ≠ 0) →
      0 < (f (1,0)).re → False := by
    intro f hf hp hright hleft hbottom htop hr0
    have hr1 : 0 < (f (1,1)).re := positive_everywhere
      (Complex.continuous_re.comp (hf.comp (continuous_const.prodMk continuous_id))) hright hr0 1
    have hbim : (f (1,0)).im ≤ 0 := by
      have he := (squared_parts hp (1,0)).2
      have h := hB 1
      nlinarith
    have hbd : 0 < (f (0,0)).re - (f (0,0)).im := positive_everywhere
      ((Complex.continuous_re.comp (hf.comp (continuous_id.prodMk continuous_const))).sub
        (Complex.continuous_im.comp (hf.comp (continuous_id.prodMk continuous_const)))) hbottom
      (show 0 < (f (1,0)).re - (f (1,0)).im by linarith) 0
    have hli0 : (f (0,0)).im < 0 := by
      have he := (squared_parts hp (0,0)).1
      have h := hL 0
      by_contra hh
      have hh' := le_of_not_gt hh
      nlinarith [sq_nonneg ((f (0,0)).re - (f (0,0)).im)]
    have hli1 : (f (0,1)).im < 0 := by
      have hh := positive_everywhere
        (Complex.continuous_im.comp (hf.comp (continuous_const.prodMk continuous_id))).neg
        (fun t => neg_ne_zero.mpr (hleft t)) (neg_pos.mpr hli0) 1
      change 0 < -(f (0,1)).im at hh
      linarith
    have hlr1 : (f (0,1)).re ≤ 0 := by
      have he := (squared_parts hp (0,1)).2
      have h := hT 0
      nlinarith
    have hts : (f (1,1)).re + (f (1,1)).im < 0 := by
      have hh := positive_everywhere
        (((Complex.continuous_re.comp (hf.comp (continuous_id.prodMk continuous_const))).add
          (Complex.continuous_im.comp (hf.comp (continuous_id.prodMk continuous_const)))).neg)
        (fun s => neg_ne_zero.mpr (htop s))
        (show 0 < -((f (0,1)).re + (f (0,1)).im) by linarith) 1
      change 0 < -((f (1,1)).re + (f (1,1)).im) at hh
      linarith
    have hri1 : 0 ≤ (f (1,1)).im := by
      have he := (squared_parts hp (1,1)).2
      have h := hT 1
      nlinarith
    linarith
  rcases lt_or_gt_of_ne (hright 0) with hneg | hpos
  · apply impossible (fun z => -f z) hf.neg
    · intro z; simpa only [neg_sq] using hp z
    · intro t; exact neg_ne_zero.mpr (hright t)
    · intro t; exact neg_ne_zero.mpr (hleft t)
    · intro s; change -((f (s,0)).re) - -((f (s,0)).im) ≠ 0
      intro he; apply hbottom s; linarith
    · intro s; change -((f (s,1)).re) + -((f (s,1)).im) ≠ 0
      intro he; apply htop s; linarith
    · simpa using neg_pos.mpr hneg
  · exact impossible f hf hp hright hleft hbottom htop hpos

lemma continuous_toComplex : Continuous toComplex := by unfold toComplex; fun_prop

lemma toComplex_re (z : Square) : (toComplex z).re = (z.1 : ℝ) := by simp [toComplex]

lemma toComplex_im (z : Square) : (toComplex z).im = (z.2 : ℝ) := by simp [toComplex]

lemma toComplex_injective : Function.Injective toComplex := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [toComplex_re, toComplex_im] at hr hi
  exact Prod.ext (Subtype.ext hr) (Subtype.ext hi)

theorem paths_cross {p q : I → Square} (hp : Continuous p) (hq : Continuous q)
    (hp0 : (p 0).1 = 0) (hp1 : (p 1).1 = 1)
    (hq0 : (q 0).2 = 1) (hq1 : (q 1).2 = 0) :
    ∃ s t, p s = q t := by
  let g : Square → ℂ := fun z => toComplex (p z.1) - toComplex (q z.2)
  have hg : Continuous g := (continuous_toComplex.comp (hp.comp continuous_fst)).sub
    (continuous_toComplex.comp (hq.comp continuous_snd))
  have hr (s t : I) : (g (s,t)).re = (p s).1 - (q t).1 := by
    simp [g, toComplex_re]
  have hi (s t : I) : (g (s,t)).im = (p s).2 - (q t).2 := by
    simp [g, toComplex_im]
  obtain ⟨⟨s,t⟩, hz⟩ := square_zero hg
    (fun t => by rw [hr, hp0]; simpa using (q t).1.property.1)
    (fun t => by rw [hr, hp1]; simpa using (q t).1.property.2)
    (fun s => by rw [hi, hq0]; simpa using (p s).2.property.2)
    (fun s => by rw [hi, hq1]; simpa using (p s).2.property.1)
  exact ⟨s, t, toComplex_injective (sub_eq_zero.mp hz)⟩

theorem connected_joinedIn_open {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {K V : Set X} (hK : IsPreconnected K)
    (hV : IsOpen V) (hKV : K ⊆ V) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    JoinedIn V x y := by
  let : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  let f : K → V := fun z => ⟨z.val, hKV z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hconn : IsPreconnected (range f) := isPreconnected_range hf
  have hmem : f ⟨y,hy⟩ ∈ connectedComponent (f ⟨x,hx⟩) :=
    hconn.subset_connectedComponent ⟨⟨x,hx⟩, rfl⟩ ⟨⟨y,hy⟩, rfl⟩
  rw [← pathComponent_eq_connectedComponent] at hmem
  obtain ⟨p⟩ := hmem
  exact ⟨p.map continuous_subtype_val, fun t => (p t).property⟩

theorem continuum_crosses_path {K : Set Square} (hK : IsPreconnected K)
    {a b : Square} (ha : a ∈ K) (hb : b ∈ K) (ha0 : a.1 = 0) (hb1 : b.1 = 1)
    {q : I → Square} (hq : Continuous q) (hq0 : (q 0).2 = 1) (hq1 : (q 1).2 = 0) :
    ∃ t, q t ∈ K := by
  by_contra hn
  have hKV : K ⊆ (range q)ᶜ := by
    rintro x hx ⟨t, rfl⟩
    exact hn ⟨t, hx⟩
  obtain ⟨p, hp⟩ := connected_joinedIn_open hK
    (isCompact_range hq).isClosed.isOpen_compl hKV ha hb
  obtain ⟨s,t,hst⟩ := paths_cross p.continuous hq
    (by simpa using ha0) (by simpa using hb1) hq0 hq1
  exact hp s ⟨t, hst.symm⟩

lemma clopen_neighborhood_of_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X} (hU : IsOpen U)
    (hC : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let S := {s : Set X // IsClopen s ∧ x ∈ s}
  have hnull : Disjoint Uᶜ (⋂ s : S, (s : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_compl_left_iff_subset.mpr hC
  obtain ⟨T, hT⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : S => (s : Set X)) (fun s => s.property.1.isClosed)
    (Set.disjoint_iff_inter_eq_empty.mp hnull)
  refine ⟨⋂ s ∈ T, (s : Set X), isClopen_biInter_finset (fun s _ => s.property.1),
    mem_iInter₂.mpr (fun s _ => s.property.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp (Set.disjoint_iff_inter_eq_empty.mpr hT)

lemma clopen_separator_of_components {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcomp : ∀ x ∈ A, connectedComponent x ⊆ Bᶜ) :
    ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B := by
  classical
  have hh (x : A) : ∃ W : Set X, IsClopen W ∧ x.val ∈ W ∧ W ⊆ Bᶜ :=
    clopen_neighborhood_of_component x.val hB.isOpen_compl (hcomp x.val x.property)
  choose W hW hxW hWB using hh
  have hcover : A ⊆ ⋃ x : A, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxW ⟨x,hx⟩⟩
  obtain ⟨T, hT⟩ := hA.isCompact.elim_finite_subcover W (fun x => (hW x).isOpen) hcover
  refine ⟨⋃ x ∈ T, W x, isClopen_biUnion_finset (fun x _ => hW x), hT, ?_⟩
  rw [disjoint_left]
  rintro z hz hzB
  obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hz
  exact hWB x hx hzB

theorem level_continuum {f : Square → ℝ} (hf : Continuous f) {c : ℝ}
    (hbottom : ∀ s, f (s,0) ≤ c) (htop : ∀ s, c ≤ f (s,1)) :
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧
      (∀ z ∈ C, f z = c) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) := by
  classical
  let Z : Set Square := {z | f z = c}
  have hZ : IsClosed Z := isClosed_eq hf continuous_const
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let A : Set Z := {z | z.val.1 = 0}
  let B : Set Z := {z | z.val.1 = 1}
  have hA : IsClosed A := isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hB : IsClosed B := isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hex : ∃ x ∈ A, ∃ y ∈ B, y ∈ connectedComponent x := by
    by_contra hn
    have hc : ∀ x ∈ A, connectedComponent x ⊆ Bᶜ := by
      intro x hx y hy hyB
      exact hn ⟨x,hx,y,hyB,hy⟩
    obtain ⟨W,hW,hAW,hWB⟩ := clopen_separator_of_components hA hB hc
    let L : Set Square := {z | z.1 = 0}
    let R : Set Square := {z | z.1 = 1}
    have hL : IsClosed L := isClosed_eq continuous_fst continuous_const
    have hR : IsClosed R := isClosed_eq continuous_fst continuous_const
    let C0 : Set Square := Subtype.val '' W ∪ L
    let C1 : Set Square := Subtype.val '' Wᶜ ∪ R
    have hC0 : IsClosed C0 := (hZ.isClosedMap_subtype_val W hW.isClosed).union hL
    have hC1 : IsClosed C1 := (hZ.isClosedMap_subtype_val Wᶜ hW.compl.isClosed).union hR
    have hd : Disjoint C0 C1 := by
      rw [disjoint_left]
      intro z hz0 hz1
      rcases hz0 with ⟨w,hw,hwz⟩ | hzL
      · rcases hz1 with ⟨v,hv,hvz⟩ | hzR
        · have hvw : v = w := Subtype.ext (hvz.trans hwz.symm)
          exact hv (hvw.symm ▸ hw)
        · apply disjoint_left.mp hWB hw
          change w.val.1 = 1
          rw [hwz]
          exact hzR
      · rcases hz1 with ⟨v,hv,hvz⟩ | hzR
        · apply hv
          apply hAW
          change v.val.1 = 0
          rw [hvz]
          exact hzL
        · have hn01 : (0 : I) ≠ 1 := by norm_num
          exact hn01 ((show z.1 = 0 from hzL).symm.trans hzR)
    obtain ⟨v,hv0,hv1,hvr⟩ := exists_continuous_zero_one_of_isClosed hC0 hC1 hd
    let g : Square → ℂ := fun z => ((2 * v z - 1 : ℝ) : ℂ) +
      ((f z - c : ℝ) : ℂ) * Complex.I
    have hg : Continuous g := by unfold g; fun_prop
    have hr (z) : (g z).re = 2 * v z - 1 := by simp [g]
    have hi (z) : (g z).im = f z - c := by simp [g]
    obtain ⟨z,hgz⟩ := square_zero hg
      (fun t => by rw [hr, hv0 (show (0,t) ∈ C0 from Or.inr rfl)]; norm_num)
      (fun t => by rw [hr, hv1 (show (1,t) ∈ C1 from Or.inr rfl)]; norm_num)
      (fun s => by rw [hi]; linarith [hbottom s])
      (fun s => by rw [hi]; linarith [htop s])
    have hre := congrArg Complex.re hgz
    have him := congrArg Complex.im hgz
    rw [hr, Complex.zero_re] at hre
    rw [hi, Complex.zero_im] at him
    have hz : z ∈ Z := by change f z = c; linarith
    by_cases hw : (⟨z,hz⟩ : Z) ∈ W
    · have he := hv0 (show z ∈ C0 from Or.inl ⟨⟨z,hz⟩,hw,rfl⟩)
      change v z = 0 at he
      linarith
    · have he := hv1 (show z ∈ C1 from Or.inl ⟨⟨z,hz⟩,hw,rfl⟩)
      change v z = 1 at he
      linarith
  obtain ⟨x,hx,y,hy,hyx⟩ := hex
  refine ⟨Subtype.val '' connectedComponent x,
    isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn, ?_, ?_, ?_⟩
  · rintro z ⟨w,hw,rfl⟩
    exact w.property
  · exact ⟨x.val, ⟨x,mem_connectedComponent,rfl⟩,hx⟩
  · exact ⟨y.val, ⟨y,hyx,rfl⟩,hy⟩

end CannonPlanar

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

theorem drain_path_variation [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) {x y : X} (p : Path x y) {m M : ℝ}
    (hp : ∀ t, f (p t) ∈ Icc m M) :
    |drain f A x - drain f A y| ≤ M - m := by
  have h := flood_path_variation (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) p
    (m := -M) (M := -m) (by intro t; constructor <;> linarith [(hp t).1, (hp t).2])
  simpa only [drain, neg_sub_neg, abs_sub_comm, neg_sub_neg] using h

theorem flood_strict_side [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, f x ≤ B) {x : X} {t : ℝ} (hxt : flood f A x < t) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, flood f A (p s) < t := by
  obtain ⟨c, hc, hct⟩ := (csInf_lt_iff (floodThresholds_bddBelow f A x)
    (floodThresholds_nonempty hA hfB x)).mp hxt
  obtain ⟨y, hy, p, hp⟩ := hc
  refine ⟨y, hy, p, fun s => ?_⟩
  exact (flood_le_of_path hy (suffix p s) (fun u => hp (max u s))).trans_lt hct

theorem drain_strict_side [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, B ≤ f x) {x : X} {t : ℝ} (hxt : t < drain f A x) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, t < drain f A (p s) := by
  have hnegb : ∀ z, -f z ≤ -B := fun z => neg_le_neg (hfB z)
  have hneg : flood (fun z => -f z) A x < -t := by dsimp [drain] at hxt; linarith
  obtain ⟨y, hy, p, hp⟩ := flood_strict_side hA hnegb hneg
  refine ⟨y, hy, p, fun s => ?_⟩
  dsimp [drain]
  have := hp s
  linarith

lemma drain_min_le [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, B ≤ f x) {x y : X} (p : Path x y) {m : ℝ}
    (hp : ∀ t, m ≤ f (p t)) : min m (drain f A y) ≤ drain f A x := by
  have h := flood_le_max (f := fun z => -f z) hA (B := -B)
    (fun z => neg_le_neg (hfB z)) p (M := -m) (fun t => neg_le_neg (hp t))
  rcases le_max_iff.mp h with h | h
  · exact (min_le_left _ _).trans (by dsimp [drain]; linarith)
  · exact (min_le_right _ _).trans (by dsimp [drain]; linarith)

lemma first_level_prefix {f : X → ℝ} (hf : Continuous f) {x y : X}
    (p : Path x y) {s : ℝ} (hx : s ≤ f x) (hy : f y ≤ s) :
    ∃ z : X, ∃ q : Path x z, f z = s ∧ ∀ t, s ≤ f (q t) := by
  let g : I → ℝ := f ∘ p
  have hg : Continuous g := hf.comp p.continuous
  have hgne : {t : I | g t = s}.Nonempty := by
    have hs : s ∈ Icc (g 1) (g 0) := by simpa [g] using And.intro hy hx
    obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) 0 hg hs
    exact ⟨t, ht⟩
  have hgc : IsCompact {t : I | g t = s} := (isClosed_eq hg continuous_const).isCompact
  obtain ⟨t₀, ht₀, hmin⟩ := hgc.exists_isMinOn hgne
    (continuous_subtype_val.continuousOn : ContinuousOn (fun t : I => (t : ℝ)) _)
  change g t₀ = s at ht₀
  have hbefore : ∀ u : I, u ≤ t₀ → s ≤ g u := by
    intro u hu
    by_contra hgus
    have hgus : g u < s := lt_of_not_ge hgus
    have huts : u < t₀ := lt_of_le_of_ne hu (by intro h; rw [h, ht₀] at hgus; exact lt_irrefl _ hgus)
    have hs : s ∈ Icc (g u) (g 0) := ⟨hgus.le, by simpa [g] using hx⟩
    obtain ⟨v, hv, hvs⟩ := intermediate_value_Icc'
      (show (0 : I) ≤ u from u.property.1) hg.continuousOn hs
    have htv : (t₀ : ℝ) ≤ v := hmin hvs
    have hvt : v < t₀ := hv.2.trans_lt huts
    exact (not_lt_of_ge htv) hvt
  refine ⟨p t₀, pathPrefix p t₀, ht₀, fun t => ?_⟩
  exact hbefore (min t t₀) (min_le_right _ _)

theorem regularized_low_side [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A B : Set X} (hA : A.Nonempty) (hB : B.Nonempty)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAtop : ∀ z ∈ A, f z = 0) {x : X} {t : ℝ} (ht : 0 < t)
    (hxt : drain (flood f A) B x < t) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, drain (flood f A) B (p s) < t := by
  let F := flood f A
  let H := drain F B
  have hF0 : ∀ z, 0 ≤ F z := fun z => (hf0 z).trans (le_flood hA hf1 z)
  have hHF : ∀ z, H z ≤ F z := drain_le hB hF0
  have hlow (z : X) (hz : F z < t) :
      ∃ y ∈ A, ∃ p : Path z y, ∀ s, H (p s) < t := by
    obtain ⟨y, hy, p, hp⟩ := flood_strict_side hA hf1 hz
    exact ⟨y, hy, p, fun s => (hHF _).trans_lt (hp s)⟩
  by_cases hxF : F x < t
  · exact hlow x hxF
  obtain ⟨s, hms, hst⟩ := exists_between (max_lt (show H x < t from hxt) ht)
  have hxs : H x < s := (le_max_left _ _).trans_lt hms
  have hs0 : 0 < s := (le_max_right _ _).trans_lt hms
  have hAcopy := hA
  obtain ⟨y, hy⟩ := hAcopy
  have hFy : F y = 0 := (flood_eq_on_band hA hf1 hy).trans (hAtop y hy)
  obtain ⟨z, q, hzs, hq⟩ := first_level_prefix (continuous_flood hA hf hf1)
    (PathConnectedSpace.somePath x y) (hst.le.trans (le_of_not_gt hxF))
    (by dsimp [F] at hFy; linarith)
  have hqH : ∀ u, H (q u) < t := by
    intro u
    have hm := drain_min_le hB hF0 (pathPrefix q u) (m := s)
      (fun v => hq (min v u))
    change min s (H (q u)) ≤ H x at hm
    have hle : H (q u) ≤ H x := by
      rcases le_total s (H (q u)) with h | h
      · rw [min_eq_left h] at hm
        exact False.elim ((not_le_of_gt hxs) hm)
      · simpa only [min_eq_right h] using hm
    exact hle.trans_lt hxt
  obtain ⟨w, hw, p, hp⟩ := hlow z (by simpa only [F, hzs] using hst)
  refine ⟨w, hw, q.trans p, fun u => ?_⟩
  have hu : (q.trans p) u ∈ range q ∪ range p := by
    rw [← Path.trans_range]
    exact mem_range_self u
  rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [← hv]; exact hqH v
  · rw [← hv]; exact hp v

end CannonRegularization

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

lemma path_bounds_of_pairwise {f : X → ℝ} (hf : Continuous f) {x y : X}
    (p : Path x y) {E : ℝ} (hE : ∀ s t, |f (p s)-f (p t)| ≤ E) :
    ∃ m M : ℝ, (∀ t, f (p t) ∈ Icc m M) ∧ M-m ≤ E := by
  obtain ⟨s,_,hs⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set I).Nonempty)
    (hf.comp p.continuous).continuousOn
  obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set I).Nonempty)
    (hf.comp p.continuous).continuousOn
  refine ⟨f (p s),f (p t),fun q => ⟨hs (mem_univ q),ht (mem_univ q)⟩,?_⟩
  exact (le_abs_self _).trans (hE t s)

theorem flood_drain_path_osc [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {A B : Set X}
    (hA : A.Nonempty) (hB : B.Nonempty) (hfI : ∀ x, f x ∈ Icc 0 1)
    {x y : X} (p : Path x y) {E : ℝ}
    (hE : ∀ s t, |f (p s)-f (p t)| ≤ E) :
    |drain (flood f A) B x-drain (flood f A) B y| ≤ E := by
  obtain ⟨m,M,hp,hmM⟩ := path_bounds_of_pairwise hf p hE
  have hupper : ∀ x, f x ≤ 1 := fun x => (hfI x).2
  have hg := continuous_flood hA hf hupper
  have hpair : ∀ s t, |flood f A (p s)-flood f A (p t)| ≤ E := by
    intro s t
    apply (flood_path_variation hA hupper (p.subpath s t) (m := m) (M := M) ?_).trans hmM
    intro q
    exact hp _
  obtain ⟨m',M',hp',hwidth⟩ := path_bounds_of_pairwise hg p hpair
  apply (drain_path_variation hB (B := 0) ?_ p hp').trans hwidth
  intro z
  exact (hfI z).1.trans (le_flood hA hupper z)

end CannonRegularization

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_LiftPath
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
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonChart

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma liftPath_apply (e : X → Y) (he : IsEmbedding e) {a b : X}
    (p : Path (e a) (e b)) (hp : ∀ t, p t ∈ range e) (t : unitInterval) :
    e (liftPath e he p hp t) = p t := by
  have hh := he.toHomeomorph.apply_symm_apply ⟨p t,hp t⟩
  exact congrArg Subtype.val hh

lemma lift_joinedIn (e : X → Y) (he : IsEmbedding e) {a b : X} {S : Set Y}
    (hS : S ⊆ range e) (hp : JoinedIn S (e a) (e b)) :
    JoinedIn (e ⁻¹' S) a b := by
  obtain ⟨p,hp⟩ := hp
  let hpr : ∀ t, p t ∈ range e := fun t => hS (hp t)
  refine ⟨liftPath e he p hpr,fun t => ?_⟩
  change e (liftPath e he p hpr t) ∈ S
  rw [liftPath_apply e he p hpr]
  exact hp t

end CannonChart

namespace CannonLevel

open CannonPlanar CannonRegularization

theorem separating_level {f : Square → ℝ} {A B : Set Square}
    (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAedge : ∀ s, (s,0) ∈ A) (hBedge : ∀ s, (s,1) ∈ B)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ A, f z = 0) (hBf : ∀ z ∈ B, f z = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let H := drain (flood f A) B
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧
      (∀ z ∈ C, H z = t) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) ∧
      (∀ {x y : Square} (p : Path x y), H x < t → t < H y →
        ∃ s, p s ∈ C) := by
  let F := flood f A
  let H := drain F B
  have hF0 : ∀ z, 0 ≤ F z := fun z => (hf0 z).trans (le_flood hA.nonempty hf1 z)
  have hFc : Continuous F := continuous_flood hA.nonempty hf hf1
  have hHc : Continuous H := continuous_drain hB.nonempty hFc hF0
  obtain ⟨hHr,hHA,hHB⟩ := regularized_values hA.nonempty hB.nonempty hf0 hf1 hAf hBf
  obtain ⟨C,hCc,hCn,hCH,⟨a,ha,ha0⟩,⟨b,hb,hb1⟩⟩ := level_continuum hHc
    (c := t) (fun s => by rw [show H (s,0) = 0 from hHA _ (hAedge s)]; exact ht0.le)
    (fun s => by rw [show H (s,1) = 1 from hHB _ (hBedge s)]; exact ht1.le)
  refine ⟨C,hCc,hCn,hCH,⟨a,ha,ha0⟩,⟨b,hb,hb1⟩,?_⟩
  intro x y p hx hy
  obtain ⟨u,hu,lo,hlo⟩ := regularized_low_side hA.nonempty hB.nonempty hf hf0 hf1 hAf ht0 hx
  obtain ⟨v,hv,hi,hhi⟩ := drain_strict_side hB.nonempty hF0 hy
  obtain ⟨qa,hqa⟩ := hA.joinedIn u hu (0,0) (hAedge 0)
  obtain ⟨qb,hqb⟩ := hB.joinedIn v hv (0,1) (hBedge 0)
  let low : Path x (0,0) := lo.trans qa
  let high : Path y (0,1) := hi.trans qb
  have hlow : ∀ s, H (low s) < t := by
    intro s
    have hs : low s ∈ range lo ∪ range qa := by rw [← Path.trans_range]; exact mem_range_self s
    rcases hs with ⟨r,hr⟩ | ⟨r,hr⟩
    · rw [← hr]; exact hlo r
    · rw [← hr, show H (qa r) = 0 from hHA _ (hqa r)]; exact ht0
  have hhigh : ∀ s, t < H (high s) := by
    intro s
    have hs : high s ∈ range hi ∪ range qb := by rw [← Path.trans_range]; exact mem_range_self s
    rcases hs with ⟨r,hr⟩ | ⟨r,hr⟩
    · rw [← hr]; exact hhi r
    · rw [← hr, show H (qb r) = 1 from hHB _ (hqb r)]; exact ht1
  let q := high.symm.trans (p.symm.trans low)
  obtain ⟨s,hs⟩ := continuum_crosses_path hCn.isPreconnected ha hb ha0 hb1 q.continuous
    (by simp [q]) (by simp [q])
  have hqs : q s ∈ range high.symm ∪ (range p.symm ∪ range low) := by
    rw [← Path.trans_range, ← Path.trans_range]
    exact mem_range_self s
  rcases hqs with ⟨r,hr⟩ | ⟨r,hr⟩ | ⟨r,hr⟩
  · have ht := hhigh (unitInterval.symm r)
    have he := hCH _ hs
    change H (high.symm r) > t at ht
    rw [hr,he] at ht
    exact False.elim (lt_irrefl _ ht)
  · exact ⟨unitInterval.symm r, hr.symm ▸ hs⟩
  · have ht := hlow r
    rw [hr,hCH _ hs] at ht
    exact False.elim (lt_irrefl _ ht)

theorem rectangle_separating_level {f : Square → ℝ}
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ topBand, f z = 0) (hBf : ∀ z ∈ bottomBand, f z = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let H := drain (flood f topBand) bottomBand
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧ C ⊆ centralRectangle ∧
      (∀ z ∈ C, H z = t) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) ∧
      (∀ {x y : Square} (p : Path x y), H x < t → t < H y → ∃ s, p s ∈ C) := by
  obtain ⟨C,hCc,hCn,hCH,hCl,hCr,hCs⟩ := separating_level topBand_pathConnected bottomBand_pathConnected
    (by intro s; change (0 : ℝ) ≤ 1 / 3; norm_num)
    (by intro s; change (2 : ℝ) / 3 ≤ 1; norm_num)
    hf hf0 hf1 hAf hBf ht0 ht1
  refine ⟨C,hCc,hCn,?_,hCH,hCl,hCr,hCs⟩
  obtain ⟨_,hHA,hHB⟩ := regularized_values topBand_pathConnected.nonempty
    bottomBand_pathConnected.nonempty hf0 hf1 hAf hBf
  intro z hz
  constructor
  · by_contra h
    have he := hHA z (show z ∈ topBand from (lt_of_not_ge h).le)
    rw [hCH z hz] at he
    exact (ne_of_gt ht0) he
  · by_contra h
    have he := hHB z (show z ∈ bottomBand from (lt_of_not_ge h).le)
    rw [hCH z hz] at he
    exact (ne_of_lt ht1) he

end CannonLevel

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Hat
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
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonGrid

theorem interpolate_variation (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z w : Square) (E : ℝ)
    (hf : ∀ i j, weight N z i ≠ 0 → weight N w j ≠ 0 →
      |f (vertex N hN i)-f (vertex N hN j)| ≤ E) :
    |interpolate N hN f z-interpolate N hN f w| ≤ E := by
  have hi : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) ∈
      Set.Icc (interpolate N hN f w-E) (interpolate N hN f w+E) := by
    intro i hi
    have hh := interpolate_bounds_of_support N hN f w
      (f (vertex N hN i)-E) (f (vertex N hN i)+E) (by
        intro j hj
        have hb := abs_sub_le_iff.mp (hf i j hi hj)
        constructor <;> linarith [hb.1,hb.2])
    constructor <;> linarith [hh.1,hh.2]
  have hh := interpolate_bounds_of_support N hN f z _ _ hi
  exact abs_sub_le_iff.mpr ⟨by linarith [hh.2],by linarith [hh.1]⟩

end CannonGrid

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_LocalOscillation
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
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonScalarLocal

open CannonGrid CannonCells CannonRegularization CannonChart

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

local instance instLocallyPathConnectedSpaceElemRealUnitInterval_solutions : LocallyPathConnectedSpace unitInterval :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

local instance instPathConnectedSpaceSquare : PathConnectedSpace Square :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem local_oscillation
    (e : Square → X) (he : Topology.IsEmbedding e)
    (L J r : ℝ) (hL : 1 ≤ L) (hJ : 0 < J) (hr : 0 < r)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (x : X) (hchart : Metric.ball x (L*(L*J+1)*r) ⊆ range e)
    (q : ι → X) (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (raw : Square → ℝ) (hrawI : ∀ z, raw z ∈ Icc 0 1)
    (hraw : ∀ a b : Square, ∀ p : Path a b,
      |raw a-raw b| ≤ cost (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ (range p))
    (N : ℕ) (hN : 0 < N)
    (hmesh : ∀ z : Square, ∀ i : Index N, weight N z i ≠ 0 →
      dist (e z) (e (vertex N hN i)) < r)
    (T B : Set Square) (hT : T.Nonempty) (hB : B.Nonempty)
    (a b : Square) (ha : dist x (e a) ≤ J*r) (hb : dist x (e b) ≤ J*r) :
    |drain (flood (interpolate N hN raw) T) B a -
      drain (flood (interpolate N hN raw) T) B b| ≤
      ∑ i ∈ Finset.univ.filter (fun i => dist (q i) x ≤ (L*(L*J+1)+3)*r), ρ i := by
  classical
  have hLp : 0 < L := by linarith
  have hinner : 0 < L*J+1 := by positivity
  have hrad : L*(J*r) ≤ L*(L*J+1)*r := by
    have hj : J ≤ L*J := le_mul_of_one_le_left hJ.le hL
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show J ≤ L*J+1 by linarith) hLp.le) hr.le
    simpa only [mul_assoc] using hh
  have hsmall : {z : X | dist x z < L*(J*r)} ⊆ range e := by
    intro z hz
    apply hchart
    rw [Metric.mem_ball,dist_comm]
    exact hz.trans_le hrad
  obtain ⟨p,hp⟩ := lift_joinedIn e he hsmall (hpaths x (e a) (e b) (J*r)
    (mul_pos hJ hr) ha hb)
  apply flood_drain_path_osc (continuous_interpolate N hN raw) hT hB
    (fun z => interpolate_bounds N hN raw hrawI z) p
  intro s t
  apply interpolate_variation
  intro i j hi hj
  have hvi : dist x (e (vertex N hN i)) ≤ (L*J+1)*r := by
    have hd := dist_triangle x (e (p s)) (e (vertex N hN i))
    have hh := hp s
    change dist x (e (p s)) < L*(J*r) at hh
    have hm := hmesh (p s) i hi
    nlinarith
  have hvj : dist x (e (vertex N hN j)) ≤ (L*J+1)*r := by
    have hd := dist_triangle x (e (p t)) (e (vertex N hN j))
    have hh := hp t
    change dist x (e (p t)) < L*(J*r) at hh
    have hm := hmesh (p t) j hj
    nlinarith
  have hlarge : {z : X | dist x z < L*((L*J+1)*r)} ⊆ range e := by
    intro z hz
    apply hchart
    simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_comm,mul_assoc] using hz
  obtain ⟨p',hp'⟩ := lift_joinedIn e he hlarge
    (hpaths x _ _ ((L*J+1)*r) (mul_pos hinner hr) hvi hvj)
  apply (hraw _ _ p').trans
  unfold cost
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨z,⟨u,rfl⟩,hcell⟩ := (mem_indices _ _ k).mp hk
    have hh := hp' u
    change dist x (e (p' u)) < L*((L*J+1)*r) at hh
    change dist (e (p' u)) (q k) < 2*r at hcell
    have ht := dist_triangle (q k) (e (p' u)) x
    rw [dist_comm (q k) (e (p' u)),dist_comm (e (p' u)) x] at ht
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    nlinarith
  · intro k _ _
    exact hρ k

end CannonScalarLocal

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_RawFunction
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
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonApprox

open CannonGrid CannonRegularization CannonLevel CannonCells CannonBands

variable {ι : Type*} [Fintype ι]

theorem scalar_level (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hcross : Admissible C ρ) (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ A : Set CannonGrid.Square, IsCompact A ∧ IsConnected A ∧ A ⊆ centralRectangle ∧
      (∀ z ∈ A, scalar C ρ n hn z = t) ∧ (∃ z ∈ A, z.1 = 0) ∧ (∃ z ∈ A, z.1 = 1) ∧
      (∀ {x y : CannonGrid.Square} (p : Path x y), scalar C ρ n hn x < t →
        t < scalar C ρ n hn y → ∃ s, p s ∈ A) := by
  obtain ⟨hf,hfI,hT,hB⟩ := initial_properties C ρ hρ hcross n hn
  exact rectangle_separating_level hf (fun z => (hfI z).1) (fun z => (hfI z).2) hT hB ht.1 ht.2

theorem scalar_local_oscillation {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e)
    (L J r : ℝ) (hL : 1 ≤ L) (hJ : 0 < J) (hr : 0 < r)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (x : X) (hchart : Metric.ball x (L*(L*J+1)*r) ⊆ range e)
    (q : ι → X) (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcross : Admissible (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ)
    (n : ℕ) (hn : 0 < n)
    (hmesh : ∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
      dist (e z) (e (vertex (3*n) (by omega) i)) < r)
    (a b : CannonGrid.Square) (ha : dist x (e a) ≤ J*r) (hb : dist x (e b) ≤ J*r) :
    let C := fun i => e ⁻¹' Metric.ball (q i) (2*r)
    |scalar C ρ n hn a-scalar C ρ n hn b| ≤
      ∑ i ∈ Finset.univ.filter (fun i => dist (q i) x ≤ (L*(L*J+1)+3)*r), ρ i := by
  let C := fun i => e ⁻¹' Metric.ball (q i) (2*r)
  obtain ⟨hrawI,_,_,hraw⟩ := rawFunction_properties C ρ hρ hcross
  exact CannonScalarLocal.local_oscillation e he L J r hL hJ hr hpaths x hchart q ρ hρ
    (rawFunction C ρ) hrawI hraw (3*n) (by omega) hmesh topBand bottomBand
    topBand_pathConnected.nonempty bottomBand_pathConnected.nonempty a b ha hb

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_SquareMapRange
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
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonCharts

lemma squareMap_range : range squareMap = Icc (1 : ℝ) 2 ×ˢ Icc (-6 : ℝ) 6 := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    change 1+(w.1:ℝ) ∈ Icc 1 2 ∧ 12*(w.2:ℝ)-6 ∈ Icc (-6) 6
    constructor <;> constructor <;> linarith [w.1.property.1,w.1.property.2,w.2.property.1,w.2.property.2]
  · rintro ⟨hx,hy⟩
    let u : unitInterval := ⟨z.1-1,by constructor <;> linarith [hx.1,hx.2]⟩
    let v : unitInterval := ⟨(z.2+6)/12,by constructor <;> linarith [hy.1,hy.2]⟩
    refine ⟨(u,v),?_⟩
    dsimp [squareMap,u,v]
    ext <;> dsimp <;> ring

end CannonCharts

open Set MeasureTheory
open scoped NNReal ENNReal

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_ChartSquareInterior
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
section
section
section
open Set Topology Metric unitInterval

namespace CannonCharts

lemma chart_square_interior_eq {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) :
    interior (range (e ∘ squareMap)) = e '' (Ioo (1:ℝ) 2 ×ˢ Ioo (-6:ℝ) 6) := by
  have hpre : e ⁻¹' range (e ∘ squareMap) = range squareMap := by
    ext z
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,he.injective hw⟩
    · rintro ⟨w,rfl⟩
      exact mem_range_self w
  have hi : e ⁻¹' interior (range (e ∘ squareMap)) = Ioo (1:ℝ) 2 ×ˢ Ioo (-6:ℝ) 6 := by
    rw [he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous,hpre,
      squareMap_range,interior_prod_eq,interior_Icc,interior_Icc]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨w,rfl⟩ := interior_subset hz
    exact ⟨squareMap w,hi ▸ hz,rfl⟩
  · rintro z ⟨w,hw,rfl⟩
    change w ∈ e ⁻¹' interior (range (e ∘ squareMap))
    rwa [hi]

lemma chart_square_pathConnected {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) : IsPathConnected (interior (range (e ∘ squareMap))) := by
  rw [chart_square_interior_eq e he]
  exact ((convex_Ioo (𝕜 := ℝ) (1:ℝ) 2).isPathConnected
    ⟨3/2,by norm_num⟩ |>.prod
    ((convex_Ioo (𝕜 := ℝ) (-6:ℝ) 6).isPathConnected
    ⟨0,by norm_num⟩)).image he.continuous

lemma chart_origin_outside_square {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) : e (0,0) ∉ interior (range (e ∘ squareMap)) := by
  intro hz
  rw [chart_square_interior_eq e he] at hz
  obtain ⟨w,hw,hwe⟩ := hz
  have hwz : w = (0,0) := he.injective hwe
  subst w
  norm_num at hw

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_Extend
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
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology

namespace CannonApprox

open CannonGrid CannonLevel CannonChart Metric

theorem exists_chart_lateral_diameter {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ A : Set CannonGrid.Square, IsCompact A →
      (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A) := by
  let l : Set CannonGrid.Square := {z | z.1 = 0}
  let r : Set CannonGrid.Square := {z | z.1 = 1}
  have hl : IsCompact l := (isClosed_eq continuous_fst continuous_const).isCompact
  have hr : IsCompact r := (isClosed_eq continuous_fst continuous_const).isCompact
  have hdis : Disjoint (e '' l) (e '' r) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy := he.injective (hxz.trans hyz.symm)
    have h01 : (0 : unitInterval) = 1 := hx.symm.trans ((congrArg Prod.fst hxy).trans hy)
    exact zero_ne_one h01
  obtain ⟨d,hd,hsep⟩ := Metric.exists_pos_forall_lt_edist
    (hl.image he.continuous) (hr.image he.continuous).isClosed hdis
  refine ⟨d,by exact_mod_cast hd,?_⟩
  intro A hA hAl hAr
  obtain ⟨x,hx,hxl⟩ := hAl
  obtain ⟨y,hy,hyr⟩ := hAr
  have hh := hsep (e x) ⟨x,hxl,rfl⟩ (e y) ⟨y,hyr,rfl⟩
  rw [edist_nndist] at hh
  have hdist : (d : ℝ) ≤ dist (e x) (e y) := by exact_mod_cast hh.le
  exact hdist.trans (dist_le_diam_of_mem (hA.image he.continuous).isBounded
    (mem_image_of_mem e hx) (mem_image_of_mem e hy))

theorem scalar_ambient_level {X : Type*} [MetricSpace X]
    (e : CannonGrid.Square → X) (he : Topology.IsEmbedding e)
    {ι : Type*} [Fintype ι] (C : ι → Set CannonGrid.Square) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hadm : Admissible C ρ) (n : ℕ) (hn : 0 < n)
    (d₁ : ℝ) (hd₁ : ∀ A : Set CannonGrid.Square, IsCompact A →
      (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A))
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ A ⊆ e '' centralRectangle ∧
      d₁ ≤ diam A ∧ (∀ z ∈ A, extend e (scalar C ρ n hn) z = t) ∧
      (∀ {a b : CannonGrid.Square} (p : Path (e a) (e b)),
        (∀ s, p s ∈ range e) → scalar C ρ n hn a < t → t < scalar C ρ n hn b →
        ∃ s, p s ∈ A) := by
  obtain ⟨A,hA,hcon,hcentral,hf,hl,hr,hhit⟩ := scalar_level C ρ hρ hadm n hn ht
  refine ⟨e '' A,hA.image he.continuous,hcon.image e he.continuous.continuousOn,
    image_mono hcentral,hd₁ A hA hl hr,?_,?_⟩
  · rintro z ⟨x,hx,rfl⟩
    rw [extend_apply e he.injective]
    exact hf x hx
  · intro a b p hp ha hb
    obtain ⟨s,hs⟩ := hhit (liftPath e he p hp) ha hb
    refine ⟨s,?_⟩
    rw [← liftPath_apply e he p hp s]
    exact mem_image_of_mem e hs

end CannonApprox

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

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

end CannonCrossEnergy

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_OscillationPairwise
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
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonScalarEnergy

open CannonCrossEnergy CannonPacking

lemma oscillation_le_of_pairwise {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A)
    {E : ℝ} (hE : 0 ≤ E) (hpair : ∀ x ∈ A, ∀ y ∈ A, |f x-f y| ≤ E) :
    oscillation f A ≤ E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simpa [CannonCrossEnergy.oscillation] using hE
  obtain ⟨x,hx,heqx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,heqy⟩ := (hA.image hf).sInf_mem (hne.image f)
  have hh := (le_abs_self (f x-f y)).trans (hpair x hx y hy)
  simpa only [CannonCrossEnergy.oscillation,← heqx,← heqy] using hh

lemma oscillation_nonneg_of_compact {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A) :
    0 ≤ oscillation f A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [CannonCrossEnergy.oscillation]
  · exact oscillation_nonneg hf hA hne

theorem uniform_local_energy_bound {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (Q : ℕ) (C A b : ℝ) (hp : PolynomialPacking (X := X) Q C)
    (hC : 0 ≤ C) (hA : 0 < A) (hb : 0 < b) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max A (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → b*r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        ∀ (f : Y → ℝ), Continuous f → ∀ (cells : α → Set Y),
        (∀ i, IsCompact (cells i)) → ∀ (ρ : β → ℝ), (∀ j, 0 ≤ ρ j) →
        (∀ i, ∀ x ∈ cells i, ∀ y ∈ cells i, |f x-f y| ≤
          ∑ j ∈ Finset.univ.filter (fun j => dist (q j) (centers i) ≤ A*r), ρ j) →
        (∑ i, (oscillation f (cells i))^2) ≤ E*(∑ j, (ρ j)^2) := by
  classical
  obtain ⟨Bq,hBq⟩ := exists_overlap_bound Q C A 1 hp hC hA zero_lt_one
  obtain ⟨Bp,hBp⟩ := exists_overlap_bound Q C A b hp hC hA hb
  refine ⟨(Bq:ℝ)*Bp,by positivity,?_⟩
  intro α β _ _ centers q r hr hscale hc hq f hf cells hcells ρ hρ hlocal
  let R : α → Finset β := fun i => Finset.univ.filter
    (fun j => dist (q j) (centers i) ≤ A*r)
  have hscaleq : max A 1*r ≤ 1 := (mul_le_mul_of_nonneg_right
    (max_le_max_left A (le_max_left 1 b)) hr.le).trans hscale
  have hscalep : max A b*r ≤ 1 := (mul_le_mul_of_nonneg_right
    (max_le_max_left A (le_max_right 1 b)) hr.le).trans hscale
  have hrow : ∀ i, (R i).card ≤ Bq := by
    intro i
    simpa only [R,dist_comm] using hBq q Finset.univ (centers i) r hr hscaleq
      (fun i _ j _ hij => by simpa using hq i j hij)
  have hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ Bp := by
    intro j
    simpa only [R,Finset.mem_filter,Finset.mem_univ,true_and] using
      hBp centers Finset.univ (q j) r hr hscalep (fun i _ j _ hij => hc i j hij)
  calc
    (∑ i, (oscillation f (cells i))^2) ≤ ∑ i, (∑ j ∈ R i, ρ j)^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (oscillation_nonneg_of_compact hf (hcells i))
        (oscillation_le_of_pairwise hf (hcells i)
          (Finset.sum_nonneg (fun j _ => hρ j)) (hlocal i)) 2
    _ ≤ (Bq:ℝ)*Bp*(∑ j, (ρ j)^2) :=
      CannonTransfer.overlap_energy R ρ Bq Bp hrow hcol

end CannonScalarEnergy

namespace CannonApprox

open CannonGrid CannonLevel CannonPacking CannonScalarEnergy CannonCrossEnergy CannonCells

theorem exists_scalar_energy_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (C L J b : ℝ) (hp : PolynomialPacking (X := X) Q C)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hJ : 0 < J) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : CannonGrid.Square → X), Topology.IsEmbedding e →
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max (L*(L*J+1)+3) (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → b*r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        (∀ i, Metric.ball (centers i) (L*(L*J+1)*r) ⊆ range e) →
        ∀ (ρ : β → ℝ), (∀ i, 0 ≤ ρ i) →
        Admissible (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ →
        ∀ (n : ℕ) (hn : 0 < n),
        (∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
          dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
        (∑ i, (CannonCrossEnergy.oscillation
          (scalar (fun j => e ⁻¹' Metric.ball (q j) (2*r)) ρ n hn)
          (e ⁻¹' Metric.closedBall (centers i) (J*r)))^2) ≤ E*(∑ j, (ρ j)^2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < L*(L*J+1)+3 := by positivity
  obtain ⟨E,hE,hbound⟩ := uniform_local_energy_bound (Y := CannonGrid.Square)
    Q C (L*(L*J+1)+3) b hp hC hA hb
  refine ⟨E,hE,?_⟩
  intro e he α β _ _ centers q r hr hscale hcenters hq hchart ρ hρ hadm n hn hmesh
  have hf := (scalar_properties _ ρ hρ hadm n hn).1
  apply hbound centers q r hr hscale hcenters hq _ hf
    (fun i => e ⁻¹' Metric.closedBall (centers i) (J*r))
    (fun i => (isClosed_closedBall.preimage he.continuous).isCompact) ρ hρ
  intro i x hx y hy
  exact scalar_local_oscillation e he L J r hL hJ hr hpaths (centers i) (hchart i)
    q ρ hρ hadm n hn hmesh x y (by simpa [dist_comm] using hx)
      (by simpa [dist_comm] using hy)

end CannonApprox

open Set Metric Topology

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ScalarAnnularConstant
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
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonApprox

open CannonGrid CannonChart CannonPacking CannonCrossEnergy CannonScalarEnergy CannonAnnular Metric

theorem exists_scalar_annular_constant {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : CannonGrid.Square → X), Topology.IsEmbedding e →
      ∀ (d₁ : ℝ), (∀ A : Set CannonGrid.Square, IsCompact A →
        (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A)) →
      ∀ {β γ : Type*} [Fintype β] [Fintype γ]
        (ξ : β → X) (p : γ → X) (h : X → X), Continuous h →
      ∀ (o : X) (R r d₀ s : ℝ),
      0 < R → R ≤ 1 → 4*R < d₁ → 0 < r → r ≤ R/2 →
      (L*(L*2+1)+3)*r ≤ R/4 →
      max (C+2) (max c 1)*(r/R) ≤ 1 →
      0 < s → L*s ≤ R/2 → Metric.ball o (4*R) ⊆ range e →
      (∀ i j, i ≠ j → r/R ≤ dist (ξ i) (ξ j)) →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ y : X, ∃ j, dist (p j) y ≤ r) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        dist (h u) (h v) ≤ C/R * dist u v) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        c/R * dist u v ≤ dist (h u) (h v)) →
      (∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
        R ≤ dist u v → d₀ ≤ dist (h u) (h v)) →
      ∀ (ω : β → ℝ), MacroscopicAdmissible ξ (r/R) d₀ ω →
      ∀ (ρ : γ → ℝ), (∀ j, 0 ≤ ρ j) →
      Admissible (fun j => e ⁻¹' Metric.ball (p j) (2*r)) ρ →
      ∀ (n : ℕ) (hn : 0 < n),
      (∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
        dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
      ∀ a b : CannonGrid.Square, dist o (e a) ≤ s → dist o (e b) ≤ s →
      let f := scalar (fun j => e ⁻¹' Metric.ball (p j) (2*r)) ρ n hn
      (f b-f a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  let A := L*(L*2+1)+3
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg L]
  obtain ⟨E,hE,hbound⟩ := exists_packed_annular_constant Q CP C c A hpack hCP hC hc hA
  refine ⟨E,hE,?_⟩
  intro e he d₁ hd₁ β γ _ _ ξ p h hh o R r d₀ s hR hRone hdR hr hrR hAr
    hscaleT hs hsR hchart hξsep hpsep hpnet hzoom hlow hlarge ω hω ρ hρ hadm n hn hmesh a b ha hb
  let Cells := fun j => e ⁻¹' Metric.ball (p j) (2*r)
  let f := scalar Cells ρ n hn
  have hf := (scalar_properties Cells ρ hρ hadm n hn).1
  have hfI := (scalar_properties Cells ρ hρ hadm n hn).2.1
  let α := {j : γ // R/2 ≤ dist (p j) o ∧ dist (p j) o ≤ 3*R}
  let q : α → X := fun i => p i.val
  have hq (i : α) : R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R := i.property
  have hqsep (i j : α) (hne : i ≠ j) : r ≤ dist (q i) (q j) :=
    hpsep i.val j.val (fun heq => hne (Subtype.ext heq))
  have hnet (y : X) (hy : R ≤ dist y o) (hy' : dist y o ≤ 2*R) :
      ∃ i : α, dist (q i) y ≤ r := by
    obtain ⟨j,hj⟩ := hpnet y
    have ht₁ := dist_triangle y (p j) o
    have ht₂ := dist_triangle (p j) y o
    rw [dist_comm y (p j)] at ht₁
    have hmem : R/2 ≤ dist (p j) o ∧ dist (p j) o ≤ 3*R := by constructor <;> linarith
    exact ⟨⟨j,hmem⟩,hj⟩
  have hchartq (i : α) : Metric.ball (q i) (L*(L*2+1)*r) ⊆ range e := by
    intro y hy
    apply hchart
    change dist y o < 4*R
    have ht := dist_triangle y (q i) o
    have hhq := (hq i).2
    change dist y (q i) < L*(L*2+1)*r at hy
    change A*r ≤ R/4 at hAr
    dsimp [A] at hAr
    nlinarith
  have hinner : 2 < L*(L*2+1) := by nlinarith [sq_nonneg (L-1)]
  have hclosedq (i : α) : Metric.closedBall (q i) (2*r) ⊆ range e := by
    intro y hy
    apply hchartq i
    change dist y (q i) < L*(L*2+1)*r
    exact (show dist y (q i) ≤ 2*r from hy).trans_lt (mul_lt_mul_of_pos_right hinner hr)
  let K (i : α) := e ⁻¹' Metric.closedBall (q i) (2*r)
  have hK (i : α) : IsCompact (K i) := (isClosed_closedBall.preimage he.continuous).isCompact
  have hKn (i : α) : (K i).Nonempty := by
    obtain ⟨x,hx⟩ := hclosedq i (Metric.mem_closedBall_self (by positivity : 0 ≤ 2*r))
    refine ⟨x,?_⟩
    change e x ∈ Metric.closedBall (q i) (2*r)
    rw [hx]
    exact Metric.mem_closedBall_self (by positivity)
  let lo := fun i => sInf (f '' K i)
  let hi := fun i => sSup (f '' K i)
  have hlu (i : α) : lo i ≤ hi i :=
    csInf_le_csSup ((hKn i).image f) ((hK i).image hf).bddBelow ((hK i).image hf).bddAbove
  have hrange (i : α) (z : X) (hz : dist z (q i) ≤ 2*r) :
      extend e f z ∈ Icc (lo i) (hi i) := by
    obtain ⟨x,rfl⟩ := hclosedq i hz
    rw [extend_apply e he.injective]
    exact mem_rangeInterval hf (hK i) hz
  have hlocal (i : α) : hi i-lo i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ A*r), ρ j := by
    apply oscillation_le_of_pairwise hf (hK i)
      (Finset.sum_nonneg (fun j _ => hρ j))
    intro x hx y hy
    exact scalar_local_oscillation e he L 2 r hL (by norm_num) hr hpaths (q i)
      (hchartq i) p ρ hρ hadm n hn hmesh x y
      (by simpa only [K,mem_preimage,mem_closedBall,dist_comm] using hx)
      (by simpa only [K,mem_preimage,mem_closedBall,dist_comm] using hy)
  have hscaleS : max A 1*r ≤ 1 := by
    rw [max_eq_left hAone]
    exact hAr.trans ((div_le_self hR.le (by norm_num : (1:ℝ) ≤ 4)).trans hRone)
  have hordered (a b : CannonGrid.Square) (ha : dist o (e a) ≤ s) (hb : dist o (e b) ≤ s)
      (hab : f a ≤ f b) :
      (f b-f a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
    obtain ⟨π,hπ⟩ := hpaths o (e a) (e b) s hs ha hb
    have hπr (v : unitInterval) : π v ∈ range e := by
      apply hchart
      change dist (π v) o < 4*R
      have hv := hπ v
      change dist o (π v) < L*s at hv
      rw [dist_comm] at hv
      linarith
    have hlev : ∀ t : ℝ, ∃ S : Set X, t ∈ Ioo (f a) (f b) →
        IsPreconnected S ∧ 4*R < diam S ∧ (∃ z ∈ S, dist z o ≤ R/2) ∧
        ∀ z ∈ S, extend e f z = t := by
      intro t
      by_cases ht : t ∈ Ioo (f a) (f b)
      · have ht01 : t ∈ Ioo (0:ℝ) 1 :=
          ⟨(hfI a).1.trans_lt ht.1,ht.2.trans_le (hfI b).2⟩
        obtain ⟨S,hS,hcon,_,hd,hval,hhit⟩ :=
          scalar_ambient_level e he Cells ρ hρ hadm n hn d₁ hd₁ t ht01
        obtain ⟨v,hv⟩ := hhit π hπr ht.1 ht.2
        refine ⟨S,fun _ => ⟨hcon.isPreconnected,hdR.trans_le hd,⟨π v,hv,?_⟩,hval⟩⟩
        have hpv := hπ v
        change dist o (π v) < L*s at hpv
        simpa only [dist_comm] using hpv.le.trans hsR
      · exact ⟨∅,fun htt => (ht htt).elim⟩
    choose Clevel hlevel using hlev
    exact hbound q ξ p h hh (extend e f) lo hi o R r d₀ (f a) (f b)
      hR hr hrR hAr hscaleT hscaleS hab hlu hq hqsep hξsep hpsep hnet hzoom hlow
      hlarge hrange ω hω ρ hρ hlocal Clevel hlevel
  rcases le_total (f a) (f b) with hab | hab
  · exact hordered a b ha hb hab
  · change (f b-f a)^2 ≤ _
    have hsquare : (f b-f a)^2 = (f a-f b)^2 := by ring
    rw [hsquare]
    exact hordered b a hb ha hab

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Dirac
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
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

attribute [local instance] Classical.propDecidable

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

lemma dirac_apply (p : X) (S : Set X) (hS : MeasurableSet S) :
    (dirac p S : ℝ) = if p ∈ S then 1 else 0 := by
  classical
  rw [dirac, FiniteMeasure.mk_apply]
  rw [Measure.dirac_apply' p hS]
  by_cases hp : p ∈ S <;> simp [hp]

lemma sum_apply {κ : Type*} (F : κ → FiniteMeasure X) (s : Finset κ) (S : Set X) :
    ((∑ i ∈ s, F i) S : ℝ) = ∑ i ∈ s, (F i S : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, FiniteMeasure.coeFn_add, Pi.add_apply,
      NNReal.coe_add, ih]

theorem atomic_apply (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (S : Set X) (hS : MeasurableSet S) :
    (atomic p w M hM S : ℝ) = M*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) := by
  classical
  rw [atomic, sum_apply]
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteMeasure.smul_apply]
  change ((Real.toNNReal (M*w i^2) * dirac (p i) S : NNReal) : ℝ) = _
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hM (sq_nonneg _)),
    dirac_apply _ S hS]
  split_ifs <;> simp

lemma atomic_mass (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    ((atomic p w M hM).mass : ℝ) = M*(∑ i, (w i)^2) := by
  simpa only [FiniteMeasure.mass, mem_univ, Finset.filter_true] using
    atomic_apply p w M hM univ MeasurableSet.univ

theorem mass_bound (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 < M)
    (C : ℝ) (henergy : (∑ i, (w i)^2) ≤ C/M) :
    ((atomic p w M hM.le).mass : ℝ) ≤ C := by
  rw [atomic_mass]
  exact (mul_le_mul_of_nonneg_left henergy hM.le).trans_eq (by field_simp)

end CannonAtomic

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ClosedAnnulus
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
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

open Set MeasureTheory

attribute [local instance] Classical.propDecidable

theorem record_annular_bound {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (p : ι → X) (w : ι → ℝ) (M M' E D L : ℝ) (hM : 0 < M)
    (hE : 0 ≤ E) (_hL : 0 < L) (hrecord : M' ≤ M/L)
    (S : Set X) (hS : MeasurableSet S)
    (hbound : D^2 ≤ E*M'*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2)) :
    D^2 ≤ (E/L)*(atomic p w M hM.le S : ℝ) := by
  classical
  rw [atomic_apply p w M hM.le S hS]
  have hs : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc
    D^2 ≤ E*M'*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) := hbound
    _ ≤ E*(M/L)*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrecord hE) hs
    _ = (E/L)*(M*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2)) := by ring

end CannonAtomic

open Set Filter Metric Topology

open Set Filter Topology

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_Osc
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
open scoped NNReal ENNReal
open Set Filter Metric Topology
open Set Filter Topology

namespace CannonScales

lemma inverse_geometric_tendsto_zero {a : ℝ} (ha : 1 < a) :
    Tendsto (fun n : ℕ => (a^n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt ha)

end CannonScales

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonScalarLimit

lemma continuous_osc {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) :
    Continuous (fun f : C(X, ℝ) => osc K f) :=
  (hK.continuous_sSup continuous_eval).sub (hK.continuous_sInf continuous_eval)

lemma tendsto_osc {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) {f : ℕ → C(X, ℝ)} {u : C(X, ℝ)}
    (hf : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun n => osc K (f n)) atTop (𝓝 (osc K u)) :=
  (continuous_osc hK).tendsto u |>.comp hf

theorem closed_domination_limit {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hμ : Tendsto μ atTop (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {a : ℕ → ℝ} {b C : ℝ} (ha : Tendsto a atTop (𝓝 b)) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, a n ≤ C * (μ n K : ℝ)) :
    b ≤ C * (ν K : ℝ) := by
  rcases eq_or_lt_of_le hC with hC | hC
  · subst C
    simpa using le_of_tendsto ha (hbound.mono (by intro n hn; simpa using hn))
  have he : ∀ᶠ n in atTop,
      ENNReal.ofReal (a n / C) ≤ (μ n : Measure X) K := by
    filter_upwards [hbound] with n hn
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    apply ENNReal.ofReal_le_iff_le_toReal (by simp) |>.mpr
    change a n / C ≤ ((μ n K : ℝ≥0) : ℝ)
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  have ht := ENNReal.continuous_ofReal.tendsto (b / C) |>.comp (ha.div_const C)
  have hl := (Filter.limsup_le_limsup he).trans
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ hK)
  simp only [Function.comp_def] at ht
  rw [ht.limsup_eq] at hl
  have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hl
  have hh : b / C ≤ (ν K : ℝ) := by
    exact hreal
  exact (div_le_iff₀ hC).mp hh |>.trans_eq (mul_comm _ _)

theorem oscillation_measure_limit {X Y : Type*}
    [TopologicalSpace X] [LocallyCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : Set X} (hK : IsCompact K) {B : Set Y} (hB : IsClosed B)
    {f : ℕ → C(X, ℝ)} {u : C(X, ℝ)} (hf : Tendsto f atTop (𝓝 u))
    {μ : ℕ → FiniteMeasure Y} {ν : FiniteMeasure Y} (hμ : Tendsto μ atTop (𝓝 ν))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ n in atTop, (osc K (f n)) ^ 2 ≤ C * (μ n B : ℝ)) :
    (osc K u) ^ 2 ≤ C * (ν B : ℝ) :=
  closed_domination_limit hμ hB ((tendsto_osc hK hf).pow 2) hC hb

end CannonScalarLimit

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_InteriorScalar
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

namespace CannonScales

lemma inverse_scale_ratio {a : ℝ} (ha : 0 < a) {N l : ℕ} (hl : l ≤ N) :
    (a^N)⁻¹/(a^l)⁻¹ = (a^(N-l))⁻¹ := by
  have hp : a^N = a^(N-l)*a^l := by rw [← pow_add,Nat.sub_add_cancel hl]
  rw [hp,mul_inv]
  field_simp

lemma exists_ratio_threshold {a : ℝ} (ha : 1 < a) (A B : ℝ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (a^m)⁻¹ ≤ 1/2 ∧ A*(a^m)⁻¹ ≤ 1/4 ∧ B*(a^m)⁻¹ ≤ 1 := by
  have hzero := inverse_geometric_tendsto_zero ha
  have h₁ : ∀ᶠ m in Filter.atTop, (a^m)⁻¹ < 1/2 :=
    hzero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have h₂ : ∀ᶠ m in Filter.atTop, A*(a^m)⁻¹ < 1/4 :=
    (tendsto_const_nhds.mul hzero).eventually (gt_mem_nhds (by simp))
  have h₃ : ∀ᶠ m in Filter.atTop, B*(a^m)⁻¹ < 1 :=
    (tendsto_const_nhds.mul hzero).eventually (gt_mem_nhds (by simp))
  obtain ⟨m₀,hm₀⟩ := Filter.eventually_atTop.mp (h₁.and (h₂.and h₃))
  exact ⟨m₀,fun m hm => ⟨(hm₀ m hm).1.le,(hm₀ m hm).2.1.le,(hm₀ m hm).2.2.le⟩⟩

end CannonScales

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
-- module Solutions.OAIQ046_CN.Cannon_Modulus_GeometricAnnularCompactTails
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

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology

theorem geometric_annular_compact_tails {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (a : ℝ) (ha : 1 < a) (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L) (hdc : d ≤ c)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (hexp : ∀ (o : X) (l : ℕ), ∃ h : X → X, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ C/(a^l)⁻¹*dist u v ∧
        c/(a^l)⁻¹*dist u v ≤ dist (h u) (h v))
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (e : Square → X) (he : IsEmbedding e) (N : ℕ → ℕ)
    (ρ : ∀ n, ι (N n) → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p (N n) i) (2*(a^(N n))⁻¹)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < (a^(N n))⁻¹) :
    let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)
    ∃ E : ℝ, 0 ≤ E ∧ ∀ K : Set X, IsCompact K → K ⊆ interior (range e) →
      ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K,
      ∀ x y : interior (range e),
        dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
        (f n x-f n y)^2 ≤ E*M (N n-l)*
          (∑ i ∈ Finset.univ.filter (fun i =>
            (a^l)⁻¹/4 ≤ dist (p (N n) i) o ∧ dist (p (N n) i) o ≤ 4*(a^l)⁻¹),
            (ρ n i)^2) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
    (ρ n) (hρ n) (hadm n) (m n) (hm n)
  obtain ⟨E,hE,hbound⟩ := exists_scalar_annular_constant Q CP C c L hpack hCP hC hc hL hpaths
  obtain ⟨d₁,hd₁,hdiam⟩ := exists_chart_lateral_diameter e he
  obtain ⟨m₀,hm₀⟩ := exists_ratio_threshold ha (L*(L*2+1)+3) (max (C+2) (max c 1))
  have hap : 0 < a := zero_lt_one.trans ha
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hcover (k : ℕ) (x : X) : ∃ i, x ∈ ball (p k i) (2*(a^k)⁻¹) := by
    obtain ⟨i,hi⟩ := hpnet k x
    refine ⟨i,?_⟩
    rw [mem_ball,dist_comm]
    exact hi.trans_lt (by have := inv_pos.mpr (pow_pos hap k); linarith)
  refine ⟨E,hE,fun K hK hKU => ?_⟩
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_thickening_subset_open isOpen_interior hKU
  have hscl := inverse_geometric_tendsto_zero ha
  have hsmall : ∀ᶠ l in atTop, 4*(a^l)⁻¹ < min δ d₁ :=
    (tendsto_const_nhds.mul hscl).eventually (gt_mem_nhds (by simpa using lt_min hδ hd₁))
  obtain ⟨l₀,hl₀⟩ := eventually_atTop.mp hsmall
  refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => ?_⟩
  let R := (a^l)⁻¹
  let r := (a^(N n))⁻¹
  have hR : 0 < R := inv_pos.mpr (pow_pos hap l)
  have hr : 0 < r := inv_pos.mpr (pow_pos hap (N n))
  have hln : l ≤ N n := by omega
  have hrat : r/R = (a^(N n-l))⁻¹ := inverse_scale_ratio hap hln
  have hconstraints := hm₀ (N n-l) (by omega)
  rw [← hrat] at hconstraints
  have hRone : R ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha.le)
  have hRd : 4*R < d₁ := (hl₀ l hl).trans_le (min_le_right _ _)
  have hchart : ball o (4*R) ⊆ range e := by
    intro z hz
    apply interior_subset
    apply hδU
    exact mem_thickening_iff.mpr ⟨o,ho,
      (mem_ball.mp hz).trans ((hl₀ l hl).trans_le (min_le_left _ _))⟩
  have hrR : r ≤ R/2 := by
    have hh := (div_le_iff₀ hR).mp hconstraints.1
    linarith
  have hAr : (L*(L*2+1)+3)*r ≤ R/4 := by
    have hh := (div_le_iff₀ hR).mp (show ((L*(L*2+1)+3)*r)/R ≤ 1/4 by
      simpa only [mul_div_assoc] using hconstraints.2.1)
    linarith
  obtain ⟨h,hh,hlocal⟩ := hexp o l
  obtain ⟨_,ω,hω,hωE⟩ := sphere_macro_modulus_minimum φ d hd hdia (p (N n-l))
    ((a^(N n-l))⁻¹) (hcover (N n-l))
  have hω' : MacroscopicAdmissible (p (N n-l)) (r/R) d ω := by
    simpa only [hrat] using hω
  obtain ⟨zx,hzx⟩ := interior_subset x.property
  obtain ⟨zy,hzy⟩ := interior_subset y.property
  have hzdist : dist o (e zy) ≤ R/(2*L) := by
    rw [hzy,dist_comm]
    exact hy
  have hzero : dist o (e zx) ≤ R/(2*L) := by
    rw [hzx,dist_comm]
    exact hx
  have hlarge (u v : X) (hu : dist u o ≤ 2*R) (hv : dist v o ≤ 2*R)
      (huv : R ≤ dist u v) : d ≤ dist (h u) (h v) := by
    have hu' : dist u o ≤ 3*R := by linarith
    have hv' : dist v o ≤ 3*R := by linarith
    have hlow := (hlocal u v hu' hv').2
    calc
      d ≤ c := hdc
      _ = c/R*R := by field_simp
      _ ≤ c/R*dist u v := mul_le_mul_of_nonneg_left huv (div_nonneg hc.le hR.le)
      _ ≤ dist (h u) (h v) := hlow
  have hs : 0 < R/(2*L) := by positivity
  have hLs : L*(R/(2*L)) ≤ R/2 := by field_simp; linarith
  have hmain := hbound e he d₁ hdiam (p (N n-l)) (p (N n)) h hh o R r d (R/(2*L))
    hR hRone hRd hr hrR hAr hconstraints.2.2 hs hLs hchart
    (fun i j hij => by rw [hrat]; exact hpsep (N n-l) i j hij)
    (hpsep (N n)) (hpnet (N n))
    (fun u v hu hv => (hlocal u v hu hv).1)
    (fun u v hu hv => (hlocal u v hu hv).2) hlarge ω hω' (ρ n) (hρ n)
    (hadm n) (m n) (hm n) (hmesh n) zy zx hzdist hzero
  rw [hωE] at hmain
  have hfx : f n x = scalar (fun i => e ⁻¹' ball (p (N n) i) (2*r)) (ρ n) (m n) (hm n) zx := by
    change extend e _ x.val = _
    rw [← hzx]
    exact extend_apply e he.injective _ zx
  have hfy : f n y = scalar (fun i => e ⁻¹' ball (p (N n) i) (2*r)) (ρ n) (m n) (hm n) zy := by
    change extend e _ y.val = _
    rw [← hzy]
    exact extend_apply e he.injective _ zy
  change (f n x-f n y)^2 ≤ _
  rw [hfx,hfy]
  exact hmain

end CannonApprox

open Set Filter Topology TopologicalSpace Metric

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_GeometricRecordAnnuli
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

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology MeasureTheory

theorem geometric_record_annuli {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (a : ℝ) (ha : 1 < a) (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L) (hdc : d ≤ c)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (hexp : ∀ (o : X) (l : ℕ), ∃ h : X → X, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ C/(a^l)⁻¹*dist u v ∧
        c/(a^l)⁻¹*dist u v ≤ dist (h u) (h v))
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (e : Square → X) (he : IsEmbedding e) (N : ℕ → ℕ)
    (ρ : ∀ n, ι (N n) → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p (N n) i) (2*(a^(N n))⁻¹)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < (a^(N n))⁻¹)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hrecord : ∀ n l, l ≤ N n →
      CannonCells.modulus (fun i => ball (p (N n-l) i) (2*(a^(N n-l))⁻¹)) (macroFamily d) ≤
      (lam^l)⁻¹*CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d)) :
    let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    let f := fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)
    let μ := fun n => CannonAtomic.atomic (p (N n)) (ρ n) (M (N n))
      (by apply Real.sInf_nonneg; rintro t ⟨w,_,rfl⟩; exact sq_nonneg _)
    ∃ E : ℝ, 0 ≤ E ∧ ∀ K : Set X, IsCompact K → K ⊆ interior (range e) →
      ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K,
      ∀ x y : interior (range e),
        dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
        (f n x-f n y)^2 ≤ (E/(lam^l)) *
          (μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  obtain ⟨E,hE,hann⟩ := geometric_annular_compact_tails φ d hd hdia a ha Q CP C c L
    hpack hCP hC hc hL hdc hpaths hexp ι p hpsep hpnet e he N ρ hρ hadm m hm hmesh
  refine ⟨E,hE,fun K hK hKU => ?_⟩
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => ?_⟩
  have hap : 0 < a := zero_lt_one.trans ha
  have hM : 0 < M (N n) := (sphere_macro_modulus_minimum φ d hd hdia (p (N n))
    ((a^(N n))⁻¹) (fun z => by
      obtain ⟨i,hi⟩ := hpnet (N n) z
      refine ⟨i,?_⟩
      rw [mem_ball,dist_comm]
      exact hi.trans_lt (by have := inv_pos.mpr (pow_pos hap (N n)); linarith))).1
  have hrec : M (N n-l) ≤ M (N n)/(lam^l) := by
    simpa only [inv_mul_eq_div] using hrecord n l (by omega)
  have hS : MeasurableSet {z : X | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} :=
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).measurableSet
  exact CannonAtomic.record_annular_bound (p (N n)) (ρ n) (M (N n)) (M (N n-l)) E
    _ (lam^l) hM hE (pow_pos (zero_lt_one.trans_le hlam) l) hrec _ hS
    (by
      convert hann l hl n hn o ho x y hx hy using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ext i
      simp only [Finset.mem_filter, Set.mem_ofPred_eq])

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

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_ConnectedLimit
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

namespace CannonMeasureOscillation

open CannonScalarLimit Metric

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

lemma osc_sq_le_of_pairwise {Y : Type*} [TopologicalSpace Y]
    {f : Y → ℝ} (hf : Continuous f) {A : Set Y} (hA : IsCompact A)
    {E : ℝ} (hE : 0 ≤ E)
    (hpair : ∀ x ∈ A, ∀ y ∈ A, (f x-f y)^2 ≤ E) : (osc A f)^2 ≤ E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simpa [osc] using hE
  obtain ⟨x,hx,heqx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,heqy⟩ := (hA.image hf).sInf_mem (hne.image f)
  simpa only [osc,← heqx,← heqy] using hpair x hx y hy

lemma compact_subtype_closedBall {X : Type*} [MetricSpace X] [CompactSpace X]
    {U : Set X} {o : X} {s : ℝ} (hsub : closedBall o s ⊆ U) :
    IsCompact (Subtype.val ⁻¹' closedBall o s : Set U) := by
  apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
  have he : Subtype.val '' (Subtype.val ⁻¹' closedBall o s : Set U) = closedBall o s := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z,hsub hz⟩,hz,rfl⟩
  rw [he]
  exact isCompact_closedBall o s

theorem annular_to_measure {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X) (hU : IsOpen U)
    (f : ℕ → C(U,ℝ)) (u : C(U,ℝ)) (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a L E : ℝ) (ha : 1 < a) (hL : 0 < L) (hE : 0 ≤ E)
    (hann : ∀ K : Set X, IsCompact K → K ⊆ U → ∃ l₀ m₀ : ℕ,
      ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K, ∀ x y : U,
      dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ E*(μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ))
    (hf : Tendsto f atTop (𝓝 u)) (hμ : Tendsto μ atTop (𝓝 ν)) :
    ∀ K : Set X, IsCompact K → K ⊆ U → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ o ∈ K,
        closedBall o s ⊆ U ∧
        (osc (Subtype.val ⁻¹' closedBall o s : Set U) u)^2 ≤
          E*(ν (closedBall o ((8*a*L)*s)) : ℝ) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  intro K hK hKU
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hap : 0 < a := zero_lt_one.trans ha
  have hden : 0 < 2*L := by positivity
  let s₀ := min (δ/2) ((a^l₀)⁻¹/(2*L))
  have hs₀ : 0 < s₀ := lt_min (by positivity) (by positivity)
  refine ⟨s₀,hs₀,fun s hs hss o ho => ?_⟩
  have hsδ : s < δ := lt_of_le_of_lt (hss.trans (min_le_left _ _)) (by linarith)
  have hB : closedBall o s ⊆ U := by
    intro z hz
    exact hδU (mem_thickening_iff.mpr ⟨o,ho,(mem_closedBall.mp hz).trans_lt hsδ⟩)
  have hsR : 2*L*s ≤ (a^l₀)⁻¹ := by
    have hh := (le_div_iff₀ hden).mp (hss.trans (min_le_right _ _))
    nlinarith
  obtain ⟨l,hl,hl₁,hl₂⟩ := inverse_geometric_near ha l₀ (mul_pos hden hs) hsR
  have hsinner : s ≤ (a^l)⁻¹/(2*L) := (le_div_iff₀ hden).mpr (by nlinarith [hl₁])
  have hA : IsCompact (Subtype.val ⁻¹' closedBall o s : Set U) := compact_subtype_closedBall hB
  refine ⟨hB,?_⟩
  apply oscillation_measure_limit hA isClosed_closedBall hf hμ hE
  filter_upwards [hN.eventually (eventually_ge_atTop (l+m₀))] with n hn
  apply osc_sq_le_of_pairwise (f n).continuous hA (mul_nonneg hE (NNReal.coe_nonneg _))
  intro x hx y hy
  have hh := hann l hl n hn o ho x y
    ((mem_closedBall.mp hx).trans hsinner) ((mem_closedBall.mp hy).trans hsinner)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hE
  exact_mod_cast (μ n).apply_mono (show
    {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} ⊆
      closedBall o ((8*a*L)*s) from fun z hz =>
    mem_closedBall.mpr (hz.2.trans (by nlinarith [hl₂])))

end CannonMeasureOscillation

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_ReciprocalPowLog
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

namespace CannonMeasureOscillation

open CannonScalarLimit Metric

lemma reciprocal_pow_log {a lam : ℝ} (ha : 1 < a) (hlam : 0 < lam) (l : ℕ) :
    ((a^l)⁻¹) ^ (Real.log lam / Real.log a) = (lam^l)⁻¹ := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hlog : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (inv_pos.mpr (pow_pos hap l)) _)
    (inv_pos.mpr (pow_pos hlam l))
  rw [Real.log_rpow (inv_pos.mpr (pow_pos hap l)),Real.log_inv,Real.log_inv,
    Real.log_pow,Real.log_pow]
  field_simp

theorem annular_to_holder {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X) (hU : IsOpen U)
    (f : ℕ → C(U,ℝ)) (u : C(U,ℝ)) (μ : ℕ → FiniteMeasure X)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a L E A lam : ℝ) (ha : 1 < a) (hL : 0 < L) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hlam : 1 < lam) (hmass : ∀ n, ((μ n).mass : ℝ) ≤ A)
    (hu : ∀ x, u x ∈ Icc (0:ℝ) 1)
    (hann : ∀ K : Set X, IsCompact K → K ⊆ U → ∃ l₀ m₀ : ℕ,
      ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n → ∀ o ∈ K, ∀ x y : U,
      dist x.val o ≤ (a^l)⁻¹/(2*L) → dist y.val o ≤ (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ (E/(lam^l))*(μ n {z | (a^l)⁻¹/4 ≤ dist z o ∧ dist z o ≤ 4*(a^l)⁻¹} : ℝ))
    (hf : Tendsto f atTop (𝓝 u)) :
    0 < Real.log lam/(2*Real.log a) ∧
      ∀ K : Set X, IsCompact K → K ⊆ U → ∃ D : ℝ, 0 ≤ D ∧
        ∀ x y : U, x.val ∈ K → y.val ∈ K →
          |u x-u y| ≤ D*(dist x y)^(Real.log lam/(2*Real.log a)) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let α := Real.log lam/(2*Real.log a)
  have hα : 0 < α := div_pos (Real.log_pos hlam) (mul_pos (by norm_num) (Real.log_pos ha))
  refine ⟨hα,fun K hK hKU => ?_⟩
  obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
  have hap : 0 < a := zero_lt_one.trans ha
  have hlamp : 0 < lam := zero_lt_one.trans hlam
  have hden : 0 < 2*L := by positivity
  let s₀ := (a^l₀)⁻¹/(2*L)
  have hs₀ : 0 < s₀ := by positivity
  let D₀ := Real.sqrt (E*A)*(a*(2*L))^α
  have hD₀ : 0 ≤ D₀ := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨max D₀ (s₀^α)⁻¹,le_trans hD₀ (le_max_left _ _),fun x y hx _hy => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [sub_self,abs_zero,dist_self]
    positivity
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  by_cases hsmall : dist x y ≤ s₀
  · obtain ⟨l,hl,hl₁,hl₂⟩ := inverse_geometric_near ha l₀ (mul_pos hden hdist)
      (by simpa only [mul_comm] using (le_div_iff₀ hden).mp hsmall)
    have hinner : dist x y ≤ (a^l)⁻¹/(2*L) := (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hl₁)
    have hpair : (u x-u y)^2 ≤ (E/(lam^l))*A := by
      apply le_of_tendsto ((continuous_eval_const x).tendsto u |>.comp hf |>.sub
        ((continuous_eval_const y).tendsto u |>.comp hf) |>.pow 2)
      filter_upwards [hN.eventually (eventually_ge_atTop (l+m₀))] with n hn
      apply (hann l hl n hn x.val hx x y (by simp; positivity)
        (by simpa only [Subtype.dist_eq,dist_comm] using hinner)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hE (pow_nonneg hlamp.le l))
      exact (show (μ n _ : ℝ) ≤ ((μ n).mass : ℝ) by exact_mod_cast (μ n).apply_le_mass _).trans
        (hmass n)
    have hid : ((a^l)⁻¹)^α * ((a^l)⁻¹)^α = (lam^l)⁻¹ := by
      rw [← Real.rpow_add (inv_pos.mpr (pow_pos hap l))]
      convert reciprocal_pow_log ha hlamp l using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [α]
      field_simp
      ring_nf
    have hsq : (Real.sqrt (E*A)*((a^l)⁻¹)^α)^2 = (E/(lam^l))*A := by
      rw [mul_pow,Real.sq_sqrt (mul_nonneg hE hA),pow_two,hid]
      ring
    have hnear : |u x-u y| ≤ Real.sqrt (E*A)*((a^l)⁻¹)^α := by
      have hnn : 0 ≤ Real.sqrt (E*A)*((a^l)⁻¹)^α := by positivity
      have habs : |u x-u y|^2 = (u x-u y)^2 := sq_abs _
      nlinarith
    have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr (pow_nonneg hap.le l)) hl₂.le hα.le
    have hround : Real.sqrt (E*A)*((a^l)⁻¹)^α ≤ D₀*(dist x y)^α := by
      apply (mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg _)).trans_eq
      dsimp [D₀]
      rw [show a*(2*L*dist x y) = (a*(2*L))*dist x y by ring,
        Real.mul_rpow (by positivity) hdist.le]
      ring
    exact (hnear.trans hround).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hdist.le _))
  · have hpow : s₀^α ≤ (dist x y)^α := Real.rpow_le_rpow hs₀.le (le_of_not_ge hsmall) hα.le
    have hone : 1 ≤ (s₀^α)⁻¹*(dist x y)^α := by
      have hp : 0 < s₀^α := Real.rpow_pos_of_pos hs₀ _
      calc
        1 = (s₀^α)⁻¹*s₀^α := (inv_mul_cancel₀ hp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp.le)
    have hunit : |u x-u y| ≤ 1 := abs_le.mpr ⟨by linarith [(hu x).1,(hu y).2],by linarith [(hu x).2,(hu y).1]⟩
    exact hunit.trans (hone.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hdist.le _)))

end CannonMeasureOscillation

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
-- module Solutions.OAIQ046_CN.Cannon_Energy_GeometricLimitMeasureHolder
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

namespace CannonApprox

open CannonGrid CannonChart CannonCharts CannonScales CannonPacking CannonAnnular
open Set Metric Filter Topology MeasureTheory

theorem geometric_limit_measure_holder {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (a : ℝ) (ha : 1 < a) (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L) (hdc : d ≤ c)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (hexp : ∀ (o : X) (l : ℕ), ∃ h : X → X, Continuous h ∧
      ∀ u v, dist u o ≤ 3*(a^l)⁻¹ → dist v o ≤ 3*(a^l)⁻¹ →
        dist (h u) (h v) ≤ C/(a^l)⁻¹*dist u v ∧
        c/(a^l)⁻¹*dist u v ≤ dist (h u) (h v))
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (e : Square → X) (he : IsEmbedding e) (N : ℕ → ℕ)
    (ρ : ∀ n, ι (N n) → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p (N n) i) (2*(a^(N n))⁻¹)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < (a^(N n))⁻¹)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hrecord : ∀ n l, l ≤ N n →
      CannonCells.modulus (fun i => ball (p (N n-l) i) (2*(a^(N n-l))⁻¹)) (macroFamily d) ≤
      (lam^l)⁻¹*CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
    (hN : StrictMono N) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ n, (∑ i, (ρ n i)^2) ≤ A /
      CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
    (u : C(interior (range e),ℝ)) (ν : FiniteMeasure X)
    (hu : ∀ x, u x ∈ Icc (0:ℝ) 1)
    (hf : Tendsto (fun n => interiorScalar e he (p (N n)) ((a^(N n))⁻¹)
      (ρ n) (hρ n) (hadm n) (m n) (hm n)) atTop (𝓝 u))
    (hμ : Tendsto (fun n => CannonAtomic.atomic (p (N n)) (ρ n)
      (CannonCells.modulus (fun i => ball (p (N n) i) (2*(a^(N n))⁻¹)) (macroFamily d))
      (by apply Real.sInf_nonneg; rintro t ⟨w,_,rfl⟩; exact sq_nonneg _)) atTop (𝓝 ν)) :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ K : Set X, IsCompact K → K ⊆ interior (range e) → ∃ s₀ : ℝ, 0 < s₀ ∧
        ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ o ∈ K,
          closedBall o s ⊆ interior (range e) ∧
          (CannonScalarLimit.osc (Subtype.val ⁻¹' closedBall o s : Set (interior (range e))) u)^2 ≤
            E*(ν (closedBall o ((8*a*L)*s)) : ℝ)) ∧
      (1 < lam → 0 < Real.log lam/(2*Real.log a) ∧
        ∀ K : Set X, IsCompact K → K ⊆ interior (range e) → ∃ D : ℝ, 0 ≤ D ∧
          ∀ x y : interior (range e), x.val ∈ K → y.val ∈ K →
            |u x-u y| ≤ D*(dist x y)^(Real.log lam/(2*Real.log a))) := by
  classical
  let M := fun n => CannonCells.modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  have hM (n : ℕ) : 0 < M n := (sphere_macro_modulus_minimum φ d hd hdia (p n)
    ((a^n)⁻¹) (fun z => by
      obtain ⟨i,hi⟩ := hpnet n z
      refine ⟨i,?_⟩
      rw [mem_ball,dist_comm]
      exact hi.trans_lt (by
        have := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) n)
        linarith))).1
  let μ := fun n => CannonAtomic.atomic (p (N n)) (ρ n) (M (N n)) (hM (N n)).le
  have hmass (n : ℕ) : ((μ n).mass : ℝ) ≤ A :=
    CannonAtomic.mass_bound (p (N n)) (ρ n) (M (N n)) (hM (N n)) A (henergy n)
  obtain ⟨E,hE,hann⟩ := geometric_record_annuli φ d hd hdia a ha Q CP C c L
    hpack hCP hC hc hL hdc hpaths hexp ι p hpsep hpnet e he N ρ hρ hadm m hm hmesh
    lam hlam hrecord
  refine ⟨E,hE,?_,?_⟩
  · apply CannonMeasureOscillation.annular_to_measure (interior (range e)) isOpen_interior
      _ u μ ν N hN.tendsto_atTop a L E ha (zero_lt_one.trans_le hL) hE _ hf hμ
    intro K hK hKU
    obtain ⟨l₀,m₀,hann⟩ := hann K hK hKU
    refine ⟨l₀,m₀,fun l hl n hn o ho x y hx hy => (hann l hl n hn o ho x y hx hy).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
    exact div_le_self hE (one_le_pow₀ hlam)
  · intro hlamp
    exact CannonMeasureOscillation.annular_to_holder (interior (range e)) isOpen_interior
      _ u μ N hN.tendsto_atTop a L E A lam ha (zero_lt_one.trans_le hL) hE hA
      hlamp hmass hu hann hf

end CannonApprox

open scoped NNReal ENNReal
open Set Metric

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_TransformedScalarEnergyConstant
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

namespace CannonApprox

open CannonGrid CannonLevel CannonChart CannonPacking CannonScalarEnergy CannonCrossEnergy
open Set Metric Filter Topology

theorem exists_transformed_scalar_energy_constant {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP L J B b : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hJ : 0 < J) (hB : 0 < B) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : Square → X), IsEmbedding e →
      ∀ (g : X ≃ₜ X), (∀ x y, b*dist x y ≤ dist (g.symm x) (g.symm y)) →
        (∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y) →
      ∀ {α β : Type*} [Fintype α] [Fintype β] (centers : α → X) (q : β → X) (r : ℝ),
        0 < r → max (L*(L*(B*J)+1)+3) (max 1 b)*r ≤ 1 →
        (∀ i j, i ≠ j → r ≤ dist (centers i) (centers j)) →
        (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
        (∀ i, ball (g.symm (centers i)) (L*(L*(B*J)+1)*r) ⊆ range e) →
        ∀ (ρ : β → ℝ), (∀ i, 0 ≤ ρ i) →
          Admissible (fun i => e ⁻¹' ball (q i) (2*r)) ρ →
        ∀ (n : ℕ) (hn : 0 < n),
        (∀ z : Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
          dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
        (∑ i, (oscillation
          ((extend e (scalar (fun j => e ⁻¹' ball (q j) (2*r)) ρ n hn)) ∘ g.symm)
          (closedBall (centers i) (J*r)))^2) ≤ E*(∑ j, (ρ j)^2) := by
  obtain ⟨E,hE,hbound⟩ := exists_scalar_energy_constant Q CP L (B*J) b
    hpack hCP hL (mul_pos hB hJ) hb hpaths
  refine ⟨E,hE,?_⟩
  intro e he g hglower hgupper α β _ _ centers q r hr hscale hc hq hchart ρ hρ hadm n hn hmesh
  let f := scalar (fun j => e ⁻¹' ball (q j) (2*r)) ρ n hn
  have hf : Continuous f := (scalar_properties _ ρ hρ hadm n hn).1
  have hsep (i j : α) (hij : i ≠ j) : b*r ≤ dist (g.symm (centers i)) (g.symm (centers j)) :=
    (mul_le_mul_of_nonneg_left (hc i j hij) hb.le).trans (hglower _ _)
  apply le_trans _ (hbound e he (g.symm ∘ centers) q r hr hscale hsep hq hchart
    ρ hρ hadm n hn hmesh)
  apply Finset.sum_le_sum
  intro i _
  let S := closedBall (centers i) (J*r)
  let T := e ⁻¹' closedBall (g.symm (centers i)) (B*J*r)
  have hT : IsCompact T := (isClosed_closedBall.preimage he.continuous).isCompact
  have hsub : ((extend e f) ∘ g.symm) '' S ⊆ f '' T := by
    rintro v ⟨z,hz,rfl⟩
    have hdist : dist (g.symm z) (g.symm (centers i)) ≤ B*J*r := by
      exact (hgupper z (centers i)).trans (by
        have hh := mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hB.le
        nlinarith)
    have hinside : g.symm z ∈ range e := by
      apply hchart i
      rw [mem_ball]
      have hLpos : 0 < L := zero_lt_one.trans_le hL
      have hBJ : 0 < B*J := mul_pos hB hJ
      have hstep : B*J ≤ L*(B*J) := by nlinarith
      have hprod : B*J ≤ L*(L*(B*J)) :=
        hstep.trans (mul_le_mul_of_nonneg_left hstep hLpos.le)
      exact hdist.trans_lt (mul_lt_mul_of_pos_right (by nlinarith) hr)
    obtain ⟨w,hw⟩ := hinside
    refine ⟨w,by simpa only [T,mem_preimage,mem_closedBall,hw] using hdist,?_⟩
    rw [Function.comp_apply,← hw,extend_apply e he.injective]
  have hh := oscillation_mono_range (f := (extend e f) ∘ g.symm) (g := f)
    (S := S) (T := T) ⟨centers i,mem_closedBall_self (mul_nonneg hJ.le hr.le)⟩
    (hT.image hf).bddAbove (hT.image hf).bddBelow hsub
  exact pow_le_pow_left₀ hh.1 hh.2 2

end CannonApprox

namespace CannonApprox

open CannonGrid CannonLevel CannonChart CannonPacking CannonScalarEnergy CannonCrossEnergy
open Set Metric Filter Topology

theorem transformed_scalar_energy_tail {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP L J B b : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hJ : 0 < J) (hB : 0 < B) (hb : 0 < b)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (e : Square → X) (he : IsEmbedding e) (g : X ≃ₜ X)
    (hglower : ∀ x y, b*dist x y ≤ dist (g.symm x) (g.symm y))
    (hgupper : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (ρ : ∀ n, ι n → ℝ) (hρ : ∀ n i, 0 ≤ ρ n i)
    (hadm : ∀ n, Admissible (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n))
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hmesh : ∀ n z, ∀ i : Index (3*m n), weight (3*m n) z i ≠ 0 →
      dist (e z) (e (vertex (3*m n) (by have := hm n; omega) i)) < r n)
    (M : ℕ → ℝ) (hMlim : Tendsto M atTop atTop) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ n, (∑ i, (ρ n i)^2) ≤ A/M n) (K : Set X)
    (hK : IsCompact K) (hKU : K ⊆ g '' interior (range e)) :
    let F := fun n => (extend e
      (scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n))) ∘ g.symm
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ᶠ n in atTop,
        (∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
          closedBall (p n i) (J*r n) ⊆ g '' interior (range e)) ∧
        meshEnergy (p n) (r n) J (F n) K ≤ D/M n) ∧
      Tendsto (fun n => meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0) := by
  classical
  let F := fun n => (extend e
    (scalar (fun i => e ⁻¹' ball (p n i) (2*r n)) (ρ n) (m n) (hm n))) ∘ g.symm
  obtain ⟨E,hE,hbound⟩ := exists_transformed_scalar_energy_constant Q CP L J B b
    hpack hCP hL hJ hB hb hpaths
  let K₀ := g.symm '' K
  have hK₀ : IsCompact K₀ := hK.image g.symm.continuous
  have hK₀U : K₀ ⊆ interior (range e) := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,hwz⟩ := hKU hz
    simpa only [← hwz,g.symm_apply_apply] using hw
  obtain ⟨δ,hδ,hδU⟩ := hK₀.exists_thickening_subset_open isOpen_interior hK₀U
  let T := L*(L*(B*J)+1)
  let S := max (T+3) (max 1 b)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hBJ : 0 < B*J := mul_pos hB hJ
  have hstep : B*J ≤ L*(B*J) := by nlinarith
  have hprod : B*J ≤ L*(L*(B*J)) :=
    hstep.trans (mul_le_mul_of_nonneg_left hstep hLpos.le)
  have hT : B*J < T := by dsimp [T]; nlinarith
  have hsmall₁ : ∀ᶠ n in atTop, S*r n < 1 := by
    have ht : Tendsto (fun n => S*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => S*r n) atTop (𝓝 (S*0)))
    exact ht.eventually_lt_const zero_lt_one
  have hsmall₂ : ∀ᶠ n in atTop, (T+2*B)*r n < δ := by
    have ht : Tendsto (fun n => (T+2*B)*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => (T+2*B)*r n) atTop (𝓝 ((T+2*B)*0)))
    exact ht.eventually_lt_const hδ
  have htail : ∀ᶠ n in atTop,
      (∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
        closedBall (p n i) (J*r n) ⊆ g '' interior (range e)) ∧
      meshEnergy (p n) (r n) J (F n) K ≤ (E*A)/M n := by
    filter_upwards [hsmall₁,hsmall₂] with n hn₁ hn₂
    have hnear (i : ι n) (hi : (ball (p n i) (2*r n) ∩ K).Nonempty) :
        ball (g.symm (p n i)) (T*r n) ⊆ interior (range e) := by
      obtain ⟨z,hzi,hzK⟩ := hi
      intro w hw
      apply hδU
      refine mem_thickening_iff.mpr ⟨g.symm z,⟨z,hzK,rfl⟩,?_⟩
      have hzdist : dist (g.symm (p n i)) (g.symm z) < B*(2*r n) :=
        (hgupper _ _).trans_lt (mul_lt_mul_of_pos_left (by
          simpa only [mem_ball,dist_comm] using hzi) hB)
      exact (dist_triangle w (g.symm (p n i)) (g.symm z)).trans_lt
        ((add_lt_add (mem_ball.mp hw) hzdist).trans_le (by nlinarith))
    refine ⟨?_,?_⟩
    · intro i hi z hz
      have hdz : dist (g.symm z) (g.symm (p n i)) < T*r n := by
        apply (hgupper _ _).trans_lt
        exact (mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hB.le).trans_lt
          (by have hh := mul_lt_mul_of_pos_right hT (hr n); nlinarith)
      exact ⟨g.symm z,hnear i hi (mem_ball.mpr hdz),g.apply_symm_apply z⟩
    · let α := {i : ι n // (ball (p n i) (2*r n) ∩ K).Nonempty}
      have hcenters (i j : α) (hij : i ≠ j) : r n ≤ dist (p n i.val) (p n j.val) :=
        hpsep n i.val j.val (fun h => hij (Subtype.ext h))
      have hh := hbound e he g hglower hgupper (fun i : α => p n i.val) (p n) (r n)
        (hr n) hn₁.le hcenters (hpsep n) (fun i => (hnear i.val i.property).trans interior_subset)
        (ρ n) (hρ n) (hadm n) (m n) (hm n) (hmesh n)
      exact hh.trans ((mul_le_mul_of_nonneg_left (henergy n) hE).trans_eq (by ring))
  refine ⟨E*A,mul_nonneg hE hA,htail,?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _))
    (htail.mono (fun _ hn => hn.2))
  simpa only [div_eq_mul_inv,mul_zero] using
    (tendsto_const_nhds.mul hMlim.inv_tendsto_atTop :
      Tendsto (fun n => (E*A)*(M n)⁻¹) atTop (𝓝 ((E*A)*0)))

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

open Set Metric Topology

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma onDomain_eq {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (f : C(Ω,ℝ)) (x : X) (hx : x ∈ Ω) : onDomain f x = f ⟨x,hx⟩ := by simp only [onDomain,dite_eq_left hx]

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
-- module Solutions.OAIQ046_CN.Cannon_ScalarLimits_CompactVariationRegion
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
section
section
section
open Set Topology Metric unitInterval

namespace CannonVariation

open Filter

lemma compact_variation_region {X : Type*} [MetricSpace X] (Ω : Set X)
    (hΩ : IsOpen Ω) (P : Set X) (hP : IsCompact P) (hPne : P.Nonempty)
    (hPΩ : P ⊆ Ω) (z₀ : X) (hz₀ : z₀ ∉ Ω) :
    ∃ O : Set X, IsOpen O ∧ Oᶜ.Nonempty ∧ closure O ⊆ Ω ∧ P ⊆ O ∧
      ∃ d : ℝ, 0 < d ∧ ∀ x ∈ O, d ≤ dist x z₀ := by
  obtain ⟨O,hO,hPO,hOΩ⟩ := hP.exists_isOpen_closure_subset (hΩ.mem_nhdsSet.mpr hPΩ)
  have hzO : z₀ ∉ closure O := fun h => hz₀ (hOΩ h)
  have hOne : (closure O).Nonempty := hPne.mono (hPO.trans subset_closure)
  have hd : 0 < infDist z₀ (closure O) := isClosed_closure.notMem_iff_infDist_pos hOne |>.mp hzO
  refine ⟨O,hO,⟨z₀,fun h => hzO (subset_closure h)⟩,hOΩ,hPO,
    infDist z₀ (closure O),hd,?_⟩
  intro x hx
  exact (infDist_le_dist_of_mem (subset_closure hx)).trans_eq (dist_comm z₀ x)

end CannonVariation

end

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonVariation CannonComparison
open CannonPacking CannonApprox CannonGrid CannonChart CannonCharts CannonCells CannonPlanar
open Set Metric Filter Topology MeasureTheory

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_exponential_records_impossible (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    ∀ lam : ℝ, 1 < lam →
    (∀ B : ℝ, ∃ n,
      B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)/lam^n) → False := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet lam hlam hunbounded
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  obtain ⟨e,he,A,hA,N,hN,hMlim,hrecord,ρ,m,hm,hρ,hadm,henergy,hmesh,u,hu,hvar,
      ν,_hν,ψ,hψ,hflim,hμlim⟩ :=
    boundary_record_scalar_limit D hδ φ d hd hdia hdc ι p hpsep hpnet lam hlam.le hunbounded
  let E := e ∘ squareMap
  have hE : IsEmbedding E := he.isEmbedding.comp squareMap_embedding
  let Ns := N ∘ ψ
  have hNs : StrictMono Ns := hN.comp hψ
  let w := fun n => ρ (ψ n)
  let ms := m ∘ ψ
  have hms : ∀ n, 0 < ms n := fun n => hm (ψ n)
  have hw : ∀ n i, 0 ≤ w n i := fun n => hρ (ψ n)
  have hadms : ∀ n, Admissible (fun i => E ⁻¹' ball (p (Ns n) i) (2*(a^(Ns n))⁻¹)) (w n) :=
    fun n => hadm (ψ n)
  obtain ⟨Q,CP,_hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨L,hL,hpaths⟩ := boundary_controlled_paths D hδ φ
  obtain ⟨_C,_hC,_hmeasure,hholder⟩ := geometric_limit_measure_holder φ d hd hdia a ha Q CP
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (1/((8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*3^2)) L
    hpack hCP.le (by positivity) (by positivity) hL hdc hpaths
    (boundary_smallball_expansion D hδ) ι p hpsep hpnet E hE Ns w hw hadms ms hms
    (fun n => hmesh (ψ n)) lam hlam.le (fun n => hrecord (ψ n)) hNs A hA.le
    (fun n => henergy (ψ n)) u ν hu hflim hμlim
  obtain ⟨hα,huholder⟩ := hholder hlam
  let Ω := interior (range E)
  obtain ⟨top,bot,htop,hbot⟩ := hvar
  have hv : ∃ v ∈ Ω, ∃ w ∈ Ω, onDomain u v ≠ onDomain u w := by
    refine ⟨top,top.property,bot,bot.property,?_⟩
    simpa only [onDomain_eq u top top.property,onDomain_eq u bot bot.property,htop,hbot] using
      (zero_ne_one : (0:ℝ) ≠ 1)
  obtain ⟨v₀,w₀,q,hq,hqvar⟩ := ordered_variation_path Ω (chart_square_pathConnected e he) (onDomain u) hv
  let P := range q
  have hP : IsCompact P := isCompact_range q.continuous
  have hPc : IsConnected P := isConnected_range q.continuous
  let z₀ := e (0,0)
  have hz₀ : z₀ ∉ Ω := chart_origin_outside_square e he
  obtain ⟨O,hO,hOc,hOΩ,hPO,d₀,hd₀,hsep⟩ :=
    compact_variation_region Ω isOpen_interior P hP hPc.nonempty hq z₀ hz₀
  let r : ℕ → ℝ := fun n => (a^(Ns n))⁻¹
  have hr : ∀ n, 0 < r n := fun n => inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    simpa only [r,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hNs.tendsto_atTop
  let f := fun n => scalar (fun i => E ⁻¹' ball (p (Ns n) i) (2*r n)) (w n) (ms n) (hms n)
  let H := fun n => CannonChart.extend E (f n)
  have hfprop (n : ℕ) := scalar_properties _ (w n) (hw n) (hadms n) (ms n) (hms n)
  have hHrange : ∀ n y, H n y ∈ Icc (0:ℝ) 1 := by
    intro n y
    by_cases hy : y ∈ range E
    · obtain ⟨z,rfl⟩ := hy
      change CannonChart.extend E (f n) (E z) ∈ Icc (0:ℝ) 1
      rw [CannonChart.extend_apply E hE.injective]
      exact (hfprop n).2.1 z
    · change Function.extend E (f n) (fun _ => 0) y ∈ Icc (0:ℝ) 1
      rw [Function.extend_apply' _ _ y hy]
      norm_num
  have hHcont (n : ℕ) : ContinuousOn (H n) Ω :=
    (continuousOn_extend E hE (f n) (hfprop n).1).mono interior_subset
  have hHlim : ∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn H (onDomain u) atTop K := by
    intro K hK hKΩ
    apply uniform_onDomain H u ?_ K hK hKΩ
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hflim
  obtain ⟨d₁,hd₁,hlateral⟩ := exists_chart_lateral_diameter E hE
  have hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ S : Set (Boundary D), IsCompact S ∧ IsConnected S ∧ d₁ ≤ diam S ∧
        (∀ y ∈ S, H n y = τ) ∧
        ∀ v w : Boundary D, ∀ γ : Path v w, range γ ⊆ Ω →
          H n v < τ → τ < H n w → (S ∩ range γ).Nonempty := by
    intro n τ hτ
    obtain ⟨S,hS,hSc,_hSU,hSd,hSH,hhit⟩ := scalar_ambient_level E hE
      (fun i => E ⁻¹' ball (p (Ns n) i) (2*r n)) (w n) (hw n) (hadms n)
      (ms n) (hms n) d₁ hlateral τ hτ
    refine ⟨S,hS,hSc,hSd,hSH,?_⟩
    intro v w γ hγ hv hw'
    obtain ⟨v',rfl⟩ := interior_subset (hγ γ.source_mem_range)
    obtain ⟨w',rfl⟩ := interior_subset (hγ γ.target_mem_range)
    have hv' : f n v' < τ := by simpa only [H,CannonChart.extend_apply E hE.injective] using hv
    have hw'' : τ < f n w' := by simpa only [H,CannonChart.extend_apply E hE.injective] using hw'
    obtain ⟨t,ht⟩ := hhit γ (fun t => interior_subset (hγ (mem_range_self t))) hv' hw''
    exact ⟨γ t,ht,mem_range_self t⟩
  apply boundary_holder_scalar_impossible D hδ φ (fun n => ι (Ns n)) (fun n => p (Ns n)) r
    hr hrlim (fun n => hpsep (Ns n)) (fun n => hpnet (Ns n)) Ω O P isOpen_interior hO hOc hOΩ
    hP hPc hPO u ⟨v₀,q.source_mem_range,w₀,q.target_mem_range,hqvar.ne⟩
    (Real.log lam/(2*Real.log a)) hα huholder z₀ d₀ hd₀ hsep H hHrange hHcont hHlim d₁ hd₁ hlevels
  intro g K hK hKU J hJ
  let gg := boundaryHomeomorph D ⟨δ,hδ⟩ g
  let B := 2*Real.exp (visualExponent δ*(2*(3*D.graph.dist 1 g⁻¹+4*δ):ℕ))
  let Ag := 2*Real.exp (visualExponent δ*(2*(3*D.graph.dist 1 g+4*δ):ℕ))
  have hAg : 0 < Ag := by dsimp [Ag]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hupper : ∀ x y, dist (gg.symm x) (gg.symm y) ≤ B*dist x y :=
    boundaryTranslate_lipschitz_bound D hδ g⁻¹
  have hlower : ∀ x y, Ag⁻¹*dist x y ≤ dist (gg.symm x) (gg.symm y) := by
    intro x y
    have hh : dist (gg (gg.symm x)) (gg (gg.symm y)) ≤ Ag*dist (gg.symm x) (gg.symm y) :=
      boundaryTranslate_lipschitz_bound D hδ g (gg.symm x) (gg.symm y)
    simp only [gg.apply_symm_apply] at hh
    calc Ag⁻¹*dist x y = dist x y/Ag := by ring
         _ ≤ dist (gg.symm x) (gg.symm y) := (div_le_iff₀ hAg).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨_C,_hC,_htail,hzero⟩ := transformed_scalar_energy_tail Q CP L J B Ag⁻¹ hpack hCP.le hL
    hJ hB (inv_pos.mpr hAg) hpaths E hE gg hlower hupper (fun n => ι (Ns n))
    (fun n => p (Ns n)) r hr hrlim (fun n => hpsep (Ns n)) w hw hadms ms hms
    (fun n => hmesh (ψ n)) (M ∘ Ns) (hMlim.comp hψ.tendsto_atTop) A hA.le
    (fun n => henergy (ψ n)) K hK hKU
  exact hzero

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryModulusSubexponential
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
section
section
namespace CannonRelease

open CannonGraph CannonVisual CannonCells CannonCharts Set Metric

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_modulus_subexponential_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    ∀ lam : ℝ, 1 < lam → ∃ B : ℝ, 0 < B ∧ ∀ n,
      modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d) ≤ B*lam^n := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro d hd hdia hdc ι hι p hsep hnet lam hlam
  have hn := boundary_exponential_records_impossible D hδ φ d hd hdia hdc ι p hsep hnet lam hlam
  have hbnd : ∃ B : ℝ, ∀ n,
      modulus (fun i => ball (p n i) (2*(Real.exp (2*visualExponent δ)^n)⁻¹))
        (macroFamily d)/lam^n ≤ B := by
    by_contra h
    apply hn
    intro B
    by_contra hB
    apply h
    refine ⟨B,fun n => ?_⟩
    exact le_of_not_gt (fun hh => hB ⟨n,hh⟩)
  obtain ⟨B,hB⟩ := hbnd
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),fun n => ?_⟩
  have hh := hB n
  have hl : 0 < lam^n := pow_pos (lt_trans zero_lt_one hlam) n
  exact (div_le_iff₀ hl).mp (hh.trans (le_max_left ..))

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

theorem solution.{v, u_1} : type_of% @OAI.CannonRelease.boundary_modulus_subexponential_oai.{v, u_1} := @OAI.CannonRelease.boundary_modulus_subexponential_oai.{v, u_1}
