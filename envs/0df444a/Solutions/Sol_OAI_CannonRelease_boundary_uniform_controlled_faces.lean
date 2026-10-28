-- Prove2me | solution 1 for OAI.CannonRelease.boundary_uniform_controlled_faces
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:15:17.958615+00:00
-- url     : https://prove2.me/submissions/11dcbba1-0fd9-4582-a569-267ea0f52a02

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

local instance instSetoidBasedRay_2_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_4_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_7_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_8_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_9_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Plane
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
namespace CannonRegularDisk
open Metric
open Set Metric Topology

section Topological
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma IsRegularDisk.isOpen {U : Set X} (hU : IsRegularDisk U) : IsOpen U := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  exact he.isOpenMap _ isOpen_ball

lemma IsRegularDisk.image {U : Set X} (hU : IsRegularDisk U) (f : X ≃ₜ Y) :
    IsRegularDisk (f '' U) := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  exact ⟨f ∘ e,f.isOpenEmbedding.comp he,q,r,hr,by rw [image_comp]⟩

lemma IsRegularDisk.preimage {U : Set Y} (hU : IsRegularDisk U) (f : X ≃ₜ Y) :
    IsRegularDisk (f ⁻¹' U) := by
  simpa only [Homeomorph.image_symm] using hU.image f.symm

end Topological

section Metric
variable {X : Type*} [MetricSpace X]

lemma small_regular_disk (φ : X ≃ₜ RoundSphere) (x : X) {η : ℝ} (hη : 0<η) :
    ∃ U : Set X, IsRegularDisk U ∧ x ∈ U ∧ closure U ⊆ ball x η := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (-φ x)
  have ht : h.target=univ := stereographic'_target _
  have hx : φ x ∈ h.source := by
    rw [show h.source={-φ x}ᶜ from stereographic'_source _]
    exact ne_neg_of_mem_unit_sphere ℝ (φ x)
  let e : Plane → X := φ.symm ∘ h.symm
  have he : IsOpenEmbedding e := φ.symm.isOpenEmbedding.comp (h.symm.isOpenEmbedding ht)
  let q := h (φ x)
  have heq : e q=x := by
    dsimp [e,q]
    rw [h.left_inv hx,φ.symm_apply_apply]
  have hn : e ⁻¹' ball x η ∈ 𝓝 q := by
    apply he.continuous.continuousAt.preimage_mem_nhds
    rw [heq]
    exact ball_mem_nhds x hη
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let U := e '' ball q (r/2)
  have hU : IsRegularDisk U := ⟨e,he,q,r/2,half_pos hr,rfl⟩
  refine ⟨U,hU,⟨q,mem_ball_self (half_pos hr),heq⟩,?_⟩
  have hc : closure U ⊆ e '' closedBall q (r/2) := by
    apply closure_minimal (image_mono ball_subset_closedBall)
    exact ((isCompact_closedBall q (r/2)).image he.continuous).isClosed
  rintro y hy
  obtain ⟨z,hz,rfl⟩ := hc hy
  exact hsub (hz.trans_lt (half_lt_self hr))

theorem uniform_regular_disk_neighborhoods [CompactSpace X] (φ : X ≃ₜ RoundSphere)
    {η : ℝ} (hη : 0<η) :
    ∃ e : ℝ, 0<e ∧ ∀ x : X, ∃ U : Set X,
      IsRegularDisk U ∧ ball x e ⊆ U ∧ closure U ⊆ ball x η := by
  choose U hU hmem hsmall using fun x => small_regular_disk φ x (half_pos hη)
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,hmem x⟩
  obtain ⟨e,he,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x => (hU x).isOpen) hcover
  refine ⟨e,he,fun x => ?_⟩
  obtain ⟨p,hp⟩ := hLeb x (mem_univ x)
  have hxp : dist x p < η/2 := hsmall p (subset_closure (hp (mem_ball_self he)))
  refine ⟨U p,hU p,hp,?_⟩
  intro y hy
  have hyp := hsmall p hy
  have htri := dist_triangle y p x
  rw [dist_comm p x] at htri
  change dist y x<η
  change dist y p<η/2 at hyp
  linarith
end Metric
end CannonRegularDisk

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
namespace CannonPaths
lemma expansion_image_small {R C s e d q : ℝ}
    (hR : 0<R) (hC : 0<C) (_hs : 0 < s) (hsR : s ≤ R)
    (he : 0<e) (hq : 0≤q) (hd : d<(e/C)*s)
    (hexp : q*R*max R d ≤ C*R*d) : q<e := by
  have hc : q*max R d ≤ C*d := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left (le_max_left R d) hq
  have hd' : C*d<e*s := by
    rw [div_mul_eq_mul_div] at hd
    have hh := (lt_div_iff₀ hC).mp hd
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsR he.le
  exact (mul_lt_mul_iff_right₀ hR).mp (by linarith)
end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths CannonRegularDisk Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance instSetoidBasedRay_14_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_controlled_regular_disks (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ c : ℝ, 0 < c ∧ c≤1 ∧ ∀ (x : Boundary D) (s : ℝ), 0 < s → s≤1 →
      ∃ U : Set (Boundary D), IsRegularDisk U ∧ ball x (c*s) ⊆ U ∧ closure U ⊆ ball x s := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1≤A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨e,he,hdisks⟩ := uniform_regular_disk_neighborhoods φ
    (show 0<1/(2*(B*A)) by positivity)
  let c := min 1 (e/C)
  have hc : 0 < c := lt_min zero_lt_one (div_pos he hC)
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro x s hs hsone
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hsone
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  obtain ⟨V,hV,hinner,houter⟩ := hdisks (f (Quotient.mk' r : Boundary D))
  have hcomm (z w : Boundary D) : boundaryDist D hδ z w = boundaryDist D hδ w z := dist_comm z w
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)=0 := dist_self _
  refine ⟨f ⁻¹' V,hV.preimage f,?_,?_⟩
  · intro y hy
    apply hinner
    have hy' : boundaryDist D hδ (Quotient.mk' r) y < c*s := by
      change boundaryDist D hδ y (Quotient.mk' r) < c*s at hy
      exact (hcomm (Quotient.mk' r) y).trans_lt hy
    have hy'' : boundaryDist D hδ (Quotient.mk' r) y < (e/C)*s :=
      hy'.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le)
    have hh := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).1
    change boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
      max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r))*
      max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y) ≤
      C*visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y at hh
    rw [hself,max_eq_left (visualScale_pos δ k).le] at hh
    have hsmall := expansion_image_small (visualScale_pos δ k) hC hs hk he dist_nonneg hy'' hh
    change boundaryDist D hδ (f y) (f (Quotient.mk' r)) < e
    rwa [hcomm]
  · intro y hy
    have hy' : f y ∈ closure V := by rwa [←f.preimage_closure] at hy
    have him : boundaryDist D hδ (f (Quotient.mk' r)) (f y)<1/(2*(B*A)) := by
      have hh := houter hy'
      change boundaryDist D hδ (f y) (f (Quotient.mk' r)) < 1/(2*(B*A)) at hh
      rwa [hcomm] at hh
    have hd : boundaryDist D hδ (Quotient.mk' r) y < s := by
      by_contra hn
      have hh := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
      change visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y ≤
        B*(boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r))*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at hh
      rw [hself,max_eq_left (visualScale_pos δ k).le] at hh
      have hfar := expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs
        dist_nonneg (le_of_not_gt hn) hk' hh
      have hhalf : 1/(2*(B*A))<1/(B*A) := by
        apply one_div_lt_one_div_of_lt (mul_pos hB hAp)
        nlinarith [mul_pos hB hAp]
      exact (hfar.trans_lt him).not_ge hhalf.le
    change boundaryDist D hδ y (Quotient.mk' r) < s
    exact (hcomm y (Quotient.mk' r)).trans_lt hd

end CannonRelease

end
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

local instance instSetoidBasedRay_27_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_29_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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

local instance instSetoidBasedRay_31_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryControlledDiskCover
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
namespace CannonDiskColoring
open Set Finset

attribute [local instance] Classical.propDecidable

lemma finite_relation_coloring {I : Type*} [Fintype I]
    (R : I → I → Prop) (hsym : ∀ ⦃left right⦄, R left right → R right left) {B : ℕ}
    (hdegree : ∀ i, ((Finset.univ : Finset I).filter (R i)).card ≤ B) :
    ∃ color : I → Fin (B+1), ∀ i j, i≠j → R i j → color i≠color j := by
  classical
  suffices ∀ S : Finset I, ∃ color : I → Fin (B+1),
      ∀ i∈S, ∀ j∈S, i≠j → R i j → color i≠color j by
    obtain ⟨color,h⟩ := this Finset.univ
    exact ⟨color,fun i j => h i (mem_univ _) j (mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc⟩ := ih
    let N := S.filter (R a)
    have hN : N.card ≤ B := (Finset.card_le_card (by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ i,(mem_filter.mp hi).2⟩)).trans (hdegree a)
    have hn : (N.image c).card < Fintype.card (Fin (B+1)) := by
      have hh := (card_image_le (s:=N) (f:=c)).trans hN
      simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hh
    obtain ⟨v,_,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (t:=Finset.univ) (by simpa only [card_univ] using hn)
    let d := Function.update c a v
    refine ⟨d,?_⟩
    intro i hi j hj hij hR
    by_cases hia : i=a
    · subst i
      have hja : j≠a := Ne.symm hij
      have hjS : j∈S := (Finset.mem_insert.mp hj).resolve_left hja
      have hcv : c j≠v := by
        intro h
        apply hv
        rw [←h]
        exact Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hjS,hR⟩)
      simpa only [d,Function.update_self,Function.update_of_ne hja] using hcv.symm
    · have hiS : i∈S := (Finset.mem_insert.mp hi).resolve_left hia
      by_cases hja : j=a
      · subst j
        have hcv : c i≠v := by
          intro h
          apply hv
          rw [←h]
          exact Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hiS,hsym hR⟩)
        simpa only [d,Function.update_self,Function.update_of_ne hia] using hcv
      · have hjS : j∈S := (Finset.mem_insert.mp hj).resolve_left hja
        simpa only [d,Function.update_of_ne hia,Function.update_of_ne hja] using hc i hiS j hjS hij hR

end CannonDiskColoring

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Plane
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

namespace CannonFiniteFaces

theorem finite_components_of_dense_regions {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {V : Set X} (hV : IsOpen V)
    {ι : Type*} [Finite ι] (S : ι → Set X)
    (hS : ∀ i, S i⊆V) (hc : ∀ i, IsPreconnected (S i))
    (hd : Dense (⋃ i, S i)) : Finite (ConnectedComponents V) := by
  classical
  let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let f : V → ConnectedComponents V := ConnectedComponents.mk
  have hf : Continuous f := ConnectedComponents.continuous_coe
  let U : ι → Set V := fun i => Subtype.val ⁻¹' S i
  have hUi (i : ι) : IsPreconnected (U i) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    have he : Subtype.val '' U i=S i := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hS i hx⟩,hx,rfl⟩
    rw [he]
    exact hc i
  have hfi (i : ι) : (f '' U i).Finite :=
    ((hUi i).image f hf.continuousOn).subsingleton.finite
  have hfin : (f '' (⋃ i, U i)).Finite := by
    rw [image_iUnion]
    exact finite_iUnion hfi
  have hden : Dense (⋃ i, U i) := by
    have hh := hd.preimage hV.isOpenMap_subtype_val
    simpa only [preimage_iUnion] using hh
  have hdenf : Dense (f '' (⋃ i, U i)) :=
    ConnectedComponents.surjective_coe.denseRange.dense_image hf hden
  have he : f '' (⋃ i, U i)=univ := hfin.isClosed.closure_eq.symm.trans hdenf.closure_eq
  exact finite_univ_iff.mp (he ▸ hfin)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma nonzero_functional_surjective (f : E →L[ℝ] ℝ) (hf : f≠0) :
    Function.Surjective f := by
  obtain ⟨v,hv⟩ : ∃ v, f v≠0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext v
    exact hn v
  intro y
  refine ⟨(y/f v) • v,?_⟩
  simp only [map_smul,smul_eq_mul]
  exact div_mul_cancel₀ y hv

theorem hyperplane_chambers {ι : Type*} [Finite ι]
    (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ) (hf : ∀ i, f i≠0) :
    ∃ S : (ι → Bool) → Set E,
      (∀ s, Convex ℝ (S s)) ∧ Dense (⋃ s, S s) ∧
      (∀ s, S s⊆{x | ∀ i, f i x≠c i}) := by
  classical
  let S : (ι → Bool) → Set E := fun s => ⋂ i,
    if s i=true then {x | c i<f i x} else {x | f i x < c i}
  have hconv (s : ι → Bool) : Convex ℝ (S s) := by
    apply convex_iInter
    intro i
    split_ifs
    · exact (convex_Ioi (c i)).linear_preimage (f i).toLinearMap
    · exact (convex_Iio (c i)).linear_preimage (f i).toLinearMap
  have heq : (⋃ s, S s)={x | ∀ i, f i x≠c i} := by
    ext x
    constructor
    · intro hx i
      obtain ⟨s,hs⟩ := mem_iUnion.mp hx
      have hh := mem_iInter.mp hs i
      split_ifs at hh with h
      · exact ne_of_gt hh
      · exact ne_of_lt hh
    · intro hx
      refine mem_iUnion.mpr ⟨fun i => decide (c i<f i x),?_⟩
      apply mem_iInter.mpr
      intro i
      dsimp
      split_ifs with hi
      · exact of_decide_eq_true hi
      · have hh : ¬c i<f i x := by simpa using hi
        exact lt_of_le_of_ne (le_of_not_gt hh) (hx i)
  have hopen (i : ι) : IsOpen {x | f i x≠c i} :=
    isOpen_compl_singleton.preimage (f i).continuous
  have hdense (i : ι) : Dense {x | f i x≠c i} :=
    (dense_compl_singleton (c i)).preimage
      ((f i).isOpenMap (nonzero_functional_surjective (f i) (hf i)))
  have hden : Dense {x | ∀ i, f i x≠c i} := by
    have hh := dense_iInter_of_isOpen hopen hdense
    simpa only [mem_iInter,ofPred_forall] using hh
  refine ⟨S,hconv,heq ▸ hden,?_⟩
  intro s
  rw [←heq]
  exact subset_iUnion S s

theorem segment_supporting_line (a b : Plane) :
    ∃ f : Plane →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  classical
  let x₀ : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let x₁ : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  by_cases hd : b 0=a 0
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 0 1)) h
      norm_num [x₀] at hh
    · have hcv : Convex ℝ {x | x₀ x=x₀ a} :=
        (convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap
      exact hcv.segment_subset rfl hd
  · let f := x₁-((b 1-a 1)/(b 0-a 0)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 1 1)) h
      norm_num [f,x₀,x₁,PiLp.single_apply] at hh
    · have hab : f b=f a := by
        change b 1-((b 1-a 1)/(b 0-a 0))*b 0=a 1-((b 1-a 1)/(b 0-a 0))*a 0
        have hn : b 0-a 0≠0 := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      have hcv : Convex ℝ {x | f x=f a} :=
        (convex_singleton (f a)).linear_preimage f.toLinearMap
      exact hcv.segment_subset rfl hab

theorem finite_components_chart_support {X : Type*} [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace X] [LocallyConnectedSpace X]
    (e : Plane → X) (he : IsOpenEmbedding e) (p : X) (heR : range e={p}ᶜ)
    {K : Set X} (hK : IsClosed K) (P : Finset (Plane×Plane))
    (hs : K⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) :
    Finite (ConnectedComponents (Kᶜ : Set X)) := by
  classical
  choose f hf hseg using fun q : P => segment_supporting_line q.val.1 q.val.2
  obtain ⟨S,hconv,hden,havoid⟩ := hyperplane_chambers f (fun q => f q q.val.1) hf
  have hsub (s : P → Bool) : e '' S s⊆Kᶜ := by
    rintro _ ⟨x,hx,rfl⟩ hxK
    obtain ⟨y,hy,hexy⟩ := hs hxK
    have hey : y=x := he.injective hexy
    subst y
    obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp hy
    exact havoid s hx ⟨q,hq⟩ (hseg ⟨q,hq⟩ hxq)
  have hde : DenseRange e := by
    change Dense (range e)
    rw [heR,dense_compl_singleton_iff_not_open]
    intro hopen
    have hall : ({p} : Set X)=univ :=
      (show IsClopen ({p} : Set X) from ⟨isClosed_singleton,hopen⟩).eq_univ
        (singleton_nonempty p)
    have hep : e 0=p := mem_singleton_iff.mp (hall.symm ▸ mem_univ (e 0))
    have hn : e 0∈({p}ᶜ : Set X) := heR ▸ mem_range_self 0
    exact hn (mem_singleton_iff.mpr hep)
  apply finite_components_of_dense_regions hK.isOpen_compl (fun s => e '' S s)
    hsub (fun s => (hconv s).isPreconnected.image e he.continuous.continuousOn)
  rw [←image_iUnion]
  exact hde.dense_image he.continuous hden

end CannonFiniteFaces

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_ExpansionGlobalUpper
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
namespace CannonPaths
lemma expansion_global_upper {R C d q a b : ℝ} (hR : 0<R) (hq : 0≤q)
    (hexp : q*max R a*max R b≤C*R*d) : q*R≤C*d := by
  have hh : q*R*R≤C*R*d := by
    calc
      q*R*R ≤ q*max R a*max R b := by gcongr <;> exact le_max_left ..
      _ ≤ C*R*d := hexp
  apply (mul_le_mul_iff_right₀ hR).mp
  nlinarith
end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance expansionGlobalUpperSetoid_r3a9fd7_1 : Setoid (BasedRay D) := raySetoid D
theorem boundary_uniform_expanding_homeomorphs :
    let _ := visualMetricSpace D hδ
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (x : Boundary D) (s : ℝ), 0 < s → s≤1 →
      ∃ f : Boundary D ≃ₜ Boundary D,
        (∀ y z, dist (f y) (f z)*s≤C*dist y z) ∧
        (∀ y, s≤dist x y → η≤dist (f x) (f y)) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1≤A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  refine ⟨C,1/(B*A),hC,by positivity,?_⟩
  intro x s hs hs₁
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hs₁
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  refine ⟨f,?_,?_⟩
  · intro y z
    have h := expansion_global_upper (visualScale_pos δ k) dist_nonneg
      (visual_expansion_ray D hδ r k y z).1
    change dist (f y) (f z)*visualScale δ k≤C*dist y z at h
    exact (mul_le_mul_of_nonneg_left hk dist_nonneg).trans h
  · intro y hy
    have h := (visual_expansion_ray D hδ r k (Quotient.mk' r) y).2
    change visualScale δ k*boundaryDist D hδ (Quotient.mk' r) y ≤
      B*(boundaryDist D hδ (f (Quotient.mk' r)) (f y)*
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)) *
        max (visualScale δ k) (boundaryDist D hδ (Quotient.mk' r) y)) at h
    have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r)=0 := dist_self _
    rw [hself,max_eq_left (visualScale_pos δ k).le] at h
    exact expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs dist_nonneg hy hk' h

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
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SpherePuncturedChart
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

namespace CannonPolygonal
open CannonRegularDisk

variable {X : Type*} [TopologicalSpace X]

theorem sphere_punctured_chart
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (p : X) :
    ∃ e : Plane → X, IsOpenEmbedding e ∧ range e={p}ᶜ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (φ p)
  have ht : h.target=univ := stereographic'_target _
  have hs : h.source={φ p}ᶜ := stereographic'_source _
  let e : Plane → X := φ.symm ∘ h.symm
  have he : IsOpenEmbedding e := φ.symm.isOpenEmbedding.comp (h.symm.isOpenEmbedding ht)
  refine ⟨e,he,?_⟩
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    change φ.symm (h.symm z)≠p
    intro hh
    have hz : h.symm z∈h.source := h.map_target (by rw [ht]; trivial)
    rw [hs] at hz
    apply hz
    have hh' := congrArg φ hh
    simpa only [φ.apply_symm_apply,mem_singleton_iff] using hh'
  · intro hx
    have hxp : φ x∈h.source := by
      rw [hs]
      exact fun hh => hx (mem_singleton_iff.mpr (φ.injective (mem_singleton_iff.mp hh)))
    refine ⟨h (φ x),?_⟩
    dsimp only [e,Function.comp_apply]
    rw [h.left_inv hxp,φ.symm_apply_apply]
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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Arc
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonEmbeddedArc.Arc.instFintypeRefinementIndex _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embedded arcs and compatible finite subdivisions. -/

section
section
section
noncomputable section
open Set unitInterval Topology

namespace CannonEmbeddedArc

variable {X : Type*} [TopologicalSpace X]

namespace Arc
lemma spliceFun_right (a b : Arc X) {u v t : I} (huv : u < v)
    (hend : b 1 = a v) (ht : v ≤ t) : spliceFun a b u v t = a t := by
  by_cases htv : t = v
  · subst t
    simp [spliceFun,not_le.mpr huv,div_self (sub_ne_zero.mpr (show (v : ℝ) ≠ u from ne_of_gt huv)),hend]
  · have hvt : v < t := lt_of_le_of_ne ht (Ne.symm htv)
    simp [spliceFun,not_le.mpr (huv.trans hvt),not_le.mpr hvt]

lemma splice_range_subset (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    range (splice a b huv hs he ha) ⊆ range a ∪ range b := by
  rintro _ ⟨t,rfl⟩
  change spliceFun a b u v t ∈ range a ∪ range b
  by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hs t ht]
    exact Or.inr (mem_range_self _)
  · rw [spliceFun_outside a b ht]
    exact Or.inl (mem_range_self _)

@[simp] lemma splice_one (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    splice a b huv hs he ha 1 = a 1 :=
  spliceFun_right a b huv he (unitInterval.le_one v)

lemma sliceParam_interior {u v t : I} (huv : u < v) (ht : t ∈ Ioo u v) :
    0 < sliceParam huv t ⟨ht.1.le,ht.2.le⟩ ∧
    sliceParam huv t ⟨ht.1.le,ht.2.le⟩ < 1 := by
  constructor
  · change 0 < ((t : ℝ)-u)/((v : ℝ)-u)
    exact div_pos (sub_pos.mpr ht.1) (sub_pos.mpr huv)
  · change ((t : ℝ)-u)/((v : ℝ)-u) < 1
    rw [div_lt_one (sub_pos.mpr (show (u : ℝ)<v from huv))]
    exact sub_lt_sub_right (show (t : ℝ)<v from ht.2) _

lemma spliceFun_same_outside_open (a b : Arc X) {u v t : I} (huv : u < v)
    (hend : b 1 = a v) (ht : t ∉ Ioo u v) :
    spliceFun a b u v t = a t := by
  rcases le_or_gt t u with h|h
  · exact spliceFun_left a b u v t h
  · exact spliceFun_right a b huv hend (le_of_not_gt (fun h' => ht ⟨h,h'⟩))

lemma splice_preimage (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (S : Set X) (hS : ∀ t : I, 0<t → t<1 → b t ∉ S) :
    (splice a b huv hs he ha) ⁻¹' S = (a ⁻¹' S) \ Ioo u v := by
  ext t
  change spliceFun a b u v t ∈ S ↔ a t ∈ S ∧ t ∉ Ioo u v
  by_cases ht : t ∈ Ioo u v
  · rw [spliceFun_middle a b huv hs t ⟨ht.1.le,ht.2.le⟩]
    have hi := sliceParam_interior huv ht
    simp [ht,hS _ hi.1 hi.2]
  · rw [spliceFun_same_outside_open a b huv he ht]
    simp [ht]

lemma ordConnected_sdiff_Ioo {S : Set I} (hS : OrdConnected S) {u v : I}
    (huv : u < v) (hne : ¬(u ∈ S ∧ v ∈ S)) : OrdConnected (S \ Ioo u v) := by
  constructor
  intro x hx y hy t ht
  refine ⟨hS.out hx.1 hy.1 ht,?_⟩
  intro htm
  have hxu : x ≤ u := le_of_not_gt (fun h => hx.2 ⟨h,ht.1.trans_lt htm.2⟩)
  have hvy : v ≤ y := le_of_not_gt (fun h => hy.2 ⟨htm.1.trans_le ht.2,h⟩)
  exact hne ⟨hS.out hx.1 hy.1 ⟨hxu,huv.le.trans hvy⟩,
    hS.out hx.1 hy.1 ⟨hxu.trans huv.le,hvy⟩⟩

lemma splice_ordConnected (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (S : Set X) (hS : ∀ t : I, 0<t → t<1 → b t ∉ S)
    (hc : OrdConnected (a ⁻¹' S)) (hne : ¬(b 0 ∈ S ∧ b 1 ∈ S)) :
    OrdConnected ((splice a b huv hs he ha) ⁻¹' S) := by
  rw [splice_preimage a b huv hs he ha S hS]
  apply ordConnected_sdiff_Ioo hc huv
  simpa only [mem_preimage,←hs,←he] using hne

lemma splice_target_preimage (a b e : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (hb : range b ⊆ range e)
    (hfirstlast : ∀ t : I, a t ∈ range e → t ∈ Icc u v) :
    (splice a b huv hs he ha) ⁻¹' range e = Icc u v := by
  ext t
  change spliceFun a b u v t ∈ range e ↔ t ∈ Icc u v
  by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hs t ht]
    exact ⟨fun _ => ht,fun _ => hb (mem_range_self _)⟩
  · rw [spliceFun_outside a b ht]
    exact ⟨fun hm => (ht (hfirstlast t hm)).elim,fun hm => (ht hm).elim⟩

lemma subarc_interior_parameter {p q t : I} (hpq : p≠q) (ht₀ : 0<t) (ht₁ : t<1) :
    0 < Icc.convexComb p q t ∧ Icc.convexComb p q t < 1 := by
  have hpq' : (p : ℝ)≠q := fun h => hpq (Subtype.ext h)
  have ht₀' : (0:ℝ)<t := ht₀
  have ht₁' : (t:ℝ)<1 := ht₁
  rcases lt_or_gt_of_ne hpq' with h|h
  · have h₀ : (p:ℝ)<(1-(t:ℝ))*p+(t:ℝ)*q := by nlinarith
    have h₁ : (1-(t:ℝ))*p+(t:ℝ)*q<(q:ℝ) := by nlinarith
    exact ⟨lt_of_le_of_lt p.property.1 h₀,lt_of_lt_of_le h₁ q.property.2⟩
  · have h₀ : (q:ℝ)<(1-(t:ℝ))*p+(t:ℝ)*q := by nlinarith
    have h₁ : (1-(t:ℝ))*p+(t:ℝ)*q<(p:ℝ) := by nlinarith
    exact ⟨lt_of_le_of_lt q.property.1 h₀,lt_of_lt_of_le h₁ p.property.2⟩

lemma Compatible.subarc_avoids {e f : Arc X} (h : Compatible e f)
    {p q : I} (hpq : p≠q) (t : I) (ht₀ : 0<t) (ht₁ : t<1) :
    e.subarc p q hpq t ∉ range f := by
  rintro ⟨s,hs⟩
  have hi := subarc_interior_parameter hpq ht₀ ht₁
  rcases (h.1 (Icc.convexComb p q t) s hs.symm).1 with he|he
  · exact (ne_of_gt hi.1) he
  · exact (ne_of_lt hi.2) he

lemma Compatible.subarc_not_both {e f : Arc X} (h : Compatible e f)
    {p q : I} (hpq : p≠q) : ¬(e.subarc p q hpq 0 ∈ range f ∧
      e.subarc p q hpq 1 ∈ range f) := by
  simp only [subarc_zero,subarc_one]
  rintro ⟨hp,hq⟩
  exact hpq (e.injective (h.2 ⟨mem_range_self _,hp⟩ ⟨mem_range_self _,hq⟩))

theorem repair_one [T2Space X] (a e : Arc X) :
    ∃ a' : Arc X, a' 0 = a 0 ∧ a' 1 = a 1 ∧
      OrdConnected (a' ⁻¹' range e) ∧
      range a' ⊆ range a ∪ range e ∧
      (∀ f : Arc X, Compatible e f →
        range a' ∩ range f ⊆ range a ∩ range f) ∧
      (∀ f : Arc X, Compatible e f → OrdConnected (a ⁻¹' range f) →
        OrdConnected (a' ⁻¹' range f)) ∧
      ((range a ∩ range e).Nonempty ∨ a'=a) := by
  classical
  by_cases hne : (a ⁻¹' range e).Nonempty
  · obtain ⟨u,v,huv,hu,hv,hfl⟩ := first_last a e hne
    have hmeet : (range a ∩ range e).Nonempty := ⟨a u,mem_range_self _,hu⟩
    rcases eq_or_lt_of_le huv with heq|huv
    · have hsingle : a ⁻¹' range e = {u} := by
        ext t
        constructor
        · intro ht
          apply mem_singleton_iff.mpr
          have h := hfl t ht
          exact le_antisymm (heq ▸ h.2) h.1
        · intro ht
          have htu : t=u := mem_singleton_iff.mp ht
          subst t
          exact hu
      refine ⟨a,rfl,rfl,?_,subset_union_left,fun _ _ => subset_rfl,
        fun _ _ h => h,Or.inl hmeet⟩
      rw [hsingle]
      exact ordConnected_singleton
    · obtain ⟨p,hp⟩ := hu
      obtain ⟨q,hq⟩ := hv
      have hpq : p≠q := by
        intro h
        have hav : a u = a v := hp.symm.trans ((congrArg e h).trans hq)
        exact huv.ne (a.injective hav)
      let b := e.subarc p q hpq
      have hs : b 0 = a u := (subarc_zero e p q hpq).trans hp
      have he : b 1 = a v := (subarc_one e p q hpq).trans hq
      have hb : range b ⊆ range e := subarc_range_subset e p q hpq
      have ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b :=
        fun t ht hm => ht (hfl t (hb hm))
      let a' := splice a b huv hs he ha
      refine ⟨a',splice_zero a b huv hs he ha,splice_one a b huv hs he ha,?_,?_,?_,?_,
        Or.inl hmeet⟩
      · rw [splice_target_preimage a b e huv hs he ha hb hfl]
        exact ordConnected_Icc
      · exact (splice_range_subset a b huv hs he ha).trans (union_subset_union subset_rfl hb)
      · intro f hf x hx
        obtain ⟨t,ht⟩ := hx.1
        have ht' : t ∈ a' ⁻¹' range f := by
          change a' t ∈ range f
          rw [ht]
          exact hx.2
        rw [splice_preimage a b huv hs he ha (range f)
          (fun t ht₀ ht₁ => hf.subarc_avoids hpq t ht₀ ht₁)] at ht'
        have heval : a' t = a t := spliceFun_same_outside_open a b huv he ht'.2
        exact ⟨⟨t,heval.symm.trans ht⟩,hx.2⟩
      · intro f hf hc
        exact splice_ordConnected a b huv hs he ha (range f)
          (fun t ht₀ ht₁ => hf.subarc_avoids hpq t ht₀ ht₁) hc
          (hf.subarc_not_both hpq)
  · have hempty : a ⁻¹' range e = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨a,rfl,rfl,?_,subset_union_left,fun _ _ => subset_rfl,
      fun _ _ h => h,Or.inr rfl⟩
    rw [hempty]
    exact ordConnected_empty

theorem repair_finite [T2Space X] {ι : Type*} (E : ι → Arc X) (S : Finset ι)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i≠j → Compatible (E i) (E j)) (a : Arc X) :
    ∃ a' : Arc X, a' 0 = a 0 ∧ a' 1 = a 1 ∧
      (∀ i ∈ S, OrdConnected (a' ⁻¹' range (E i))) ∧
      (∀ x ∈ range a', x ∈ range a ∨ ∃ i ∈ S,
        x ∈ range (E i) ∧ (range a ∩ range (E i)).Nonempty) ∧
      (∀ f : Arc X, (∀ i ∈ S, Compatible (E i) f) →
        range a' ∩ range f ⊆ range a ∩ range f) ∧
      (∀ f : Arc X, (∀ i ∈ S, Compatible (E i) f) →
        OrdConnected (a ⁻¹' range f) → OrdConnected (a' ⁻¹' range f)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨a,rfl,rfl,by simp,fun _ hx => Or.inl hx,fun _ _ => subset_rfl,
      fun _ _ h => h⟩
  | @insert i S hi ih =>
    have hpairS : ∀ i ∈ S, ∀ j ∈ S, i≠j → Compatible (E i) (E j) :=
      fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    obtain ⟨a₁,h₀,h₁,hconn,hsupp,hold,hretain⟩ := ih hpairS
    have hcomp : ∀ j ∈ S, Compatible (E j) (E i) := by
      intro j hj
      exact hpair j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
        (fun h => hi (h ▸ hj))
    have hcross := hold (E i) hcomp
    obtain ⟨a₂,h₂₀,h₂₁,h₂conn,h₂supp,h₂old,h₂retain,h₂change⟩ := repair_one a₁ (E i)
    refine ⟨a₂,h₂₀.trans h₀,h₂₁.trans h₁,?_,?_,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact h₂conn
      · exact h₂retain (E j) (hcomp j hj).symm (hconn j hj)
    · intro x hx
      by_cases hx₁ : x ∈ range a₁
      · rcases hsupp x hx₁ with hx₀|⟨j,hj,hxj,hjmeet⟩
        · exact Or.inl hx₀
        · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,hxj,hjmeet⟩
      · have hxi : x ∈ range (E i) := (h₂supp hx).resolve_left hx₁
        have hmeet : (range a ∩ range (E i)).Nonempty := by
          rcases h₂change with ⟨y,hy⟩|heq
          · exact ⟨y,hcross hy⟩
          · exact False.elim (hx₁ (heq ▸ hx))
        exact Or.inr ⟨i,Finset.mem_insert_self _ _,hxi,hmeet⟩
    · intro f hf
      exact (h₂old f (hf i (Finset.mem_insert_self _ _))).trans
        (hold f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    · intro f hf hc
      exact h₂retain f (hf i (Finset.mem_insert_self _ _))
        (hretain f (fun j hj => hf j (Finset.mem_insert_of_mem hj)) hc)

section Metric
variable {Y : Type*} [MetricSpace Y]

lemma separated_of_near (a b a' b' : Arc Y) {B L : ℝ}
    (ha : ∀ x ∈ range a', ∃ y ∈ range a, dist x y ≤ B)
    (hb : ∀ x ∈ range b', ∃ y ∈ range b, dist x y ≤ B)
    (hsep : ∀ x ∈ range a, ∀ y ∈ range b, L+2*B < dist x y) :
    ∀ x ∈ range a', ∀ y ∈ range b', L < dist x y := by
  intro x hx y hy
  obtain ⟨x₀,hx₀,hxx₀⟩ := ha x hx
  obtain ⟨y₀,hy₀,hyy₀⟩ := hb y hy
  have hfar := hsep x₀ hx₀ y₀ hy₀
  have htri := dist_triangle4 x₀ x y y₀
  rw [dist_comm x₀ x] at htri
  linarith

lemma meets_at_most_one (a b e : Arc Y) {B : ℝ}
    (hsep : ∀ x ∈ range a, ∀ y ∈ range b, B < dist x y)
    (he : Metric.diam (range e) ≤ B) :
    ¬ ((range a ∩ range e).Nonempty ∧ (range b ∩ range e).Nonempty) := by
  rintro ⟨⟨x,hxa,hxe⟩,⟨y,hyb,hye⟩⟩
  exact (hsep x hxa y hyb).not_ge
    ((Metric.dist_le_diam_of_mem e.compact_range.isBounded hxe hye).trans he)

end Metric

section Convex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

lemma mappedSegment_range (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y)
    {C : Set E} (hC : Convex ℝ C) (hx : x∈C) (hy : y∈C) :
    range (mappedSegment e he hinj x y hxy) ⊆ e '' C := by
  rintro _ ⟨t,rfl⟩
  refine ⟨Path.segment x y t,?_,rfl⟩
  rw [Path.segment_apply]
  exact hC.segment_subset hx hy (lineMap_mem_segment ℝ x y t.property)

end Convex

end Arc
end CannonEmbeddedArc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_HomeoPlane
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
namespace CannonRegularDisk
open Metric

universe u v
variable {X : Type u} [TopologicalSpace X]
lemma IsRegularDisk.homeo_plane {U : Set X} (hU : IsRegularDisk U) : Nonempty (U ≃ₜ Plane) := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  let b : Plane ≃ₜ ball q r := Homeomorph.unitBall.trans
    (OpenPartialHomeomorph.unitBallBall q r hr).toHomeomorphSourceTarget
  exact ⟨(b.trans (he.isEmbedding.homeomorphImage (ball q r))).symm⟩

lemma IsRegularDisk.tietzeExtension {U : Set X} (hU : IsRegularDisk U) :
    TietzeExtension.{v} U := by
  let : TietzeExtension.{v} Plane := TietzeExtension.of_homeo (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ))
  obtain ⟨e⟩ := hU.homeo_plane
  exact TietzeExtension.of_homeo e

theorem IsRegularDisk.extend {Y : Type v} [TopologicalSpace Y] [NormalSpace Y]
    {U : Set X} (hU : IsRegularDisk U) {S : Set Y} (hS : IsClosed S)
    (f : C(S,X)) (hf : ∀ y, f y∈U) :
    ∃ F : C(Y,X), (∀ y, F y∈U) ∧ F.restrict S=f := by
  let : TietzeExtension.{v} U := hU.tietzeExtension
  exact f.exists_forall_mem_restrict_eq hS hf

end CannonRegularDisk

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

theorem open_preconnected_arc {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y : E} (hx : x∈U) (hy : y∈U) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_open_preconnected hU hc hx hy) hne
end CannonPolygonal

namespace CannonRegularDisk
variable {X : Type*} [TopologicalSpace X]
lemma IsRegularDisk.isPathConnected {U : Set X} (hU : IsRegularDisk U) : IsPathConnected U := by
  obtain ⟨h⟩ := hU.homeo_plane
  let _ : PathConnectedSpace U := h.symm.surjective.pathConnectedSpace h.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

lemma IsRegularDisk.punctured_pathConnected [T1Space X] {U : Set X}
    (hU : IsRegularDisk U) (p : X) : IsPathConnected (U\{p}) := by
  by_cases hp : p∈U
  · obtain ⟨h⟩ := hU.homeo_plane
    let q : U := ⟨p,hp⟩
    have hc := isPathConnected_compl_singleton_of_one_lt_rank (E:=Plane)
      (by rw [←Module.finrank_eq_rank]; simp) (h q)
    have hi := hc.image (continuous_subtype_val.comp h.symm.continuous)
    have heq : (fun z : Plane => (h.symm z).val) '' {h q}ᶜ=U\{p} := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨(h.symm z).property,?_⟩
        intro he
        have he' : h.symm z=q := Subtype.ext (mem_singleton_iff.mp he)
        have hh := congrArg h he'
        exact hz (by simpa using hh)
      · rintro ⟨hx,hxp⟩
        refine ⟨h ⟨x,hx⟩,?_,by simp⟩
        intro he
        apply hxp
        have hh := h.injective (mem_singleton_iff.mp he)
        exact mem_singleton_iff.mpr (congrArg Subtype.val hh)
    change IsPathConnected ((fun z : Plane => (h.symm z).val) '' {h q}ᶜ) at hi
    rwa [heq] at hi
  · have heq : U\{p}=U := by
      ext x
      simp only [mem_sdiff,mem_singleton_iff]
      exact ⟨And.left,fun hx => ⟨hx,fun h => hp (h ▸ hx)⟩⟩
    rw [heq]
    exact hU.isPathConnected
end CannonRegularDisk

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {X : Type*} [TopologicalSpace X] [T1Space X]

theorem regular_disk_chart_arc (e : Plane → X) (he : IsOpenEmbedding e)
    (p : X) (hrange : range e={p}ᶜ) {U : Set X} (hU : IsRegularDisk U)
    {x y : X} (hx : x∈U) (hy : y∈U) (hxp : x≠p) (hyp : y≠p) (hxy : x≠y) :
    ∃ a : Arc X, a 0=x ∧ a 1=y ∧ range a⊆U ∧
      ∃ P : Finset (Plane×Plane), range a⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
  let V := U\{p}
  have hV : IsOpen V := hU.isOpen.sdiff isClosed_singleton
  have hVc : IsPathConnected V := hU.punctured_pathConnected p
  have hVs : V⊆range e := by intro z hz; rw [hrange]; exact hz.2
  have hc : IsPreconnected (e ⁻¹' V) :=
    hVc.isConnected.isPreconnected.preimage_of_isOpenMap he.injective he.isOpenMap hVs
  obtain ⟨u,hu⟩ := hVs ⟨hx,by simpa using hxp⟩
  obtain ⟨v,hv⟩ := hVs ⟨hy,by simpa using hyp⟩
  have huv : u≠v := fun h => hxy (hu.symm.trans ((congrArg e h).trans hv))
  obtain ⟨b,hb₀,hb₁,hbV,P,hP⟩ := open_preconnected_arc (hV.preimage he.continuous) hc
    (show u∈e ⁻¹' V from by rw [mem_preimage,hu]; exact ⟨hx,by simpa using hxp⟩)
    (show v∈e ⁻¹' V from by rw [mem_preimage,hv]; exact ⟨hy,by simpa using hyp⟩) huv
  let a : Arc X := ⟨⟨fun t => e (b t),he.continuous.comp b.continuous⟩,he.injective.comp b.injective⟩
  refine ⟨a,(congrArg e hb₀).trans hu,(congrArg e hb₁).trans hv,?_,P,?_⟩
  · rintro _ ⟨t,rfl⟩
    exact (hbV (mem_range_self t)).1
  · rintro _ ⟨t,rfl⟩
    exact ⟨b t,hP (mem_range_self t),rfl⟩
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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_NetJoined
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

namespace CannonGraphCore
variable {X : Type*} [MetricSpace X] [PreconnectedSpace X]

theorem net_joined {r : ℝ} (hr : 0 < r) (T Q : Set X) (hTQ : T⊆Q)
    (hcover : ∀ x : X, ∃ t∈T, dist x t ≤ r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r → JoinedIn Q x y)
    {a : X} (ha : a∈T) : ∀ b∈T, JoinedIn Q a b := by
  let U := ⋃ (t : X) (_ : t∈T) (_ : JoinedIn Q a t), ball t (2*r)
  let V := ⋃ (t : X) (_ : t∈T) (_ : ¬JoinedIn Q a t), ball t (2*r)
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    simp only [U,mem_iUnion] at hzU
    obtain ⟨t,ht,hjt,hzt⟩ := hzU
    simp only [V,mem_iUnion] at hzV
    obtain ⟨u,hu,hju,hzu⟩ := hzV
    have hdt : dist z t<2*r := hzt
    have hdu : dist z u<2*r := hzu
    have htu : dist t u<4*r := by
      have hh := dist_triangle t z u
      rw [dist_comm t z] at hh
      linarith
    exact hju (hjt.trans (hjoin t ht u hu htu))
  have hcover' : (univ : Set X)⊆U∪V := by
    intro x _
    obtain ⟨t,ht,hxt⟩ := hcover x
    have hxt' : x∈ball t (2*r) := hxt.trans_lt (by linarith)
    by_cases hj : JoinedIn Q a t
    · exact Or.inl (mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨ht,mem_iUnion.mpr ⟨hj,hxt'⟩⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨ht,mem_iUnion.mpr ⟨hj,hxt'⟩⟩⟩)
  have haU : a∈U := mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨ha,
    mem_iUnion.mpr ⟨JoinedIn.refl (hTQ ha),mem_ball_self (by positivity)⟩⟩⟩
  have hall := isPreconnected_univ.subset_left_of_subset_union hU hV hdisj hcover' ⟨a,mem_univ a,haU⟩
  intro b hb
  have hbU := hall (mem_univ b)
  simp only [U,mem_iUnion] at hbU
  obtain ⟨t,ht,hjt,hbt⟩ := hbU
  apply hjt.trans (hjoin t ht b hb ?_)
  have hbt' : dist b t<2*r := hbt
  rw [dist_comm]
  linarith

end CannonGraphCore

namespace CannonGraphCore
variable {X ι : Type*} [TopologicalSpace X]

theorem component_whole_edges (E : ι → C(I,X)) (T : Set X) (a : X)
    (_ha : a∈T)
    (hT : ∀ t∈T, JoinedIn ((⋃ i, range (E i))∪T) a t) :
    let Q := (⋃ i, range (E i))∪T
    let J := {i : ι // E i 0∈pathComponentIn Q a}
    pathComponentIn Q a = (⋃ j : J, range (E j.val))∪T := by
  dsimp only
  let Q := (⋃ i, range (E i))∪T
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  have hed (i : ι) : range (E i)⊆Q := by
    intro x hx
    exact Or.inl (mem_iUnion.mpr ⟨i,hx⟩)
  have hc (i : ι) : IsPathConnected (range (E i)) := isPathConnected_range (E i).continuous
  apply Set.Subset.antisymm
  · intro x hx
    rcases pathComponentIn_subset hx with h|h
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      have h₀ : E i 0∈pathComponentIn Q a := hx.trans ((hc i).joinedIn x hi _ (mem_range_self 0) |>.mono (hed i))
      exact Or.inl (mem_iUnion.mpr ⟨⟨i,h₀⟩,hi⟩)
    · exact Or.inr h
  · intro x hx
    rcases hx with h|h
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact i.property.trans ((hc i.val).joinedIn _ (mem_range_self 0) _ hi |>.mono (hed i.val))
    · exact hT x h

theorem path_range_in_component {Q : Set X} {a x y : X} (hax : JoinedIn Q a x)
    (p : Path x y) (hp : range p⊆Q) : range p⊆pathComponentIn Q a := by
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  intro z hz
  have hc : IsPathConnected (range p) := isPathConnected_range p.continuous
  have hx : x∈range p := ⟨0,p.source⟩
  exact hax.trans ((hc.joinedIn x hx z hz).mono hp)
end CannonGraphCore

namespace CannonGraphCore
variable {X ι : Type*} [TopologicalSpace X]
theorem component_retains_edges (E : ι → C(I,X)) {Q : Set X} {a x : X}
    (hEQ : (⋃ i, range (E i))⊆Q) (hx : x∈pathComponentIn Q a)
    (hxE : x∈⋃ i, range (E i)) :
    x∈⋃ j : {i : ι // E i 0∈pathComponentIn Q a}, range (E j.val) := by
  let _ : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxE
  have h₀ : E i 0∈pathComponentIn Q a := hx.trans
    (((isPathConnected_range (E i).continuous).joinedIn x hi _ (mem_range_self 0)).mono
      (fun z hz => hEQ (mem_iUnion.mpr ⟨i,hz⟩)))
  exact mem_iUnion.mpr ⟨⟨i,h₀⟩,hi⟩
end CannonGraphCore

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

namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma segments_card (P : Finset I) : (segments P).card ≤ P.card^2 := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp [Finset.card_product,pow_two])

end Arc
end CannonEmbeddedArc

noncomputable section
namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma subdivision_mark_vertex (a : Arc X) (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P)
    {t : I} (ht : t∈P) : Vertex (subdivArc a P) (a t) := by
  obtain ⟨p,q,hpq,hpt,htq⟩ := consecutive_cover P h₀ h₁ t
  let z : segments P := ⟨(p,q),(mem_segments P p q).mpr hpq⟩
  refine ⟨z,?_⟩
  by_cases htp : t=p
  · exact Or.inl (by simp [z,htp])
  · have htq : t=q := by
      by_contra h
      exact hpq.2.2.2 t ht (lt_of_le_of_ne hpt (Ne.symm htp)) (lt_of_le_of_ne htq h)
    exact Or.inr (by simp [z,htq])

variable {ι κ : Type*} (E : ι → Arc X) (A : κ → Arc X)
    (P : κ → Finset I) (Q : ι → Finset I)

variable (hE : Pairwise (fun e f => Compatible (E e) (E f)))
    (hA : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))))
    (hinterval : ∀ i e, (A i ⁻¹' range (E e))=∅ ∨
      ∃ u∈P i, ∃ v∈P i, u≤v ∧ A i ⁻¹' range (E e)=Icc u v)
    (hmark : ∀ i e t, E e t∈A i '' (P i : Set I) → t∈Q e)

variable (hP₀ : ∀ i, 0∈P i) (hP₁ : ∀ i, 1∈P i)
    (hQ₀ : ∀ e, 0∈Q e) (hQ₁ : ∀ e, 1∈Q e)

include hQ₀ hQ₁ in
lemma refinement_old_mark_vertex (e : ι) {t : I} (ht : t∈Q e) :
    Vertex (refinementArc E A P Q) (E e t) := by
  obtain ⟨z,hz⟩ := subdivision_mark_vertex (E e) (Q e) (hQ₀ e) (hQ₁ e) ht
  exact ⟨Sum.inl ⟨e,z⟩,hz⟩

include hmark hP₀ hP₁ hQ₀ hQ₁ in
lemma refinement_new_mark_vertex (i : κ) {t : I} (ht : t∈P i) :
    Vertex (refinementArc E A P Q) (A i t) := by
  classical
  by_cases h : ∃ e, A i t∈range (E e)
  · obtain ⟨e,w,hw⟩ := h
    rw [← hw]
    apply refinement_old_mark_vertex E A P Q hQ₀ hQ₁ e
    exact hmark i e w ⟨t,ht,hw.symm⟩
  · obtain ⟨z,hz⟩ := subdivision_mark_vertex (A i) (P i) (hP₀ i) (hP₁ i) ht
    have hf : FreeSegment E A P i z := by
      intro e he
      apply h
      refine ⟨e,he ?_⟩
      rcases hz with hz|hz
      · exact ⟨0,hz⟩
      · exact ⟨1,hz⟩
    exact ⟨Sum.inr ⟨i,⟨z,hf⟩⟩,hz⟩

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
open Set unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma free_segment_original [T2Space X] {ι : Type*} (E : ι → Arc X)
    (a b : Arc X) (P : Finset I) (z : segments P)
    (hinterval : ∀ e, (b ⁻¹' range (E e))=∅ ∨
      ∃ u∈P, ∃ v∈P, u≤v ∧ b ⁻¹' range (E e)=Icc u v)
    (hfree : ∀ e, ¬range (subdivArc b P z) ⊆ range (E e))
    (hsupp : ∀ x∈range b, x∈range a ∨ ∃ e, x∈range (E e)) :
    range (subdivArc b P z) ⊆ range a := by
  apply range_subset_of_interior a.compact_range.isClosed
  intro t ht₀ ht₁
  rcases hsupp _ (subdivArc_range_subset b P z (mem_range_self t)) with h|⟨e,he⟩
  · exact h
  · obtain h|h := (free_segment_intersection (segment_consecutive P z)
      (hinterval e) (hfree e)).1 t he
    · exact (ht₀ h).elim
    · exact (ht₁ h).elim

lemma intersectionCount_eq_card {ι : Type*} [Fintype ι] (E : ι → Arc X) (S : Set X) :
    intersectionCount E S = by classical exact (Finset.univ.filter
      (fun i => (range (E i) ∩ S).Nonempty)).card := by
  classical
  simp only [intersectionCount,Finset.sum_boole,Nat.cast_id]

lemma sum_indicator_le_card {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (∑ i, if p i then 1 else 0) ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = _ := by simp

lemma refinement_local_count {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (A B : κ → Arc X) (P : κ → Finset I) (Q : ι → Finset I)
    (hsource : ∀ i z, FreeSegment E A P i z → range (subdivArc (A i) (P i) z) ⊆ range (B i))
    (p q : ℕ) (hP : ∀ i, (P i).card≤p) (hQ : ∀ e, (Q e).card≤q) (S : Set X) :
    intersectionCount (refinementArc E A P Q) S ≤
      intersectionCount E S*q^2 + intersectionCount B S*p^2 := by
  classical
  unfold intersectionCount
  change (∑ z : (Σ e : ι, segments (Q e)) ⊕
    (Σ i : κ, {z : segments (P i) // FreeSegment E A P i z}),
    if (range (refinementArc E A P Q z) ∩ S).Nonempty then 1 else 0) ≤ _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma]
  apply Nat.add_le_add
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    by_cases he : (range (E e) ∩ S).Nonempty
    · simp only [he,ite_true,one_mul]
      calc
        _ ≤ Fintype.card (segments (Q e)) := sum_indicator_le_card _
        _ = (segments (Q e)).card := Fintype.card_coe _
        _ ≤ (Q e).card^2 := segments_card _
        _ ≤ q^2 := Nat.pow_le_pow_left (hQ e) 2
    · simp only [he,ite_false,zero_mul]
      apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro z _
      apply ite_eq_right
      rintro ⟨x,hx,hS⟩
      exact he ⟨x,subdivArc_range_subset (E e) (Q e) z hx,hS⟩
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (range (B i) ∩ S).Nonempty
    · simp only [hi,ite_true,one_mul]
      calc
        _ ≤ Fintype.card {z : segments (P i) // FreeSegment E A P i z} := sum_indicator_le_card _
        _ ≤ Fintype.card (segments (P i)) := Fintype.card_subtype_le _
        _ = (segments (P i)).card := Fintype.card_coe _
        _ ≤ (P i).card^2 := segments_card _
        _ ≤ p^2 := Nat.pow_le_pow_left (hP i) 2
    · simp only [hi,ite_false,zero_mul]
      apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro z _
      apply ite_eq_right
      rintro ⟨x,hx,hS⟩
      exact hi ⟨x,hsource i z.val z.property hx,hS⟩

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IncidentEdges
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
namespace CannonEmbeddedArc
open Set Metric unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [MetricSpace X]

theorem repair_local {ι : Type*} [Fintype ι] (E : ι → Arc X)
    (hE : Pairwise (fun e f => Compatible (E e) (E f))) (a : Arc X)
    {B : ℝ} (hB : 0≤B) (hdiam : ∀ e, diam (range (E e))≤B) :
    ∃ b : Arc X, b 0=a 0 ∧ b 1=a 1 ∧
      (∀ e, OrdConnected (b ⁻¹' range (E e))) ∧
      (∀ x∈range b, x∈range a ∨ ∃ e, x∈range (E e)) ∧
      (∀ x∈range b, ∃ y∈range a, dist x y≤B) ∧
      (∀ e, (range b ∩ range (E e)).Nonempty → (range a ∩ range (E e)).Nonempty) ∧
      diam (range b)≤diam (range a)+2*B := by
  classical
  let S := Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)
  obtain ⟨b,h₀,h₁,hconn,hsupp,hcross,_⟩ := repair_finite E S (fun e _ f _ hef => hE hef) a
  have hnew (e : ι) (he : (range b ∩ range (E e)).Nonempty) :
      (range a ∩ range (E e)).Nonempty := by
    by_cases heS : e∈S
    · exact (Finset.mem_filter.mp heS).2
    · have hcomp : ∀ f∈S, Compatible (E f) (E e) := by
        intro f hf
        exact hE (fun h => heS (h ▸ hf))
      exact he.mono (hcross (E e) hcomp)
  have hnear : ∀ x∈range b, ∃ y∈range a, dist x y≤B := by
    intro x hx
    rcases hsupp x hx with hxa|⟨e,he,hxe,y,hya,hye⟩
    · exact ⟨x,hxa,by simpa using hB⟩
    · exact ⟨y,hya,(Metric.dist_le_diam_of_mem (E e).compact_range.isBounded hxe hye).trans
        (hdiam e)⟩
  refine ⟨b,h₀,h₁,?_,?_,hnear,hnew,?_⟩
  · intro e
    by_cases he : e∈S
    · exact hconn e he
    · have hempty : b ⁻¹' range (E e)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e,
          hnew e ⟨b t,mem_range_self t,ht⟩⟩)
      rw [hempty]
      exact ordConnected_empty
  · intro x hx
    rcases hsupp x hx with h|⟨e,_,he,_⟩
    · exact Or.inl h
    · exact Or.inr ⟨e,he⟩
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    obtain ⟨x₀,hx₀,hxx₀⟩ := hnear x hx
    obtain ⟨y₀,hy₀,hyy₀⟩ := hnear y hy
    have hxy₀ := Metric.dist_le_diam_of_mem a.compact_range.isBounded hx₀ hy₀
    have htri := dist_triangle4 x x₀ y₀ y
    rw [dist_comm y₀ y] at htri
    linarith

lemma original_incidence_count {ι : Type*} [Fintype ι] (E : ι → Arc X) (a : Arc X)
    {B : ℝ} (hB : 0<B) (ha : diam (range a)≤B) (M : ℕ)
    (hcount : ∀ x, intersectionCount E (ball x (2*B))≤M) :
    (incidentEdges E a).card≤M := by
  classical
  have hsub : (Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)) ⊆
      Finset.univ.filter (fun e => (range (E e) ∩ ball (a 0) (2*B)).Nonempty) := by
    intro e he
    obtain ⟨x,hxa,hxe⟩ := (Finset.mem_filter.mp he).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ e,x,hxe,?_⟩
    exact ((Metric.dist_le_diam_of_mem a.compact_range.isBounded hxa (mem_range_self 0)).trans ha).trans_lt
      (by linarith)
  have hc := hcount (a 0)
  rw [intersectionCount_eq_card] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma breakpoints_local {ι : Type*} [Fintype ι] (E : ι → Arc X) (a b : Arc X) (M : ℕ)
    (hM : (incidentEdges E a).card≤M)
    (hconn : ∀ e, OrdConnected (b ⁻¹' range (E e)))
    (hnew : ∀ e, (range b ∩ range (E e)).Nonempty → (range a ∩ range (E e)).Nonempty) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧ P.card≤2*M+2 ∧
      ∀ e, (b ⁻¹' range (E e))=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ b ⁻¹' range (E e)=Icc u v := by
  classical
  let S := Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)
  obtain ⟨P,h₀,h₁,hcard,hP⟩ := finite_breakpoints E S b (fun e _ => hconn e)
  refine ⟨P,h₀,h₁,hcard.trans (by dsimp [S,incidentEdges] at *; omega),?_⟩
  intro e
  by_cases he : e∈S
  · exact hP e he
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e,hnew e ⟨b t,mem_range_self t,ht⟩⟩)

lemma simultaneous_old_breakpoints {ι κ : Type*} (E : ι → Arc X) (A : κ → Arc X)
    (P : κ → Finset I) (p : ℕ) (hP : ∀ i, (P i).card≤p)
    (hunique : ∀ e i j, (range (A i) ∩ range (E e)).Nonempty →
      (range (A j) ∩ range (E e)).Nonempty → i=j) :
    ∃ Q : ι → Finset I, (∀ e, 0∈Q e ∧ 1∈Q e ∧ (Q e).card≤p+2) ∧
      (∀ i e t, E e t∈A i '' (P i : Set I) → t∈Q e) := by
  classical
  have hex (e : ι) : ∃ Q : Finset I, 0∈Q ∧ 1∈Q ∧ Q.card≤p+2 ∧
      ∀ i t, E e t∈A i '' (P i : Set I) → t∈Q := by
    by_cases hmeet : ∃ i, (range (A i) ∩ range (E e)).Nonempty
    · obtain ⟨i,hi⟩ := hmeet
      obtain ⟨Q,h₀,h₁,hcard,hmark⟩ := old_breakpoints (A i) (E e) (P i)
      refine ⟨Q,h₀,h₁,hcard.trans (Nat.add_le_add_right (hP i) 2),?_⟩
      intro j t ht
      have hji : j=i := hunique e j i ⟨E e t,image_subset_range _ _ ht,mem_range_self t⟩ hi
      subst j
      exact hmark t ht
    · refine ⟨{0,1},by simp,by simp,by simp,?_⟩
      intro i t ht
      exact (hmeet ⟨i,E e t,image_subset_range _ _ ht,mem_range_self t⟩).elim
  choose Q hQ using hex
  exact ⟨Q,fun e => ⟨(hQ e).1,(hQ e).2.1,(hQ e).2.2.1⟩,fun i e => (hQ e).2.2.2 i⟩

lemma count_ball_le_one {κ : Type*} [Fintype κ] (A : κ → Arc X) {B : ℝ}
    (hsep : ∀ i j, i≠j → ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y)
    (x : X) : intersectionCount A (ball x (2*B))≤1 := by
  classical
  rw [intersectionCount_eq_card]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  obtain ⟨y,hy,hry⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨z,hz,hrz⟩ := (Finset.mem_filter.mp hj).2
  have hfar := hsep i j hne y hy z hz
  have ht := dist_triangle y x z
  rw [dist_comm x z] at ht
  change dist y x<2*B at hry
  change dist z x<2*B at hrz
  linarith

lemma intersectionCount_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (e : κ ≃ ι) (S : Set X) :
    intersectionCount (E ∘ e) S=intersectionCount E S := by
  classical
  exact e.sum_comp (fun i => if (range (E i) ∩ S).Nonempty then (1:ℕ) else 0)

lemma support_reindex {ι κ : Type*} (E : ι → Arc X) (e : κ ≃ ι) :
    (⋃ j, range ((E ∘ e) j))=⋃ i, range (E i) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨e j,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.symm i,by simpa using hi⟩

lemma vertex_reindex {ι κ : Type*} (E : ι → Arc X) (e : κ ≃ ι) (x : X) :
    Vertex (E ∘ e) x ↔ Vertex E x := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨e j,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.symm i,by simpa using hi⟩

theorem separated_stage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (A : κ → Arc X) {B : ℝ} (hB : 0<B) (M : ℕ)
    (hE : Pairwise (fun e f => Compatible (E e) (E f)))
    (hEd : ∀ e, diam (range (E e))≤B) (hAd : ∀ i, diam (range (A i))≤B)
    (hcount : ∀ x, intersectionCount E (ball x (2*B))≤M)
    (hsep : ∀ i j, i≠j → ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (⋃ e, range (E e)) ⊆ (⋃ j, range (F j)) ∧
      (∀ x, Vertex E x → Vertex F x) ∧
      (∀ i, Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ stageBound M) ∧
      (⋃ j, range (F j)) ⊆ (⋃ e, range (E e)) ∪ (⋃ i, range (A i)) := by
  classical
  choose A' h₀ h₁ hconn hsupp hnear hnew hdiam using
    fun i => repair_local E hE (A i) hB.le hEd
  have hsep' (i j : κ) (hij : i≠j) :
      ∀ x∈range (A' i), ∀ y∈range (A' j), B<dist x y := by
    apply separated_of_near (A i) (A j) (A' i) (A' j) (hnear i) (hnear j)
    intro x hx y hy
    have hh := hsep i j hij x hx y hy
    linarith
  have hdisj : Pairwise (fun i j => Disjoint (range (A' i)) (range (A' j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hh := hsep' i j hij x hi x hj
    simp only [dist_self] at hh
    linarith
  have hunique (e : ι) (i j : κ) (hi : (range (A' i) ∩ range (E e)).Nonempty)
      (hj : (range (A' j) ∩ range (E e)).Nonempty) : i=j := by
    by_contra hij
    exact meets_at_most_one (A' i) (A' j) (E e) (hsep' i j hij) (hEd e) ⟨hi,hj⟩
  choose P hP₀ hP₁ hPcard hinterval using fun i => breakpoints_local E (A i) (A' i) M
    (original_incidence_count E (A i) hB (hAd i) M hcount) (hconn i) (hnew i)
  obtain ⟨Q,hQ,hmark⟩ := simultaneous_old_breakpoints E A' P (2*M+2) hPcard hunique
  have hQcard (e : ι) : (Q e).card≤2*M+4 := by have h := (hQ e).2.2; omega
  let R := RefinementIndex E A' P Q
  let F₀ : R → Arc X := refinementArc E A' P Q
  have hcomp : Pairwise (fun e f => Compatible (F₀ e) (F₀ f)) :=
    refinement_compatible E A' P Q hE hdisj hinterval hmark
  have hsource (i : κ) (z : segments (P i)) (hz : FreeSegment E A' P i z) :
      range (subdivArc (A' i) (P i) z) ⊆ range (A i) :=
    free_segment_original E (A i) (A' i) (P i) z (hinterval i) hz (hsupp i)
  have hcover : (⋃ e, range (E e)) ∪ (⋃ i, range (A' i))=⋃ j, range (F₀ j) :=
    refinement_cover E A' P Q hP₀ hP₁ (fun e => (hQ e).1) (fun e => (hQ e).2.1)
  have hdF (j : R) : diam (range (F₀ j))≤B := by
    rcases j with ⟨e,z⟩|⟨i,z⟩
    · exact (Metric.diam_mono (subdivArc_range_subset (E e) (Q e) z)
        (E e).compact_range.isBounded).trans (hEd e)
    · exact (Metric.diam_mono (hsource i z.val z.property)
        (A i).compact_range.isBounded).trans (hAd i)
  have hcF (x : X) : intersectionCount F₀ (ball x (2*B))≤ stageBound M := by
    have hc := refinement_local_count E A' A P Q hsource (2*M+2) (2*M+4) hPcard hQcard (ball x (2*B))
    have hm := hcount x
    have ha := count_ball_le_one A hsep x
    have ha' : intersectionCount A (ball x (2*B))*(2*M+2)^2 ≤ (2*M+2)^2 := by
      calc
        _ ≤ 1*(2*M+2)^2 := Nat.mul_le_mul_right _ ha
        _ = _ := one_mul _
    exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hm) ha')
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let F : Fin (Fintype.card R) → Arc X := F₀ ∘ e
  have hsF : (⋃ j, range (F j))=⋃ j, range (F₀ j) := support_reindex F₀ e
  refine ⟨Fintype.card R,F,fun i j hij => hcomp (fun h => hij (e.injective h)),?_,?_,?_,?_,
    fun j => hdF (e j),?_,?_⟩
  · rw [hsF,← hcover]
    exact subset_union_left
  · intro x hx
    rw [vertex_reindex]
    obtain ⟨j,hj⟩ := hx
    rcases hj with hj|hj
    · rw [← hj]
      exact refinement_old_mark_vertex E A' P Q (fun e => (hQ e).1) (fun e => (hQ e).2.1)
        j (hQ j).1
    · rw [← hj]
      exact refinement_old_mark_vertex E A' P Q (fun e => (hQ e).1) (fun e => (hQ e).2.1)
        j (hQ j).2.1
  · intro i
    rw [vertex_reindex,vertex_reindex,← h₀ i,← h₁ i]
    exact ⟨refinement_new_mark_vertex E A' P Q hmark hP₀ hP₁
      (fun e => (hQ e).1) (fun e => (hQ e).2.1) i (hP₀ i),
      refinement_new_mark_vertex E A' P Q hmark hP₀ hP₁
      (fun e => (hQ e).1) (fun e => (hQ e).2.1) i (hP₁ i)⟩
  · intro i
    refine ⟨A' i,h₀ i,h₁ i,?_,?_⟩
    · rw [hsF,← hcover]
      exact (subset_iUnion (fun i => range (A' i)) i).trans subset_union_right
    · exact (hdiam i).trans (by linarith [hAd i])
  · intro x
    rw [intersectionCount_reindex]
    exact hcF x
  · rw [hsF]
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    rcases j with ⟨j,z⟩|⟨i,z⟩
    · exact Or.inl (mem_iUnion_of_mem j (subdivArc_range_subset (E j) (Q j) z hj))
    · exact Or.inr (mem_iUnion_of_mem i (hsource i z.val z.property hj))

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
namespace Arc
open Set Metric

variable {X : Type*} [MetricSpace X]

theorem colored_stages {κ : Type*} [Fintype κ] (A : κ → Arc X) (color : κ → ℕ)
    {B : ℝ} (hB : 0<B) (hAd : ∀ i, diam (range (A i))≤B)
    (hsep : ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) (N : ℕ) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (∀ i, color i<N → Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, color i<N → ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ colorBound N) ∧
      (⋃ j, range (F j)) ⊆ (⋃ i, range (A i)) := by
  classical
  induction N with
  | zero =>
    refine ⟨0,Fin.elim0,?_,?_,?_,?_,?_,?_⟩
    · intro i; exact i.elim0
    · intro i hi; omega
    · intro i hi; omega
    · intro i; exact i.elim0
    · intro x; simp [intersectionCount,colorBound]
    · simp
  | succ N ih =>
    obtain ⟨k,E,hEc,hEv,hEj,hEd,hEt,hEs⟩ := ih
    let K := {i : κ // color i=N}
    let A₀ : K → Arc X := fun i => A i.val
    have hsep₀ (i j : K) (hne : i≠j) :
        ∀ x∈range (A₀ i), ∀ y∈range (A₀ j), 4*B<dist x y :=
      hsep i.val j.val (fun h => hne (Subtype.ext h)) (i.property.trans j.property.symm)
    obtain ⟨n,F,hFc,hFE,hFv,hFa,hFj,hFd,hFt,hFs⟩ :=
      separated_stage E A₀ hB (colorBound N) hEc hEd (fun i => hAd i.val) hEt hsep₀
    refine ⟨n,F,hFc,?_,?_,hFd,hFt,?_⟩
    · intro i hi
      by_cases h : color i<N
      · exact ⟨hFv _ (hEv i h).1,hFv _ (hEv i h).2⟩
      · exact hFa ⟨i,by omega⟩
    · intro i hi
      by_cases h : color i<N
      · obtain ⟨b,h₀,h₁,hs,hd⟩ := hEj i h
        exact ⟨b,h₀,h₁,hs.trans hFE,hd⟩
      · exact hFj ⟨i,by omega⟩
    · apply hFs.trans
      apply union_subset hEs
      intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion_of_mem i.val hi

theorem colored_arc_graph {κ : Type*} [Fintype κ] (A : κ → Arc X) (N : ℕ)
    (color : κ → Fin N) {B : ℝ} (hB : 0<B) (hAd : ∀ i, diam (range (A i))≤B)
    (hsep : ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (∀ i, Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ colorBound N) ∧
      (⋃ j, range (F j)) ⊆ (⋃ i, range (A i)) := by
  obtain ⟨n,F,hc,hv,hj,hd,ht,hs⟩ := colored_stages A (fun i => (color i).val) hB hAd
    (fun i j hij hc => hsep i j hij (Fin.ext hc)) N
  exact ⟨n,F,hc,fun i => hv i (color i).isLt,fun i => hj i (color i).isLt,hd,ht,hs⟩

end Arc
end CannonEmbeddedArc

namespace CannonRegularDisk
open Metric
open Set CannonEmbeddedArc

variable {X : Type*} [TopologicalSpace X]

theorem IsRegularDisk.exists_arc {U : Set X} (hU : IsRegularDisk U)
    {x y : X} (hx : x∈U) (hy : y∈U) (hxy : x≠y) :
    ∃ a : Arc X, a 0=x ∧ a 1=y ∧ range a ⊆ U := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  have huv : u≠v := fun h => hxy (congrArg e h)
  refine ⟨Arc.mappedSegment e he.continuous he.injective u v huv,by simp,by simp,?_⟩
  exact Arc.mappedSegment_range e he.continuous he.injective u v huv (convex_ball q r) hu hv

end CannonRegularDisk

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_BoundaryControlledEmbeddedArcs
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
namespace CannonRelease
open Set Metric CannonGraph CannonRegularDisk CannonEmbeddedArc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_controlled_embedded_arcs (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L r₀ : ℝ, 1≤L ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ x y : Boundary D, x≠y → dist x y<2*r →
        ∃ a : Arc (Boundary D), a 0=x ∧ a 1=y ∧
          range a ⊆ ball x (L*r) ∧ Metric.diam (range a) ≤ L*r := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc₁,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  refine ⟨4/c,c/2,(one_le_div hc).mpr (by linarith),half_pos hc,?_⟩
  intro r hr hrc x y hxy hd
  let s := 2*r/c
  have hs : 0 < s := div_pos (by positivity) hc
  have hs₁ : s≤1 := (div_le_one hc).mpr (by linarith)
  have hcs : c*s=2*r := by dsimp [s]; field_simp
  obtain ⟨U,hU,hinner,houter⟩ := hdisks x s hs hs₁
  have hxU : x∈U := hinner (mem_ball_self (mul_pos hc hs))
  have hyU : y∈U := hinner (by simpa only [mem_ball,dist_comm,hcs] using hd)
  obtain ⟨a,ha₀,ha₁,haU⟩ := hU.exists_arc hxU hyU hxy
  have harange : range a ⊆ ball x s := haU.trans (subset_closure.trans houter)
  have heq : 2*s=(4/c)*r := by dsimp [s]; ring
  refine ⟨a,ha₀,ha₁,harange.trans (ball_subset_ball ?_),?_⟩
  · rw [←heq]
    linarith
  · rw [←heq]
    exact Metric.diam_le_of_subset_closedBall hs.le (harange.trans ball_subset_closedBall)

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_SeparatedArcColoring
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
namespace CannonEmbeddedArc
namespace Arc
open Set Metric

variable {X : Type*} [MetricSpace X]

theorem separated_arc_coloring {T κ : Type*} [Fintype T] [Fintype κ]
    (q : T → X) (src tgt : κ → T) (hpair : Function.Injective (fun i => (src i,tgt i)))
    (A : κ → Arc X) (h₀ : ∀ i, A i 0=q (src i)) (h₁ : ∀ i, A i 1=q (tgt i))
    {B : ℝ} (hB : 0<B) (hd : ∀ i, diam (range (A i))≤B) (K : ℕ)
    (hlocal : ∀ x, ((Finset.univ : Finset T).filter (fun t => dist x (q t)≤7*B)).card≤K) :
    ∃ color : κ → Fin (K^2+1), ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y := by
  classical
  let R : κ → κ → Prop := fun i j => dist (q (src i)) (q (src j))≤6*B
  have hcount (i : κ) : ((Finset.univ : Finset κ).filter (R i)).card≤K^2 := by
    let S := (Finset.univ : Finset T).filter (fun t => dist (q (src i)) (q t)≤7*B)
    have hmaps : Set.MapsTo (fun j => (src j,tgt j))
        (↑((Finset.univ : Finset κ).filter (R i)) : Set κ) (↑(S×ˢS) : Set (T×T)) := by
      intro j hj
      have hh := (Finset.mem_filter.mp hj).2
      have hst : dist (q (src j)) (q (tgt j))≤B := by
        rw [← h₀ j,← h₁ j]
        exact (Metric.dist_le_diam_of_mem (A j).compact_range.isBounded
          (mem_range_self 0) (mem_range_self 1)).trans (hd j)
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      · dsimp [R] at hh
        linarith
      · have ht := dist_triangle (q (src i)) (q (src j)) (q (tgt j))
        dsimp [R] at hh
        linarith
    calc
      _ ≤ (S×ˢS).card := Finset.card_le_card_of_injOn _ hmaps hpair.injOn
      _ = S.card^2 := by simp [pow_two]
      _ ≤ K^2 := Nat.pow_le_pow_left (hlocal (q (src i))) 2
  obtain ⟨color,hc⟩ := CannonDiskColoring.finite_relation_coloring R
    (fun i j h => by simpa only [R,dist_comm] using h) hcount
  refine ⟨color,?_⟩
  intro i j hij hcij x hx y hy
  have hfar : 6*B<dist (q (src i)) (q (src j)) := lt_of_not_ge (fun h => hc i j hij h hcij)
  have hxi : dist (q (src i)) x≤B := by
    rw [← h₀ i]
    exact (Metric.dist_le_diam_of_mem (A i).compact_range.isBounded (mem_range_self 0) hx).trans (hd i)
  have hyj : dist y (q (src j))≤B := by
    rw [← h₀ j]
    exact (Metric.dist_le_diam_of_mem (A j).compact_range.isBounded hy (mem_range_self 0)).trans (hd j)
  have ht := dist_triangle4 (q (src i)) x y (q (src j))
  linarith

end Arc
end CannonEmbeddedArc

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_SquareSide
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
namespace CannonRegularDisk
open Metric
open unitInterval

variable {X : Type*} [TopologicalSpace X]

lemma squareSide_closed (i : Fin 4) : IsClosed (squareSide i) := by
  fin_cases i <;> dsimp [squareSide] <;> exact isClosed_eq (by fun_prop) continuous_const

lemma squareBoundary_closed : IsClosed squareBoundary :=
  isClosed_iUnion_of_finite squareSide_closed

theorem square_boundary_map (a b c d : C(I,X))
    (h₀₀ : a 0=c 0) (h₀₁ : a 1=d 0) (h₁₀ : b 0=c 1) (h₁₁ : b 1=d 1) :
    ∃ f : C(squareBoundary,X),
      (∀ t, f ⟨(0,t),mem_squareBoundary _ |>.mpr (Or.inl rfl)⟩=a t) ∧
      (∀ t, f ⟨(1,t),mem_squareBoundary _ |>.mpr (Or.inr (Or.inl rfl))⟩=b t) ∧
      (∀ s, f ⟨(s,0),mem_squareBoundary _ |>.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩=c s) ∧
      (∀ s, f ⟨(s,1),mem_squareBoundary _ |>.mpr (Or.inr (Or.inr (Or.inr rfl)))⟩=d s) := by
  classical
  let S (i : Fin 4) : Set squareBoundary := Subtype.val ⁻¹' squareSide i
  have hS (i : Fin 4) : IsClosed (S i) := (squareSide_closed i).preimage continuous_subtype_val
  have hc : ⋃ i, S i=univ := by
    ext z
    simp only [mem_iUnion,mem_univ,iff_true]
    exact (mem_iUnion.mp z.property : ∃ i, z.val∈squareSide i)
  let g : Fin 4 → C(I×I,X) :=
    ![a.comp ⟨Prod.snd,continuous_snd⟩,b.comp ⟨Prod.snd,continuous_snd⟩,
      c.comp ⟨Prod.fst,continuous_fst⟩,d.comp ⟨Prod.fst,continuous_fst⟩]
  let f (i : Fin 4) : C(S i,X) :=
    (g i).comp ⟨fun z => z.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
  have heq (i j : Fin 4) (z : squareBoundary) (hi : z∈S i) (hj : z∈S j) :
      f i ⟨z,hi⟩=f j ⟨z,hj⟩ := by
    fin_cases i <;> fin_cases j <;>
      simp only [S,squareSide,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.isValue,Fin.reduceFinMk,mem_preimage,mem_ofPred_eq] at hi hj <;>
      simp [f,g,hi,hj] <;> simp_all
  let F := CannonClosedGluing.glue S hS hc f heq
  have hF (i : Fin 4) (z : squareBoundary) (hz : z∈S i) : F z=g i z.val := by
    exact CannonClosedGluing.glue_apply S hS hc f heq i ⟨z,hz⟩
  refine ⟨F,fun t => hF 0 _ rfl,fun t => hF 1 _ rfl,
    fun s => hF 2 _ rfl,fun s => hF 3 _ rfl⟩

theorem IsRegularDisk.fill_square {U : Set X} (hU : IsRegularDisk U)
    (a b c d : C(I,X))
    (h₀₀ : a 0=c 0) (h₀₁ : a 1=d 0) (h₁₀ : b 0=c 1) (h₁₁ : b 1=d 1)
    (ha : range a⊆U) (hb : range b⊆U) (hc : range c⊆U) (hd : range d⊆U) :
    ∃ F : C(I×I,X), (∀ z, F z∈U) ∧
      (∀ t, F (0,t)=a t) ∧ (∀ t, F (1,t)=b t) ∧
      (∀ s, F (s,0)=c s) ∧ (∀ s, F (s,1)=d s) := by
  obtain ⟨f,hfa,hfb,hfc,hfd⟩ := square_boundary_map a b c d h₀₀ h₀₁ h₁₀ h₁₁
  have hf (z : squareBoundary) : f z∈U := by
    have hz (v : I×I) (hv : v∈squareBoundary) (h : z.val=v) : z=⟨v,hv⟩ := Subtype.ext h
    rcases (mem_squareBoundary z.val).mp z.property with h|h|h|h
    · have he := hz (0,z.val.2) (by simp [mem_squareBoundary]) (Prod.ext h rfl)
      rw [he,hfa]; exact ha (mem_range_self _)
    · have he := hz (1,z.val.2) (by simp [mem_squareBoundary]) (Prod.ext h rfl)
      rw [he,hfb]; exact hb (mem_range_self _)
    · have he := hz (z.val.1,0) (by simp [mem_squareBoundary]) (Prod.ext rfl h)
      rw [he,hfc]; exact hc (mem_range_self _)
    · have he := hz (z.val.1,1) (by simp [mem_squareBoundary]) (Prod.ext rfl h)
      rw [he,hfd]; exact hd (mem_range_self _)
  obtain ⟨F,hFU,hF⟩ := hU.extend squareBoundary_closed f hf
  have hFe (z : squareBoundary) : F z.val=f z := congrArg (fun f : C(squareBoundary,X) => f z) hF
  exact ⟨F,hFU,fun t => (hFe _).trans (hfa t),fun t => (hFe _).trans (hfb t),
    fun s => (hFe _).trans (hfc s),fun s => (hFe _).trans (hfd s)⟩

end CannonRegularDisk

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

lemma glue_apply (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0))
    (i : Fin n) (z : I×I) (hz : z∈strip n i) :
    glue n hn F hF z=F i (z.1,coordinate n i ⟨z,hz⟩) := by
  exact CannonClosedGluing.glue_apply (strip n) (strip_closed n) (strip_cover n hn)
    (fun i => patch n i (F i)) (patch_agree n F hF) i ⟨z,hz⟩

lemma parameter_coordinate (n : ℕ) (hn : 0<n) (i : Fin n) (z : strip n i) :
    parameter n hn i (coordinate n i z)=z.val.2 := by
  apply Subtype.ext
  change ((i:ℝ)+((n:ℝ)*(z.val.2:ℝ)-(i:ℝ)))/n=(z.val.2:ℝ)
  field_simp
  ring

end CannonGrid

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [MetricSpace X]

lemma subdivision_fine (f : C(I,X)) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ hn : 0<n, ∀ (i : Fin n) (t : I),
      dist (f (parameter n hn i t)) (f (point n hn i.castSucc)) < r := by
  have hu : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu r hr
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
  let n := N+1
  have hn : 0<n := Nat.succ_pos N
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  refine ⟨n,hn,fun i t => hclose ?_⟩
  change |((i:ℝ)+(t:ℝ))/n-(i:ℝ)/n|<δ
  rw [← sub_div,add_sub_cancel_left,abs_of_nonneg (div_nonneg t.property.1 hnR.le)]
  exact ((div_le_div_iff_of_pos_right hnR).mpr t.property.2).trans_lt (by simpa [n] using hN)

end CannonGrid

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

lemma glue_zero_right (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) (s : I) :
    glue n hn F hF (s,0)=F ⟨0,hn⟩ (s,0) := by
  have hz : (s,0)∈strip n ⟨0,hn⟩ := by simp [strip]
  rw [glue_apply n hn F hF ⟨0,hn⟩ (s,0) hz]
  congr 1
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [coordinate]

lemma glue_one_right (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) (s : I) :
    glue n hn F hF (s,1)=F ⟨n-1,by omega⟩ (s,1) := by
  have hn' : ((n-1:ℕ):ℝ)+1=n := by norm_cast; omega
  have hz : (s,1)∈strip n ⟨n-1,by omega⟩ := by
    change ((n-1:ℕ):ℝ)≤n*(1:ℝ) ∧ n*(1:ℝ)≤((n-1:ℕ):ℝ)+1
    constructor <;> linarith
  rw [glue_apply n hn F hF ⟨n-1,by omega⟩ (s,1) hz]
  congr 1
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (n:ℝ)*1-((n-1:ℕ):ℝ)=1
  linarith

lemma glue_bottom (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0))
    (f : C(I,X)) (hf : ∀ i t, F i (0,t)=f (parameter n hn i t)) (t : I) :
    glue n hn F hF (0,t)=f t := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (0,t)))
  rw [glue_apply n hn F hF i (0,t) hi,hf,parameter_coordinate]

end CannonGrid

namespace CannonLoopApproximation
open Set Metric Topology unitInterval CannonRegularDisk CannonGrid

variable {X : Type*} [MetricSpace X]

theorem loop_approximation {r L C : ℝ} (hr : 0 < r) (hL : 1≤L) (_hC : 0<C)
    (T S : Set X)
    (hcover : ∀ x : X, ∃ v∈T, dist x v ≤ r)
    (hconnect : ∀ x y : X, dist x y ≤ r →
      ∃ p : Path x y, ∀ t, dist (p t) x≤L*r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r →
      ∃ p : Path x y, range p⊆S ∧ ∀ t, dist (p t) x≤3*L*r)
    (hdisks : ∀ x : X, ∃ U : Set X, IsRegularDisk U ∧
      ball x ((3*L+2)*r)⊆U ∧ U⊆ball x (C*r))
    (f : C(I,X)) (hf : f 0=f 1) :
    ∃ H : C(I×I,X), (∀ t, H (0,t)=f t) ∧
      (∀ t, H (1,t)∈S) ∧ (∀ s, H (s,0)=H (s,1)) ∧
      (∀ s s' t, dist (H (s,t)) (H (s',t))<2*C*r) := by
  classical
  choose v hvT hvd using hcover
  choose c hcd using fun x => hconnect x (v x) (hvd x)
  obtain ⟨n,hn,hnfine⟩ := subdivision_fine f hr
  let p (i : Fin (n+1)) := f (point n hn i)
  have hstep (i : Fin n) : dist (p i.succ) (p i.castSucc) < r := by
    simpa only [parameter_one] using hnfine i 1
  have hvstep (i : Fin n) : dist (v (p i.castSucc)) (v (p i.succ))<4*r := by
    have h := dist_triangle4 (v (p i.castSucc)) (p i.castSucc) (p i.succ) (v (p i.succ))
    have h₀ := hvd (p i.castSucc)
    have h₁ := hvd (p i.succ)
    rw [dist_comm (v (p i.castSucc)) (p i.castSucc),dist_comm (p i.castSucc) (p i.succ)] at h
    linarith [hstep i]
  choose b hbS hbd using fun i : Fin n =>
    hjoin _ (hvT (p i.castSucc)) _ (hvT (p i.succ)) (hvstep i)
  choose U hU hUin hUout using fun i : Fin n => hdisks (p i.castSucc)
  have haU (i : Fin n) : range (f.comp (parameter n hn i))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (f (parameter n hn i t)) (p i.castSucc)<(3*L+2)*r
    nlinarith [hnfine i t]
  have hbU (i : Fin n) : range (b i)⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (b i t) (p i.castSucc)<(3*L+2)*r
    have h := dist_triangle (b i t) (v (p i.castSucc)) (p i.castSucc)
    rw [dist_comm (v (p i.castSucc)) (p i.castSucc)] at h
    nlinarith [hbd i t,hvd (p i.castSucc)]
  have hcU (i : Fin n) : range (c (p i.castSucc))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (c (p i.castSucc) t) (p i.castSucc)<(3*L+2)*r
    nlinarith [hcd (p i.castSucc) t]
  have hdU (i : Fin n) : range (c (p i.succ))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (c (p i.succ) t) (p i.castSucc)<(3*L+2)*r
    have h := dist_triangle (c (p i.succ) t) (p i.succ) (p i.castSucc)
    nlinarith [hcd (p i.succ) t,hstep i]
  have hfill (i : Fin n) : ∃ F : C(I×I,X), (∀ z, F z∈U i) ∧
      (∀ t, F (0,t)=f (parameter n hn i t)) ∧
      (∀ t, F (1,t)=b i t) ∧
      (∀ s, F (s,0)=c (p i.castSucc) s) ∧ (∀ s, F (s,1)=c (p i.succ) s) := by
    exact (hU i).fill_square (f.comp (parameter n hn i)) (b i).toContinuousMap
      (c (p i.castSucc)).toContinuousMap (c (p i.succ)).toContinuousMap
      (by simp [p]) (by simp [p]) (by simp) (by simp) (haU i) (hbU i) (hcU i) (hdU i)
  choose F hFU hFa hFb hFc hFd using hfill
  have hFF (i j : Fin n) (hij : (i:ℕ)+1=(j:ℕ)) (s : I) : F i (s,1)=F j (s,0) := by
    rw [hFd,hFc]
    have heq : i.succ=j.castSucc := Fin.ext hij
    rw [heq]
  let H := glue n hn F hFF
  refine ⟨H,glue_bottom n hn F hFF f hFa,?_,?_,?_⟩
  · intro t
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (1,t)))
    rw [show H (1,t)=_ from glue_apply n hn F hFF i (1,t) hi,hFb]
    exact hbS i (mem_range_self _)
  · intro s
    rw [show H (s,0)=_ from glue_zero_right n hn F hFF s,
      show H (s,1)=_ from glue_one_right n hn F hFF s,hFc,hFd]
    have hlast : (⟨n-1,by omega⟩ : Fin n).succ=Fin.last n := Fin.ext (by simp; omega)
    have hzero : (⟨0,hn⟩ : Fin n).castSucc=0 := rfl
    have hp : p (⟨0,hn⟩ : Fin n).castSucc=p (⟨n-1,by omega⟩ : Fin n).succ := by
      simp only [hlast,hzero,p,point_zero,point_last,hf]
    exact congrArg (fun x => c x s) hp
  · intro s s' t
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (s,t)))
    have hi' : (s',t)∈strip n i := hi
    rw [show H (s,t)=_ from glue_apply n hn F hFF i (s,t) hi,
      show H (s',t)=_ from glue_apply n hn F hFF i (s',t) hi']
    have h₀ := hUout i (hFU i (s,coordinate n i ⟨(s,t),hi⟩))
    have h₁ := hUout i (hFU i (s',coordinate n i ⟨(s',t),hi'⟩))
    have h := dist_triangle (F i (s,coordinate n i ⟨(s,t),hi⟩)) (p i.castSucc)
      (F i (s',coordinate n i ⟨(s',t),hi'⟩))
    rw [dist_comm (p i.castSucc)] at h
    change dist _ _<C*r at h₀ h₁
    linarith

end CannonLoopApproximation

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IntersectionCountEmbedding
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

namespace CannonEmbeddedArc.Arc
variable {X : Type*} [TopologicalSpace X]
lemma intersectionCount_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (e : κ ↪ ι) (S : Set X) :
    intersectionCount (E ∘ e) S ≤ intersectionCount E S := by
  classical
  simp only [intersectionCount_eq_card]
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact e.injective h

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
variable {X : Type*} [MetricSpace X]

theorem connected_core [PreconnectedSpace X] [Nonempty X]
    {r : ℝ} (hr : 0 < r) {n : ℕ} (F : Fin n → Arc X) (T : Set X)
    (hcover : ∀ x : X, ∃ t∈T, dist x t ≤ r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r → JoinedIn ((⋃ i, range (F i))∪T) x y) :
    ∃ m : ℕ, ∃ e : Fin m ↪ Fin n,
      IsPathConnected ((⋃ j, range (F (e j)))∪T) ∧
      (∀ x∈T, ∀ y : X, ∀ p : Path x y,
        range p⊆(⋃ i, range (F i)) → range p⊆(⋃ j, range (F (e j)))) := by
  classical
  obtain ⟨a,ha,_⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
  let Q := (⋃ i, range (F i))∪T
  have haQ : a∈Q := Or.inr ha
  have hT := CannonGraphCore.net_joined hr T Q subset_union_right hcover hjoin ha
  let J := {i : Fin n // F i 0∈pathComponentIn Q a}
  let eqv := (Fintype.equivFin J).symm
  let e : Fin (Fintype.card J) ↪ Fin n := ⟨fun j => (eqv j).val,
    Subtype.val_injective.comp eqv.injective⟩
  have hs : (⋃ j, range (F (e j)))=⋃ j : J, range (F j.val) := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨eqv j,hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨eqv.symm j,by simpa only [e,Function.Embedding.coeFn_mk,eqv.apply_symm_apply] using hj⟩
  have hcore : pathComponentIn Q a=(⋃ j, range (F (e j)))∪T := by
    rw [hs]
    exact CannonGraphCore.component_whole_edges (fun i => (F i).map) T a ha hT
  refine ⟨Fintype.card J,e,?_,?_⟩
  · rw [←hcore]
    exact isPathConnected_pathComponentIn haQ
  · intro x hx y p hp z hz
    have hzP := CannonGraphCore.path_range_in_component (hT x hx) p (hp.trans subset_union_left) hz
    rw [hs]
    exact CannonGraphCore.component_retains_edges (fun i => (F i).map) subset_union_left hzP (hp hz)
end CannonEmbeddedArc.Arc

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

lemma turn_const (z : Circle) : turn (.const I z)=0 := by
  rw [turn_eq_of_lift (.const I z) (.const I (Complex.arg z)) (fun _ => Circle.exp_arg z)]
  simp

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

lemma turn_standard_loop :
    turn (Circle.exp.comp ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩)=2*Real.pi := by
  rw [turn_eq_of_lift _ ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩ (fun _ => rfl)]
  simp

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

lemma winding_const (a z : ℂ) (hz : z∉range (ContinuousMap.const I a)) :
    winding (.const I a) z hz=0 := by
  let k := direction (ContinuousMap.const I a-.const I z)
    (fun t ht => hz ⟨t,sub_eq_zero.mp ht⟩)
  change turn k=0
  have hk : k=.const I (k 0) := by ext t; rfl
  rw [hk,turn_const]

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

lemma winding_convex_zero (f : C(I,ℂ)) (hf : f 0=f 1) {S : Set ℂ}
    (hS : Convex ℝ S) (hfrange : range f⊆S) {z : ℂ} (hzS : z∉S) :
    winding f z (fun hz => hzS (hfrange hz))=0 := by
  let a := f 0
  let H : C(I×I,ℂ) := ⟨fun w => (1-(w.1:ℝ)) • f w.2+(w.1:ℝ) • a,by fun_prop⟩
  have hH (w : I×I) : H w∈S := by
    exact hS (hfrange (mem_range_self w.2)) (hfrange (mem_range_self 0))
      (sub_nonneg.mpr w.1.property.2) w.1.property.1 (by ring)
  have hclosed (s : I) : H (s,0)=H (s,1) := by simp only [H,ContinuousMap.coe_mk,hf]
  have h₀ (t : I) : H (0,t)=f t := by simp [H]
  have h₁ (t : I) : H (1,t)=a := by simp [H]
  have hz : z∉range H := by rintro ⟨w,rfl⟩; exact hzS (hH w)
  have hza : z∉range (ContinuousMap.const I a) := by
    rintro ⟨t,ht⟩
    exact hzS (ht ▸ hfrange (mem_range_self 0))
  rw [winding_eq_of_homotopy f (.const I a) z _ hza H hclosed h₀ h₁ hz]
  exact winding_const a z hza

lemma roundLoop_closed (a : ℂ) (R : ℝ) : roundLoop a R 0=roundLoop a R 1 := by
  simp [roundLoop]

lemma winding_roundLoop_center (a : ℂ) {R : ℝ} (hR : 0<R) :
    winding (roundLoop a R) a (center_not_roundLoop a hR)=2*Real.pi := by
  have heq : direction (roundLoop a R-.const I a)
      (fun t ht => center_not_roundLoop a hR ⟨t,sub_eq_zero.mp ht⟩)=
      Circle.exp.comp ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩ := by
    ext t
    simp only [direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,
      roundLoop,ContinuousMap.coe_mk,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,Circle.norm_coe,mul_one,
      ContinuousMap.comp_apply]
    field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
  simp only [winding,heq,turn_standard_loop]

lemma winding_roundLoop_inside (a z : ℂ) {R : ℝ} (hR : 0<R) (hz : dist z a<R) :
    ∃ h : z∉range (roundLoop a R), winding (roundLoop a R) z h=2*Real.pi := by
  have hp (s : I) : Path.segment a z s∉range (roundLoop a R) := by
    have hs : Path.segment a z s∈ball a R := by
      apply (convex_ball a R).segment_subset (mem_ball_self hR) hz
      rw [←Path.range_segment]; exact mem_range_self s
    rintro ⟨t,ht⟩
    have hd := roundLoop_dist a hR.le t
    rw [ht] at hd
    exact hs.not_ge hd.ge
  have hz' : z∉range (roundLoop a R) := by simpa only [Path.target] using hp 1
  refine ⟨hz',?_⟩
  have heq := winding_moving_point (roundLoop a R) (roundLoop_closed a R)
    (Path.segment a z).toContinuousMap hp
  change winding (roundLoop a R) (Path.segment a z 0) _ =
    winding (roundLoop a R) (Path.segment a z 1) _ at heq
  have heq' : winding (roundLoop a R) a (center_not_roundLoop a hR)=
      winding (roundLoop a R) z hz' := by simpa only [Path.source,Path.target] using heq
  rw [←heq',winding_roundLoop_center a hR]

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_stable_near (f g : C(I,ℂ)) (hf : f 0=f 1) (hg : g 0=g 1)
    (z : ℂ) (hz : z∉range f) (hnear : ∀ t, dist (g t) (f t)<dist (f t) z) :
    ∃ hg' : z∉range g, winding f z hz=winding g z hg' := by
  let H : C(I×I,ℂ) := ⟨fun w => (1-(w.1:ℝ)) • f w.2+(w.1:ℝ) • g w.2,by fun_prop⟩
  have hdist (s t : I) : dist (H (s,t)) (f t)≤dist (g t) (f t) := by
    have heq : H (s,t)-f t=(s:ℝ) • (g t-f t) := by
      dsimp only [H,ContinuousMap.coe_mk]
      module
    rw [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
    rw [dist_eq_norm]
    exact mul_le_of_le_one_left (norm_nonneg (g t-f t)) s.property.2
  have hH : z∉range H := by
    rintro ⟨⟨s,t⟩,heq⟩
    have h := (hdist s t).trans_lt (hnear t)
    rw [heq,dist_comm z (f t)] at h
    exact h.false
  have h₀ (t : I) : H (0,t)=f t := by simp [H]
  have h₁ (t : I) : H (1,t)=g t := by simp [H]
  have hg' : z∉range g := by
    rintro ⟨t,ht⟩
    exact hH ⟨(1,t),(h₁ t).trans ht⟩
  refine ⟨hg',winding_eq_of_homotopy f g z hz hg' H ?_ h₀ h₁ hH⟩
  intro s
  simp only [H,ContinuousMap.coe_mk,hf,hg]

lemma index_eq (f : C(I,ℂ)) {z : ℂ} (hz : z∉range f) : index f z=winding f z hz := by
  simp only [index,dite_eq_left hz]

lemma index_eventually_eq (f : C(I,ℂ)) (hf : f 0=f 1) {z : ℂ} (hz : z∉range f) :
    ∀ᶠ w in 𝓝 z, index f w=index f z := by
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  filter_upwards [Metric.ball_mem_nhds z hε] with w hw
  have hw' : w∉range f := hball hw
  rw [index_eq f hw',index_eq f hz]
  have hp (s : I) : Path.segment z w s∉range f := by
    apply hball
    apply (convex_ball z ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]; exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z w).toContinuousMap hp
  change winding f (Path.segment z w 0) _ = winding f (Path.segment z w 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

lemma index_zero_outside_closedBall (f : C(I,ℂ)) (hf : f 0=f 1)
    (a : ℂ) (R : ℝ) (hbound : ∀ t, dist (f t) a≤R) {z : ℂ} (hz : R<dist z a) :
    index f z=0 := by
  have hfr : range f⊆closedBall a R := by rintro _ ⟨t,rfl⟩; exact hbound t
  have hzS : z∉closedBall a R := not_le.mpr hz
  have hz' : z∉range f := fun h => hzS (hfr h)
  rw [index_eq f hz']
  exact winding_convex_zero f hf (convex_closedBall a R) hfr hzS

lemma index_near_roundLoop (a : ℂ) {R : ℝ} (hR : 0<R) (g : C(I,ℂ))
    (hg : g 0=g 1) (hnear : ∀ t, dist (g t) (roundLoop a (R/2) t)<R/4)
    {z : ℂ} (hz : dist z a<R/4) : index g z=2*Real.pi := by
  obtain ⟨hzf,hwind⟩ := winding_roundLoop_inside a z (half_pos hR) (by linarith)
  have hclose (t : I) : dist (g t) (roundLoop a (R/2) t)<dist (roundLoop a (R/2) t) z := by
    have htri := dist_triangle (roundLoop a (R/2) t) z a
    rw [roundLoop_dist a (half_pos hR).le] at htri
    linarith [hnear t]
  obtain ⟨hzg,heq⟩ := winding_stable_near (roundLoop a (R/2)) g
    (roundLoop_closed a (R/2)) hg z hzf hclose
  rw [index_eq g hzg,←heq,hwind]

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
lemma chartIndex_apply (e : ℂ → X) (he : IsOpenEmbedding e) (f : C(I,ℂ)) (z : ℂ) :
    chartIndex e he f (e z)=index f z := by
  simp only [chartIndex,ite_eq_left (mem_range_self z),he.toOpenPartialHomeomorph_left_inv]

omit [T2Space X] in
lemma chartIndex_zero_off_disk (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {x : X} (hx : x∉e '' closedBall a R) :
    chartIndex e he f x=0 := by
  classical
  by_cases hxe : x∈range e
  · obtain ⟨z,rfl⟩ := hxe
    rw [chartIndex_apply]
    apply index_zero_outside_closedBall f hf a R hbound
    apply lt_of_not_ge
    intro hz
    exact hx ⟨z,hz,rfl⟩
  · simp only [chartIndex,ite_eq_right hxe]

lemma chartIndex_eventually_eq (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {x : X} (hx : x∉range (e ∘ f)) :
    ∀ᶠ y in 𝓝 x, chartIndex e he f y=chartIndex e he f x := by
  classical
  by_cases hxe : x∈range e
  · let h := he.toOpenPartialHomeomorph e
    have hinv : e (h.symm x)=x := he.toOpenPartialHomeomorph_right_inv e hxe
    have hz : h.symm x∉range f := by
      rintro ⟨t,ht⟩
      exact hx ⟨t,by change e (f t)=x; rw [ht,hinv]⟩
    have hc : ContinuousAt h.symm x := h.symm.continuousAt (by
      simpa only [OpenPartialHomeomorph.symm_source,h,IsOpenEmbedding.toOpenPartialHomeomorph_target] using hxe)
    have hv := hc.eventually (index_eventually_eq f hf hz)
    filter_upwards [hv,he.isOpen_range.mem_nhds hxe] with y hy hye
    simpa only [chartIndex,ite_eq_left hye,ite_eq_left hxe] using hy
  · have hxK : x∉e '' closedBall a R := fun hk => hxe (image_subset_range _ _ hk)
    have hc : IsClosed (e '' closedBall a R) :=
      ((isCompact_closedBall a R).image he.continuous).isClosed
    filter_upwards [hc.isOpen_compl.mem_nhds hxK] with y hy
    rw [chartIndex_zero_off_disk e he f hf a R hbound hy,
      chartIndex_zero_off_disk e he f hf a R hbound hxK]

theorem chartIndex_eq_on_preconnected (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {S : Set X} (hS : IsPreconnected S)
    (havoid : S⊆(range (e ∘ f))ᶜ) {x y : X} (hx : x∈S) (hy : y∈S) :
    chartIndex e he f x=chartIndex e he f y := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hc : IsLocallyConstant (fun z : S => chartIndex e he f z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.eventually
      (chartIndex_eventually_eq e he f hf a R hbound (havoid z.property))
  exact hc.apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩

theorem near_roundLoop_separates (e : ℂ → X) (he : IsOpenEmbedding e)
    (a : ℂ) {R : ℝ} (hR : 0<R) (g : C(I,ℂ)) (hg : g 0=g 1)
    (hnear : ∀ t, dist (g t) (roundLoop a (R/2) t)<R/4)
    {S : Set X} (hS : IsPreconnected S) (havoid : S⊆(range (e ∘ g))ᶜ)
    {z : ℂ} (hz : dist z a<R/4) (hzS : e z∈S) : S⊆e '' closedBall a R := by
  have hbound (t : I) : dist (g t) a≤R := by
    have h := dist_triangle (g t) (roundLoop a (R/2) t) a
    rw [roundLoop_dist a (half_pos hR).le] at h
    linarith [hnear t]
  intro y hy
  by_contra hyK
  have heq := chartIndex_eq_on_preconnected e he g hg a R hbound hS havoid hzS hy
  rw [chartIndex_apply,index_near_roundLoop a hR g hg hnear hz,
    chartIndex_zero_off_disk e he g hg a R hbound hyK] at heq
  have := Real.pi_pos
  linarith

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma chart_loop_neighborhood (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) {d : ℝ} (hd : 0<d) :
    ∃ ε : ℝ, 0<ε ∧ ∀ t : I, ∀ y : X, dist y (e (f t))<ε →
      y∈range e ∧ dist ((he.toOpenPartialHomeomorph e).symm y) (f t)<d := by
  let K : Set X := range (e ∘ f)
  have hK : IsCompact K := isCompact_range (he.continuous.comp f.continuous)
  obtain ⟨δ,hδ,hδsub⟩ := hK.exists_cthickening_subset_open he.isOpen_range
    (by rintro _ ⟨t,rfl⟩; exact mem_range_self _)
  let U : Set X := cthickening δ K
  let h := he.toOpenPartialHomeomorph e
  have hc : ContinuousOn h.symm U := by
    apply h.symm.continuousOn.mono
    simpa only [h,OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using hδsub
  have hu : UniformContinuousOn h.symm U := (isClosed_cthickening (δ:=δ) (E:=K)).isCompact.uniformContinuousOn_of_continuous hc
  obtain ⟨ε,hε,hεeq⟩ := Metric.uniformContinuousOn_iff.mp hu d hd
  refine ⟨min δ ε,lt_min hδ hε,fun t y hy => ?_⟩
  have ht : e (f t)∈K := mem_range_self t
  have hyU : y∈U := closedBall_subset_cthickening ht δ ((hy.trans_le (min_le_left ..)).le)
  have htU : e (f t)∈U := self_subset_cthickening K ht
  refine ⟨hδsub hyU,?_⟩
  have hh := hεeq y hyU (e (f t)) htU (hy.trans_le (min_le_right ..))
  simpa only [h,he.toOpenPartialHomeomorph_left_inv] using hh

omit [CompactSpace X] in
lemma small_complex_chart (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (x : X) {η : ℝ} (hη : 0<η) :
    ∃ (e : ℂ → X), IsOpenEmbedding e ∧ ∃ (a : ℂ) (R : ℝ),
      e a=x ∧ 0<R ∧ e '' closedBall a R⊆ball x η := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (-φ x)
  have ht : h.target=univ := stereographic'_target _
  have hx : φ x∈h.source := by
    rw [show h.source={-φ x}ᶜ from stereographic'_source _]
    exact ne_neg_of_mem_unit_sphere ℝ (φ x)
  let e : ℂ → X := φ.symm ∘ h.symm ∘ complexPlane
  have he : IsOpenEmbedding e :=
    φ.symm.isOpenEmbedding.comp ((h.symm.isOpenEmbedding ht).comp complexPlane.isOpenEmbedding)
  let a := complexPlane.symm (h (φ x))
  have hea : e a=x := by
    dsimp only [e,a,Function.comp_apply]
    rw [complexPlane.apply_symm_apply,h.left_inv hx,φ.symm_apply_apply]
  have hn : e ⁻¹' ball x η∈𝓝 a := by
    apply he.continuous.continuousAt.preimage_mem_nhds
    rw [hea]
    exact ball_mem_nhds x hη
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨e,he,a,r/2,hea,half_pos hr,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact hs (hz.trans_lt (half_lt_self hr))

theorem uniform_robust_separating_loops
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {η : ℝ} (hη : 0<η) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x : X, ∃ f : C(I,X), f 0=f 1 ∧
      ∀ g : C(I,X), g 0=g 1 → (∀ t, dist (g t) (f t)<ε) →
      ∀ S : Set X, IsPreconnected S → S⊆(range g)ᶜ → x∈S → S⊆ball x η := by
  classical
  choose e he a R hea hR hsmall using fun p : X => small_complex_chart φ p (half_pos hη)
  let U (p : X) := e p '' ball (a p) (R p/4)
  have hU (p : X) : IsOpen (U p) := (he p).isOpenMap _ isOpen_ball
  have hpU (p : X) : p∈U p := ⟨a p,mem_ball_self (div_pos (hR p) (by norm_num)),hea p⟩
  have hcover : (univ : Set X)⊆⋃ p, U p := fun x _ => mem_iUnion.mpr ⟨x,hpU x⟩
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  choose ε hε htolerance using fun p : X =>
    chart_loop_neighborhood (e p) (he p) (roundLoop (a p) (R p/2)) (show 0<R p/4 from div_pos (hR p) (by norm_num))
  obtain ⟨ε₀,hε₀,hε₀T⟩ : ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ p∈T, ε₀≤ε p := by
    clear hT
    induction T using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert p T hp ih =>
      obtain ⟨b,hb,hbT⟩ := ih
      refine ⟨min (ε p) b,lt_min (hε p) hb,?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact min_le_left ..
      · exact (min_le_right ..).trans (hbT q hq)
  refine ⟨ε₀,hε₀,fun x => ?_⟩
  obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hT (mem_univ x))
  obtain ⟨z,hz,hzx⟩ := hx
  let f : C(I,X) := ⟨fun t => e p (roundLoop (a p) (R p/2) t),
    (he p).continuous.comp (roundLoop (a p) (R p/2)).continuous⟩
  refine ⟨f,by change e p _=e p _; rw [roundLoop_closed],fun g hg hnear S hS havoid hxS => ?_⟩
  have htol (t : I) := htolerance p t (g t) ((hnear t).trans_le (hε₀T p hp))
  let h := (he p).toOpenPartialHomeomorph (e p)
  let g' : C(I,ℂ) := ⟨fun t => h.symm (g t),by
    apply h.symm.continuousOn.comp_continuous g.continuous
    intro t
    simpa only [h,OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using (htol t).1⟩
  have hg' : g' 0=g' 1 := by change h.symm (g 0)=h.symm (g 1); rw [hg]
  have hgg (t : I) : e p (g' t)=g t := (he p).toOpenPartialHomeomorph_right_inv _ (htol t).1
  have hbound := near_roundLoop_separates (e p) (he p) (a p) (hR p) g' hg'
    (fun t => (htol t).2) hS (show S⊆(range (e p ∘ g'))ᶜ by
      intro y hy hy'
      obtain ⟨t,ht⟩ := hy'
      exact havoid hy ⟨t,(hgg t).symm.trans ht⟩) hz (hzx.symm ▸ hxS)
  intro y hy
  have hyp := hsmall p (hbound hy)
  have hxp := hsmall p ⟨z,(hz.le.trans (show R p/4≤R p by linarith [hR p])),hzx⟩
  have htri := dist_triangle y p x
  rw [dist_comm p x] at htri
  change dist y p<η/2 at hyp
  change dist x p<η/2 at hxp
  change dist y x<η
  linarith

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem loop_approximation_separates
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {C B η : ℝ} (hC : 0<C) (hB : 0<B) (hη : 0<η)
    (hexpand : ∀ x : X, ∀ s : ℝ, 0 < s → s≤1 → ∃ f : X ≃ₜ X,
      (∀ y z, dist (f y) (f z)*s≤C*dist y z) ∧
      (∀ y, s≤dist x y → η≤dist (f x) (f y))) :
    ∃ L : ℝ, 1≤L ∧ ∀ r : ℝ, 0 < r → r≤1/L → ∀ Q : Set X,
      (∀ f : C(I,X), f 0=f 1 → ∃ g : C(I,X), g 0=g 1 ∧ range g⊆Q ∧
        ∀ t, dist (g t) (f t)<B*r) →
      ∀ S : Set X, IsPreconnected S → S⊆Qᶜ → ∀ x∈S, ∀ y∈S, dist x y<L*r := by
  obtain ⟨ε,hε,htemplate⟩ := uniform_robust_separating_loops φ hη
  let L := 1+C*B/ε
  have hL : 1≤L := by dsimp [L]; linarith [div_pos (mul_pos hC hB) hε]
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hεL : C*B<ε*L := by
    dsimp [L]
    have heq : ε*(1+C*B/ε)=ε+C*B := by field_simp
    rw [heq]
    linarith
  refine ⟨L,hL,fun r hr hrs Q happrox S hS havoid x hx y hy => ?_⟩
  have hs : 0<L*r := mul_pos hLp hr
  have hs₁ : L*r≤1 := by
    have hh := (le_div_iff₀ hLp).mp hrs
    nlinarith
  obtain ⟨f,hfLip,hfFar⟩ := hexpand x (L*r) hs hs₁
  obtain ⟨l,hl,hsep⟩ := htemplate (f x)
  let l₀ : C(I,X) := ⟨fun t => f.symm (l t),by fun_prop⟩
  have hl₀ : l₀ 0=l₀ 1 := by change f.symm (l 0)=f.symm (l 1); rw [hl]
  obtain ⟨g,hg,hgQ,hgclose⟩ := happrox l₀ hl₀
  let g₁ : C(I,X) := ⟨fun t => f (g t),by fun_prop⟩
  have hg₁ : g₁ 0=g₁ 1 := by change f (g 0)=f (g 1); rw [hg]
  have hclose (t : I) : dist (g₁ t) (l t)<ε := by
    have hh := hfLip (g t) (l₀ t)
    have ht : f (l₀ t)=l t := f.apply_symm_apply _
    rw [ht] at hh
    have hgt := mul_lt_mul_of_pos_left (hgclose t) hC
    have hq : dist (g₁ t) (l t)*L<C*B := by
      change dist (f (g t)) (l t)*L<C*B
      nlinarith [hh,hgt]
    nlinarith [hq,hεL]
  have hSf : IsPreconnected (f '' S) := hS.image f f.continuous.continuousOn
  have hSfavoid : f '' S⊆(range g₁)ᶜ := by
    rintro _ ⟨z,hz,rfl⟩ ⟨t,ht⟩
    have htz : g t=z := f.injective ht
    exact havoid hz (htz ▸ hgQ (mem_range_self t))
  have hsmall := hsep g₁ hg₁ hclose (f '' S) hSf hSfavoid (mem_image_of_mem f hx)
  have hyclose := hsmall (mem_image_of_mem f hy)
  change dist (f y) (f x)<η at hyclose
  rw [dist_comm] at hyclose
  by_contra hxy
  exact (hfFar y (le_of_not_gt hxy)).not_gt hyclose

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NetArcGraphSet
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

namespace CannonEmbeddedArc.Arc
open Set Metric

variable {X : Type*} [MetricSpace X]
theorem net_arc_graph_in_set (Q : ℕ) (C L : ℝ)
    (hp : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hL : 1≤L) :
    ∃ K : ℕ, ∀ (r : ℝ), 0 < r → 7*L*r≤1 → ∀ T : Finset X,
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      ∀ S : Set X, (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
        ∃ a : Arc X, a 0=x ∧ a 1=y ∧ diam (range a)≤L*r ∧ range a⊆S) →
      ∃ n : ℕ, ∃ F : Fin n → Arc X,
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
           Vertex F x ∧ Vertex F y ∧ ∃ b : Arc X, b 0=x ∧ b 1=y ∧
             range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*L*r) ∧
        (∀ j, diam (range (F j))≤L*r) ∧
        (∀ x, intersectionCount F (ball x (2*L*r))≤K) ∧
        (⋃ j, range (F j))⊆S := by
  classical
  have hLpos : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨K,hK⟩ := CannonPacking.exists_overlap_bound Q C (7*L) 1 hp hC (by positivity) zero_lt_one
  refine ⟨colorBound (K^2+1),?_⟩
  intro r hr hs T hsep S harc
  let P := {p : T×T // p.1≠p.2 ∧ dist p.1.val p.2.val<4*r}
  have hAP (p : P) : ∃ a : Arc X, a 0=p.val.1.val ∧ a 1=p.val.2.val ∧ diam (range a)≤L*r ∧ range a⊆S :=
    harc p.val.1.val p.val.1.property p.val.2.val p.val.2.property
      (fun h => p.property.1 (Subtype.ext h)) p.property.2
  choose A h₀ h₁ hd hAS using hAP
  have hlocal (x : X) : ((Finset.univ : Finset T).filter
      (fun t => dist x t.val≤7*(L*r))).card≤K := by
    have hscale : max (7*L) 1*r≤1 := by rw [max_eq_left (by linarith : (1:ℝ)≤7*L)]; exact hs
    have hsep' : ∀ i∈(Finset.univ : Finset T), ∀ j∈(Finset.univ : Finset T),
        i≠j → 1*r≤dist i.val j.val := by
      intro i _ j _ hij
      simpa only [one_mul] using (hsep i.val i.property j.val j.property
        (fun h => hij (Subtype.ext h)))
    simpa only [mul_assoc] using hK (fun t : T => t.val) Finset.univ x r hr hscale hsep'
  obtain ⟨color,hcolor⟩ := separated_arc_coloring (fun t : T => t.val)
    (fun p : P => p.val.1) (fun p : P => p.val.2)
    (fun i j h => Subtype.ext h) A h₀ h₁ (mul_pos hLpos hr) hd K hlocal
  obtain ⟨n,F,hFc,hFv,hFj,hFd,hFt,hFs⟩ := colored_arc_graph A (K^2+1) color (mul_pos hLpos hr) hd hcolor
  refine ⟨n,F,hFc,?_,hFd,?_,hFs.trans (iUnion_subset hAS)⟩
  · intro x hx y hy hxy hnear
    let p : P := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h),hnear⟩
    have hv := hFv p
    obtain ⟨b,hb₀,hb₁,hbs,hbd⟩ := hFj p
    refine ⟨?_,?_,b,?_,?_,hbs,?_⟩
    · simpa only [h₀,p] using hv.1
    · simpa only [h₁,p] using hv.2
    · exact hb₀.trans (h₀ p)
    · exact hb₁.trans (h₁ p)
    · simpa only [mul_assoc] using hbd
  · simpa only [mul_assoc] using hFt

end CannonEmbeddedArc.Arc

namespace CannonRelease
open Set Metric CannonGraph CannonPacking CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_polygonal_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A r₀ : ℝ, 1≤A ∧ 0 < r₀ ∧ ∃ K : ℕ, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun i j => Compatible (F i) (F j)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
          Vertex F x ∧ Vertex F y ∧ ∃ b : Arc (Boundary D), b 0=x ∧ b 1=y ∧
            range b⊆(⋃ j, range (F j)) ∧ diam (range b)≤3*A*r) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        ((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc₁,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  obtain ⟨Q,C,_,hC,hp⟩ := relative_polynomial_packing D hδ
  let A := 8/c
  have hA : 1≤A := by dsimp [A]; apply (le_div_iff₀ hc).mpr; linarith
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨K,hK⟩ := net_arc_graph_in_set Q C A hp hC.le hA
  refine ⟨A,1/(7*A),hA,by positivity,K,?_⟩
  intro r hr hrs T hsep p hpT
  have hscale : 7*A*r≤1 := by
    have h := (le_div_iff₀ (by positivity : 0<7*A)).mp hrs
    nlinarith
  have hs : 4*r/c≤1 := by
    apply (div_le_one hc).mpr
    have hh : A*c=8 := by dsimp [A]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hscale hc.le]
  obtain ⟨e,he,heR⟩ := CannonPolygonal.sphere_punctured_chart φ p
  let J := {q : T×T // q.1≠q.2 ∧ dist q.1.val q.2.val<4*r}
  have hj (j : J) : ∃ a : Arc (Boundary D), a 0=j.val.1.val ∧ a 1=j.val.2.val ∧
      diam (range a)≤A*r ∧ ∃ P : Finset (Plane×Plane),
        range a⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
    let x := j.val.1.val
    let y := j.val.2.val
    obtain ⟨U,hU,hin,hout⟩ := hdisks x (4*r/c) (by positivity) hs
    have heq : c*(4*r/c)=4*r := by field_simp
    have hx : x∈U := hin (by rw [heq]; exact mem_ball_self (by positivity))
    have hy : y∈U := hin (by rw [heq]; change dist y x<4*r; rw [dist_comm]; exact j.property.2)
    have hxp : x≠p := fun h => hpT (h ▸ j.val.1.property)
    have hyp : y≠p := fun h => hpT (h ▸ j.val.2.property)
    have hxy : x≠y := fun h => j.property.1 (Subtype.ext h)
    obtain ⟨a,ha₀,ha₁,has,P,hP⟩ := CannonPolygonal.regular_disk_chart_arc e he p heR hU hx hy hxp hyp hxy
    refine ⟨a,ha₀,ha₁,?_,P,hP⟩
    calc
      diam (range a) ≤ diam (ball x (4*r/c)) := diam_mono (has.trans (subset_closure.trans hout)) (isBounded_ball ..)
      _ ≤ 2*(4*r/c) := diam_ball (by positivity)
      _ = A*r := by dsimp [A]; ring
  choose B hB₀ hB₁ hBd R hBR using hj
  have ht (t : T) : ∃ q : Plane, e q=t.val := by
    have ht' : t.val∈range e := by rw [heR]; exact fun h => hpT ((mem_singleton_iff.mp h) ▸ t.property)
    exact ht'
  choose q hq using ht
  let P := (Finset.univ.biUnion R)∪(Finset.univ.image (fun t : T => (q t,q t)))
  let S := e '' (⋃ z∈P, segment ℝ z.1 z.2)
  have hBS (j : J) : range (B j)⊆S := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hBR j hx
    obtain ⟨s,hs,hzs⟩ := mem_iUnion₂.mp hz
    refine ⟨z,mem_iUnion₂.mpr ⟨s,?_,hzs⟩,rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hs⟩)
  have hTS : (T:Set (Boundary D))⊆S := by
    intro x hx
    let t : T := ⟨x,hx⟩
    refine ⟨q t,mem_iUnion₂.mpr ⟨(q t,q t),?_,left_mem_segment ..⟩,hq t⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  obtain ⟨n,F,hFc,hFj,hFd,hFt,hFS⟩ := hK r hr hscale T hsep S (by
    intro x hx y hy hxy hnear
    let j : J := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h),hnear⟩
    exact ⟨B j,hB₀ j,hB₁ j,hBd j,hBS j⟩)
  exact ⟨e,he,heR,P,n,F,hFc,hFj,hFd,hFt,union_subset hFS hTS⟩
end CannonRelease

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_polygonal_loop_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A B r₀ : ℝ, 1≤A ∧ 0<B ∧ 0 < r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        (∀ (f : C(I,Boundary D)), f 0=f 1 →
          ∃ H : C(I×I,Boundary D), (∀ t, H (0,t)=f t) ∧
            (∀ t, H (1,t)∈(⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
            (∀ s, H (s,0)=H (s,1)) ∧
            (∀ s s' t, dist (H (s,t)) (H (s',t))<B*r)) := by
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  obtain ⟨A,rG,hA,hrG,K,hgraph⟩ := boundary_uniform_polygonal_graph D hδ φ
  obtain ⟨L,rA,hL,hrA,harc⟩ := boundary_controlled_embedded_arcs D hδ φ
  obtain ⟨c,hc,_,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left ..)
  have hMp : 0<3*M+2 := by linarith
  let C := (3*M+2)/c
  have hC : 0<C := div_pos hMp hc
  refine ⟨A,2*C,min rG (min rA (c/(3*M+2))),hA,by positivity,
    lt_min hrG (lt_min hrA (div_pos hc hMp)),K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e₀,he₀,he₀R,P,n₀,F₀,hFc₀,hFj₀,hFd₀,hFt₀,hFS₀⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep p hpT
  have hjoin₀ (x : Boundary D) (hx : x∈(T:Set (Boundary D)))
      (y : Boundary D) (hy : y∈(T:Set (Boundary D))) (hd : dist x y<4*r) :
      JoinedIn ((⋃ j, range (F₀ j))∪(T:Set (Boundary D))) x y := by
    by_cases heq : x=y
    · subst y
      exact JoinedIn.refl (Or.inr hx)
    · obtain ⟨_,_,b,hb₀,hb₁,hbs,_⟩ := hFj₀ x hx y hy heq hd
      exact ⟨⟨b.map,hb₀,hb₁⟩,fun t => Or.inl (hbs (mem_range_self t))⟩
  obtain ⟨n,e,hconn,hretain⟩ := connected_core hr F₀ (T:Set (Boundary D)) hcover hjoin₀
  let F := F₀ ∘ e
  have hFc : Pairwise (fun i j => Compatible (F i) (F j)) := fun i j hij =>
    hFc₀ (fun h => hij (e.injective h))
  have hFd (j : Fin n) : diam (range (F j))≤A*r := hFd₀ (e j)
  have hFt (x : Boundary D) : intersectionCount F (ball x (2*A*r))≤K :=
    (intersectionCount_embedding F₀ e _).trans (hFt₀ x)
  have hFj (x : Boundary D) (hx : x∈T) (y : Boundary D) (hy : y∈T)
      (hne : x≠y) (hd : dist x y<4*r) :
      ∃ b : Arc (Boundary D), b 0=x ∧ b 1=y ∧
        range b⊆(⋃ j, range (F j)) ∧ diam (range b)≤3*A*r := by
    obtain ⟨_,_,b,hb₀,hb₁,hbs,hbd⟩ := hFj₀ x hx y hy hne hd
    exact ⟨b,hb₀,hb₁,hretain x hx y ⟨b.map,hb₀,hb₁⟩ hbs,hbd⟩
  have hFS : ((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e₀ '' (⋃ q∈P, segment ℝ q.1 q.2) := by
    apply Subset.trans _ hFS₀
    apply union_subset_union_left
    exact iUnion_subset (fun j => (show range (F₀ (e j)) ⊆ ⋃ i, range (F₀ i) from subset_iUnion (fun i => range (F₀ i)) (e j)))
  refine ⟨e₀,he₀,he₀R,P,n,F,hFc,hFd,hFt,hconn,hFS,?_⟩
  intro f hf
  have hcon (x y : Boundary D) (hd : dist x y ≤ r) :
      ∃ p : Path x y, ∀ t, dist (p t) x≤M*r := by
    by_cases heq : x=y
    · subst y
      exact ⟨Path.refl x,fun t => by simp; positivity⟩
    · obtain ⟨a,ha₀,ha₁,hs,_⟩ := harc r hr
        (hrs.trans ((min_le_right ..).trans (min_le_left ..))) x y heq (by linarith)
      refine ⟨⟨a.map,ha₀,ha₁⟩,fun t => ?_⟩
      have h := hs (mem_range_self t)
      change dist (a t) x<L*r at h
      exact h.le.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le)
  have hj (x : Boundary D) (hx : x∈(T:Set (Boundary D)))
      (y : Boundary D) (hy : y∈(T:Set (Boundary D))) (hd : dist x y<4*r) :
      ∃ p : Path x y, range p⊆(⋃ j, range (F j))∪(T:Set (Boundary D)) ∧
        ∀ t, dist (p t) x≤3*M*r := by
    by_cases heq : x=y
    · subst y
      refine ⟨Path.refl x,?_,fun t => by simp; positivity⟩
      rintro z ⟨t,rfl⟩
      exact Or.inr hx
    · obtain ⟨b,hb₀,hb₁,hbs,hbd⟩ := hFj x hx y hy heq hd
      refine ⟨⟨b.map,hb₀,hb₁⟩,hbs.trans subset_union_left,fun t => ?_⟩
      have h := dist_le_diam_of_mem b.compact_range.isBounded (mem_range_self t) (mem_range_self 0)
      rw [hb₀] at h
      exact h.trans (hbd.trans (by nlinarith [le_max_left A L]))
  have hds (x : Boundary D) : ∃ U : Set (Boundary D), IsRegularDisk U ∧
      ball x ((3*M+2)*r)⊆U ∧ U⊆ball x (C*r) := by
    have hs₁ : C*r≤1 := by
      have hh := hrs.trans ((min_le_right ..).trans (min_le_right ..))
      have hh' := (le_div_iff₀ hMp).mp hh
      dsimp only [C]
      rw [div_mul_eq_mul_div]
      apply (div_le_one hc).mpr
      nlinarith [hh']
    obtain ⟨U,hU,hin,hout⟩ := hdisks x (C*r) (mul_pos hC hr) hs₁
    have heq : c*(C*r)=(3*M+2)*r := by dsimp [C]; field_simp
    exact ⟨U,hU,by simpa only [heq] using hin,subset_closure.trans hout⟩
  simpa only [mul_assoc] using CannonLoopApproximation.loop_approximation hr hM hC
    (T:Set (Boundary D)) ((⋃ j, range (F j))∪(T:Set (Boundary D)))
    hcover hcon hj hds f hf

end CannonRelease

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_polygonal_complement_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0 < r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        (∀ S : Set (Boundary D), IsPreconnected S →
          S⊆((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ →
          ∀ x∈S, ∀ y∈S, dist x y<L*r) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,B,rG,hA,hB,hrG,K,hgraph⟩ := boundary_uniform_connected_polygonal_loop_graph D hδ φ
  obtain ⟨C,η,hC,hη,hexpand⟩ := boundary_uniform_expanding_homeomorphs D hδ
  obtain ⟨L,hL,hseparate⟩ := CannonWinding.loop_approximation_separates φ hC hB hη hexpand
  have hLp : 0<L := zero_lt_one.trans_le hL
  refine ⟨A,L,min rG (1/L),hA,hL,lt_min hrG (one_div_pos.mpr hLp),K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,happrox⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep hcover p hpT
  refine ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,?_⟩
  apply hseparate r hr (hrs.trans (min_le_right ..))
  intro f hf
  obtain ⟨H,hH₀,hH₁,hHc,hHd⟩ := happrox f hf
  let g : C(I,Boundary D) := ⟨fun t => H (1,t),by fun_prop⟩
  refine ⟨g,hHc 1,?_,?_⟩
  · rintro _ ⟨t,rfl⟩
    exact hH₁ t
  · intro t
    change dist (H (1,t)) (f t)<B*r
    rw [←hH₀ t]
    exact hHd 1 0 t

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_BoundaryLocallyConnected
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

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_finite_face_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0 < r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        Finite (ConnectedComponents ((((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ) : Set (Boundary D))) ∧
        (∀ S : Set (Boundary D), IsPreconnected S →
          S⊆((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ →
          ∀ x∈S, ∀ y∈S, dist x y<L*r) := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyConnectedSpace (Boundary D) := φ.locallyConnectedSpace
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  obtain ⟨A,L,r₀,hA,hL,hr₀,K,hgraph⟩ := boundary_uniform_connected_polygonal_complement_graph D hδ φ
  refine ⟨A,L,r₀,hA,hL,hr₀,K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,hsmall⟩ := hgraph r hr hrs T hsep hcover p hpT
  refine ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,?_,hsmall⟩
  have hclosed : IsClosed ((⋃ j, range (F j))∪(T:Set (Boundary D))) :=
    (isClosed_iUnion_of_finite (fun j => (F j).compact_range.isClosed)).union T.finite_toSet.isClosed
  exact CannonFiniteFaces.finite_components_chart_support e he p heR hclosed P hFS
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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ChartLabel
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

namespace CannonFaceIncidence
open Set Topology

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
variable {Y : Type*} [TopologicalSpace Y]

omit [DiscreteTopology D] in
lemma chartLabel_continuous (e : Y → X) (he : Continuous e) {V : Set X}
    {π : V → D} (hπ : Continuous π) : Continuous (chartLabel e π) :=
  hπ.comp ((he.comp continuous_subtype_val).subtype_mk _)

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y] in
lemma region_chartLabel (e : Y → X) {V : Set X} (π : V → D) (d : D) :
    region _ (chartLabel e π) d=e ⁻¹' region V π d := by
  ext x
  rfl

end CannonFaceIncidence

namespace CannonFaceIncidence
open Set Topology

variable {X Y D : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace D] [DiscreteTopology D]

omit [DiscreteTopology D] in
lemma labelPull_continuous (e : Y → X) (he : Continuous e)
    {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V) {π : V → D} (hπ : Continuous π) :
    Continuous (labelPull e hW π) :=
  (chartLabel_continuous e he hπ).comp (Homeomorph.setCongr hW).continuous

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] in
lemma region_labelPull (e : Y → X) {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V)
    (π : V → D) (d : D) : region W (labelPull e hW π) d=e ⁻¹' region V π d := by
  subst W
  exact region_chartLabel e π d

omit [TopologicalSpace D] [DiscreteTopology D] in
lemma incident_labelPull (e : Y → X) (he : IsOpenMap e) (hc : Continuous e)
    {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V) (π : V → D) (x : Y) :
    incident W (labelPull e hW π) x=incident V π (e x) := by
  ext d
  change x∈closure (region W (labelPull e hW π) d) ↔ e x∈closure (region V π d)
  rw [region_labelPull, ← he.preimage_closure_eq_closure_preimage hc (region V π d)]
  rfl

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_PullChartUnionCompl
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
open Set Topology CannonFaceIncidence unitInterval

variable {ι X D : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]
  [TopologicalSpace D] [DiscreteTopology D]

omit [Fintype ι] [T2Space X] in
lemma pullChart_union_compl (e : ℂ → X) (he : IsEmbedding e) (F : ι → Arc X)
    (hF : ∀ i, range (F i)⊆range e) :
    (⋃ i,range (pullChart e he (F i) (hF i)))ᶜ=e ⁻¹' (⋃ i,range (F i))ᶜ := by
  simp only [pullChart_range,preimage_compl,preimage_iUnion]

theorem chart_tame_face_structure (e : ℂ → X) (he : IsOpenEmbedding e)
    (F : ι → Arc X) (hrange : ∀ i, range (F i)⊆range e)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ))
    (hQ : ∀ i, e ⁻¹' range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set X) → D} (hπ : Continuous π) :
    ∃ (S : D → Set ι) (labels : ι → Bool → D),
      (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
      (∀ d i, i∈S d ↔ d∈range (labels i)) := by
  let Fc : ι → Arc ℂ := fun i => pullChart e he.isEmbedding (F i) (hrange i)
  have heFc (i : ι) (t : I) : e (Fc i t)=F i t := map_pullChart e he.isEmbedding (F i) (hrange i) t
  have hEq : (⋃ i,range (Fc i))ᶜ=e ⁻¹' (⋃ i,range (F i))ᶜ :=
    pullChart_union_compl e he.isEmbedding F hrange
  let πc := labelPull e hEq π
  have hπc : Continuous πc := labelPull_continuous e he.continuous hEq hπ
  have hFc : Pairwise (fun i j => Compatible (Fc i) (Fc j)) := by
    intro i j hij
    exact pullChart_compatible e he.isEmbedding (F i) (F j) (hrange i) (hrange j) (hF hij)
  have hQc : ∀ i, range (Fc i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    intro i
    rw [show range (Fc i)=e ⁻¹' range (F i) from pullChart_range ..]
    exact hQ i
  choose labels hlabels using tame_edge_incident_labels Fc hFc Q hQc hπc
  refine ⟨fun d => regionEdges Fc πc d,labels,?_,?_⟩
  · intro d
    have hc := tame_region_closure Fc hFc Q hQc hπc d
    have hinc : ∀ z, incident _ πc z=incident _ π (e z) :=
      incident_labelPull e he.isOpenMap he.continuous hEq π
    apply Subset.antisymm
    · intro x hx
      by_cases hxR : x∈region _ π d
      · exact Or.inl hxR
      have hxK : x∈⋃ i,range (F i) := by
        by_contra hn
        exact hxR (closure_region_inside
          (isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed)).isOpen_compl hπ hx hn)
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
      have hx' : Fc i t∈closure (region _ πc d) := by
        change d∈incident _ πc (Fc i t)
        rw [hinc,heFc]
        exact hx
      rw [hc] at hx'
      rcases hx' with hx'|hx'
      · have hx'' := hx'
        rw [show region _ πc d=e ⁻¹' region _ π d from region_labelPull e hEq π d] at hx''
        exact (hxR (by simpa only [mem_preimage,heFc] using hx'')).elim
      · right
        obtain ⟨j,hj,s,hs⟩ := mem_iUnion₂.mp hx'
        exact mem_iUnion₂.mpr ⟨j,hj,s,by simpa only [heFc] using congrArg e hs⟩
    · rintro x (hx|hx)
      · exact subset_closure hx
      · obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hx
        have hx' := region_edge_in_closure Fc hFc Q hQc hπc hi (mem_range_self t)
        change d∈incident _ πc (Fc i t) at hx'
        rw [hinc,heFc] at hx'
        exact hx'
  · intro d i
    constructor
    · rintro ⟨t,ht₀,ht₁,ht⟩
      rwa [hlabels i t ht₀ ht₁] at ht
    · intro hd
      let t : I := ⟨1/2,by constructor <;> norm_num⟩
      have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
      have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
      refine ⟨t,ht₀,ht₁,?_⟩
      rwa [hlabels i t ht₀ ht₁]

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
-- module Solutions.OAIQ046_CN.Cannon_Topology_ComponentRegionConnected
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

namespace CannonFaceLabels
open Set Topology CannonFaceIncidence

variable {X : Type*} [TopologicalSpace X]

theorem component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  have he : region V ConnectedComponents.mk (ConnectedComponents.mk x)=
      Subtype.val '' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨hy,hπ⟩
      exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hπ,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,ConnectedComponents.coe_eq_coe'.mpr hz⟩
  rw [he]
  exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
end CannonFaceLabels

end
end
end
end
end
end
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
-- module Solutions.OAIQ046_CN.Cannon_Topology_Plane
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

namespace CannonPlaneLinear

lemma preimage_segment (x y : Plane) :
    complexPlaneL ⁻¹' segment ℝ x y=segment ℝ (complexPlaneL.symm x) (complexPlaneL.symm y) := by
  calc
    _=complexPlaneL.symm '' segment ℝ x y := by
      ext z
      constructor
      · intro hz
        exact ⟨complexPlaneL z,hz,complexPlaneL.symm_apply_apply z⟩
      · rintro ⟨w,hw,rfl⟩
        simpa using hw
    _=segment ℝ (complexPlaneL.symm x) (complexPlaneL.symm y) := by
      simpa using image_segment ℝ complexPlaneL.symm.toLinearEquiv.toAffineEquiv.toAffineMap x y

lemma finite_segments_pull (P : Finset (Plane × Plane)) :
    ∃ Q : Finset (ℂ × ℂ), complexPlaneL ⁻¹' (⋃ p∈P,segment ℝ p.1 p.2)=
      ⋃ q∈Q,segment ℝ q.1 q.2 := by
  classical
  refine ⟨P.image (fun p => (complexPlaneL.symm p.1,complexPlaneL.symm p.2)),?_⟩
  simp only [preimage_iUnion,preimage_segment]
  ext z
  simp
end CannonPlaneLinear

noncomputable section
open Set Topology

namespace CannonConnectedSupport
variable {X : Type*} [TopologicalSpace X] [T1Space X]

theorem finite_extras_absorbed {K T : Set X} (hK : IsClosed K) (hT : T.Finite)
    (hconn : IsPreconnected (K∪T)) (hnt : (K∪T).Nontrivial) : T⊆K := by
  intro x hxT
  by_contra hxK
  let S := K∪T
  let _ : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  let z : S := ⟨x,Or.inr hxT⟩
  have he : ({z} : Set S)ᶜ=Subtype.val ⁻¹' (K∪(T\{x})) := by
    ext y
    simp only [mem_compl_iff,mem_singleton_iff,mem_preimage,mem_union,mem_sdiff]
    constructor
    · intro hy
      rcases y.property with hyK|hyT
      · exact Or.inl hyK
      · exact Or.inr ⟨hyT,fun h => hy (Subtype.ext h)⟩
    · intro hy h
      subst y
      rcases hy with hzK|hzT
      · exact hxK hzK
      · exact hzT.2 rfl
  have hc : IsClopen ({z} : Set S) := by
    refine ⟨isClosed_singleton,?_⟩
    rw [←isClosed_compl_iff,he]
    exact (hK.union (hT.sdiff).isClosed).preimage continuous_subtype_val
  have hall := hc.eq_univ (singleton_nonempty z)
  obtain ⟨a,ha,b,hb,hab⟩ := hnt
  have ha' : (⟨a,ha⟩ : S)=z := mem_singleton_iff.mp (hall.symm ▸ mem_univ _)
  have hb' : (⟨b,hb⟩ : S)=z := mem_singleton_iff.mp (hall.symm ▸ mem_univ _)
  exact hab (congrArg Subtype.val (ha'.trans hb'.symm))
end CannonConnectedSupport

noncomputable section
open Set Topology

namespace CannonFaceLabels
variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

lemma complement_components_discrete {K : Set X} (hK : IsClosed K) :
    DiscreteTopology (ConnectedComponents (Kᶜ : Set X)) := by
  let _ : LocallyConnectedSpace (Kᶜ : Set X) := hK.isOpen_compl.locallyConnectedSpace
  infer_instance
end CannonFaceLabels

end
end
end
end
end
end
end
end
end
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

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

  CannonFaceIncidence CannonFaceLabels CannonPlaneLinear CannonIncidence
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_controlled_faces_oai (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0 < r₀ ∧ ∃ K J : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ Q : Finset (ℂ × ℂ), ∃ n : ℕ, 0<n ∧ ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun i j => Compatible (F i) (F j)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        (∀ x, intersectionCount F (ball x ((L+1)*r))≤J) ∧
        IsPathConnected (⋃ j,range (F j)) ∧ (T:Set (Boundary D))⊆(⋃ j,range (F j)) ∧
        (⋃ j,range (F j))⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) ∧
        Finite (ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))) ∧
        (∀ R : Set (Boundary D), IsPreconnected R → R⊆(⋃ j,range (F j))ᶜ →
          ∀ x∈R, ∀ y∈R, dist x y<L*r) ∧
        (let Faces := ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))
         let π : ((⋃ j,range (F j))ᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
         ∃ (S : Faces → Set (Fin n)) (labels : Fin n → Bool → Faces),
           (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
           (∀ d i, i∈S d ↔ d∈range (labels i)) ∧
           (∀ d, Nat.card (S d)≤J)) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyConnectedSpace (Boundary D) := φ.locallyConnectedSpace
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let s : SphereTwo := Classical.choice inferInstance
  let _ : Nontrivial (Boundary D) := ⟨⟨φ.symm s,φ.symm (-s),
    fun h => (ne_neg_of_mem_unit_sphere ℝ s) (φ.symm.injective h)⟩⟩
  obtain ⟨a,b,hab⟩ := exists_pair_ne (Boundary D)
  have hdist : 0<dist a b := dist_pos.mpr hab
  dsimp only
  obtain ⟨A,L,rG,hA,hL,hrG,K,hgraph⟩ := boundary_uniform_finite_face_graph D hδ φ
  obtain ⟨Q₀,C,hQ₀,hC,hpoly⟩ := relative_polynomial_packing D hδ
  obtain ⟨B,hB⟩ := uniform_larger_trace Q₀ C (L+1) hpoly hC.le (by linarith)
  refine ⟨A,L,min rG (min (dist a b/4) (1/(L+2))),hA,hL,
    lt_min hrG (lt_min (by positivity) (by positivity)),K,B*K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  have hrG' : r ≤ rG := hrs.trans (min_le_left ..)
  have hrD : r≤dist a b/4 := hrs.trans ((min_le_right ..).trans (min_le_left ..))
  have hrL : r≤1/(L+2) := hrs.trans ((min_le_right ..).trans (min_le_right ..))
  have hscale : (L+2)*r≤1 := by have hh := (le_div_iff₀ (by linarith : 0<L+2)).mp hrL; nlinarith
  have hTnt : (T:Set (Boundary D)).Nontrivial := by
    obtain ⟨u,hu,hau⟩ := hcover a
    obtain ⟨v,hv,hbv⟩ := hcover b
    refine ⟨u,hu,v,hv,?_⟩
    intro heq
    subst v
    have hh := dist_triangle a u b
    rw [dist_comm u b] at hh
    linarith
  obtain ⟨e₀,he₀,he₀R,P,n,F,hFc,hFd,hFt,hconn,hFS,hfinite,hsmall⟩ :=
    hgraph r hr hrG' T hsep hcover p hpT
  let V : Set (Boundary D) := ⋃ j,range (F j)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun j => (F j).compact_range.isClosed)
  have hTV : (T:Set (Boundary D))⊆V := CannonConnectedSupport.finite_extras_absorbed
    hV T.finite_toSet hconn.isConnected.isPreconnected (hTnt.mono subset_union_right)
  have heq : V∪(T:Set (Boundary D))=V := union_eq_left.mpr hTV
  change IsPathConnected (V∪(T:Set (Boundary D))) at hconn
  change V∪(T:Set (Boundary D))⊆e₀ '' _ at hFS
  change Finite (ConnectedComponents ((V∪(T:Set (Boundary D)))ᶜ : Set (Boundary D))) at hfinite
  change ∀ R : Set (Boundary D), IsPreconnected R → R⊆(V∪(T:Set (Boundary D)))ᶜ →
    ∀ x∈R, ∀ y∈R, dist x y<L*r at hsmall
  rw [heq] at hconn hFS hfinite hsmall
  have hn : 0<n := by
    by_contra hn
    have hn0 : n=0 := Nat.eq_zero_of_not_pos hn
    obtain ⟨x,hx⟩ := hTnt.nonempty
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hTV hx)
    exact (Nat.not_lt_zero i.val) (hn0 ▸ i.isLt)
  let e : ℂ → Boundary D := e₀ ∘ complexPlaneL
  have he : IsOpenEmbedding e := he₀.comp complexPlaneL.toHomeomorph.isOpenEmbedding
  have heR : range e={p}ᶜ := by rw [show range e=range e₀ from (complexPlaneL.surjective.range_comp e₀),he₀R]
  obtain ⟨Q,hQ⟩ := finite_segments_pull P
  have hVS : V⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hFS hx
    refine ⟨complexPlaneL.symm y,?_,by simp [e,Function.comp_def]⟩
    rw [←hQ]
    simpa using hy
  have hrange (i : Fin n) : range (F i)⊆range e :=
    (subset_iUnion (fun j => range (F j)) i).trans (hVS.trans (image_subset_range ..))
  have hQs (i : Fin n) : e ⁻¹' range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := hVS (mem_iUnion.mpr ⟨i,hz⟩)
    exact he.injective heq ▸ hw
  have hwide (x : Boundary D) : intersectionCount F (ball x ((L+1)*r))≤B*K := by
    have hh := hB r A hr hA (by convert hscale using 1; ring) T hsep hcover
      (fun i => range (F i)) K (fun x => by simpa only [traceCard,intersectionCount_eq_card] using hFt x) x
    simpa only [traceCard,intersectionCount_eq_card] using hh
  let Faces := ConnectedComponents (Vᶜ : Set (Boundary D))
  let _ : DiscreteTopology Faces := complement_components_discrete hV
  let π : (Vᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
  have hπ : Continuous π := ConnectedComponents.continuous_coe
  obtain ⟨S,labels,hcl,hlabels⟩ := chart_tame_face_structure e he F hrange hFc Q hQs hπ
  refine ⟨e,he,heR,Q,n,hn,F,hFc,hFd,hFt,hwide,hconn,hTV,hVS,hfinite,hsmall,
    S,labels,hcl,hlabels,?_⟩
  intro d
  have hR := component_region_connected Vᶜ d
  obtain ⟨x,hx⟩ := hR.nonempty
  have hRd : region Vᶜ π d⊆closedBall x (L*r) := by
    intro y hy
    simpa only [mem_closedBall,dist_comm] using (hsmall _ hR.isPreconnected (region_subset Vᶜ π d) x hx y hy).le
  have hclose : closure (region Vᶜ π d)⊆closedBall x (L*r) :=
    closure_minimal hRd isClosed_closedBall
  have hsub : S d⊆{i | (range (F i)∩ball x ((L+1)*r)).Nonempty} := by
    intro i hi
    refine ⟨F i 0,mem_range_self 0,?_⟩
    have hh : F i 0∈closure (region Vᶜ π d) := by
      rw [hcl d]
      exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩)
    have hd := hclose hh
    change dist (F i 0) x≤L*r at hd
    change dist (F i 0) x<(L+1)*r
    nlinarith
  calc
    Nat.card (S d)≤Nat.card {i | (range (F i)∩ball x ((L+1)*r)).Nonempty} :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    _=intersectionCount F (ball x ((L+1)*r)) := by
      simp [intersectionCount_eq_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
    _≤B*K := hwide x
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

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonRelease.boundary_uniform_controlled_faces_oai.{u_1} := @OAI.CannonRelease.boundary_uniform_controlled_faces_oai.{u_1}
