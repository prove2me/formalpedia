-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:52:41.70114+00:00
-- url     : https://prove2.me/submissions/63aa7fce-e2c0-4f66-ba95-91db36f2b230

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean:L32-L76
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_EdgeProjection_crossMass_edge_sum
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_mono
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_peeling
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_weighted_splitting

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

lemma lossRatio_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lossRatio x :=
  div_nonneg (Real.log_nonneg hx) (Real.sqrt_nonneg _)

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

omit [Fintype V] in
lemma crossMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : 0 ≤ crossMass G w A B := by
  classical
  exact sum_nonneg fun u _ ↦ sum_nonneg fun v _ ↦ by
    split_ifs
    · exact mul_nonneg (hw u) (hw v)
    · exact le_rfl

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma triangleMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ triangleMass G w := div_nonneg
      (sum_nonneg fun u _ ↦ mul_nonneg (hw u) (triangleAt_nonneg G hw u)) (by norm_num)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Projection ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

omit [Fintype V] [Fintype U] in
lemma edgeMap_injective (h : EdgeProjection H G π) : Function.Injective h.edgeMap := by
  intro e f hef
  have heq := congrArg Subtype.val hef
  have hpair := h.inj e.src e.dst f.src f.dst e.adj f.adj
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  exact Subtype.ext (Prod.ext hpair.1 hpair.2)

omit [Fintype V] [Fintype U] in
lemma mass_image_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset U) :
    mass w (A.image π) ≤ mass (w ∘ π) A := by
  classical
  exact sum_image_le_of_nonneg (fun _ _ ↦ hw _)

lemma crossMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset U) :
    crossMass H (w ∘ π) A B ≤ crossMass G w (A.image π) (B.image π) := by
  classical
  rw [crossMass_edge_sum, crossMass_edge_sum]
  calc
    _ ≤ ∑ e : EdgeState H,
        if (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π
          then w (h.edgeMap e).src * w (h.edgeMap e).dst else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : e.src ∈ A ∧ e.dst ∈ B
      · have hi : (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π :=
          ⟨mem_image.2 ⟨e.src, he.1, rfl⟩, mem_image.2 ⟨e.dst, he.2, rfl⟩⟩
        simp only [he, hi]
        exact le_rfl
      · simp only [he, ↓reduceIte]
        split_ifs
        · exact mul_nonneg (hw _) (hw _)
        · exact le_rfl
    _ ≤ _ := sum_injective_le h.edgeMap h.edgeMap_injective
      (fun e ↦ if e.src ∈ A.image π ∧ e.dst ∈ B.image π then w e.src * w e.dst else 0)
      (fun e ↦ by split_ifs; exact mul_nonneg (hw _) (hw _); exact le_rfl)

lemma crossBound (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {C : ℝ} (hC : 0 ≤ C) (hc : CrossBound G w C) : CrossBound H (w ∘ π) C := by
  classical
  intro x hx A B hA hB
  have hAi := mass_image_le (π := π) hw A
  have hBi := mass_image_le (π := π) hw B
  exact (h.crossMass_le hw A B).trans ((hc x hx _ _ (hAi.trans hA) (hBi.trans hB)).trans
    (mul_le_mul_of_nonneg_left (growth_mono hx (mass_nonneg hw _) (mass_nonneg (fun u ↦ hw (π u)) _) hAi) hC))

omit [Fintype V] in
lemma neighbor_injective (h : EdgeProjection H G π) (a : U) :
    Set.InjOn π (neighbors H a) := by
  intro b hb c hc heq
  exact (h.inj a b a c ((mem_neighbors _ _ _).1 hb) ((mem_neighbors _ _ _).1 hc) rfl heq).2

lemma neighborhood_image (h : EdgeProjection H G π) (a : U) :
    (neighbors H a).image π ⊆ neighbors G (π a) := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hb
  exact (mem_neighbors _ _ _).2 (h.map_adj _ _ ((mem_neighbors _ _ _).1 hc))

lemma neighborMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (a : U) :
    neighborMass H (w ∘ π) a ≤ neighborMass G w (π a) := by
  classical
  calc
    _ = mass w ((neighbors H a).image π) := (sum_image (h.neighbor_injective a)).symm
    _ ≤ _ := mass_mono hw (h.neighborhood_image a)

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.TriangleBound ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma EdgeProjection.of_le {G H : SimpleGraph V} (hHG : H ≤ G) : EdgeProjection H G id where
  map_adj := fun _ _ h ↦ hHG h
  inj := fun _ _ _ _ _ _ h1 h2 ↦ ⟨h1,h2⟩

lemma neighborMass_bot (w : V → ℝ) (u : V) : neighborMass (⊥ : SimpleGraph V) w u = 0 := by
  simp [neighborMass, neighbors, mass]

lemma triangleMass_bot (w : V → ℝ) : triangleMass (⊥ : SimpleGraph V) w = 0 := by
  simp [triangleMass,triangleAt,neighbors]

lemma splittingConstant_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ splittingConstant C := by
  unfold splittingConstant smoothingConstant entropyConstant exceptionalConstant
  positivity

/-- One reduction step, allowing an arbitrary finite vertex type of copies. -/
lemma neighborhood_reduction (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hε : splittingConstant C * Numerical.lossRatio x ≤ 1)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ (U : Type u) (_ : Fintype U) (J : SimpleGraph U) (π : U → V),
      EdgeProjection J G π ∧ (∀ a, neighborMass J (w ∘ π) a ≤ Real.exp (Real.sqrt x)) ∧
      (1-splittingConstant C * Numerical.lossRatio x) * triangleMass G w - edgeMass G w / x ≤
        triangleMass J (w ∘ π) := by
  have hx0 : 0 < x := by linarith
  have hw0 := fun v ↦ (hw v).le
  have hε0 : 0 ≤ splittingConstant C * Numerical.lossRatio x :=
    mul_nonneg (splittingConstant_nonneg hC) (Numerical.lossRatio_nonneg (by linarith))
  obtain ⟨H,hHG,hc,hpeel⟩ := peeling G hw (one_div_pos.2 hx0)
  have hprojH := EdgeProjection.of_le hHG
  have hcH : CrossBound H w C := by
    simpa only [Function.comp_id] using hprojH.crossBound hw0 (by linarith) hCross
  have hLH : ∀ u, neighborMass H w u ≤ Real.exp x := by
    intro u
    exact (hprojH.neighborMass_le hw0 u).trans (hL u)
  by_cases hne : Nonempty (EdgeState H)
  · let := hne
    obtain ⟨J,hproj,hJ,hT⟩ := weighted_splitting hw hC hcH hx hc hLH
    refine ⟨EdgeState H,inferInstance,J,EdgeState.src,?_,hJ,?_⟩
    · exact ⟨fun a b h ↦ hHG (hproj.map_adj a b h),hproj.inj⟩
    · change (1-splittingConstant C * Numerical.lossRatio x) * triangleMass H w ≤
        triangleMass J (w ∘ EdgeState.src) at hT
      have hh := mul_le_mul_of_nonneg_left hpeel (sub_nonneg.2 hε)
      have hm := div_nonneg (edgeMass_nonneg G hw0) hx0.le
      rw [one_div_mul_eq_div] at hh
      nlinarith only [hT, hh, mul_nonneg hε0 hm]
  · have hbot : H = ⊥ := by
      apply SimpleGraph.ext
      funext a b
      apply propext
      simpa only [SimpleGraph.bot_adj, iff_false] using
        (fun hab : H.Adj a b ↦ hne ⟨⟨(a,b),hab⟩⟩)
    rw [hbot,triangleMass_bot] at hpeel
    refine ⟨V,inferInstance,⊥,id,EdgeProjection.of_le bot_le,?_,?_⟩
    · intro a
      simp only [Function.comp_id,neighborMass_bot]
      exact (Real.exp_pos _).le
    · simp only [Function.comp_id,triangleMass_bot]
      rw [one_div_mul_eq_div] at hpeel
      nlinarith [mul_nonneg hε0 (triangleMass_nonneg G hw0)]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction.{u}
