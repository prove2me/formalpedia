-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:57:49.713391+00:00
-- url     : https://prove2.me/submissions/84e3ab26-e570-4768-bcde-8d03996f719e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean:L140-L161
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_triangle_bound_scale

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

lemma scale_ge {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : X ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 1 ≤ scale X n := hX.trans ih
    dsimp [scale]
    nlinarith

lemma scale_ge_add {X : ℝ} (hX : 2 ≤ X) (n : ℕ) : X + n ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    simp only [scale, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma exists_iteration_threshold (a : ℝ) :
    ∃ X : ℝ, 32 ≤ X ∧ a * lossRatio X ≤ 1/4 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ ↦ a * lossRatio x) atTop (nhds 0) := by
    simpa only [lossRatio, Real.sqrt_eq_rpow, mul_zero] using h.const_mul a
  have he : ∀ᶠ x : ℝ in atTop, a * lossRatio x < 1/4 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨X,hX⟩ := eventually_atTop.1 he
  exact ⟨max 32 X, le_max_left _ _, (hX (max 32 X) (le_max_right _ _)).le⟩

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

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

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

/-- The weighted triangle theorem with a size-independent constant. -/
theorem weighted_triangles {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ v, 0 < w v) → CrossBound G w C → triangleMass G w ≤ B * edgeMass G w := by
  obtain ⟨X,hX,hsmall⟩ := Numerical.exists_iteration_threshold (splittingConstant C)
  refine ⟨2*(1+Real.exp X/3),by positivity,?_⟩
  intro V _ G w hw hCross
  obtain ⟨n,hn⟩ := exists_nat_ge (mass w (univ : Finset V))
  have hL : ∀ v, neighborMass G w v ≤ Real.exp (Numerical.scale X n) := by
    intro v
    calc
      _ ≤ mass w univ := mass_mono (fun v ↦ (hw v).le) (subset_univ _)
      _ ≤ n := hn
      _ ≤ Numerical.scale X n := by
        have hh := Numerical.scale_ge_add (by linarith : 2 ≤ X) n
        linarith
      _ ≤ Real.exp (Numerical.scale X n) := by linarith [Real.add_one_le_exp (Numerical.scale X n)]
  have ht := triangle_bound_scale hC hX hsmall n G w hw hCross hL
  have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
  have hB : 0 ≤ 1+Real.exp X/3 := by positivity
  have hq : 0 ≤ (1/2:ℝ)^n := by positivity
  nlinarith [mul_nonneg hB hq, mul_nonneg (mul_nonneg hB hq) he]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles.{u}
