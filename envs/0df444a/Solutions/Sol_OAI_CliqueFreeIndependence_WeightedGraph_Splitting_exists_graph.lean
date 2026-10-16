-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:44:52.58898+00:00
-- url     : https://prove2.me/submissions/075a2352-e07f-4864-b262-fefa8c2e78d7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/SplittingLoss.lean:L157-L219
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_exists_positive_ge
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_shared_rejection
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_expected_loss_le
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_neighborMass_le
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_projection
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_triangleMass_surviving_le
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_sum_eq

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma commonMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = ∑ z ∈ neighbors G u, if G.Adj v z then w z else 0 := by
  classical
  unfold commonMass mass
  rw [← filter_mem_eq_inter, sum_filter]
  simp only [mem_neighbors]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.EdgeState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq
namespace EdgeState
variable {G : SimpleGraph V}
lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

end EdgeState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.TriangleState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace TriangleState
variable {G : SimpleGraph V}
lemma sum_weight (w : V → ℝ) : (∑ t : TriangleState G, weight w t) = 6 * triangleMass G w := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z), triangleMass_eq_sum]
  simp only [triangleAt, commonMass_eq_sum, mul_sum, mul_ite, mul_zero, mul_assoc]

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.LocalWalk ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

lemma normalizer_eq : normalizer G w = 6 * triangleMass G w := by
  rw [normalizer, EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v),
    triangleMass_eq_sum]
  simp only [triangleAt, mul_sum, mul_assoc]

variable {G w}
lemma normalizer_pos [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : 0 < normalizer G w := by
  exact sum_pos (fun e _ ↦ mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) univ_nonempty

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
lemma sharp_bound_le (p q : I → ℝ) : 2 * dist p q / (1 + dist p q) ≤ 2 * dist p q := by
  have hd : 0 ≤ dist p q := div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply div_le_self (by positivity) (by linarith)

lemma positive_output {p : I → J → ℝ} {q : (I → J) → ℝ} (hq : Law q)
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y)
    {f : I → J} (hf : 0 < q f) (i : I) : 0 < p i (f i) := by
  rw [← hm]
  exact hf.trans_le (by
    have h := single_le_sum (s := univ) (a := f)
      (f := fun g ↦ if g i = f i then q g else 0)
      (fun g _ ↦ by split_ifs <;> simp_all [hq.1 g]) (mem_univ f)
    simpa using h)

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.SplittingLoss ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
open FiniteCoupling
variable {G : SimpleGraph V}

lemma surviving_mass_eq {w : V → ℝ}
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) =
      6 * triangleMass G w - ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t) := by
  rw [← TriangleState.sum_weight, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : Survives F good t <;> simp [bad, ht]

open FiniteEntropy FiniteKernel LocalWalk

/-- Splitting from a joint kernel preserving first coordinates, with two averaged losses. -/
lemma exists_graph [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) (hK : Stochastic K)
    (hblock : ∀ e z, e.src ≠ z.src → K e z = 0)
    {a D δ : ℝ}
    (hD : (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) ≤ D)
    (hδ : (∑ e, law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-a) then K e y else 0) ≤ δ) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp a) ∧
      (1 - 6 * D - 6 * δ) * triangleMass G w ≤ triangleMass H (w ∘ EdgeState.src) := by
  obtain ⟨q,hq,hm,hp⟩ := shared_rejection K hK
  have hp' (i j : EdgeState G) : (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j) :=
    (hp i j).trans (sharp_bound_le (K i) (K j))
  let b : EdgeState G → EdgeState G → Prop := fun e y ↦ w e.dst * Real.exp (-a) ≤ K y e
  let good : (EdgeState G → EdgeState G) → EdgeState G → Prop := fun F e ↦ b e (F e)
  have hb (e y : EdgeState G) : K e y * bad (b e y) =
      if K y e < w e.dst * Real.exp (-a) then K e y else 0 := by
    by_cases h : K y e < w e.dst * Real.exp (-a)
    · simp [b,bad,h,not_le.2 h]
    · simp [b,bad,h,le_of_not_gt h]
  have hloss := expected_loss_le hw hc K hq hm hp' good b (fun _ _ ↦ Iff.rfl)
  simp_rw [hb] at hloss
  have hZ := (normalizer_pos hw hc).le
  have hZeq := normalizer_eq G w
  have hbound : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w * (6 * D + 6 * δ) :=
    hloss.trans (mul_le_mul_of_nonneg_left (by linarith [hD,hδ]) hZ)
  let S : (EdgeState G → EdgeState G) → ℝ := fun F ↦
    ∑ t : TriangleState G, if Survives F (good F) t then TriangleState.weight w t else 0
  have havg : normalizer G w * (1 - 6 * D - 6 * δ) ≤ ∑ F, q F * S F := by
    dsimp [S]
    simp_rw [surviving_mass_eq]
    rw [show (∑ F, q F * (6 * triangleMass G w -
        ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t))) =
        6 * triangleMass G w - ∑ F, q F * ∑ t : TriangleState G,
          TriangleState.weight w t * bad (Survives F (good F) t) by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hq.2, one_mul]]
    nlinarith
  obtain ⟨F,hFq,hFS⟩ := exists_positive_ge hq S havg
  have hF (e : EdgeState G) : (F e).src = e.src := by
    have hpos := positive_output hq hm hFq e
    by_contra hn
    have hzero := hblock e (F e) (Ne.symm hn)
    linarith
  let H := graph F hF (good F)
  refine ⟨H,projection F hF (good F),?_,?_⟩
  · intro z
    apply neighborMass_le w F hF (good F) K (fun a e ↦ (hK a).1 e)
      (fun a ↦ (hK a).2) (Real.exp_pos a).le ?_ z
    intro e he
    have hh : w e.dst * Real.exp (-a) ≤ K (F e) e := he
    have ht := mul_le_mul_of_nonneg_left hh (Real.exp_pos a).le
    have hid : Real.exp a * (w e.dst * Real.exp (-a)) = w e.dst := by
      calc
        _ = w e.dst * (Real.exp a * Real.exp (-a)) := by ring
        _ = _ := by rw [← Real.exp_add]; simp
    rwa [hid] at ht
  · have ht := triangleMass_surviving_le (fun v ↦ (hw v).le) F hF (good F)
    change S F ≤ 6 * triangleMass H (w ∘ EdgeState.src) at ht
    rw [hZeq] at hFS
    nlinarith only [ht, hFS]

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling
open FiniteEntropy FiniteKernel LocalWalk


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph.{u}
