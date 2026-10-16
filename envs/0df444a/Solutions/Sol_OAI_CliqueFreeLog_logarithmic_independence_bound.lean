-- Prove2me | solution 1 for OAI.CliqueFreeLog.logarithmic_independence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:16.98369+00:00
-- url     : https://prove2.me/submissions/bcfa962e-bd5c-48da-95ef-607d15b0e028

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Main.lean:L20-L82
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CliqueFreeLog.logarithmic_independence_bound.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CliqueFreeLog_logarithmic_independence_bound) verbatim and is proved by it.
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_maximum_degree_independence
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_cross_bound
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_weighted_triangles

-- ---- from OAI.Combinatorics.CliqueFree.IndependentSet ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma exists_optimizer_triangle_bound (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      IsOptimizer G w → G.CliqueFree (k+2) → triangleMass G w ≤ B * edgeMass G w := by
  have hC : 1 ≤ 16*((k : ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨B,hB,hbound⟩ := weighted_triangles.{u} hC
  exact ⟨B,hB,fun G w hw hf ↦ hbound G w (fun v ↦ (optimizer_stationary hw v).1)
    (optimizer_cross_bound k G hw hf)⟩

lemma degree_induce_le (G : SimpleGraph V) (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (fun u : (G.induce (A : Set V)).neighborSet v ↦
      (⟨u.val.val, u.property⟩ : G.neighborSet v))
    (fun u z h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : G.neighborSet v ↦ (x : V)) h)

omit [Fintype V] in
lemma indepSet_image_induce (G : SimpleGraph V) (A : Finset V) (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set (A : Set V))) :
    G.IsIndepSet (I.map ⟨Subtype.val, Subtype.val_injective⟩ : Set V) := by
  classical
  intro a ha b hb hab
  obtain ⟨a',ha',rfl⟩ := mem_map.1 ha
  obtain ⟨b',hb',rfl⟩ := mem_map.1 hb
  exact hI ha' hb' (fun h ↦ hab (congrArg Subtype.val h))

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.MaxDegree ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma indepNum_induce_le (G : SimpleGraph V) (A : Finset V) :
    (G.induce (A : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨I,hI⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  have h := (indepSet_image_induce G A I hI.isIndepSet).card_le_indepNum
  simpa only [card_map,hI.card_eq] using h

lemma degree_cutoff_card (G : SimpleGraph V) {d : ℝ} (hd : 0 < d)
    (hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ)*d) :
    (Fintype.card V : ℝ)/2 ≤ ((univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d).card : ℝ) := by
  classical
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d
  have hv (v : V) (h : v ∈ Aᶜ) : 2*d ≤ (G.degree v : ℝ) := by
    have hh : ¬(G.degree v : ℝ) ≤ 2*d := by simpa [A] using h
    exact le_of_lt (lt_of_not_ge hh)
  have hlow := sum_le_sum (s := Aᶜ) fun v h ↦ hv v h
  simp only [sum_const,nsmul_eq_mul] at hlow
  have hu : (∑ v ∈ Aᶜ, (G.degree v : ℝ)) ≤ ∑ v, (G.degree v : ℝ) := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hcard : (A.card : ℝ)+(Aᶜ.card : ℝ) = Fintype.card V := by
    exact_mod_cast card_add_card_compl A
  change (Fintype.card V : ℝ)/2 ≤ (A.card : ℝ)
  rw [hsum] at hu
  nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Main ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeLog
open CliqueFreeIndependence.WeightedGraph

lemma sum_degrees_real {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ v, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- The logarithmic independence bound for ordinary clique exclusion and the graph's own
average degree, with a constant uniform in graph size and average degree. -/
theorem logarithmic_independence_bound (r : ℕ) (hr : 4 ≤ r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        G.CliqueFree r → 2 ≤ averageDegree G →
        c * (Fintype.card V : ℝ) * Real.log (averageDegree G) / averageDegree G ≤
          (G.indepNum : ℝ) := by
  classical
  obtain ⟨B,hB,htri⟩ := exists_optimizer_triangle_bound.{0} (r-2)
  let D : ℝ := 3+3*B/2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1/(16*D),by positivity,?_⟩
  intro V _ G hf hd
  let d : ℝ := averageDegree G
  have hd2 : 2 ≤ d := hd
  have hdpos : 0 < d := by linarith
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    intro hn
    have hz : averageDegree G = 0 := by simp [averageDegree,hn]
    rw [hz] at hd
    norm_num at hd
  have hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ)*d := by
    rw [sum_degrees_real]
    dsimp [d, averageDegree]
    field_simp
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d
  have hAcard : (Fintype.card V : ℝ)/2 ≤ (Fintype.card (A : Set V) : ℝ) := by
    have he : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    rw [he]
    exact degree_cutoff_card G hdpos hsum
  have hk : r-2+2 = r := Nat.sub_add_cancel (by omega)
  have hfree : (G.induce (A : Set V)).CliqueFree (r-2+2) := by
    rw [hk]
    exact (G.cliqueFree_induce_iff _ _).2 hf.cliqueFreeOn
  have hdeg (v : (A : Set V)) : ((G.induce (A : Set V)).degree v : ℝ) ≤ 2*d := by
    have hv : (G.degree v : ℝ) ≤ 2*d := (mem_filter.1 v.property).2
    exact (Nat.cast_le.2 (degree_induce_le G A v)).trans hv
  have hmax := maximum_degree_independence (r-2) hB.le (by linarith : 3 ≤ 2*d)
    htri (G.induce (A : Set V)) hfree hdeg
  have hi : ((G.induce (A : Set V)).indepNum : ℝ) ≤ G.indepNum :=
    Nat.cast_le.2 (indepNum_induce_le G A)
  have hlog : Real.log d ≤ Real.log (2*d) :=
    Real.log_le_log hdpos (by linarith)
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hnum : (Fintype.card V : ℝ)*Real.log d/2 ≤
      (Fintype.card (A : Set V) : ℝ)*Real.log (2*d) := by
    have h1 := mul_le_mul_of_nonneg_right hAcard hlog0
    have h2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (Fintype.card (A : Set V)))
    nlinarith
  have hden : 0 < 8*D*d := by positivity
  have hcompare := div_le_div_of_nonneg_right hnum hden.le
  change (Fintype.card (A : Set V) : ℝ)*Real.log (2*d)/(4*D*(2*d)) ≤ _ at hmax
  have heq : (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d =
      ((Fintype.card V : ℝ)*Real.log d/2)/(8*D*d) := by
    field_simp
    ring
  change (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d ≤ _
  rw [heq]
  apply hcompare.trans
  have hdeneq : 8*D*d = 4*D*(2*d) := by ring
  rw [hdeneq]
  exact hmax.trans hi

end CliqueFreeLog

end

end OAI

-- ---- mission target ----
open OAI OAI.CliqueFreeLog
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open CliqueFreeIndependence.WeightedGraph

theorem solution (r : ℕ) (hr : 4 ≤ r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        G.CliqueFree r → 2 ≤ averageDegree G →
        c * (Fintype.card V : ℝ) * Real.log (averageDegree G) / averageDegree G ≤
          (G.indepNum : ℝ) := by
  first
    | exact OAI.CliqueFreeLog.logarithmic_independence_bound r hr
    | exact OAI.CliqueFreeLog.logarithmic_independence_bound
    | (apply OAI.CliqueFreeLog.logarithmic_independence_bound <;> assumption)
    | (intros; apply OAI.CliqueFreeLog.logarithmic_independence_bound <;> assumption)
