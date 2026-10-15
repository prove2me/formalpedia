-- Prove2me | solution 1 for OAI.QAC.reflectionTerms_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:09:57.436457+00:00
-- url     : https://prove2.me/submissions/1c37d0df-c129-411e-a488-4a48f3b40408

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean:L84-L101
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.reflectionTerms_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_mul {N : ℕ} (a b : Fin N → QubitOperator) :
    tensorMatrix a * tensorMatrix b = tensorMatrix (fun i => a i * b i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => a i (x i) z * b i z (y i))).symm

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Count ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.join_zero {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    (A.join B).zero = A.zero * B.zero := by
  classical
  dsimp only [Count.zero, Count.join]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · by_cases hB : i ∈ B.support <;> simp [hA, hB]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Reflection ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma reflectionTerms_support {N : ℕ} (l : List (Count N)) :
    ∀ p ∈ reflectionTerms l, ∀ i ∈ p.2.support, ∃ A ∈ l, i ∈ A.support := by
  induction l with
  | nil => simp [reflectionTerms,Count.empty]
  | cons A l ih =>
    intro p hp i hi
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨B,hB,hiB⟩ := ih p hp i hi
      exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ⟨A,List.mem_cons_self ..,hi⟩
      · obtain ⟨B,hB,hiB⟩ := ih q hq i hi
        exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩

lemma reflectionTerms_disjoint {N : ℕ} (A : Count N) (l : List (Count N))
    (h : ∀ B ∈ l, Disjoint A.support B.support) (p : ℝ × Count N) (hp : p ∈ reflectionTerms l) :
    Disjoint A.support p.2.support := by
  apply Finset.disjoint_left.mpr
  intro i hiA hip
  obtain ⟨B,hB,hiB⟩ := reflectionTerms_support l p hp i hip
  exact Finset.disjoint_left.mp (h B hB) hiA hiB

lemma reflectionTerms_sum {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum = reflectList l := by
  induction l with
  | nil => simp [reflectionTerms,reflectList]
  | cons A l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    rw [reflectionTerms,List.map_append,List.sum_append,List.map_map]
    have heq : ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)) =
        (reflectionTerms l).map (fun p => ((-2:ℝ) • A.zero) * (p.1 • p.2.zero)) := by
      apply List.map_congr_left
      intro p hp
      rw [A.join_zero p.2 (reflectionTerms_disjoint A l ha p hp),smul_mul_smul_comm]
    change ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum +
      ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)).sum = _
    rw [heq,List.sum_map_mul_left,ih hl]
    simp only [reflectList,List.map_cons,List.prod_cons,reflect,sub_mul,one_mul,neg_smul,neg_mul]
    abel

section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

end BilinearBudget

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum = reflectList l := by
  first
    | exact OAI.QAC.reflectionTerms_sum l hl
    | exact OAI.QAC.reflectionTerms_sum
    | (apply OAI.QAC.reflectionTerms_sum <;> assumption)
    | (intros; apply OAI.QAC.reflectionTerms_sum <;> assumption)
