-- Prove2me | solution 1 for OAI.QAC.Count.pattern_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:57:58.826835+00:00
-- url     : https://prove2.me/submissions/0c63d047-787f-4fe5-8e56-f58a40a07792

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean:L112-L132
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.Count.pattern_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Theorems.Thm_OAI_QAC_rankOne_projection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma tensorMatrix_zero_of_zero {N : ℕ} (a : Fin N → QubitOperator)
    (i : Fin N) (hi : a i = 0) : tensorMatrix a = 0 := by
  classical
  ext x y
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

lemma tensorMatrix_projection {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, IsStarProjection (a i)) : IsStarProjection (tensorMatrix a) := by
  rw [isStarProjection_iff']
  constructor
  · rw [tensorMatrix_mul]
    congr 1
    funext i
    exact (ha i).isIdempotentElem.eq
  · rw [tensorMatrix_star]
    congr 1
    funext i
    exact (ha i).isSelfAdjoint.star_eq

lemma Count.pattern_projection {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    IsStarProjection (M.pattern F) := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi hF
  · exact (rankOne_projection (M.normalized i hi)).one_sub
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma Count.pattern_mul {N : ℕ} (M : Count N) {F G : Finset (Fin N)}
    (hF : F ⊆ M.support) (hG : G ⊆ M.support) :
    M.pattern F * M.pattern G = if F = G then M.pattern F else 0 := by
  classical
  by_cases hFG : F = G
  · subst G
    rw [ite_eq_left rfl, (M.pattern_projection F).isIdempotentElem.eq]
  rw [ite_eq_right hFG, Count.pattern, Count.pattern, tensorMatrix_mul]
  obtain ⟨i, hi⟩ : ∃ i, (i ∈ F ∧ i ∉ G) ∨ (i ∈ G ∧ i ∉ F) := by
    by_contra h
    push Not at h
    apply hFG
    ext i
    specialize h i
    aesop
  apply tensorMatrix_zero_of_zero _ i
  rcases hi with ⟨hiF, hiG⟩ | ⟨hiG, hiF⟩
  · simp only [ite_eq_left (hF hiF), ite_eq_left hiF, ite_eq_right hiG]
    exact (rankOne_projection (M.normalized i (hF hiF))).one_sub_mul_self
  · simp only [ite_eq_left (hG hiG), ite_eq_left hiG, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i (hG hiG))).mul_one_sub_self

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N : ℕ} (M : Count N) {F G : Finset (Fin N)}
    (hF : F ⊆ M.support) (hG : G ⊆ M.support) :
    M.pattern F * M.pattern G = if F = G then M.pattern F else 0 := by
  first
    | exact OAI.QAC.Count.pattern_mul M hF hG
    | exact OAI.QAC.Count.pattern_mul
    | (apply OAI.QAC.Count.pattern_mul <;> assumption)
    | (intros; apply OAI.QAC.Count.pattern_mul <;> assumption)
