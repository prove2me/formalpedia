-- Prove2me | solution 1 for OAI.QAC.Count.high_mul_pattern
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:01:26.003703+00:00
-- url     : https://prove2.me/submissions/01b430ff-8b86-4ad1-9f44-8d31161d2108

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean:L30-L43
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.Count.high_mul_pattern. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_rankOne_projection

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

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.high_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (r : ℝ) :
    M.high r * M.pattern F = if r ≤ (F.card : ℝ) then M.pattern F else 0 := by
  classical
  rw [Count.high, Finset.sum_mul, Finset.sum_eq_single F]
  · split_ifs with h
    · exact (M.pattern_projection F).isIdempotentElem.eq
    · exact zero_mul _
  · intro G hG hGF
    split_ifs
    · rw [M.pattern_mul (Finset.mem_powerset.mp hG) hF, ite_eq_right hGF]
    · exact zero_mul _
  · intro h
    exact (h (Finset.mem_powerset.mpr hF)).elim

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (r : ℝ) :
    M.high r * M.pattern F = if r ≤ (F.card : ℝ) then M.pattern F else 0 := by
  first
    | exact OAI.QAC.Count.high_mul_pattern M F hF r
    | exact OAI.QAC.Count.high_mul_pattern
    | (apply OAI.QAC.Count.high_mul_pattern <;> assumption)
    | (intros; apply OAI.QAC.Count.high_mul_pattern <;> assumption)
