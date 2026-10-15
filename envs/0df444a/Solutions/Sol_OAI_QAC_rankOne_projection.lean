-- Prove2me | solution 1 for OAI.QAC.rankOne_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:56:48.86502+00:00
-- url     : https://prove2.me/submissions/662b19c4-41bc-4eea-83e8-4fd223202810

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean:L79-L91
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.rankOne_projection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_projection {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    IsStarProjection (rankOne v) := by
  rw [isStarProjection_iff']
  refine ⟨?_, rankOne_star v⟩
  ext x y
  simp only [Matrix.mul_apply, rankOne]
  calc
    _ = v x * (∑ z, star (v z) * v z) * star (v y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      congr 1
      funext z
      ring
    _ = _ := by rw [normalized_complex hv]; ring

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

theorem solution {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    IsStarProjection (rankOne v) := by
  first
    | exact OAI.QAC.rankOne_projection hv
    | exact OAI.QAC.rankOne_projection
    | (apply OAI.QAC.rankOne_projection <;> assumption)
    | (intros; apply OAI.QAC.rankOne_projection <;> assumption)
