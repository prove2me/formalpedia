-- Prove2me | solution 1 for GlobalTheory.JR.Et.distribHaarChar_le_one_of_mem_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:15.168849+00:00
-- url     : https://prove2.me/submissions/24f73036-bddf-46a9-b1ce-7f57b275a823

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling
import Theorems.Thm_GlobalTheory_JR_Et_secondCountable_K
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)
namespace GlobalTheory.JR.Et
theorem _root_.solution (u : A.Kˣ) (hu : (u : A.K) ∈ A.OK) : distribHaarChar A.K u ≤ 1 := by
  haveI := A.secondCountable_K
  obtain ⟨-, -, -, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let μ : Measure A.K := Measure.addHaar
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  have hm0 : μ A.OK ≠ 0 := hO.measure_ne_zero μ ⟨0, h0⟩
  have hmt : μ A.OK ≠ ⊤ := hC.measure_lt_top.ne
  have hsub : u • A.OK ⊆ A.OK := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hR] at hz hu ⊢
    exact R.mul_mem hu hz
  have hle : (distribHaarChar A.K u : ℝ≥0∞) * μ A.OK ≤ 1 * μ A.OK := by
    rw [distribHaarChar_mul μ u A.OK, one_mul]; exact measure_mono hsub
  have := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 hle
  exact_mod_cast this
end GlobalTheory.JR.Et
