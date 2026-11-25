-- Prove2me | solution 1 for GlobalTheory.JR.Et.absK_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:47.452116+00:00
-- url     : https://prove2.me/submissions/770b0855-7a84-4292-aaef-cbeb34319af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling
import Theorems.Thm_GlobalTheory_JR_Et_secondCountable_K
import Theorems.Thm_GlobalTheory_JR_Et_absK_unit
import Theorems.Thm_GlobalTheory_JR_Et_absK_mul
import Theorems.Thm_GlobalTheory_JR_Et_distribHaarChar_le_one_of_mem_OK
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  intro F E _ _ _ _ _ A
  refine ⟨A.absK_mul, ?_, ?_⟩
  · intro s s' hs hs' h
    let u : A.Kˣ := ⟨s, s', h, by rw [mul_comm]; exact h⟩
    have h1 := A.distribHaarChar_le_one_of_mem_OK u hs
    have h2 := A.distribHaarChar_le_one_of_mem_OK u⁻¹ hs'
    have hprod : distribHaarChar A.K u * distribHaarChar A.K u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have : distribHaarChar A.K u = 1 := by
      refine le_antisymm h1 ?_
      calc (1 : ℝ≥0) = distribHaarChar A.K u * distribHaarChar A.K u⁻¹ := hprod.symm
        _ ≤ distribHaarChar A.K u * 1 := mul_le_mul_of_nonneg_left h2 zero_le'
        _ = distribHaarChar A.K u := mul_one _
    have e := A.absK_unit u
    change A.absK s = 1
    rw [show s = (u : A.K) from rfl, e, this, NNReal.coe_one]
  · intro μ hμ x a S _
    haveI := A.secondCountable_K
    have hset : {a' : A.K | (x : A.K) * a' - a ∈ S} = x⁻¹ • ((fun z => z + -a) ⁻¹' S) := by
      ext a'
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      simp [Units.smul_def, sub_eq_add_neg]
    rw [hset, ← distribHaarChar_mul μ x⁻¹, measure_preimage_add_right, A.absK_unit, map_inv,
      ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
end GlobalTheory.JR.Et
