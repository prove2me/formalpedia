-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.hermMat_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:06.971799+00:00
-- url     : https://prove2.me/submissions/1162aaea-5782-42e7-841d-33e207ec3473

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_sigR_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_sigR_sigR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (n : ℕ)
    (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    hermMat R σ n x ∈ HermR R σ n := by
  intro a b
  rcases lt_trichotomy a b with h | h | h
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]
    exact sigR_sigR R hinv _
  · subst h
    simp only [hermMat, lt_irrefl, dite_false]
    rw [sigR_tmul, map_one]
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]
end GlobalTheory.CompanionTheory.SW.HaarCoord
