-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitProdAlg.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:01.6092+00:00
-- url     : https://prove2.me/submissions/0eaa6ab0-3688-4c61-aae5-db43afb1cae8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_mulSupport_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg
theorem _root_.solution {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) (k : IsUnitProd b e) : IsUnitProd (a * b) (fun v => c v * e v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, k.1] with v h1 h2
    simp [h1, h2]
  · rw [finprod_mul_distrib (mulSupport_finite h) (mulSupport_finite k), mul_mul_mul_comm,
      h.2, k.2, one_mul]
end GlobalTheory.CompanionTheory.SW.UnitProdAlg
