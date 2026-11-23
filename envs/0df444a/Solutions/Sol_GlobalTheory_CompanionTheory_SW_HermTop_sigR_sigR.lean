-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.sigR_sigR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:21.480495+00:00
-- url     : https://prove2.me/submissions/c63dfd17-cb53-4245-bb3d-88aee2fe02ce

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HermTop
theorem _root_.solution {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
end GlobalTheory.CompanionTheory.SW.HermTop
