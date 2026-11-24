-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:24.059574+00:00
-- url     : https://prove2.me/submissions/8802f87c-6e65-4c84-88ab-12ce2af16fd0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_sigR_sigR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_sigR_inclR

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
theorem _root_.solution {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) {n M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a b
  simp only [gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_sigR R h, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.CompanionTheory.SW.HermTop
