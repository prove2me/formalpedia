-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.gram_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:08:15.678138+00:00
-- url     : https://prove2.me/submissions/aad3e738-6609-44b0-806b-6811caf1fd8b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_succ_succ

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
variable (ι : R →+* K) (τ : K →+* K)
variable {ι τ}
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution (hτι : ∀ r, τ (ι r) = ι r) {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) :
    gram ι τ d u = blk τ (ι (d 0)) (fun j => ι (d 0) * headU u j)
      (fun a b => gram ι τ (Fin.tail d) (tailU u) a b + τ (headU u a) * ι (d 0) * headU u b) := by
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simpa [blk] using gram_zero_zero ι τ d u
    | succ j => simpa [blk] using gram_zero_succ ι τ d u j
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simpa [blk, hτι, mul_comm] using gram_succ_zero ι τ d u i
    | succ j => simpa [blk] using gram_succ_succ ι τ d u i j
end GlobalTheory.CompanionTheory.SW.LDL
