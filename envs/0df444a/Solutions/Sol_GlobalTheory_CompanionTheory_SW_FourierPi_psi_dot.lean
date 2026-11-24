-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.psi_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:41.177995+00:00
-- url     : https://prove2.me/submissions/e8a9556a-6062-44bf-b9de-73fd6b228950

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_psi_sum

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] {ψ : R → ℂ}
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Fintype ι]
    (x y : ι → R) : ψ (x ⬝ᵥ y) = ∏ i, ψ (x i * y i) :=
  psi_sum ha hn _ _
end GlobalTheory.CompanionTheory.SW.FourierPi
