-- Prove2me | solution 1 for GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:37.681725+00:00
-- url     : https://prove2.me/submissions/d0ae491d-6ca7-4b00-8918-2c293e5876dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_symm
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_nondeg
import Theorems.Thm_GlobalTheory_JR_MeasTransport_kerL_eq
import Theorems.Thm_GlobalTheory_JR_MeasTransport_pi_selfDual
import Theorems.Thm_GlobalTheory_JR_MeasTransport_map_selfDual
import Theorems.Thm_GlobalTheory_JR_SelfDualUniq_selfDual_exists_unique_isTest


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasTransport
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm
end GlobalTheory.JR.MeasTransport
