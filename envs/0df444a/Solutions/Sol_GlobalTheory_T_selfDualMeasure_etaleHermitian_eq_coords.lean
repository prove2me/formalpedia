-- Prove2me | solution 1 for GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:21.024806+00:00
-- url     : https://prove2.me/submissions/4104b43d-18de-40a1-8cdc-d2e5d0ad0a15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureEtaleHermitianEqCoordsStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_measure_eq_coords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  first | exact @GlobalTheory.JR.Hyp.measure_eq_coords | exact GlobalTheory.JR.Hyp.measure_eq_coords | (intros; apply GlobalTheory.JR.Hyp.measure_eq_coords <;> assumption)
end _root_.GlobalTheory.T
