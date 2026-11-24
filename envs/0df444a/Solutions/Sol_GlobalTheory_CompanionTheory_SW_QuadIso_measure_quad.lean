-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:34.619083+00:00
-- url     : https://prove2.me/submissions/ea2c3d6a-2647-43f2-be11-3128274947ab

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_IsRadius_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isOpen_ball_of_isRadius
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isOpen_vball
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isTopologicalBasis_vball
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isPiSystem_vball
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_measure_ball
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
variable [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution [SecondCountableTopology K] [IsTopologicalRing K] (lam : Measure K) [lam.IsAddLeftInvariant]
    (hfin : lam {s | Valued.v s < 1} ≠ ⊤) {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) {A : Set K} (hA : MeasurableSet A) :
    lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  have hMo : IsOpen {s : K | Valued.v s < 1} := isOpen_ball_of_isRadius ⟨1, by simp⟩
  have hM : MeasurableSet {s : K | Valued.v s < 1} := hMo.measurableSet
  have hf : Measurable (fun t : K => a * t + c * t ^ 2) := by
    apply Continuous.measurable
    fun_prop
  haveI : IsFiniteMeasure (lam.restrict {s | Valued.v s < 1}) :=
    ⟨by simpa using hfin.lt_top⟩
  haveI : IsFiniteMeasure ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) :=
    Measure.isFiniteMeasure_map _ _
  have hmeas : (lam.restrict {s | Valued.v s < 1}).map (fun t : K => a * t + c * t ^ 2) =
      lam.restrict {s | Valued.v s < 1} := by
    refine ext_of_generate_finite _
      (BorelSpace.measurable_eq.trans isTopologicalBasis_vball.borel_eq_generateFrom)
      isPiSystem_vball ?_ ?_
    · rintro _ ⟨x, γ, rfl, hγ⟩
      have hB := (isOpen_vball x hγ).measurableSet
      rw [Measure.map_apply hf hB, Measure.restrict_apply (hf hB), Measure.restrict_apply hB]
      exact measure_ball lam ha hc x hγ.ne_zero
    · rw [Measure.map_apply hf MeasurableSet.univ]
      simp
  have key : ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) A =
      lam.restrict {s | Valued.v s < 1} A := by rw [hmeas]
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA), Measure.restrict_apply hA] at key
  rw [← key]
  congr 1
  ext t
  simp [and_comm]
end GlobalTheory.CompanionTheory.SW.QuadIso
