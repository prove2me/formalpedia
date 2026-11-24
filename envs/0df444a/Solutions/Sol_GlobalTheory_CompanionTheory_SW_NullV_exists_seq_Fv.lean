-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.exists_seq_Fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:15.060408+00:00
-- url     : https://prove2.me/submissions/31cb8f13-aebd-4275-b554-375094b7873b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
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
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.CompanionTheory.SW.NullV
theorem _root_.solution : ∃ t : ℕ → Fv F v, Function.Injective t ∧
    Filter.Tendsto t Filter.atTop (𝓝 0) := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one (v.adicCompletion F)
  refine ⟨fun i => x ^ i, ?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1⟩
  intro i j hij
  have : ‖x‖ ^ i = ‖x‖ ^ j := by
    have := congrArg norm hij
    simpa only [norm_pow] using this
  exact (pow_right_strictAnti₀ hx0 hx1).injective this
end GlobalTheory.CompanionTheory.SW.NullV
