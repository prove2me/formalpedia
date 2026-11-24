-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.denseRange_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:31.420282+00:00
-- url     : https://prove2.me/submissions/6f3e531b-1abb-4947-ae16-4376df457f5f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
import Theorems.Thm_GlobalTheory_AdLat_strong_approximation_mod_nat
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]
end GlobalTheory.CompanionTheory.AdeleCharLocal
