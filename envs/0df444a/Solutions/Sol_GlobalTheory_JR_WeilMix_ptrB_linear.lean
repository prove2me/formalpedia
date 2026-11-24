-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.ptrB_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:01.94784+00:00
-- url     : https://prove2.me/submissions/883d9ba9-1842-472b-8e2b-7fedb146a3fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinear
import Theorems.Thm_GlobalTheory_JR_WeilMix_integrable_mixedModel_partialFourier_integrand
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.WeilMix
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]
end GlobalTheory.JR.WeilMix
