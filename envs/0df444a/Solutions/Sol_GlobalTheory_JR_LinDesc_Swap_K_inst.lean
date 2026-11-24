-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.K_inst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:39.864482+00:00
-- url     : https://prove2.me/submissions/9eebdd64-5f9d-41db-af56-dab8ccebe141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] (A : Et F E)
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) [SecondCountableTopology F] :
    T2Space A.K ∧ SecondCountableTopology A.K := by
  have hc : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have hc' : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  let e : A.K ≃ₜ (Fin r → F) :=
    { toEquiv := (bas A hG).equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨e.isEmbedding.t2Space, e.isEmbedding.secondCountableTopology⟩
end GlobalTheory.JR.LinDesc.Swap
