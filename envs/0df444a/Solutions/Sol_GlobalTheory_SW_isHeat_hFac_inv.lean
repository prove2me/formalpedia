-- Prove2me | solution 1 for GlobalTheory.SW.isHeat_hFac_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:05.552943+00:00
-- url     : https://prove2.me/submissions/8f95f0ab-a2f4-4d58-b580-c318537465c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Theorems.Thm_GlobalTheory_SW_HeatTerm_isHeat_of_det
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ), ∀ γ ∈ UU E N, IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) :=
  fun E _ _ _ Ψ _ N γ hγ => GlobalTheory.SW.HeatTerm.isHeat_of_det Ψ γ
    fun Z hZ τ => (((GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
end GlobalTheory.SW
