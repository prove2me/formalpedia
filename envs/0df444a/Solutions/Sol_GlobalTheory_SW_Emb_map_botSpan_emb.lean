-- Prove2me | solution 1 for GlobalTheory.SW.Emb.map_botSpan_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:47.261669+00:00
-- url     : https://prove2.me/submissions/8e9d8b06-9675-4784-92e4-565dc0a798b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_botSpan_emb

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution (γ : M2 E N) :
    (botSpan (emb γ)).map (LinearMap.funLeft E E (up N)) = botSpan γ := by
  rw [botSpan_emb, Submodule.map_sup, Submodule.map_span, Set.image_singleton, ← Submodule.map_comp]
  have e1 : LinearMap.funLeft E E (up N) (Pi.single (Sum.inr 0) 1) = 0 := by
    funext j
    rcases j with j | j <;> simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.succ_ne_zero]
  have e2 : (LinearMap.funLeft E E (up N)).comp (extV E N) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext j
    rcases j with j | j <;> simp [extV, LinearMap.funLeft_apply]
  rw [e1, e2, Submodule.map_id, Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
end GlobalTheory.SW.Emb
