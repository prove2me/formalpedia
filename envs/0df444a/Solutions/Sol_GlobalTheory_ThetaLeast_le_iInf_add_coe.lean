-- Prove2me | solution 1 for GlobalTheory.ThetaLeast.le_iInf_add_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:36.482149+00:00
-- url     : https://prove2.me/submissions/3c46eab4-8213-4498-8ef5-d258a9e1df05

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
namespace GlobalTheory.ThetaLeast
theorem _root_.solution {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)
end GlobalTheory.ThetaLeast
