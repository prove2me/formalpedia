-- Prove2me | solution 1 for GlobalTheory.hermC_emb_eq_map_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:31.628363+00:00
-- url     : https://prove2.me/submissions/cfc1dcd1-8138-4507-809c-9473797e38b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_SumCMulImHermCEqSignMulTrace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) = τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) :=
  (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_herm τ G u v).symm
end _root_.GlobalTheory
end GlobalTheory
