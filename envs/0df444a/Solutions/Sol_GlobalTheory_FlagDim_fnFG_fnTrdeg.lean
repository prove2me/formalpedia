-- Prove2me | solution 1 for GlobalTheory.FlagDim.fnFG_fnTrdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:41.09847+00:00
-- url     : https://prove2.me/submissions/ea7e1f3d-7f65-49d1-98ce-e1fed1f2630e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_KapFgTrdeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_DimAddCardFlagVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_FnFGFnTrdeg
import Theorems.Thm_Formalism_L2_Pj_fnFG_of
import Theorems.Thm_Formalism_L2_Pj_fnTrdeg_of
import Theorems.Thm_GlobalTheory_FlagDim_dim_add_card_flagVar
import Theorems.Thm_GlobalTheory_Reg_kap_fg_trdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.FlagDim
namespace GlobalTheory.FlagDim
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FnFG Xo c ∧ FnTrdeg Xo c (Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨h1, h2⟩ := GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c
  refine ⟨fnFG_of Xo c h1, ?_⟩
  rw [← dim_add_card_flagVar E H Dw]
  exact fnTrdeg_of Xo c Dw.dim h2
end GlobalTheory.FlagDim
