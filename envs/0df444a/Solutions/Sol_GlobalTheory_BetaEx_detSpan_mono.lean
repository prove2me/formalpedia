-- Prove2me | solution 1 for GlobalTheory.BetaEx.detSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:28.68112+00:00
-- url     : https://prove2.me/submissions/30dbd833-7bbe-475c-a585-9b3ffc7fd8fa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]
namespace GlobalTheory.BetaEx
theorem _root_.solution {M' M : Submodule (𝓞 E) (Fin n → E)} (h : M' ≤ M) : detSpan M' ≤ detSpan M := by
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, fun i => h (hv i), rfl⟩
end GlobalTheory.BetaEx
