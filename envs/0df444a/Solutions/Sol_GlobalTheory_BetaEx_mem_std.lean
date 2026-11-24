-- Prove2me | solution 1 for GlobalTheory.BetaEx.mem_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:52.032666+00:00
-- url     : https://prove2.me/submissions/68aaa03f-74cf-4aa7-ad06-23c7e40fef37

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
theorem _root_.solution (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
end GlobalTheory.BetaEx
