-- Prove2me | solution 1 for GlobalTheory.BetaEx.exists_smul_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:29.343609+00:00
-- url     : https://prove2.me/submissions/8ea75462-8ffb-450b-87ff-0feeaed07c42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_mem_std

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
namespace GlobalTheory.BetaEx
theorem _root_.solution (v : Fin n → E) : ∃ a : 𝓞 E, a ≠ 0 ∧ a • v ∈ stdLat E n := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v
  exact ⟨d, nonZeroDivisors.ne_zero d.2, (mem_std _).2 fun j => hd j⟩
end GlobalTheory.BetaEx
