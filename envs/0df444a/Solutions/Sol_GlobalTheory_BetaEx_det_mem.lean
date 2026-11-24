-- Prove2me | solution 1 for GlobalTheory.BetaEx.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:13.41706+00:00
-- url     : https://prove2.me/submissions/ae0702eb-9957-4a1a-b183-f79684216686

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_mem_detSet

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
theorem _root_.solution {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M) :
    v.det ∈ detSpan M := Submodule.subset_span ((mem_detSet M _).2 ⟨v, hv, rfl⟩)
end GlobalTheory.BetaEx
