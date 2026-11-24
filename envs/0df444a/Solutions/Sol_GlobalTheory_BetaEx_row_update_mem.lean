-- Prove2me | solution 1 for GlobalTheory.BetaEx.row_update_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:40.375115+00:00
-- url     : https://prove2.me/submissions/57fb9b88-46ce-473b-a2a0-f8267d73cf51

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
theorem _root_.solution {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M)
    (j : Fin n) (m : Fin n → E) (hm : m ∈ M) (i : Fin n) : v.updateRow j m i ∈ M := by
  by_cases h : i = j
  · subst h; rwa [Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne h]; exact hv i
end GlobalTheory.BetaEx
