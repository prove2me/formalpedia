-- Prove2me | solution 1 for GlobalTheory.BetaEx.mem_detSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:18.418869+00:00
-- url     : https://prove2.me/submissions/6bf93639-ff0b-4c9c-8a77-67924aed2d2f

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
theorem _root_.solution (M : Submodule (𝓞 E) (Fin n → E)) (d : E) :
    d ∈ detSet M ↔ ∃ v : Matrix (Fin n) (Fin n) E, (∀ i, v i ∈ M) ∧ d = v.det := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, Matrix.det_transpose (Matrix.of v)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (Matrix.det_transpose v).symm⟩
end GlobalTheory.BetaEx
