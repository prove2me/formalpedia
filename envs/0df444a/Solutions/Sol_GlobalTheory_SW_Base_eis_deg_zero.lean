-- Prove2me | solution 1 for GlobalTheory.SW.Base.eis_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:07.265877+00:00
-- url     : https://prove2.me/submissions/e81421b3-fa10-4f7e-8bad-06743bc049fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_UU
import Theorems.Thm_GlobalTheory_SW_Base_weil_deg_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution (φ : Matrix (Fin n) (Fin 0) E → ℂ) (Z : CM Ψ 0 0) (z z' : CM Ψ n 0) :
    eis Ψ φ Z z z' = φ 0 := by
  let U : Lag E 0 := ⟨_, 1, one_mem_UU, rfl⟩
  unfold eis
  rw [tsum_eq_single U fun V hV => (hV (Subtype.ext (Subsingleton.elim _ _))).elim]
  simp [eisTerm, weil_deg_zero, hFac, dotProduct]
end GlobalTheory.SW.Base
