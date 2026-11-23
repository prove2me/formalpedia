-- Prove2me | solution 1 for GlobalTheory.SW.Base.thH_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:11.57272+00:00
-- url     : https://prove2.me/submissions/81aebbf7-3636-4a0e-8d56-4915aa4a9262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible

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
omit [IsCMField E]
namespace GlobalTheory.SW.Base
theorem _root_.solution (φ : Matrix (Fin n) (Fin 0) E → ℂ) (Z : CM Ψ 0 0) (z z' : CM Ψ n 0) :
    thH Ψ φ Z z z' = φ 0 := by
  unfold thH
  rw [tsum_eq_single 0 fun x hx => (hx (Subsingleton.elim _ _)).elim]
  simp [expo, dotProduct]
end GlobalTheory.SW.Base
