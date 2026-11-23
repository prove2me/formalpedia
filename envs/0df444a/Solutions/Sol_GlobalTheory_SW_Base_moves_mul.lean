-- Prove2me | solution 1 for GlobalTheory.SW.Base.moves_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:45.285906+00:00
-- url     : https://prove2.me/submissions/76ec990d-007d-4fa6-a177-ea37f40b1723

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
theorem _root_.solution {h g : Matrix (Fin n) (Fin n) E} {Λ Λ' Λ'' : Lt E n} (h1 : Moves g Λ Λ')
    (h2 : Moves h Λ' Λ'') : Moves (h * g) Λ Λ'' := fun v => by
  rw [h1, h2, Matrix.mulVec_mulVec]
end GlobalTheory.SW.Base
