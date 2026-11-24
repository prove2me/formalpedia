-- Prove2me | solution 1 for GlobalTheory.LatPair.maps_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:54.062408+00:00
-- url     : https://prove2.me/submissions/acf03fd8-cc33-4b4b-998c-88ead1ae3f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
namespace GlobalTheory.LatPair
theorem _root_.solution (c : 𝓀[k]ˣ) : Maps (c • P) (c • Q) x ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal]
  exact ⟨fun h y a => by simpa using h y (c * a), fun h y a => h y _⟩
end GlobalTheory.LatPair
