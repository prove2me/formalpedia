-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsExponents.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:15.495872+00:00
-- url     : https://prove2.me/submissions/0322dedc-cd29-4238-bfe9-ce76948930a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
variable {k n}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
namespace IsExponents
theorem _root_.solution {π : Representation ℂ (GL n k) V} {E E' : Multiset ((n → kˣ) →* ℂˣ)}
    (h : IsExponents π E) (h' : IsExponents π E') : E = E' := by
  classical
  ext χ
  have := (h.2 χ).trans (h'.2 χ).symm
  have h2 := Nat.cast_injective this
  convert h2
end IsExponents
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
