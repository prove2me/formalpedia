-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB_eq_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:17.122249+00:00
-- url     : https://prove2.me/submissions/5dd7a91b-6613-4605-9323-42a50c9a6036

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Theorems.Thm_GlobalTheory_SmGL_modulus_torus


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
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
theorem _root_.solution (t : n → kˣ) :
    deltaB t = modulus k (fun _ : n => Unit) (leviTorus k n t) := (modulus_torus t).symm
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
