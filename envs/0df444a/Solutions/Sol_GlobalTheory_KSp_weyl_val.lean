-- Prove2me | solution 1 for GlobalTheory.KSp.weyl_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:59.196169+00:00
-- url     : https://prove2.me/submissions/1e11b585-e8da-452b-8350-5c8742b8a8f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped Topology Classical
open GlobalTheory GlobalTheory.KSp
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.KSp
theorem _root_.solution : ((weyl c ν : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = stdJ ν E := rfl
end GlobalTheory.KSp
