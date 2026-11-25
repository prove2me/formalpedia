-- Prove2me | solution 1 for GlobalTheory.KSp.unip_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:44.500558+00:00
-- url     : https://prove2.me/submissions/3f217da4-6192-4781-9f5c-63f2debc571e

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
theorem _root_.solution (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ((unip c b hb : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromBlocks 1 b 0 1 := rfl
end GlobalTheory.KSp
