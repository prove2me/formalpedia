-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.isCompact_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:24.542399+00:00
-- url     : https://prove2.me/submissions/51873598-bbcd-4828-85d8-a78d7b57a59e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {X : Type} [TopologicalSpace X]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution (φ : SB X) : IsCompact (Function.support φ.1) := by
  have h : IsClosed (Function.support φ.1) := by
    have := (φ.2.1 {0}).isClosed_compl
    convert this using 1
    ext x
    simp
  have h2 := φ.2.2.isCompact
  rwa [tsupport, h.closure_eq] at h2
end GlobalTheory.BaireDistribution
