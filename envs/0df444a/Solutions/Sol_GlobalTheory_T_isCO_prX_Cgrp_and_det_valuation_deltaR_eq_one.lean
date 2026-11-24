-- Prove2me | solution 1 for GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:57.572854+00:00
-- url     : https://prove2.me/submissions/383fd2ae-ff39-4e7c-9108-a6ec513c0b1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrpStatement
import Theorems.Thm_GlobalTheory_PrCompactOpen_isCO_prX_Cgrp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  first | exact @GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | exact GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | (intros; apply GlobalTheory.PrCompactOpen.isCO_prX_Cgrp <;> assumption)
end _root_.GlobalTheory.T
