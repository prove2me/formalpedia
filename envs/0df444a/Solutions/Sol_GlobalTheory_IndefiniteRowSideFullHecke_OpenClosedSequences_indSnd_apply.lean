-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:03.668878+00:00
-- url     : https://prove2.me/submissions/26dbe92b-cf63-4dac-a5d0-0a87ed47adfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n Γ W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Group Γ] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
theorem _root_.solution (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ)
    (h x : GL n k) (f) : (indSnd e τ (γ, h) f).1.1 x = τ (γ, 1) (f.1.1 (x * h)) := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
