-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:35.097774+00:00
-- url     : https://prove2.me/submissions/9ff5f60d-a051-43f6-9a12-58ffdccb68b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


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
theorem _root_.solution (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (h : GL n k) :
    indSnd e τ (1, h) = ind₂ e (τ.comp (MonoidHom.inr Γ _)) h :=
  LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * h)) = f.1.1 (x * h)
    simp))
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
