-- Prove2me | solution 1 for GlobalTheory.SmGL.jacLower_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:06.785826+00:00
-- url     : https://prove2.me/submissions/f0856479-0bcf-45f3-b3e7-1ceca198cfda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_opp
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
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
namespace GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) :
    jacLower e π g = jac (opp e) π g := by
  have h : deltaHalf k m g = (deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) g)⁻¹ :=
    ((inv_inv _).symm.trans (congrArg _ (deltaHalf_opp g).symm))
  exact congrArg (fun c : ℂˣ => (c : ℂ) • jacU (opp e) π g) h
end GlobalTheory.SmGL
