-- Prove2me | solution 1 for GlobalTheory.SmGL.isSubquotient_jac_detRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:15.127085+00:00
-- url     : https://prove2.me/submissions/45c62d0d-0e91-4fb4-b991-60192e5f69a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_twKer_detRep
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_surjective


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) :
    IsSubquotient (ofChar (detLevi e χ)) (jac e (detRep n χ)) := by
  refine .of_surjective ⟨(twKer (detRep n χ) (unipRad k e) 1).liftQ LinearMap.id
    (by rw [twKer_detRep]; exact bot_le), fun g => ?_⟩ fun x => ⟨Submodule.Quotient.mk x, rfl⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • detRep n χ (leviEmb k e g) v = ofChar (detLevi e χ) g v
  simp [detRep, detLevi, mul_comm, mul_left_comm]
end GlobalTheory.SmGL
