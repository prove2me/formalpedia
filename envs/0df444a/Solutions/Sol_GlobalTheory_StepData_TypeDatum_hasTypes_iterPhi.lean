-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.hasTypes_iterPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:53.189957+00:00
-- url     : https://prove2.me/submissions/02eb5641-fca8-4536-8f0b-888b58e2091e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_reGL_val
import Theorems.Thm_GlobalTheory_StepData_det_reGL
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_hasTypes_Phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
namespace TypeDatum
theorem _root_.solution {r : Type*} [Fintype r] [DecidableEq r] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    HasTypes (μ (j + 1)) (P.iter t μ hμ j).toLevel (P.iter t μ hμ (j + 1)).toLevel (P.iterPhi t μ hμ j) := by
  have H := (P.iter t μ hμ j).hasTypes_Phi (t := t) (hμ (j + 1))
  have key : ∀ g h, om (μ (j + 1)) g (reGL (ixSucc r t j) h) (P.iterPhi t μ hμ j) =
      fun x => om (μ (j + 1)) g h ((P.iter t μ hμ j).Phi t (μ (j + 1))) (x.submatrix (ixSucc r t j) id) := by
    intro g h
    funext x
    simp only [om, TypeDatum.iterPhi, det_reGL, ← Fintype.card_congr (ixSucc r t j), ← map_inv (reGL _), reGL_val]
    congr 2
    rw [← submatrix_mul_equiv _ _ _ (Equiv.refl _), ← submatrix_mul_equiv _ _ _ (ixSucc r t j)]
    simp
  refine ⟨fun g => ?_, fun h => ?_⟩
  · have := key g 1
    rw [map_one, H.1 g] at this
    exact this
  · have := key 1 ((reGL (ixSucc r t j)).symm h)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.trans (funext fun x => congrFun (H.2 ⟨_, h.2⟩) _)
end TypeDatum
end GlobalTheory.StepData
