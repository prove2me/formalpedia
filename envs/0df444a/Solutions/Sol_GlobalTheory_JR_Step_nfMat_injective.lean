-- Prove2me | solution 1 for GlobalTheory.JR.Step.nfMat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:32.044057+00:00
-- url     : https://prove2.me/submissions/e366708e-29da-4a38-8dd0-86c2a309e7fa

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
import Theorems.Thm_GlobalTheory_JR_Step_nfMat_mulVec_castSucc
import Theorems.Thm_GlobalTheory_JR_Step_nfMat_mulVec_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
namespace GlobalTheory.JR.Step
theorem _root_.solution {r : ℕ} {k : Type} [Field k] (c : Fin (r + 1) → k) (h0 : c 0 ≠ 0) :
    Function.Injective (nfMat c).mulVec := by
  intro x y hxy
  set v := x - y with hv
  have key : nfMat c *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hxy, sub_self]
  have hs : ∀ i : Fin r, v i.succ = 0 := fun i => by
    rw [← nfMat_mulVec_castSucc c v i, key]; rfl
  have hl : c ⬝ᵥ v = 0 := by rw [← nfMat_mulVec_last c v, key]; rfl
  have h0v : v 0 = 0 := by
    rw [dotProduct, Fin.sum_univ_succ] at hl
    simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left h0
  have : v = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => exact h0v
    | succ i => exact hs i
  exact sub_eq_zero.mp this
end GlobalTheory.JR.Step
