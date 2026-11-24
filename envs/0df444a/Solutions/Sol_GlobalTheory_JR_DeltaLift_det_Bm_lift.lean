-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.det_Bm_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:32:28.080685+00:00
-- url     : https://prove2.me/submissions/c13bcfdb-be30-45a8-89cc-0272f19a7f27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_full_mulVec_cs
import Theorems.Thm_GlobalTheory_JR_DeltaLift_dot_split
import Theorems.Thm_GlobalTheory_JR_DeltaLift_dot_pow_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.DeltaLift
theorem _root_.solution (Z : Gl r k) (μ l : k) (h : (Bm Z).det = 0) :
    (Bm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h
  have hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hw ⟨i, hi⟩
    simpa [vecMul, Bm, dotProduct] using this
  set A' := full Z
  let x : ℕ → Fin r → k := fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)
  have hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : x 0 = 0 := by
        funext i; simp [x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, mulVec_zero, dotProduct_zero]
    | succ j ih =>
      intro m
      have hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1 := by
        funext i
        simp only [x, pow_succ', ← mulVec_mulVec]
        rw [full_mulVec_cs]
        simp [mul_comm]
      rw [hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']
      simp
  refine (Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · have e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l)
        = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ)) := by
      funext j
      show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _
      rw [mulVec_smul, dotProduct_smul, dot_split]
      simp [x, smul_eq_mul]
    rw [e]
    funext j
    simpa using congrArg (μ * ·) (hx j 0)
end GlobalTheory.JR.DeltaLift
