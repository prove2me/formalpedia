-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.det_Cm_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:17.541375+00:00
-- url     : https://prove2.me/submissions/1705c725-d956-4736-bf1e-5a4e19a44e65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_vecMul_full_cs
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
theorem _root_.solution (Z : Gl r k) (μ l : k) (h : (Cm Z).det = 0) :
    (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h
  have hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    rw [dotProduct_mulVec]
    simpa [mulVec, Cm, dotProduct] using this
  set A' := full Z
  let u : ℕ → Fin r → k := fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)
  have hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : u 0 = 0 := by
        funext i
        simp only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, zero_dotProduct]
    | succ j ih =>
      intro m
      have hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1 := by
        funext i
        simp only [u, pow_succ, ← vecMul_vecMul]
        rw [vecMul_full_cs]
        simp [mul_comm]
      rw [hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']
      simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · funext j
    simp only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]
    rw [dot_split]
    simpa [u, A'] using hu j 0
end GlobalTheory.JR.DeltaLift
