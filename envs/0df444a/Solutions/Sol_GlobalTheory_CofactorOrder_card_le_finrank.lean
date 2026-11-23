-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.card_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:31.216185+00:00
-- url     : https://prove2.me/submissions/a33d4537-ebaf-46d8-b3a4-97dbeb51ced5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_mulVec_eq_zero_of_det
import Theorems.Thm_GlobalTheory_CofactorOrder_ker_eq_bot_of_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution {M P Q : Matrix n n K} {D : n → K} [DecidablePred fun i => D i = 0]
    (hP : P.det = 1) (hQ : Q.det = 1) (h : P * M * Q = diagonal D) :
    Fintype.card {i // D i = 0} ≤ Module.finrank K (LinearMap.ker M.mulVecLin) := by
  set V := LinearMap.ker M.mulVecLin
  have hmem : ∀ i : {i // D i = 0}, Q *ᵥ Pi.single i.1 (1 : K) ∈ V := by
    intro i
    rw [LinearMap.mem_ker, mulVecLin_apply]
    apply mulVec_eq_zero_of_det hP
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]
    funext k
    rw [mulVec_diagonal]
    by_cases hk : k = i.1
    · subst hk; simp [i.2]
    · simp [hk]
  have hsingle : LinearIndependent K (fun i : {i // D i = 0} => (Pi.single i.1 (1 : K) : n → K)) := by
    have := (Pi.basisFun K n).linearIndependent.comp Subtype.val
      (Subtype.val_injective (p := fun i => D i = 0))
    convert this using 1
    funext i
    simp
  have hli : LinearIndependent K (fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hmapped := hsingle.map' Q.mulVecLin (ker_eq_bot_of_det hQ)
    have e : (⇑V.subtype ∘ fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) =
        ⇑Q.mulVecLin ∘ fun i => (Pi.single i.1 (1 : K) : n → K) := by
      funext i
      simp
    rw [e]
    exact hmapped
  exact hli.fintype_card_le_finrank
end GlobalTheory.CofactorOrder
