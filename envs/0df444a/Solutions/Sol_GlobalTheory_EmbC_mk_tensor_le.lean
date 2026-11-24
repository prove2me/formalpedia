-- Prove2me | solution 1 for GlobalTheory.EmbC.mk_tensor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:06.031854+00:00
-- url     : https://prove2.me/submissions/360d6b3e-91a7-4da7-a703-d7c00b10852f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MkTensorLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbC
open Cardinal TensorProduct
namespace GlobalTheory.EmbC
theorem _root_.solution (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by
  have h1 : Function.Surjective (fun l : List (A × B) => (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      exact ⟨l ++ m, by simp⟩
  refine (Cardinal.mk_le_of_surjective h1).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le Cardinal.aleph0_le_continuum ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc #A * #B ≤ 𝔠 * 𝔠 := mul_le_mul' hA hB
    _ = 𝔠 := Cardinal.continuum_mul_self
end GlobalTheory.EmbC
