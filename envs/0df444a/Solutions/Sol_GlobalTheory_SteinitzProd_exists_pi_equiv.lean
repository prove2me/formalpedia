-- Prove2me | solution 1 for GlobalTheory.SteinitzProd.exists_pi_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:07.803049+00:00
-- url     : https://prove2.me/submissions/6b269e60-0f4a-4577-a1fd-1501f9a7c3e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
import Theorems.Thm_GlobalTheory_SteinitzProd_exists_prod_pi_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.SteinitzProd
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by
  let I' : Fin (n + 1) → (Ideal R)⁰ := fun j => I (e.symm j)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_prod_pi_equiv n (fun j => I' j.succ) (I' 0)
  refine ⟨L, ?_, ⟨?_⟩⟩
  · rw [hL, ← Fin.prod_univ_succ (f := fun j => ClassGroup.mk0 (I' j))]
    exact Equiv.prod_comp e.symm (fun i => ClassGroup.mk0 (I i))
  · exact LinearEquiv.piCongrLeft' R (fun i => ↥(I i : Ideal R)) e ≪≫ₗ
      (Fin.consLinearEquiv R (fun j => ↥(I' j : Ideal R))).symm ≪≫ₗ f
end GlobalTheory.SteinitzProd
