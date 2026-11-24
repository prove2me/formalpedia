-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:17:18.281231+00:00
-- url     : https://prove2.me/submissions/c4c9ebee-d36e-408d-9804-f28d49a8ecd2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_eq_zero_of_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_map_wedgeT
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V)
    (ht : t - TensorProduct.comm R V V t = 0) : wedgeT (R := R) V t = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R V
  obtain ⟨i, hi⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hri : ∀ v, r (i v) = v := fun v ↦ LinearMap.congr_fun hi v
  have hcomm : TensorProduct.comm R V V t = t := (sub_eq_zero.1 ht).symm
  have hmap : ∀ s : V ⊗[R] V, TensorProduct.comm R (Fin n → R) (Fin n → R) (TensorProduct.map i i s)
      = TensorProduct.map i i (TensorProduct.comm R V V s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hback : ∀ s : V ⊗[R] V, TensorProduct.map r r (TensorProduct.map i i s) = s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hri]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hW : wedgeT (R := R) (Fin n → R) (TensorProduct.map i i t) = 0 :=
    wedgeT_eq_zero_of_basis (Pi.basisFun R (Fin n)) _ (by rw [hmap, hcomm])
  have := map_wedgeT r (TensorProduct.map i i t)
  rw [hW, map_zero, hback] at this
  exact this.symm
end GlobalTheory.CompanionTheory.WedgeOf
