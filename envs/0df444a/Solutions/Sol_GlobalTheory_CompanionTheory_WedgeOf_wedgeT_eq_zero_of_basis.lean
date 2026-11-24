-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:43.255391+00:00
-- url     : https://prove2.me/submissions/7a225177-b8c5-4218-a430-7e68df80558b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul_self
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul_add_swap
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_sum_sum_eq_zero_of_antisymm
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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (t : V ⊗[R] V) (ht : TensorProduct.comm R V V t = t) : wedgeT (R := R) V t = 0 := by
  set B := b.tensorProduct b with hB
  have hsym : ∀ i j, B.repr t (i, j) = B.repr t (j, i) := by
    have key : ∀ (i j : ι) (s : V ⊗[R] V),
        B.repr (TensorProduct.comm R V V s) (i, j) = B.repr s (j, i) := by
      intro i j s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [hB, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add x y hx hy => simp [map_add, hx, hy]
    intro i j
    rw [← key i j t, ht]
  have hexp : t = ∑ i, ∑ j, B.repr t (i, j) • (b i ⊗ₜ[R] b j) := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_prod_type]
    simp [hB, Module.Basis.tensorProduct_apply]
  rw [hexp]
  simp only [map_sum, map_smul]
  refine sum_sum_eq_zero_of_antisymm
    (fun i j ↦ B.repr t (i, j) • wedgeT (R := R) V (b i ⊗ₜ[R] b j)) ?_ ?_ Finset.univ
  · intro i
    simp [wedgeT_tmul_self]
  · intro i j
    show B.repr t (i, j) • _ + B.repr t (j, i) • _ = 0
    rw [hsym j i, ← smul_add, wedgeT_tmul_add_swap, smul_zero]
end GlobalTheory.CompanionTheory.WedgeOf
