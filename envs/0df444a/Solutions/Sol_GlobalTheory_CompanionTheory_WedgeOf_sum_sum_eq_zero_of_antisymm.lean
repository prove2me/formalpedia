-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.sum_sum_eq_zero_of_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:58.625895+00:00
-- url     : https://prove2.me/submissions/3d781939-3f50-49da-bab3-52c958b0adef

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
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
theorem _root_.solution {ι M : Type} [DecidableEq ι] [AddCommGroup M]
    (f : ι → ι → M) (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.sum_add_distrib, ih, hd, zero_add, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ ha a i
end GlobalTheory.CompanionTheory.WedgeOf
