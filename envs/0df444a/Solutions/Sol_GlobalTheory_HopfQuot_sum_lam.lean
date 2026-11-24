-- Prove2me | solution 1 for GlobalTheory.HopfQuot.sum_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:23.38889+00:00
-- url     : https://prove2.me/submissions/30b37d0a-b30a-4711-ac4d-4be9629af886

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_tr_comm
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_hit_apply
import Theorems.Thm_GlobalTheory_HopfQuot_lam_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (x : Λ) :
    ∑ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) = Coalgebra.counit (R := R) x := by
  have h1 : ∀ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) =
      ∑ i, c i (HopfAlgebra.antipode R (e k) * hit (c k) (x * e i)) := by
    intro k
    have : hit (c k) ∘ₗ LinearMap.mulLeft R (HopfAlgebra.antipode R (e k) * x) =
        (hit (c k) ∘ₗ LinearMap.mulLeft R x) ∘ₗ
          LinearMap.mulLeft R (HopfAlgebra.antipode R (e k)) := by
      ext y
      simp [mul_left_comm, mul_assoc]
    rw [lam_apply, this, tr_comm e c h]
    simp [tr]
  have h2 : ∀ y : Λ, ∑ k, HopfAlgebra.antipode R (e k) * hit (c k) y =
      algebraMap R Λ (Coalgebra.counit y) := by
    intro y
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp only [hit_apply]
    generalize Coalgebra.comul (R := R) y = w
    induction w with
    | zero => simp
    | add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]
    | tmul u v =>
      conv_rhs => rw [← h v]
      simp [tmul_sum, map_sum, mul_comm]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← map_sum, h2, Bialgebra.counit_mul, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have : ∑ i, Coalgebra.counit (R := R) (e i) * c i 1 = 1 := by
    have := congrArg (Coalgebra.counit (R := R)) (h 1)
    simpa [map_sum, mul_comm] using this
  rw [this, mul_one]
end GlobalTheory.HopfQuot
