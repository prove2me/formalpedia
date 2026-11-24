-- Prove2me | solution 1 for GlobalTheory.SteinitzProd.exists_prod_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:23.003606+00:00
-- url     : https://prove2.me/submissions/cd6945c0-9db8-4cd7-89ac-846cf4c2cd3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
import Theorems.Thm_GlobalTheory_SteinitzProd_classGroup_exists_integral_ideal_coprime
import Theorems.Thm_GlobalTheory_ProjModFinIso_nonempty_equiv_of_mk0_eq


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
theorem _root_.solution (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by
  have hJ0 : (J : Ideal R) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  obtain ⟨I', hcop, hcl⟩ := classGroup_exists_integral_ideal_coprime hJ0 (ClassGroup.mk0 I)
  have h1 : (1 : R) ∈ (I' : Ideal R) ⊔ J := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  refine ⟨I' * J, by rw [map_mul, hcl], ⟨?_⟩⟩
  have e1 := (GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq hcl.symm).some
  exact (e1.prodCongr (LinearEquiv.refl R _)) ≪≫ₗ coprimeEquiv _ _ u v hu hv huv ≪≫ₗ
    (Submodule.topEquiv.prodCongr (LinearEquiv.ofEq _ _ (Submonoid.coe_mul _ _ _).symm))
end GlobalTheory.SteinitzProd
