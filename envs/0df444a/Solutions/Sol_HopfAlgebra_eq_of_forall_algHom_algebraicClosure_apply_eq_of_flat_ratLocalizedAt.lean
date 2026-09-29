-- Prove2me | solution 1 for HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7d235beb-e69a-5196-9a65-acf43eded4d5

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt

set_option autoImplicit false

open scoped TensorProduct nonZeroDivisors

namespace HopfAlgebra
p2m_export "HopfAlgebra" "isReduced_of_finiteType_of_charZero"
namespace SepPoints
p2m_open "HopfAlgebra"

private theorem faithfulSMul_rat (p : ℕ) : FaithfulSMul (GaloisRep.ratLocalizedAt p) ℚ :=
  (faithfulSMul_iff_algebraMap_injective _ ℚ).mpr Subtype.val_injective

private theorem isFractionRing_rat (p : ℕ) : IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ := by
  haveI := faithfulSMul_rat p
  refine IsFractionRing.of_field (R := GaloisRep.ratLocalizedAt p) (K := ℚ) fun z => ?_
  refine ⟨⟨(z.num : ℚ), ?_⟩, ⟨(z.den : ℚ), ?_⟩, ?_⟩
  · show ((z.num : ℚ)).den.Coprime p
    simp
  · show ((z.den : ℚ)).den.Coprime p
    simp
  · change z = (z.num : ℚ) / (z.den : ℚ)
    exact (Rat.num_div_den z).symm

private theorem noZeroSMulDivisors_of_flat (p : ℕ) (H : Type) [CommRing H]
    [Algebra (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H] :
    NoZeroSMulDivisors (GaloisRep.ratLocalizedAt p) H := by
  refine ⟨fun {c x} h => or_iff_not_imp_left.2 fun hc => ?_⟩
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H)
    (mem_nonZeroDivisors_of_ne_zero hc)
  exact hreg (h.trans (smul_zero c).symm)

end HopfAlgebra.SepPoints

open HopfAlgebra.SepPoints in
theorem solution
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H)
    (hab : ∀ f : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, f a = f b) :
    a = b := by
  haveI := HopfAlgebra.SepPoints.isFractionRing_rat p
  haveI := HopfAlgebra.SepPoints.noZeroSMulDivisors_of_flat p H
  haveI : Algebra.FiniteType ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt p] H) := inferInstance
  haveI : IsReduced (ℚ ⊗[GaloisRep.ratLocalizedAt p] H) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt p] H)
  have h := Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    (R := GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) (a - b)
    (fun f => by rw [map_sub, hab f, sub_self])
  exact sub_eq_zero.mp h

end S_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
end P2MW
export P2MW.S_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt (solution)
