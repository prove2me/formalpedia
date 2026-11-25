-- Prove2me | solution 1 for GlobalTheory.UnramPushout.isReduced_nontrivial_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:29.579672+00:00
-- url     : https://prove2.me/submissions/d62f8d05-c0a1-40bf-b9ab-41c4f856f451

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.UnramPushout
open TensorProduct
namespace GlobalTheory.UnramPushout
theorem _root_.solution {A k k' : Type} [CommRing A] [Field k] [Field k']
    [Algebra A k] [Algebra A k'] [CharZero k] (P : Ideal A) [P.IsPrime]
    (hk : RingHom.ker (algebraMap A k) = P) (hk' : RingHom.ker (algebraMap A k') = P) :
    IsReduced (k ⊗[A] k') ∧ Nontrivial (k ⊗[A] k') := by
  have hu : ∀ {L : Type} [Field L] [Algebra A L], RingHom.ker (algebraMap A L) = P →
      P.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap A L) := by
    intro L _ _ h s hs
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hs (h ▸ (RingHom.mem_ker.mpr h0))
  let ι := Ideal.ResidueField.lift P (algebraMap A k) hk.ge (hu hk)
  let ι' := Ideal.ResidueField.lift P (algebraMap A k') hk'.ge (hu hk')
  letI : Algebra P.ResidueField k := ι.toAlgebra
  letI : Algebra P.ResidueField k' := ι'.toAlgebra
  haveI : IsScalarTower A P.ResidueField k :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : IsScalarTower A P.ResidueField k' :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : CharZero P.ResidueField := ⟨fun m n h => Nat.cast_injective (R := k) (by rw [← map_natCast ι, ← map_natCast ι, h])⟩
  haveI : CompatibleSMul A P.ResidueField k k' := by
    refine ⟨fun x m n => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ P) x
    have hβ := map_ne_zero_of_mem_nonZeroDivisors _ P.injective_algebraMap_quotient_residueField hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [Ideal.algebraMap_quotient_residueField_mk] at hβ ⊢
    set β := algebraMap A P.ResidueField b
    set α := algebraMap A P.ResidueField a
    have e1 : n = b • (β⁻¹ • n) := by
      rw [← algebraMap_smul P.ResidueField b, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have e2 : b • ((α / β) • m) = a • m := by
      rw [← algebraMap_smul P.ResidueField b, ← algebraMap_smul P.ResidueField a, smul_smul,
        mul_div_cancel₀ _ hβ]
    have e3 : a • (β⁻¹ • n) = (α / β) • n := by
      rw [← algebraMap_smul P.ResidueField a, smul_smul, div_eq_mul_inv]
    conv_lhs => rw [e1]
    rw [← smul_tmul b ((α / β) • m) (β⁻¹ • n), e2, smul_tmul a m (β⁻¹ • n), e3]
  let e := Algebra.TensorProduct.equivOfCompatibleSMul P.ResidueField A A k k'
  have : IsReduced (k ⊗[P.ResidueField] k') := GlobalTheory.ReducedAlg.isReduced_tensor k k'
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toEquiv.nontrivial⟩
end GlobalTheory.UnramPushout
