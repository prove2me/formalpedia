-- Prove2me | solution 1 for GlobalTheory.norm_le_one_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:00.681153+00:00
-- url     : https://prove2.me/submissions/00f1b4e7-aa85-4b7f-9fc5-9d1ae2d49278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
import Theorems.Thm_GlobalTheory_mem_maximalIdeal_integralClosure_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]
variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]
omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
namespace GlobalTheory
theorem _root_.solution {m : Ideal A} {φ : S} {s b : A} (hs : s ∉ m)
    (hb : algebraMap A S s * φ = algebraMap A S b)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0)
    (hy : (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m) :
    ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1 := by
  set v := IsLocalization.Away.lift (S := S) a (isUnit_val_comp_of_ne_zero y hya)
  have e : (y s : K) * v φ = (y b : K) := by
    have := congrArg v hb
    rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
    exact this
  rw [← hy, Ideal.mem_comap, mem_maximalIdeal_integralClosure_iff, not_lt] at hs
  have h1 := (mem_integralClosure_padicInt_iff K _).mp (y b).2
  rw [← e, IntermediateField.coe_mul, norm_mul] at h1
  exact (le_mul_of_one_le_left (norm_nonneg _) hs).trans h1
end GlobalTheory
