-- Prove2me | solution 1 for GlobalTheory.krullAkizuki
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:57.977693+00:00
-- url     : https://prove2.me/submissions/c8c86266-a2e9-4ac6-9c28-825ff81acd53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_krullAkizuki_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
include K
namespace GlobalTheory
theorem _root_.solution (B : Subalgebra A L) : IsNoetherianRing B ∧ Ring.DimensionLEOne B := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have halg : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  let T : Set L := {x | x ∈ B ∧ IsIntegral A x}
  obtain ⟨s, hsT, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := K) T).mp
    (IsNoetherian.noetherian _)
  let C := Algebra.adjoin A (s : Set L)
  have hCB : C ≤ B := Algebra.adjoin_le fun x hx => (hsT hx).1
  have hCf : Module.Finite A C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet fun x hx => (hsT hx).2
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  have hCd : Ring.DimensionLEOne C := Ring.DimensionLEOne.of_isIntegral A C
  letI : Algebra C B := (Subalgebra.inclusion hCB).toAlgebra
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Subalgebra.inclusion_injective hCB)
  refine krullAkizuki_of_birational (A := C) (B := B) fun x => ?_
  obtain ⟨c, hc, hcx⟩ := (halg.1 (x : L)).exists_integral_multiple
  have h1 : c • (x : L) ∈ Submodule.span K (s : Set L) :=
    hs ▸ Submodule.subset_span ⟨B.smul_mem x.2 c, hcx⟩
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) K _ _ h1
  have h2 : (d : A) • c • (x : L) ∈ C := Algebra.span_le_adjoin A _ hd
  refine ⟨algebraMap A C (d * c), ?_, ⟨_, h2⟩, Subtype.ext ?_⟩
  · intro h
    have h3 : algebraMap A L (d * c) = 0 := congrArg Subtype.val h
    exact mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hc (hinj (h3.trans (map_zero _).symm))
  · change algebraMap A L (d * c) * x = (d : A) • c • (x : L)
    rw [← mul_smul, Algebra.smul_def]
end GlobalTheory
