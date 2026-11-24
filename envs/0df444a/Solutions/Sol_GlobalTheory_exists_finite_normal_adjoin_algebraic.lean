-- Prove2me | solution 1 for GlobalTheory.exists_finite_normal_adjoin_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:39.748996+00:00
-- url     : https://prove2.me/submissions/ea7a537a-6e8b-42b6-a4a5-68de5dd6637f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteNormalAdjoinAlgebraic
import Theorems.Thm_GlobalTheory_exists_extend_of_ringEquiv_of_isAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
      (s : AlgebraicClosure (FractionRing R)),
      ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂)
        (h' : FractionRing R →+* FractionRing R₂)
        (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)),
        Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧
        (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧
        (∃ s₂, e s₂ = s) ∧
        ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F),
          ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  intro R _ _ _ _ _ s
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
    IntermediateField.adjoin (FractionRing R) {s}
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  let φ : FractionRing (integralClosure R L) ≃+* L :=
    (FractionRing.algEquiv (integralClosure R L) L).toRingEquiv
  have hφ : ∀ x : integralClosure R L,
      φ (algebraMap (integralClosure R L) _ x) = algebraMap (integralClosure R L) L x :=
    fun x => (FractionRing.algEquiv (integralClosure R L) L).commutes x
  refine ⟨integralClosure R L, inferInstance, inferInstance, algebraMap R _,
    φ.symm.toRingHom.comp (algebraMap (FractionRing R) L),
    (algebraMap L (AlgebraicClosure (FractionRing R))).comp φ.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : algebraMap R L a = algebraMap R L b := by
      rw [IsScalarTower.algebraMap_apply R (integralClosure R L) L,
        IsScalarTower.algebraMap_apply R (integralClosure R L) L b, hab]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L b] at h1
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) L).injective h1)
  · exact RingHom.finite_algebraMap.2 hfin
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance
  · intro r
    apply φ.injective
    rw [hφ, ← IsScalarTower.algebraMap_apply R (integralClosure R L) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact φ.apply_symm_apply _
  · refine RingHom.ext fun x => ?_
    change algebraMap L _ (φ (φ.symm (algebraMap (FractionRing R) L x))) = _
    rw [φ.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · refine ⟨φ.symm ⟨s, IntermediateField.mem_adjoin_simple_self _ s⟩, ?_⟩
    change algebraMap L _ (φ (φ.symm _)) = _
    rw [φ.apply_symm_apply]
    rfl
  · intro F _ _ g
    have : Algebra.IsAlgebraic L (AlgebraicClosure (FractionRing R)) :=
      Algebra.IsAlgebraic.tower_top (K := FractionRing R) L
    exact exists_extend_of_ringEquiv_of_isAlgebraic φ g
end GlobalTheory
