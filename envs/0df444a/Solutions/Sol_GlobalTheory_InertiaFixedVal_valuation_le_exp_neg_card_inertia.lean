-- Prove2me | solution 1 for GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:49.970001+00:00
-- url     : https://prove2.me/submissions/263457b5-8e4e-4f00-a70f-9f567ca74267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory GlobalTheory.InertiaFixedVal
namespace GlobalTheory.InertiaFixedVal
theorem _root_.solution (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L) :
    (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 →
      P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by
  intro hy hv
  classical
  let H : Subgroup (L ≃ₐ[K] L) := P.asIdeal.inertia (L ≃ₐ[K] L)
  let E : IntermediateField K L := FixedPoints.intermediateField H
  haveI : IsGaloisGroup H E L := IsGaloisGroup.subgroup (L ≃ₐ[K] L) K L H
  haveI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K E]; rfl
  let OE := integralClosure R E
  haveI : IsFractionRing OE E := integralClosure.isFractionRing_of_finite_extension K E
  haveI : IsDedekindDomain OE := integralClosure.isDedekindDomain R K E
  let f : OE →ₐ[R] integralClosure R L := ((IsScalarTower.toAlgHom R E L).comp OE.val).codRestrict _
    (fun x => x.2.map (IsScalarTower.toAlgHom R E L))
  letI : Algebra OE (integralClosure R L) := f.toRingHom.toAlgebra
  haveI : IsScalarTower OE (integralClosure R L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R OE (integralClosure R L) := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI : Algebra.IsIntegral OE (integralClosure R L) := Algebra.IsIntegral.tower_top R
  haveI : FaithfulSMul OE (integralClosure R L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun x : integralClosure R L => (x : L)) hab
    exact Subtype.ext (FaithfulSMul.algebraMap_injective E L this)
  haveI : Module.IsTorsionFree OE (integralClosure R L) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)
  haveI : Module.Finite OE (integralClosure R L) := Module.Finite.of_restrictScalars_finite R OE _
  haveI : Module.Flat OE (integralClosure R L) := inferInstance
  haveI : SMulDistribClass H (integralClosure R L) L := inferInstance
  haveI : IsGaloisGroup H OE (integralClosure R L) := IsGaloisGroup.of_isFractionRing H OE (integralClosure R L) E L

  let Q : Ideal OE := P.asIdeal.under OE
  have hPne : P.asIdeal ≠ ⊥ := P.ne_bot
  have hQne : Q ≠ ⊥ := by
    exact Ideal.under_ne_bot OE hPne
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
  have hQR : (Q.under R).IsMaximal := Ideal.IsMaximal.under R Q
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) := ⟨(IsLocalRing.eq_maximalIdeal hQR).symm⟩
  letI : Field (OE ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI : Algebra.IsIntegral R OE := ⟨fun x => integralClosure.isIntegral x⟩
  haveI : Algebra.IsIntegral (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : PerfectField (OE ⧸ Q) := by
    haveI : PerfectField (R ⧸ IsLocalRing.maximalIdeal R) := ‹PerfectField (IsLocalRing.ResidueField R)›
    exact Algebra.IsAlgebraic.perfectField (R ⧸ IsLocalRing.maximalIdeal R)
  haveI : PerfectField Q.ResidueField :=
    PerfectField.of_ringEquiv (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField Q))
  have htop : P.asIdeal.inertia H = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro σ
    exact AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x
  have hcard : Nat.card H = P.asIdeal.ramificationIdx OE := by
    have h := Ideal.card_inertia_eq_ramificationIdxIn (G := H) Q P.asIdeal
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P.asIdeal H, htop, Subgroup.card_top] at h
    exact h

  have hyE : y ∈ E := fun σ => hy σ σ.2
  let z : E := ⟨y, hyE⟩
  let w : HeightOneSpectrum OE := ⟨Q, inferInstance, hQne⟩
  haveI : P.asIdeal.LiesOver w.asIdeal := inferInstance
  have hval := HeightOneSpectrum.valuation_liesOver L w P z
  rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal P.asIdeal hQne, ← hcard] at hval
  change w.valuation E z ^ Nat.card H = P.valuation L y at hval
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hz : w.valuation E z < 1 := by
    by_contra h
    rw [not_lt] at h
    have := one_le_pow₀ (n := Nat.card H) h
    rw [hval] at this
    exact absurd hv (not_lt.mpr this)
  have hz1 : w.valuation E z ≤ WithZero.exp (-1) := by
    by_cases h0 : w.valuation E z = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at hz ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [WithZero.exp_le_exp]
      omega
  rw [← hval]
  calc w.valuation E z ^ Nat.card H ≤ WithZero.exp (-1) ^ Nat.card H := pow_le_pow_left₀ zero_le hz1 _
    _ = WithZero.exp (-(Nat.card H : ℤ)) := by
      rw [← WithZero.exp_nsmul]; congr 1; simp
end GlobalTheory.InertiaFixedVal
