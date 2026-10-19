-- Prove2me | solution 1 for MazurTransfer.Order13SameIntegralPicardFamilyRationalTorsionBound.actual_same_integral_picard_family_rational_torsion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T10:20:48.795472+00:00
-- url     : https://prove2.me/submissions/7113b333-8e03-4df8-8a85-9cd1427ad0be

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: all rational torsion of one actual integral Picard family
is finite of order dividing nineteen, via its actual mod-three/mod-five maps.
Named downstream consumer: the order-13 Jacobian torsion computation.
Rational rank zero and existence of a point of exact order nineteen are separate.
-/
import Theorems.Thm_MazurTransfer_Order13ActualRationalPicardTorsionReduction_rationalSpecializationHom_eq_one_of_pow_eq_one
import Theorems.Thm_MazurTransfer_torsion_card_dvd_nineteen_of_two_reductions

noncomputable section
namespace MazurTransfer.TorsionBoundFromThreeFiveNineteenReduction
variable {G A B : Type*} [CommGroup G] [Group A] [Group B]
variable (r3 : G →* A) (r5 : G →* B)
variable (hA : Nat.card A = 19) (hB : Nat.card B = 19)
variable (h3 : ∀ (m : ℕ), ¬ 3 ∣ m → ∀ x : G, x ^ m = 1 → r3 x = 1 → x = 1)
variable (h5 : ∀ (m : ℕ), ¬ 5 ∣ m → ∀ x : G, x ^ m = 1 → r5 x = 1 → x = 1)
include r3 r5 hA hB h3 h5 in
theorem torsion_card_dvd_nineteen : Nat.card (CommGroup.torsion G) ∣ 19 :=
  MazurTransfer.torsion_card_dvd_nineteen_of_two_reductions r3 r5 hA hB h3 h5
include r3 r5 hA hB h3 h5 in
theorem torsion_finite [Finite A] : Finite (CommGroup.torsion G) := by
  apply Nat.finite_of_card_ne_zero
  intro hz
  have h := torsion_card_dvd_nineteen r3 r5 hA hB h3 h5
  rw [hz] at h
  norm_num at h
include r3 r5 hA hB h3 h5 in
theorem torsion_pow_nineteen (x : G) (hx : IsOfFinOrder x) : x ^ 19 = 1 := by
  let t : CommGroup.torsion G := ⟨x, hx⟩
  exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_natCard t).trans (torsion_card_dvd_nineteen r3 r5 hA hB h3 h5)))
end MazurTransfer.TorsionBoundFromThreeFiveNineteenReduction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres Order13LocalIntegralCoefficientMaps
open Order13ActualRationalPicardSpecialization Order13ActualRationalPicardTorsionReduction

theorem solution :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (h : RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) D),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      let hG := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
          D from h)
      let L := hG.relativeGroupLaw
      letI : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :=
        { L.pointGroup _ with mul_comm := hG.relativeGroupLaw_isCommutative _ }
      Finite (CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase)) ∧
      Nat.card (CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase)) ∣ 19 ∧
      ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase,
        IsOfFinOrder a → a ^ 19 = 1 := by
  obtain ⟨D,h,hb,hfinite⟩ := actual_same_integral_picard_family_finite_fibres
  refine ⟨D,h,hb,?_⟩
  let hG := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
    (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
      D from h)
  let L := hG.relativeGroupLaw
  letI : IsProper D.toBase := hb.proper
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :=
    { L.pointGroup _ with mul_comm := hG.relativeGroupLaw_isCommutative _ }
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap 3 (Or.inl rfl))))
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap 5 (Or.inr rfl))))
  letI : Algebra BaseRing (ZMod 3) := (canonicalFiniteFieldMap 3 (Or.inl rfl)).toAlgebra
  letI : Algebra BaseRing (ZMod 5) := (canonicalFiniteFieldMap 5 (Or.inr rfl)).toAlgebra
  obtain ⟨hf3,hcard3⟩ := hfinite 3 (Or.inl rfl)
  obtain ⟨hf5,hcard5⟩ := hfinite 5 (Or.inr rfl)
  letI := hf3
  let r3 := rationalSpecializationHom 3 (Or.inl rfl) D L
  let r5 := rationalSpecializationHom 5 (Or.inr rfl) D L
  have h3 := rationalSpecializationHom_eq_one_of_pow_eq_one 3 (Or.inl rfl) D L
    hG.relativeGroupLaw_isCommutative
  have h5 := rationalSpecializationHom_eq_one_of_pow_eq_one 5 (Or.inr rfl) D L
    hG.relativeGroupLaw_isCommutative
  exact ⟨TorsionBoundFromThreeFiveNineteenReduction.torsion_finite r3 r5 hcard3 hcard5 h3 h5,
    TorsionBoundFromThreeFiveNineteenReduction.torsion_card_dvd_nineteen r3 r5 hcard3 hcard5 h3 h5,
    TorsionBoundFromThreeFiveNineteenReduction.torsion_pow_nineteen r3 r5 hcard3 hcard5 h3 h5⟩
#print axioms solution
