-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalArithmeticPicardTorsionBound.actual_rational_arithmetic_picard_torsion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T10:50:15.668089+00:00
-- url     : https://prove2.me/submissions/dbcf989f-7ab6-418f-a3ef-82408c933575

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the torsion subgroup of the actual arithmetic Pic0(Q)
divisor-class group is finite and has cardinality dividing nineteen.
Named downstream consumer: the order-13 rational Jacobian computation.
The arithmetic point dictionary transports the checked same-family bound.
-/
import Theorems.Thm_MazurTransfer_Order13SameIntegralPicardFamilyRationalTorsionBound_actual_same_integral_picard_family_rational_torsion_bound
import Theorems.Thm_MazurTransfer_Order13IntegralPicardRelativeArithmeticGroupEquivPublic_relative_arithmetic_group_equiv
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres Order13SameIntegralPicardFamilyRationalTorsionBound
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel

theorem solution :
    letI : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∣ 19 := by
  letI : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
  obtain ⟨D,h,hb,hfinite,hcard,hpow⟩ := actual_same_integral_picard_family_rational_torsion_bound
  let hG := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
    (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
      D from h)
  let L := hG.relativeGroupLaw
  letI : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :=
    { L.pointGroup _ with mul_comm := hG.relativeGroupLaw_isCommutative _ }
  letI : Algebra BaseRing ℚ := canonicalRationalMap.toAlgebra
  obtain ⟨EQ⟩ := Order13IntegralPicardRelativeArithmeticGroupEquivPublic.relative_arithmetic_group_equiv
    BaseRing ℚ unit104 D h
  let e : CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) ≃*
      CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ))) :=
    (EQ.subgroupMap _).trans (MulEquiv.subgroupCongr EQ.map_torsion)
  letI : Finite (CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase)) :=
    hfinite
  have hf : Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) :=
    Finite.of_injective e.symm e.symm.injective
  exact ⟨hf,(Nat.card_congr e.symm.toEquiv).symm ▸ hcard⟩
#print axioms solution
