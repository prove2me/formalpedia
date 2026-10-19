-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.generic_group_law_units_equal
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:29:07.894487+00:00
-- url     : https://prove2.me/submissions/c6f527a0-fdb8-43c5-bd15-507e2d786302

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the zero section of the SAME local Picard
model's generic group law with the chosen literal Picard representation.
Named downstream consumer: abelian-scheme rigidity, integral norm group
laws and local multiplication by nineteen.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData

noncomputable section
namespace MazurTransfer.GoodPrimeGenericLocalLawZeroProofHelpers20261018
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open PicardCanonicalRepresentationGroupIsomorphism
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem genericLocalLaw_zero :
    ((genericLocalLaw q hq).one (𝟙 _)).val =
      (localGenericPicard q hq).zeroSection := by
  unfold genericLocalLaw
  rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    change ((localLaw q hq).one (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)).val =
      (localGenericPicard q hq).zeroSection ≫
        pullback.fst (localPicard q hq).toBase (specGenericFibreInclusion (LocalRing q) ℚ)
    have hz : (localGenericPicard q hq).zeroSection ≫
        pullback.fst (localPicard q hq).toBase (specGenericFibreInclusion (LocalRing q) ℚ) =
        specGenericFibreInclusion (LocalRing q) ℚ ≫ (localPicard q hq).zeroSection :=
      RelativePic0Designation.baseChange_zeroSection_fst (localPicard q hq) ℚ
    rw [hz]
    have h := congrArg Subtype.val ((localLaw q hq).one_natural
      (𝟙 _) (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)
      (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ) (by simp))
    change (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ) ≫
      ((localLaw q hq).one (𝟙 _)).val =
        ((localLaw q hq).one (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)).val at h
    rw [localLaw_zero] at h
    exact h.symm.trans (by rw [Category.id_comp])
  · rw [pullback.lift_snd]
    exact (localGenericPicard q hq).zeroSection_toBase.symm

end MazurTransfer.GoodPrimeGenericLocalLawZeroProofHelpers20261018

open MazurTransfer
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity
open MazurTransfer.GoodPrimeGenericLocalLawZeroProofHelpers20261018
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open PicardCanonicalRepresentationGroupIsomorphism
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) :
    (genericLocalLaw q hq).one (𝟙 _) =
      (genericRepresentedLaw q hq).one (𝟙 _) := by
  apply Subtype.ext
  exact (genericLocalLaw_zero q hq).trans (genericRepresentedLaw_zero q hq).symm

#print axioms solution
