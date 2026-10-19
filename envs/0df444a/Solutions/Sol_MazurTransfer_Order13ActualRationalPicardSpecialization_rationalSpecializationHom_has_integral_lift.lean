-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalPicardSpecialization.rationalSpecializationHom_has_integral_lift
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T09:07:49.673646+00:00
-- url     : https://prove2.me/submissions/895bfc03-0670-43a2-893f-ee60bee5093e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational-to-mod-3/mod-5 group homomorphisms for
the original integral Picard family, obtained by unique local extension.
Named downstream consumer: prime-to-residue-characteristic torsion bounds.
No injectivity or rational rank conclusion is assumed or asserted here.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.ProperRelativeGroupValuationSpecialization
open MazurTransfer.Order13ActualRationalPicardSpecialization
theorem solution (q : ℕ) [Fact q.Prime] (hq : q=3 ∨ q=5)
    (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
    (L : RelativeGroupLaw BaseRing D.toBase) [IsProper D.toBase]
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :
    ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (localBaseMap q hq))) D.toBase,
      Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) ≫ x.val = a.val ∧
      (rationalSpecializationHom q hq D L a).val =
        Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ x.val := by
  let t := Spec.map (CommRingCat.ofHom (localBaseMap q hq))
  let a' := pointGroupCongr L (localRationalSpec_comp q hq).symm a
  let x := (ValuationRingProperPointRestriction.pointEquiv D.toBase (LocalRing q) ℚ t).symm a'
  refine ⟨x,?_,?_⟩
  · exact (ValuationRingProperPointRestriction.pointEquiv_extension D.toBase
      (LocalRing q) ℚ t a').trans (pointGroupCongr_coe L (localRationalSpec_comp q hq).symm a)
  · change (pointGroupCongr L (localFiniteFieldSpec_comp q hq)
      (specializationHom (LocalRing q) ℚ L t (ZMod q) (localFiniteFieldMap q) a')).val = _
    exact pointGroupCongr_coe L (localFiniteFieldSpec_comp q hq) _
#print axioms solution
