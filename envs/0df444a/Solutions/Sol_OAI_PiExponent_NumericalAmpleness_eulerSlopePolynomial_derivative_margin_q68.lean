-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:44:40.206638+00:00
-- url     : https://prove2.me/submissions/e1f494e3-54f5-491e-a908-acba73bca6f9

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_eval_nat_div_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedTop_curve_margin_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_topEuler_slopeBundle_eq_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem LineIsoInvariant.tensorDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (L : LineBundle X) : LineIsoInvariant (tensorDifference L f) := by
  intro M N e
  change f (L.tensor M) - f M = f (L.tensor N) - f N
  rw [hf (L.tensor M) (L.tensor N) (moduleTensorIso (Iso.refl L.sheaf) e), hf M N e]

theorem LineIsoInvariant.mixedDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (ls : List (LineBundle X)) : LineIsoInvariant (mixedDifference ls f) := by
  induction ls with
  | nil => exact hf
  | cons L ls ih => exact ih.tensorDifference L

theorem tensorDifference_tensor (A B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference (A.tensor B) f =
      tensorDifference A f + tensorDifference B f + mixedDifference [A,B] f := by
  funext M
  simp only [tensorDifference, mixedDifference, Pi.add_apply]
  rw [hf ((A.tensor B).tensor M) (A.tensor (B.tensor M)) (lineTensorAssoc A B M),
    hf _ _ (tensorTwistSwapIso A B M)]
  ring

theorem mixedDifference_tensor_cons (A B : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f +
        mixedDifference (A :: B :: ls) f :=
  tensorDifference_tensor A B (mixedDifference ls f) (hf.mixedDifference ls)

theorem mixedDifference_tensor_cons_of_next_eq_zero (A B : LineBundle X)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f)
    (hzero : mixedDifference (A :: B :: ls) f = 0) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  rw [mixedDifference_tensor_cons A B ls f hf, hzero, add_zero]

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

theorem lineEuler_isoInvariant {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ) :
    LineIsoInvariant (lineEuler p r) := by
  intro L M e
  exact eulerCharacteristic_iso p e r

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerPolarization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem mixedDifference_iso_cons (A B : LineBundle X) (e : A.sheaf ≅ B.sheaf)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A :: ls) f = mixedDifference (B :: ls) f := by
  funext M
  change mixedDifference ls f (A.tensor M) - mixedDifference ls f M =
    mixedDifference ls f (B.tensor M) - mixedDifference ls f M
  rw [(hf.mixedDifference ls) (A.tensor M) (B.tensor M)
    (moduleTensorIso e (Iso.refl M.sheaf))]

theorem mixedDifference_tensor_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  apply mixedDifference_tensor_cons_of_next_eq_zero A B ls f hf
  apply hdegree
  simp only [List.length_cons]
  omega

theorem mixedDifference_pow_zero_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L.pow 0 :: ls) f = 0 := by
  funext M
  change mixedDifference ls f ((L.pow 0).tensor M) - mixedDifference ls f M = 0
  rw [(hf.mixedDifference ls) ((L.pow 0).tensor M) M (moduleTensorUnit M.sheaf)]
  exact sub_self _

theorem mixedDifference_pow_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n : ℕ) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (L.pow n :: ls) f = n • mixedDifference (L :: ls) f := by
  induction n with
  | zero => simpa only [zero_nsmul] using mixedDifference_pow_zero_cons L ls f hf
  | succ n ih =>
      rw [mixedDifference_iso_cons (L.pow (n+1)) (L.tensor (L.pow n)) (Iso.refl _) ls f hf,
        mixedDifference_tensor_cons_of_degree hf hdegree L (L.pow n) ls hlen, ih]
      rw [add_comm, succ_nsmul]

theorem mixedDifference_replicate_pow (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (k n : ℕ) :
    mixedDifference (List.replicate k L) f (L.pow n) =
      (fwdDiff (1 : ℕ))^[k] (fun j => f (L.pow j)) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      change mixedDifference (List.replicate k L) f (L.tensor (L.pow n)) -
        mixedDifference (List.replicate k L) f (L.pow n) = _
      rw [(hf.mixedDifference _) (L.tensor (L.pow n)) (L.pow (n+1)) (Iso.refl _), ih, ih]
      rw [Function.iterate_succ_apply']
      rfl

theorem mixedTop_replicate (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (d : ℕ) :
    mixedTop f (List.replicate d L) =
      (fwdDiff (1 : ℕ))^[d] (fun n => f (L.pow n)) 0 := by
  rw [mixedTop, (hf.mixedDifference _) (structureLineBundle X) (L.pow 0) (Iso.refl _)]
  exact mixedDifference_replicate_pow L f hf d 0

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerTop
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem mixedEuler_replicate (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L : LineBundle X) : mixedEuler p d (List.replicate d L) = topEuler p d L :=
  mixedTop_replicate L _ (lineEuler_isoInvariant p d) d

theorem lineEuler_mixedDegreeLE [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) : MixedDegreeLE d (lineEuler p d) :=
  mixedDifference_lineEuler_of_ample_q68 p H hH d hdim

theorem mixedEuler_tensor_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (A.tensor B :: ls) = mixedEuler p d (A :: ls) + mixedEuler p d (B :: ls) :=
  congrFun (mixedDifference_tensor_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B ls hlen) (structureLineBundle X)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerSlope
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem mixedEuler_pow_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (L : LineBundle X) (n : ℕ)
    (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (L.pow n :: ls) = (n : ℤ) * mixedEuler p d (L :: ls) := by
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) L n ls hlen) (structureLineBundle X)
  simpa only [mixedEuler, mixedTop, Pi.smul_apply, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply] using he

theorem topEuler_slopeBundle_split [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) :
    topEuler p (d+1) (slopeBundle L H a b) =
      (b : ℤ) * mixedEuler p (d+1) (L :: List.replicate d (slopeBundle L H a b)) +
      (a : ℤ) * mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
  have hd : topologicalKrullDim X ≤ ((d+1 : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim
  rw [← mixedEuler_replicate p (d+1), List.replicate_succ]
  change mixedEuler p (d+1) (((L.pow b).tensor (H.pow a)) ::
    List.replicate d (slopeBundle L H a b)) = _
  rw [mixedEuler_tensor_cons p H hH (d+1) hd _ _ _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd L b _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd H a _ (by simp)]

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NumericalEulerSlopeInputs
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem eulerSlopePolynomial_derivative_margin_q68_oai [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) (hamp : (slopeBundle L H a b).IsAmple) :
    ((a:ℝ)/b+ε) * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a:ℝ)/b) ≤
      ((d+1:ℕ):ℝ) * (eulerSlopePolynomial p (d+1) L H).eval ((a:ℝ)/b) := by
  let M := slopeBundle L H a b
  let TL : ℝ := mixedEuler p (d+1) (L :: List.replicate d M)
  let TH : ℝ := mixedEuler p (d+1) (H :: List.replicate d M)
  let P := eulerSlopePolynomial p (d+1) L H
  have hdimle : topologicalKrullDim X ≤ d+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  have hvolume := topEuler_slopeBundle_eq_q68 p H hH L (d+1) hdim.le a b hb
  have hsplit : (topEuler p (d+1) M : ℝ) = (b:ℝ)*TL+(a:ℝ)*TH := by
    dsimp only [M, TL, TH]
    exact_mod_cast topEuler_slopeBundle_split p H hH L d hdimle a b
  have heq : (b:ℝ)*TL+(a:ℝ)*TH = (b:ℝ)^(d+1)*P.eval ((a:ℝ)/b) :=
    hsplit.symm.trans hvolume
  have hderivative : (b:ℝ)^d * P.derivative.eval ((a:ℝ)/b) = ((d+1:ℕ):ℝ)*TH :=
    eulerSlopePolynomial_derivative_eval_nat_div_q68 p H hH L d hdimle a b hb
  have hmix : ε*TH ≤ TL := mixedTop_curve_margin_q68 p H L hH d hdim ε hmargin
    (List.replicate d M) (by simp) (by
      intro A hA
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hA
      exact hamp)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hm : ((a:ℝ)+(b:ℝ)*ε)*TH ≤ (b:ℝ)*TL+(a:ℝ)*TH := by
    have h := mul_le_mul_of_nonneg_left hmix hbR.le
    nlinarith
  apply (mul_le_mul_iff_right₀ (pow_pos hbR (d+1))).mp
  change (b:ℝ)^(d+1) * (((a:ℝ)/b+ε)*P.derivative.eval ((a:ℝ)/b)) ≤
    (b:ℝ)^(d+1) * (((d+1:ℕ):ℝ)*P.eval ((a:ℝ)/b))
  calc
    _ = ((a:ℝ)+(b:ℝ)*ε) * ((b:ℝ)^d * P.derivative.eval ((a:ℝ)/b)) := by
      rw [pow_succ]
      field_simp [ne_of_gt hbR]
    _ = ((d+1:ℕ):ℝ) * (((a:ℝ)+(b:ℝ)*ε)*TH) := by rw [hderivative]; ring
    _ ≤ ((d+1:ℕ):ℝ) * ((b:ℝ)*TL+(a:ℝ)*TH) :=
      mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
    _ = _ := by rw [heq]; ring

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68_oai := @OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68_oai
