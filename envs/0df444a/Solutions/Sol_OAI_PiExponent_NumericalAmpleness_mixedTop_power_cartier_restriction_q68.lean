-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:40:59.832124+00:00
-- url     : https://prove2.me/submissions/27fc5d9b-2c9f-47f9-824a-7557be89caf7

import Mathlib
import Definitions.Def_OAIQ068A043
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedTop_cartier_restriction_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerRestriction
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem mixedTop_power_cartier_restriction_q68_oai [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (n : ℕ) (s : GlobalSections X (A.pow n).sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal (A.pow n) s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal (A.pow n) s).subschemeι)) := by
  have hdegree : MixedDegreeLE (d+1) (lineEuler p (d+1)) :=
    mixedDifference_lineEuler_of_ample_q68 p H hH (d+1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p (d+1))
    hdegree A n ls (by omega)) (structureLineBundle X)
  have hscale : mixedTop (lineEuler p (d+1)) (A.pow n :: ls) =
      (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, mixedTop, Pi.mul_apply, Pi.natCast_apply] using he
  rw [← hscale]
  exact mixedTop_cartier_restriction_q68 p H hH d hdim (A.pow n) s ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68_oai := @OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68_oai
