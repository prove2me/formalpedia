-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:14.113097+00:00
-- url     : https://prove2.me/submissions/b96e9657-ac99-4b5d-9a2d-7e97aba17072

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample_q68

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

theorem tensorDifference_commute (L B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference L (tensorDifference B f) = tensorDifference B (tensorDifference L f) := by
  funext M
  simp only [tensorDifference]
  rw [hf _ _ (tensorTwistSwapIso B L M)]
  ring

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

theorem mixedDifference_perm {ls ks : List (LineBundle X)} (h : ls.Perm ks)
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference ls f = mixedDifference ks f := by
  induction h with
  | nil => rfl
  | cons L h ih => exact congrArg (tensorDifference L) ih
  | swap A B ls => exact tensorDifference_commute B A _ (hf.mixedDifference ls)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

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

theorem mixedDifference_replicate_tensor_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (n : ℕ) (ls : List (LineBundle X))
    (hlen : n + ls.length = d) :
    mixedDifference (List.replicate n (A.tensor B) ++ ls) f =
      ∑ k ∈ Finset.range (n+1), n.choose k •
        mixedDifference (List.replicate k A ++ List.replicate (n-k) B ++ ls) f := by
  induction n generalizing ls with
  | zero => simp
  | succ n ih =>
      have hm (L : LineBundle X) :
          mixedDifference (L :: (List.replicate n (A.tensor B) ++ ls)) f =
            mixedDifference (List.replicate n (A.tensor B) ++ L :: ls) f :=
        mixedDifference_perm List.perm_middle.symm f hf
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_tensor_cons_of_degree hf hdegree A B _ (by
          simp only [List.length_append, List.length_replicate]; omega), hm A, hm B,
        ih (A :: ls) (by simp only [List.length_cons]; omega),
        ih (B :: ls) (by simp only [List.length_cons]; omega)]
      rw [Finset.sum_choose_succ_nsmul
        (fun a b => mixedDifference (List.replicate a A ++ List.replicate b B ++ ls) f) n,
        add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have he : n+1-k = (n-k)+1 := by omega
        congr 1
        apply mixedDifference_perm _ f hf
        rw [he, List.replicate_succ]
        simpa only [List.append_assoc, List.cons_append] using
          (List.perm_middle (a := B) (l₁ := List.replicate (n-k) B) (l₂ := ls)).append_left
            (List.replicate k A)
      · apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply mixedDifference_perm _ f hf
        simpa only [List.replicate_succ, List.cons_append, List.append_assoc] using
          (List.perm_middle (a := A)
            (l₁ := List.replicate k A ++ List.replicate (n-k) B) (l₂ := ls))

theorem mixedDifference_replicate_pow_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n k : ℕ) (ls : List (LineBundle X)) (hlen : k + ls.length = d) :
    mixedDifference (List.replicate k (L.pow n) ++ ls) f =
      n^k • mixedDifference (List.replicate k L ++ ls) f := by
  induction k generalizing ls with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_pow_cons_of_degree hf hdegree L n _ (by
          simp only [List.length_append, List.length_replicate]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k (L.pow n)) (l₂ := ls)).symm f hf,
        ih (L :: ls) (by simp only [List.length_cons]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k L) (l₂ := ls)) f hf,
        smul_smul, pow_succ']
      rfl

theorem mixedDifference_two_powers_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b k l : ℕ) (ls : List (LineBundle X))
    (hlen : k+l+ls.length=d) :
    mixedDifference (List.replicate k (A.pow a) ++ List.replicate l (B.pow b) ++ ls) f =
      (a^k * b^l) • mixedDifference (List.replicate k A ++ List.replicate l B ++ ls) f := by
  have hswap (as bs : List (LineBundle X)) :
      mixedDifference (as ++ bs ++ ls) f = mixedDifference (bs ++ as ++ ls) f :=
    mixedDifference_perm (List.perm_append_comm.append_right ls) f hf
  rw [List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree A a k _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap,
    List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree B b l _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap, smul_smul]

theorem mixedTop_tensor_powers_binomial_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b n : ℕ) (ls : List (LineBundle X))
    (hlen : n+ls.length=d) :
    mixedTop f (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedTop f (List.replicate k A ++ List.replicate (n-k) B ++ ls) := by
  have hsum := congrFun
    (mixedDifference_replicate_tensor_append hf hdegree (A.pow a) (B.pow b) n ls hlen)
    (structureLineBundle X)
  change mixedDifference _ f (structureLineBundle X) = _
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedDifference_two_powers_append hf hdegree A B a b k (n-k) ls (by omega)]
  simp only [Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Nat.cast_mul, Nat.cast_pow,
    Pi.pow_apply, Pi.natCast_apply]
  ring

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

theorem mixedEuler_perm (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    {ls ks : List (LineBundle X)} (h : ls.Perm ks) :
    mixedEuler p d ls = mixedEuler p d ks :=
  congrFun (mixedDifference_perm h _ (lineEuler_isoInvariant p d)) (structureLineBundle X)

theorem lineEuler_mixedDegreeLE [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) : MixedDegreeLE d (lineEuler p d) :=
  mixedDifference_lineEuler_of_ample_q68 p H hH d hdim

theorem mixedEuler_tensor_powers_binomial_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A B : LineBundle X) (a b n : ℕ)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    mixedEuler p d (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedEuler p d (List.replicate k A ++ List.replicate (n-k) B ++ ls) :=
  mixedTop_tensor_powers_binomial_append (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B a b n ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_MixedSlopePolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open Polynomial Finset

lemma mixedSlopePolynomial_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial d c).eval t =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * t^k := by
  simp only [mixedSlopePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem mixedSlopePolynomial_derivative (d : ℕ) (c : ℕ → ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative =
      C ((d+1 : ℕ) : ℝ) * mixedSlopePolynomial d (fun k => c (k+1)) := by
  unfold mixedSlopePolynomial
  rw [Polynomial.derivative_sum, Finset.sum_range_succ']
  simp only [Polynomial.derivative_C_mul_X_pow, Nat.cast_zero, mul_zero,
    C_0, zero_mul, add_zero, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h : (((d+1).choose (k+1) : ℕ) : ℝ) * ((k+1 : ℕ) : ℝ) =
      ((d+1 : ℕ) : ℝ) * (d.choose k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
  rw [← mul_assoc, ← C_mul]
  congr 2
  calc
    _ = (((d+1).choose (k+1) : ℝ) * ((k+1 : ℕ) : ℝ)) * c (k+1) := by ring
    _ = _ := by rw [h]; ring

lemma mixedSlopePolynomial_derivative_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative.eval t =
      (d+1 : ℕ) * (mixedSlopePolynomial d (fun k => c (k+1))).eval t := by
  rw [mixedSlopePolynomial_derivative]
  simp

theorem mixedSlopePolynomial_eval_div (d : ℕ) (c : ℕ → ℝ)
    (a b : ℝ) (hb : b ≠ 0) :
    b^d * (mixedSlopePolynomial d c).eval (a/b) =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * b^(d-k) * a^k := by
  rw [mixedSlopePolynomial_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp : b^d = b^(d-k) * b^k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [div_pow, hp]
  field_simp

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

theorem mixedEuler_replicate_iso_append (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) (n : ℕ) (ls : List (LineBundle X)) :
    mixedEuler p d (List.replicate n L ++ ls) =
      mixedEuler p d (List.replicate n M ++ ls) := by
  have he : mixedDifference (List.replicate n L ++ ls) (lineEuler p d) =
      mixedDifference (List.replicate n M ++ ls) (lineEuler p d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, List.cons_append]
        rw [mixedDifference_iso_cons L M e _ _ (lineEuler_isoInvariant p d)]
        exact congrArg (tensorDifference M) ih
  exact congrFun he (structureLineBundle X)

theorem mixedEuler_slopeBundle_eq_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (a b n : ℕ) (hb : 0 < b)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    (mixedEuler p d (List.replicate n (slopeBundle L H a b) ++ ls) : ℝ) =
      (b : ℝ)^n * (mixedSlopePolynomial n (fun k =>
        (mixedEuler p d (List.replicate k H ++ List.replicate (n-k) L ++ ls) : ℝ))).eval
          ((a : ℝ)/b) := by
  rw [mixedEuler_replicate_iso_append p d (slopeBundle L H a b)
      ((H.pow a).tensor (L.pow b))
      (moduleTensorComm (L.pow b).sheaf (H.pow a).sheaf),
    mixedEuler_tensor_powers_binomial_append p H hH d hdim H L a b n ls hlen,
    mixedSlopePolynomial_eval_div n _ _ _ (by exact_mod_cast (Nat.ne_of_gt hb))]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem eulerSlopeCoefficient_succ (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) :
    eulerSlopeCoefficient p (d+1) L H (k+1) =
      (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
  dsimp only [eulerSlopeCoefficient]
  congr 1
  apply mixedEuler_perm
  simpa only [List.replicate_succ, List.cons_append, Nat.add_sub_add_right,
    List.append_nil] using
    (List.perm_middle (a := H)
      (l₁ := List.replicate k H ++ List.replicate (d-k) L) (l₂ := [])).symm

theorem eulerSlopePolynomial_derivative_eval_nat_div_q68_oai [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) (hb : 0 < b) :
    (b : ℝ)^d * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a : ℝ)/b) =
      (d+1 : ℕ) *
        (mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) : ℝ) := by
  rw [eulerSlopePolynomial, mixedSlopePolynomial_derivative_eval]
  have hc : (fun k => eulerSlopeCoefficient p (d+1) L H (k+1)) =
      fun k => (mixedEuler p (d+1)
        (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
    funext k
    exact eulerSlopeCoefficient_succ p d L H k
  rw [hc]
  have he := mixedEuler_slopeBundle_eq_append p H hH L (d+1)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) a b d hb [H] (by simp)
  have hp : mixedEuler p (d+1) (List.replicate d (slopeBundle L H a b) ++ [H]) =
      mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
    apply mixedEuler_perm
    simpa only [List.append_nil] using
      (List.perm_middle (a := H) (l₁ := List.replicate d (slopeBundle L H a b)) (l₂ := []))
  rw [hp] at he
  calc
    _ = (d+1 : ℕ) * ((b : ℝ)^d * (mixedSlopePolynomial d (fun k =>
        (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ))).eval
          ((a : ℝ)/b)) := by ring
    _ = _ := by rw [← he]

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68_oai := @OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68_oai
