-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:14.770995+00:00
-- url     : https://prove2.me/submissions/e7561dca-8f40-4a60-99f2-0b804f722cb2

import Mathlib
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleCohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AmpleCohomologyFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem cohomology_finite_of_ample [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨d, hd, σ, hσ, s, hs, hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i, -⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let k : ℂ →+* Γ(X, ⊤) := baseScalars p
  let i : X ⟶ ProjectiveO1.projectiveSpace ℂ σ := sectionsMorphism k s hs
  have : IsClosedImmersion i := hclosed
  have hover : i ≫ polynomialProjectiveProjection ℂ σ = p := by
    rw [← projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap p)
  exact ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p i hover M q

end PiExponent.AmpleCohomologyFinite

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveDegreeAdditivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem power_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  induction n with
  | zero => simp [LineBundle.pow, modulePow, structureSheaf]
  | succ n ih =>
    have he := tensor_euler_add p hd H hH hfinite hH2 L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

end
end PiExponent.CurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleCurveDegreePositive
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_ample_section_with_zero [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (L.pow n).sheaf,
      s ≠ 0 ∧ ∃ y : X, y ∉ sectionOpen X s := by
  classical
  have : Nontrivial X := by
    by_contra h
    have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    have hz := topologicalKrullDim_zero_of_discreteTopology X
    rw [hdim] at hz
    norm_num at hz
  obtain ⟨y, hy⟩ := exists_ne (genericPoint X)
  have hclosed := CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint X hdim.le y hy
  let U : X.Opens := ⟨({y} : Set X)ᶜ, hclosed.isOpen_compl⟩
  have hη : genericPoint X ∈ U := by
    change genericPoint X ≠ y
    exact Ne.symm hy
  obtain ⟨n, hn, s, hsη, hsub, -⟩ := hL (genericPoint X) U hη
  refine ⟨n, hn, s, section_ne_zero_of_mem_isoOpen (L.pow n) s (genericPoint X) hsη,
    y, ?_⟩
  intro hys
  exact hsub hys rfl

theorem finite_nonempty_euler_pos [Finite X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (d : ℕ) :
    0 < eulerCharacteristic p d (structureSheaf X) := by
  classical
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars p).toAlgebra
  have : FiniteDimensional ℂ Γ(X, ⊤) := proper_finite_functions p
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  rw [proper_finite_euler]
  change (0 : ℤ) < (Module.finrank ℂ Γ(X, ⊤) : ℤ)
  exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Γ(X, ⊤)))

theorem section_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hzero : ∃ y : X, y ∉ sectionOpen X s)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  have hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let : Finite I.subscheme := finite_subscheme_of_curve p hdim I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := hzero
  have hyI : y ∈ I.support := by
    change y ∈ ((zeroIdeal L s).support : Set X)
    rw [zeroIdeal_support]
    exact hy
  have hyrange : y ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hyI
  obtain ⟨z, -⟩ := hyrange
  have : Nonempty I.subscheme := ⟨z⟩
  have heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, -⟩ := common_affine_frames L L x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  have : Subsingleton (cohomology (L.pow 0).sheaf 2) := by
    change Subsingleton (cohomology (structureSheaf X) 2)
    infer_instance
  have hdegree := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hdim (L.pow 0) L s hsMono I hI heq hfiniteO hfiniteL inferInstance
  change eulerCharacteristic p 1 L.sheaf -
    eulerCharacteristic p 1 (structureSheaf X) = _ at hdegree
  have hsum := proper_finite_euler_eq_sum_stalk_lengths (I.subschemeι ≫ p) 1
  have hpos := finite_nonempty_euler_pos (I.subschemeι ≫ p) 1
  rw [hdegree]
  rwa [hsum] at hpos

theorem ample_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1)
    (L : LineBundle X) (hL : L.IsAmple)
    (hfinite : FiniteLineCohomology p) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  have hH2 : LineCohomologyTwoZero X := by
    intro M
    exact ⟨fun a b =>
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68 1 p L hL M
        hdim.le 2 (by omega) a).trans
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68 1 p L hL M
        hdim.le 2 (by omega) b).symm⟩
  obtain ⟨n, hn, s, hs, hzero⟩ := exists_ample_section_with_zero hdim L hL
  have : Subsingleton (cohomology (structureSheaf X) 2) := hH2 (L.pow 0)
  have hpos := section_euler_degree_pos p hdim.le (L.pow n) s hs hzero
    (hfinite (L.pow 0)) (hfinite (L.pow n))
  rw [power_euler p hdim.le L hL hfinite hH2 L n] at hpos
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  exact (mul_pos_iff_of_pos_left hnz).mp hpos

theorem finite_line_cohomology_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) : FiniteLineCohomology p := by
  intro M q _
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q

theorem euler_degree_pos_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) :=
  ample_euler_degree_pos p hdim L hL (finite_line_cohomology_of_ample p L hL)

end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

theorem curveDegree_pos_of_ample_q68_oai
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (C : IntegralCurve X) :
    0 < curveDegree p L C := by
  exact CurveDegree.euler_degree_pos_of_ample (C.embedding ≫ p) C.dimension
    (L.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion L hL C.embedding)

end PiExponent.NumericalAmpleness

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68_oai := @OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68_oai
