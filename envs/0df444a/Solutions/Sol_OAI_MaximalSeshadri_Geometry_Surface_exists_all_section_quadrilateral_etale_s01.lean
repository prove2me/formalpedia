-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:04.132709+00:00
-- url     : https://prove2.me/submissions/2898dfe6-b7da-4327-b095-fc0c8506868b

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_integral_nodal_section_framed_etale_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_nodal_all_section_quadrilateral_s01

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ProperGlobalField
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.constantsInDegreeZero_isIso _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_proper _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_separated _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

instance Surface.isProper_structureMap (surface : Surface) : IsProper surface.structureMap := by
  have constants_bijective : Function.Bijective
      (constantsInDegreeZero surface.embeddingDimension) := by
    constructor
    · intro left right equality
      have polynomial_equality : MvPolynomial.C left =
          (MvPolynomial.C right : MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ) :=
        congrArg Subtype.val equality
      exact MvPolynomial.C_injective _ _ polynomial_equality
    · intro polynomial
      have degree_zero : polynomial.val.totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr polynomial.property
      refine ⟨polynomial.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp degree_zero).symm
  let constantsIso := (RingEquiv.ofBijective
    (constantsInDegreeZero surface.embeddingDimension) constants_bijective).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension)) :=
    constantsIso.isIso_hom
  let polynomialRing := MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ
  let grading := MvPolynomial.homogeneousSubmodule (Fin (surface.embeddingDimension + 1)) ℂ
  let : Algebra ℂ (grading 0) := SetLike.GradeZero.instAlgebra grading
  let : IsScalarTower ℂ (grading 0) polynomialRing := ⟨fun scalar homogeneous polynomial => by
    change (scalar • (homogeneous : polynomialRing)) * polynomial =
      scalar • ((homogeneous : polynomialRing) * polynomial)
    exact smul_mul_assoc scalar (homogeneous : polynomialRing) polynomial⟩
  let : Algebra.FiniteType (grading 0) polynomialRing :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) polynomialRing
  have projective_proper : IsProper (Proj.toSpecZero grading) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat grading
  let : IsIso (Spec.map
      (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension))) := by
    infer_instance
  have : IsProper (projectiveSpaceToSpec surface.embeddingDimension) := by
    unfold projectiveSpaceToSpec
    exact IsProper.stableUnderComposition.comp_mem _ _ projective_proper inferInstance
  rw [← surface.overComplex]
  infer_instance

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_GlobalQuartic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionCombination_extend_zero {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (q : Option σ → (O X ⟶ M)) (v : σ → K) :
    sectionCombination k q (fun j => j.elim 0 v) = sectionCombination k (q ∘ some) v := by
  classical
  rw [sectionCombination, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, map_zero, scalarEnd_zero,
    Limits.zero_comp, zero_add, sectionCombination, Function.comp_apply]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_EtaleQuadrilateral
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem Surface.exists_all_section_quadrilateral_etale_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
        ∃ hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0,
        (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
          Function.Surjective ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom)) ∧
        Function.Injective (analyticTaylor q hq) ∧
        (∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V) ∧
        ∀ (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
          (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
          (w : ℝ) (_ : 0 < w) (p : Exponent),
          LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
          ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  obtain ⟨d,hd,N,s,hs,y,U,hyU,hU,eL,t,het,v,hy,hint,hdim,hcart,hsup,hsne,hsm,q,
    hR,hprime,hfn,hf0,hq0,hq,u,hu,hu0,hnode,hder,hjets,hinj,hV⟩ :=
    S.ample_integral_nodal_section_framed_etale_s01 L hL
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  let : IsIntegral (doublePointQuarticIdeal k s hs v).subscheme := hint
  have hjets' := hjets
  rw [← hq0] at hjets'
  refine ⟨d*4,by omega,y,U,hyU,eL,t,het,q,hq0,hq,hjets',hinj,hV,?_⟩
  have hc : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) =
      sectionCombination k (doublePointQuartics s) v := by
    rw [sectionCombination_extend_zero]
    rfl
  have hn : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) ≠ 0 := by rwa [hc]
  let eM := sectionFrameOn (powerSection (s none) 4) U.1
    (hU.trans (sectionOpen_le_powerSection (s none) 4))
  have integralSection : IsIntegral (sectionIdeal k (augmentedQuartics s) (augmentedQuartics_cover s hs)
      (fun j => j.elim 0 v)).subscheme := hint
  have H := @generated_nodal_all_section_quadrilateral_s01 S L hL ((L.pow d).pow 4) (d*4)
    (by omega) (linePowerMul L d 4) _ _ k (augmentedQuartics s) (augmentedQuartics_cover s hs)
    (fun j => j.elim 0 v) hn integralSection hdim U y hyU hsup eL eM hR q hq hjets' u hu hu0
  apply H
  · filter_upwards [hnode] with point hpoint
    exact (congrArg (fun sectionValue => q point (affineCoefficient U eM sectionValue)) hc).trans hpoint
  · exact (congrArg (fun sectionValue => q 0 (affineCoefficient U eM sectionValue)) hc).trans hf0
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01_oai
