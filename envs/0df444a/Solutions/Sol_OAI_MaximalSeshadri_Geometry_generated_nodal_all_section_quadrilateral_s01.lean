-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:20:18.974058+00:00
-- url     : https://prove2.me/submissions/b26dfbc4-c9bb-4c15-b371-ba8bb9b6e8c9

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_of_power_iso_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_maximal_cartier_extraction_of_iso_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_nodal_ideal_branch_sum_le_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_NodalLocal_nodal_associated_quadrilateral_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_on_any_frame_s01

section
-- module Solutions.Q223_SES.Seshadri_Analytic_TaylorCoefficients
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter Set

theorem analyticCoefficients_eq_derivative (f : analyticFunctionAlgebra) (a b : ℕ) :
    analyticCoefficients f (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => f.val (x,z)) 0) 0 := by
  rw [mixedDeriv_congr_germ _ _ (analyticCoefficients_spec f).2 a b]
  exact (mixedDeriv_at_zero _ (analyticCoefficients_spec f).1 a b).symm

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_FormalSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

local instance instHasAntidiagonalExponent_2_r6c9a69_1 : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite
lemma analyticCoefficients_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticCoefficients f = analyticCoefficients g := by
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1
    (analyticCoefficients_spec g).1
  exact (analyticCoefficients_spec f).2.symm.trans (h.trans (analyticCoefficients_spec g).2)

lemma analyticFormal_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticFormal f = analyticFormal g := by
  exact congrArg biSeries (analyticCoefficients_congr f g h)

lemma analyticFormal_constantCoeff (f : analyticFunctionAlgebra) :
    constantCoeff (constantCoeff (analyticFormal f)) = f.val (0,0) := by
  have h := analyticCoefficients_eq_derivative f 0 0
  simpa [analyticFormal, biSeries, constantCoeff_mk, iteratedDeriv_zero] using h

lemma analyticCoefficients_monomial (f : analyticFunctionAlgebra) (e : Exponent) (c : ℂ)
    (heq : f.val =ᶠ[𝓝 0] (fun q => c * q.1 ^ e.1 * q.2 ^ e.2)) :
    analyticCoefficients f = fun p => if p = e then c else 0 := by
  let d : Exponent → ℂ := fun p => if p = e then c else 0
  have hd : ConvergentSeries d := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, d, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq e ‖c‖).summable
  have hde (x z : ℂ) : seriesEval d x z = c * x ^ e.1 * z ^ e.2 := by
    simp [seriesEval, d, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1 hd
  filter_upwards [(analyticCoefficients_spec f).2, heq] with q hq hqq
  rw [← hq, hde, hqq]

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open PowerSeries

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

lemma binaryEquiv_coeff (f : MvPowerSeries (Fin 2) F) (a b : ℕ) :
    coeff a (coeff b (binaryEquiv F f)) =
      MvPowerSeries.coeff (Finsupp.cons b (Finsupp.cons a 0)) f := by
  simp only [binaryEquiv, AlgEquiv.trans_apply, powerSeriesMapEquiv_coeff]
  change MvPowerSeries.coeff 0 (coeff a (MvPowerSeries.finSuccEquiv F 0
    (coeff b (MvPowerSeries.finSuccEquiv F 1 f)))) = _
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_coeff_finSuccEquiv]

lemma binaryEquiv_constantCoeff (f : MvPowerSeries (Fin 2) F) :
    constantCoeff (constantCoeff (binaryEquiv F f)) = MvPowerSeries.constantCoeff f := by
  have h := binaryEquiv_coeff f 0 0
  simpa using h

end
end MaximalSeshadri.FormalCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_CoordinateJets
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries
open MaximalSeshadri.FormalCoordinates

lemma analyticFormal_first : analyticFormal analyticFirst = C (X : PowerSeries ℂ) := by
  have hc := analyticCoefficients_monomial analyticFirst (1,0) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticFirst])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticFirst)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, coeff_X, hb, Prod.ext_iff]

lemma analyticFormal_second : analyticFormal analyticSecond = (X : BiSeries) := by
  have hc := analyticCoefficients_monomial analyticSecond (0,1) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticSecond])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticSecond)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 1 <;> simp [biCoeff, coeff_X, hb, Prod.ext_iff]

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable {X : Scheme.{0}}

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_IntegralSectionIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma ideal_prime_of_integral_subscheme {X : Scheme} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (U : X.affineOpens) (x : X)
    (hx : x ∈ U.1) (hI : x ∈ I.support) : (I.ideal U).IsPrime := by
  have hmem : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hI
  obtain ⟨z,hz⟩ := hmem
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1) := ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  rw [← I.ker_subschemeι_app U]
  exact RingHom.ker_isPrime _

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalAdic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.FormalAdic
noncomputable section
open IsLocalRing
variable {σ R : Type*} [Finite σ] [CommRing R]

lemma completion_eval_kernel (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext x
  have h := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n) hI
  have heval : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I R n x = 0 := by
    let e := Ideal.quotientEquivAlgOfEq R (show (I ^ n • ⊤ : Ideal R) = I ^ n by simp)
    dsimp only [AdicCompletion.evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply]
    exact map_eq_zero_iff e e.injective
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  rw [heval, ← LinearMap.mem_ker, ← h]
  rw [← Ideal.map_pow]
  simp

lemma trunc_eq_completion_eval (n : ℕ) :
    (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (AdicCompletion.evalₐ (MvPolynomial.idealOfVars σ R) n).toRingHom.comp
        (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingHom := by
  apply RingHom.ext
  intro f
  change (MvPowerSeries.truncTotalAlgHom σ R n) f =
    AdicCompletion.evalₐ _ n (MvPowerSeries.toAdicCompletion σ R f)
  unfold MvPowerSeries.toAdicCompletion
  erw [AdicCompletion.evalₐ_liftAlgHom]
  intro m n h
  apply AlgHom.ext
  intro p
  simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
    MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) p

omit [Finite σ] in
lemma polynomials_map_vars :
    (MvPolynomial.idealOfVars σ R).map
        (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.coe_X i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, MvPolynomial.coe_X i⟩

lemma trunc_kernel (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  let e := MvPowerSeries.toAdicCompletionAlgEquiv σ R
  rw [trunc_eq_completion_eval, ← RingHom.comap_ker,
    completion_eval_kernel _ (MvPolynomial.idealOfVars_fg σ R)]
  have he : (algebraMap (MvPolynomial σ R) (AdicCompletion (MvPolynomial.idealOfVars σ R)
      (MvPolynomial σ R))) = e.toRingHom.comp
      (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) := by
    apply RingHom.ext
    intro p
    exact (e.commutes p).symm
  rw [he, ← Ideal.map_map, ← Ideal.map_pow]
  change (Ideal.map e.toRingHom _).comap e.toRingHom = _
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective, polynomials_map_vars]

variable {K : Type*} [Field K]

omit [Finite σ] in
lemma maximalIdeal_eq_ker_constantCoeff :
    maximalIdeal (MvPowerSeries σ K) =
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ K →+* K) := by
  ext f
  rw [mem_maximalIdeal, mem_nonunits_iff, RingHom.mem_ker, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

lemma maximalIdeal_eq_vars :
    maximalIdeal (MvPowerSeries σ K) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) := by
  rw [← pow_one (Ideal.span _), ← trunc_kernel]
  ext f
  rw [maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker, RingHom.mem_ker]
  change _ ↔ Ideal.Quotient.mk _ (MvPowerSeries.truncTotal 1 f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    rw [MvPowerSeries.coeff_truncTotal _ hd, hd0]
    exact hf
  · intro hf
    simpa [MvPowerSeries.coeff_truncTotal _ (show (0 : σ →₀ ℕ).degree < 1 by simp)]
      using hf 0 (by simp)

lemma trunc_kernel_maximalIdeal (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ K n).toRingHom =
      maximalIdeal (MvPowerSeries σ K) ^ n := by
  rw [trunc_kernel, maximalIdeal_eq_vars]

end
end MaximalSeshadri.FormalAdic


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_CoordinateEquivalences
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open IsLocalRing

variable {σ K : Type*} [Finite σ] [Field K]

local notation "P" => MvPowerSeries σ K
local notation "𝔪" => maximalIdeal P

lemma mem_maximal_pow_iff (f : P) (n : ℕ) :
    f ∈ 𝔪 ^ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → MvPowerSeries.coeff d f = 0 := by
  rw [← FormalAdic.trunc_kernel_maximalIdeal, RingHom.mem_ker]
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor <;> intro h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd

lemma mem_maximal_sq_iff (f : P) :
    f ∈ 𝔪 ^ 2 ↔ MvPowerSeries.constantCoeff f = 0 ∧
      ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  rw [mem_maximal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun i => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ d hd
    by_cases he : d.degree = 0
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp he
      simpa [this] using h0
    · have he : d.degree = 1 := by omega
      obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr he
      exact h1 i

end
end MaximalSeshadri.FormalCoordinates

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri
namespace NodalLocal

open PowerSeries

noncomputable section

variable (K : Type*) [Field K]

theorem range_includeX_eq_ker_branchZ :
    (includeX K).range = (branchZ K).toLinearMap.ker := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hf
    have hz : branchZ K f = 0 := hf
    have hx : constantCoeff (branchX K f) = 0 := by rw [branch_constant, hz, map_zero]
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hx
    refine ⟨g, ?_⟩
    apply node_ext <;> simp [hg, hz]

lemma finite_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    FiniteDimensional K (PowerSeries K ⧸ multiples K f) :=
  FiniteDimensional.of_injective (branchQuotientEquiv K f hf).toLinearMap
    (branchQuotientEquiv K f hf).injective

lemma finrank_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    Module.finrank K (PowerSeries K ⧸ multiples K f) = f.order.toNat := by
  rw [(branchQuotientEquiv K f hf).finrank_eq, Module.finrank_pi]
  simp

lemma quotientZ_surjective (f : Node K) : Function.Surjective (quotientZ K f) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H g =>
    exact ⟨Submodule.Quotient.mk (liftZ K g), by simp⟩

lemma quotientX_injective (f : Node K) (hfz : branchZ K f ≠ 0) :
    Function.Injective (quotientX K f) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro q hq
  change q = 0
  induction q using Submodule.Quotient.induction_on with
  | H h =>
    have hh : includeX K h ∈ multiples K f := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨g, hg⟩ := (mem_multiples K f (includeX K h)).mp hh
    have hgz : branchZ K g = 0 := by
      have hz : branchZ K f * branchZ K g = 0 := by
        simpa using (congrArg (branchZ K) hg).symm
      exact (mul_eq_zero.mp hz).resolve_left hfz
    have hgc : constantCoeff (branchX K g) = 0 := by
      rw [branch_constant, hgz, map_zero]
    obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hgc
    have hh' : h = branchX K f * a := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : PowerSeries K) ≠ 0)
      calc
        X * h = branchX K f * branchX K g := by
          simpa using congrArg (branchX K) hg
        _ = X * (branchX K f * a) := by rw [ha]; ring
    change (Submodule.Quotient.mk h : PowerSeries K ⧸ multiples K (branchX K f)) = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_multiples]
    exact ⟨a, hh'⟩

lemma branch_quotient_exact (f : Node K) :
    Function.Exact (quotientX K f) (quotientZ K f) := by
  rw [LinearMap.exact_iff]
  ext q
  constructor
  · intro hq
    induction q using Submodule.Quotient.induction_on with
    | H g =>
      have hg : branchZ K g ∈ multiples K (branchZ K f) := by
        exact (Submodule.Quotient.mk_eq_zero _).mp hq
      obtain ⟨b, hb⟩ := (mem_multiples K _ _).mp hg
      let g' := g - f * liftZ K b
      have hz : branchZ K g' = 0 := by simp [g', hb]
      have hmem : g' ∈ (includeX K).range := by
        rw [range_includeX_eq_ker_branchZ]
        exact hz
      obtain ⟨a, ha⟩ := hmem
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [quotientX_mk, Submodule.Quotient.eq]
      rw [ha]
      change g - f * liftZ K b - g ∈ multiples K f
      rw [show g - f * liftZ K b - g = f * (-liftZ K b) by ring]
      rw [mem_multiples]
      exact dvd_mul_right _ _
  · rintro ⟨a, rfl⟩
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      change quotientZ K f (quotientX K f (Submodule.Quotient.mk a)) = 0
      simp

lemma finite_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    FiniteDimensional K (Node K ⧸ multiples K f) := by
  have := finite_branch_quotient K (branchX K f) hfx
  have := finite_branch_quotient K (branchZ K f) hfz
  exact Module.Finite.of_exact (branch_quotient_exact K f) (quotientZ_surjective K f)

theorem finrank_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    Module.finrank K (Node K ⧸ multiples K f) =
      (branchX K f).order.toNat + (branchZ K f).order.toNat := by
  have := finite_node_quotient K f hfx hfz
  have hex := LinearMap.exact_iff.mp (branch_quotient_exact K f)
  have hs : (quotientZ K f).range = ⊤ :=
    LinearMap.range_eq_top.mpr (quotientZ_surjective K f)
  have h := (quotientZ K f).finrank_range_add_finrank_ker
  rw [hs, finrank_top, hex,
    LinearMap.finrank_range_of_inj (quotientX_injective K f hfz),
    finrank_branch_quotient K _ hfz, finrank_branch_quotient K _ hfx] at h
  omega

theorem nodal_intersection_colength (f : Bivariate K)
    (hx : restrictX K f ≠ 0) (hz : restrictZ K f ≠ 0) :
    Module.finrank K (Bivariate K ⧸ intersectionIdeal K f) =
      (restrictX K f).order.toNat + (restrictZ K f).order.toNat := by
  rw [(intersectionQuotientEquiv K f).finrank_eq]
  exact finrank_node_quotient K (toNode K f) hx hz

end

end NodalLocal
end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_NodalTaylor
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open AlgebraicJets FormalCoordinates LocalComparison NodalLocal IsLocalRing
open scoped Topology

variable {R : Type*} [CommRing R] [Algebra ℂ R]

lemma bivariateTaylor_eq (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    bivariateTaylor q hq = (binaryEquiv ℂ).toAlgHom.comp (analyticTaylor q hq) := by
  apply AlgHom.ext
  intro s
  exact ((binaryEquiv ℂ).apply_symm_apply _).symm

lemma bivariateTaylor_node (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (g : R)
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    ∃ U : Bivariate ℂ, IsUnit U ∧
      bivariateTaylor q hq g = U * nodeEquation ℂ := by
  let a : analyticFunctionAlgebra := ⟨u,hu⟩
  refine ⟨analyticFormal a, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.isUnit_iff_constantCoeff,
      analyticFormal_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hu0
  · have he := analyticFormal_congr (analyticPullback q hq g)
      (a*analyticFirst*analyticSecond) hg
    change analyticFormal (analyticPullback q hq g) = _
    rw [he, map_mul, map_mul, analyticFormal_first, analyticFormal_second, nodeEquation]
    exact mul_assoc _ _ _

end
end MaximalSeshadri.AnalyticCoordinates
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_BranchFaithfulness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open IsLocalRing
open scoped nonZeroDivisors

lemma principal_curve_dimension_le_one {R : Type*} [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {g}) ≤ 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have H := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)).trans hd
  simpa only [one_add_one_eq_two] using H

theorem formal_branch_kernel {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0)
    [hgp : (Ideal.span {g}).IsPrime]
    (φ : R →+* PowerSeries K) (hφg : φ g = 0)
    (hbranch : ∃ a : R, PowerSeries.constantCoeff (φ a) = 0 ∧ φ a ≠ 0) :
    RingHom.ker φ = Ideal.span {g} := by
  have hI : Ideal.span {g} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr hφg
  let ψ := Ideal.Quotient.lift (Ideal.span {g}) φ hI
  have hcomp : ψ.comp (Ideal.Quotient.mk (Ideal.span {g})) = φ := by
    ext a
    rfl
  let : Ring.KrullDimLE 1 (R ⧸ Ideal.span {g}) :=
    Ring.krullDimLE_iff.mpr (principal_curve_dimension_le_one hd g hg)
  apply (Ideal.injective_lift_iff hI).mp
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  by_contra hne
  have hm : (RingHom.ker ψ).IsMaximal :=
    (RingHom.ker_isPrime ψ).isMaximal_of_ne_bot hne
  let := hm
  have hm' : (RingHom.ker φ).IsMaximal := by
    rw [← hcomp, ← RingHom.comap_ker]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : RingHom.ker φ ≤ RingHom.ker (PowerSeries.constantCoeff.comp φ) := by
    intro a ha
    change PowerSeries.constantCoeff (φ a) = 0
    rw [ha, map_zero]
  have he := hm'.eq_of_le (RingHom.ker_isPrime (PowerSeries.constantCoeff.comp φ)).ne_top hle
  obtain ⟨a,ha,han⟩ := hbranch
  exact han (show a ∈ RingHom.ker φ from he ▸ ha)

end
end MaximalSeshadri.NodalLocal
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalBranch
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open FormalCoordinates NodalLocal IsLocalRing
open scoped Topology

lemma binary_second_jet_witness {R : Type*} [CommRing R] [Algebra ℂ R]
    (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp τ.toRingHom)) (i : Fin 2) :
    ∃ a : R, MvPowerSeries.constantCoeff (τ a) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single i 1) (τ a) = 1 := by
  obtain ⟨a,ha⟩ := hs (Ideal.Quotient.mk _ (MvPowerSeries.X i))
  have hm := (mem_maximal_sq_iff (τ a - MvPowerSeries.X i)).mp
    (Ideal.Quotient.eq.mp ha)
  refine ⟨a, ?_, ?_⟩
  · simpa using hm.1
  · simpa [sub_eq_zero] using hm.2 i

lemma bivariate_branch_witnesses {R : Type*} [CommRing R] [Algebra ℂ R]
    (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp τ.toRingHom)) :
    (∃ a : R, PowerSeries.constantCoeff (restrictX ℂ ((binaryEquiv ℂ) (τ a))) = 0 ∧
      restrictX ℂ ((binaryEquiv ℂ) (τ a)) ≠ 0) ∧
    (∃ a : R, PowerSeries.constantCoeff (restrictZ ℂ ((binaryEquiv ℂ) (τ a))) = 0 ∧
      restrictZ ℂ ((binaryEquiv ℂ) (τ a)) ≠ 0) := by
  constructor
  · obtain ⟨a,ha0,ha1⟩ := binary_second_jet_witness τ hs 1
    refine ⟨a, ?_, ?_⟩
    · exact (binaryEquiv_constantCoeff _).trans ha0
    · intro h
      have H := congrArg (PowerSeries.coeff 1) h
      have he : Finsupp.cons 0 (Finsupp.cons 1 (0 : Fin 0 →₀ ℕ)) =
          Finsupp.single (1 : Fin 2) 1 := by
        ext j
        fin_cases j
        · simp
        · change (Finsupp.cons _ (Finsupp.cons _ 0)) (Fin.succ (0 : Fin 1)) = _
          rw [Finsupp.cons_succ]
          simp
      simp only [map_zero, restrictX_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at H
      change PowerSeries.coeff 1 (PowerSeries.coeff 0 ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [binaryEquiv_coeff,he,ha1] at H
      exact one_ne_zero H
  · obtain ⟨a,ha0,ha1⟩ := binary_second_jet_witness τ hs 0
    refine ⟨a, ?_, ?_⟩
    · rw [← restrict_constants]
      exact (binaryEquiv_constantCoeff _).trans ha0
    · intro h
      have H := congrArg (PowerSeries.coeff 1) h
      have he : Finsupp.cons 1 (Finsupp.cons 0 (0 : Fin 0 →₀ ℕ)) =
          Finsupp.single (0 : Fin 2) 1 := by
        ext j
        fin_cases j
        · simp
        · change (Finsupp.cons _ (Finsupp.cons _ 0)) (Fin.succ (0 : Fin 1)) = _
          rw [Finsupp.cons_succ]
          simp
      change PowerSeries.coeff 1 (PowerSeries.map PowerSeries.constantCoeff
        ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [PowerSeries.coeff_map] at H
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at H
      change PowerSeries.coeff 0 (PowerSeries.coeff 1 ((binaryEquiv ℂ) (τ a))) = 0 at H
      rw [binaryEquiv_coeff,he,ha1] at H
      exact one_ne_zero H

theorem nodal_branch_kernels {R : Type*} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp (analyticTaylor q hq).toRingHom))
    (g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    RingHom.ker ((restrictX ℂ).comp (bivariateTaylor q hq)).toRingHom = Ideal.span {g} ∧
    RingHom.ker ((restrictZ ℂ).comp (bivariateTaylor q hq)).toRingHom = Ideal.span {g} := by
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hw := bivariate_branch_witnesses (analyticTaylor q hq) hs
  have he (a : R) : (binaryEquiv ℂ) (analyticTaylor q hq a) = bivariateTaylor q hq a := by
    rw [bivariateTaylor_eq]; rfl
  simp only [he] at hw
  constructor
  · apply formal_branch_kernel hd g hg0 _ _ hw.1
    change restrictX ℂ (bivariateTaylor q hq g) = 0
    simp [hgU, nodeEquation]
  · apply formal_branch_kernel hd g hg0 _ _ hw.2
    change restrictZ ℂ (bivariateTaylor q hq g) = 0
    simp [hgU, nodeEquation]

end
end MaximalSeshadri.AnalyticCoordinates

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have leftSection : uF.inv ≫ F.map s =
        restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) := by
      dsimp only [uF, F, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫
          sectionMap) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
            (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s)).symm)
    have rightSection : uG.inv ≫ G.map s =
        pullbackSection (f ∣_ U) (restrictSection U.ι s) := by
      dsimp only [uG, G, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
          ((Scheme.Modules.pullback (f ∣_ U)).map_comp
            (Scheme.Modules.restrictUnitIso U.ι).inv
            ((Scheme.Modules.restrictFunctor U.ι).map s)).symm)
    exact (congrArg (coefficient eF) leftSection).symm.trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) rightSection))
  rw [he', coefficient_pullback]

end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_OpenChartDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma chart_topIso_naturality (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma structuralOpenChartMap_apply (p : X ⟶ Spec (CommRingCat.of ℂ))
    (j : Y ⟶ X) (U : X.Opens) (f : Γ(X,U)) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    structuralOpenChartMap p j U f = (j ⁻¹ᵁ U).topIso.inv (j.app U f) := by
  change (j ∣_ U).appTop (U.topIso.inv f) = _
  rw [← chart_topIso_naturality]
  simp only [CommRingCat.comp_apply]
  rw [U.topIso.inv_hom_id_apply]

lemma structuralOpenChartMap_ker (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) :
    letI : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
    letI : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
      (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
    RingHom.ker (structuralOpenChartMap p I.subschemeι U.1).toRingHom = I.ideal U := by
  ext t
  change structuralOpenChartMap p I.subschemeι U.1 t = 0 ↔ t ∈ I.ideal U
  rw [structuralOpenChartMap_apply, ← I.ker_subschemeι_app U]
  change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv (I.subschemeι.app U.1 t) = 0 ↔
    I.subschemeι.app U.1 t = 0
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma affineCoefficient_ne_zero [IsIntegral X] (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : affineCoefficient U e s ≠ 0 := by
  exact (isRegular_iff_ne_zero.mp (L.section_coefficient_regular s hs U e))

end
end MaximalSeshadri.Geometry

end

end OAI
end

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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalContainment
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

theorem pullback_section_zero_iff_local_coefficient
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) [Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    pullbackSection I.subschemeι s = 0 ↔
      U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  let π := structuralOpenChartMap p I.subschemeι U.1
  let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have hcoeff : π f = coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) := by
    rw [he]
    change (I.subschemeι ∣_ U.1).appTop
      (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = _
    rw [U.1.topIso.hom_inv_id_apply]
  have hker : f ∈ I.ideal U ↔ π f = 0 := by
    rw [← structuralOpenChartMap_ker p I U]
    rfl
  rw [show U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) = f from rfl,
    hker, hcoeff]
  constructor
  · intro h
    rw [h,restrictSection_zero,coefficient_zero]
  · intro h
    apply (L.pullback I.subschemeι).restricted_coefficient_injective
      (I.subschemeι ⁻¹ᵁ U.1).ι eF
    change coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) =
      coefficient eF (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι
        (0 : O I.subscheme ⟶ (Scheme.Modules.pullback I.subschemeι).obj L.sheaf))
    rw [restrictSection_zero,coefficient_zero]
    exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_QuadraticSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.EulerNumerics

lemma periodic_nat_gcd {α : Type*} (f : ℕ → α) (a b : ℕ)
    (ha : Function.Periodic f a) (hb : Function.Periodic f b) :
    Function.Periodic f (Nat.gcd a b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hz : a = 0
    · simpa [hz] using hb
    have hm : Function.Periodic f (b % a) := by
      intro n
      have H := ha.nat_mul (b/a) (n+b%a)
      rw [Nat.cast_id, Nat.add_assoc,Nat.mod_add_div'] at H
      exact H.symm.trans (hb n)
    rw [Nat.gcd_rec]
    exact ih (b%a) (Nat.mod_lt b (Nat.pos_of_ne_zero hz)) a hm ha

lemma periodic_nat_coprime_constant {α : Type*} (f : ℕ → α) (a b : ℕ)
    (hab : Nat.Coprime a b) (ha : Function.Periodic f a)
    (hb : Function.Periodic f b) (n : ℕ) : f n = f 0 := by
  have H := periodic_nat_gcd f a b ha hb
  rw [hab.gcd_eq_one] at H
  simpa only [Nat.cast_id,mul_one] using H.nat_mul_eq n

theorem quadratic_of_coprime_differences (f : ℕ → ℤ) (a b : ℕ)
    (hab : Nat.Coprime a b) (d e c h : ℤ)
    (ha : ∀ n, f (n+a) - f n = (n : ℤ)*d+c)
    (hb : ∀ n, f (n+b) - f n = (n : ℤ)*e+h) (n : ℕ) :
    2*f n = (n : ℤ)*((n : ℤ)-1)*(f 2-2*f 1+f 0) +
      2*(n : ℤ)*(f 1-f 0)+2*f 0 := by
  let g (n : ℕ) := f (n+2)-2*f (n+1)+f n
  have periodic (a : ℕ) (d c : ℤ)
      (ha : ∀ n, f (n+a)-f n = (n : ℤ)*d+c) : Function.Periodic g a := by
    intro n
    have H₀ := ha n
    have H₁ := ha (n+1)
    have H₂ := ha (n+2)
    dsimp [g]
    rw [show n+a+2 = n+2+a by omega,show n+a+1 = n+1+a by omega]
    push_cast at H₁ H₂
    nlinarith
  have hg (n : ℕ) : g n = f 2-2*f 1+f 0 :=
    periodic_nat_coprime_constant g a b hab (periodic a d c ha) (periodic b e h hb) n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp <;> ring
  | more n hn hn₁ =>
    have H := hg n
    dsimp [g] at H
    push_cast at hn₁ ⊢
    nlinarith

theorem slope_of_quadratic (f : ℕ → ℤ) (q : ℤ)
    (hf : ∀ n, 2*f n = (n : ℤ)*((n : ℤ)-1)*q +
      2*(n : ℤ)*(f 1-f 0)+2*f 0)
    (a : ℕ) (d c : ℤ) (ha : ∀ n, f (n+a)-f n = (n : ℤ)*d+c) :
    d = (a : ℤ)*q := by
  have H₀ := ha 0
  have H₁ := ha 1
  have F₀ := hf a
  have F₁ := hf (a+1)
  simp only [Nat.cast_zero,zero_mul,zero_add] at H₀
  rw [Nat.add_comm 1 a] at H₁
  push_cast at H₁ F₁
  nlinarith

end MaximalSeshadri.EulerNumerics

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceQuadraticEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

lemma Surface.euler_power_one (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf =
      eulerCharacteristic S.structureMap 2 L.sheaf :=
  eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit L.sheaf) 2

lemma Surface.euler_power_second_difference (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
      2*eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf +
      eulerCharacteristic S.structureMap 2 (L.pow 0).sheaf = selfIntersection S L := by
  rw [S.euler_power_one]
  rfl

theorem Surface.power_euler_quadratic (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section_s01 L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = (m : ℤ)*curveDegree S L C +
      ((a : ℤ)*curveDegree S L C+eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L a k s hs v hne hd m
    change f (m+a)-f m = _ at H
    push_cast at H
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = (m : ℤ)*curveDegree S L D +
      ((b : ℤ)*curveDegree S L D+eulerCharacteristic (D.embedding ≫ S.structureMap) 1 (O D.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L b k s' hs' v' hne' hd' m
    change f (m+b)-f m = _ at H
    push_cast at H
    linarith
  have H := EulerNumerics.quadratic_of_coprime_differences f a b hab _ _ _ _ ha' hb' n
  have hq := S.euler_power_second_difference L
  have h1 := S.euler_power_one L
  change f 2-2*f 1+f 0 = selfIntersection S L at hq
  change f 1 = _ at h1
  rw [hq,h1] at H
  exact H

theorem generated_curveDegree_eq_power_selfIntersection (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S L C = (d : ℤ)*selfIntersection S L := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  apply EulerNumerics.slope_of_quadratic f (selfIntersection S L) _ d _
    ((d : ℤ)*curveDegree S L C + eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme))
  · intro n
    have H := generated_power_euler_difference_s01 S L hL L d k s hs v hne hd n
    change f (n+d)-f n = _ at H
    push_cast at H
    linarith
  · intro n
    have H := S.power_euler_quadratic L hL n
    rw [← S.euler_power_one L] at H
    exact H

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfacePositiveSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.selfIntersection_pos (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    0 < selfIntersection S L := by
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have hp := C.ample_degree_positive_s01 S L hL
  have he := generated_curveDegree_eq_power_selfIntersection S L hL d k s hs v hne hC
  change curveDegree S L C = (d : ℤ)*selfIntersection S L at he
  rw [he] at hp
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_AllSectionQuadrilateral
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
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.NodalLocal
open MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison
open scoped Topology

theorem generated_nodal_all_section_quadrilateral_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hDim : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1)
    (hyI : y ∈ (sectionIdeal k s hs v).support)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let g := affineCoefficient U eM (sectionCombination k s v)
    ∀ (q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
      (hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0)
      (_ : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
        Function.Surjective ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
      (u : (ℂ × ℂ) → ℂ) (_ : AnalyticAt ℂ u 0) (_ : u 0 ≠ 0)
      (_ : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (_ : q 0 g = 0)
      (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
      (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (w : ℝ) (_ : 0 < w) (p : Exponent),
      LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
      ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  let g := affineCoefficient U eM (sectionCombination k s v)
  dsimp only
  intro q hq hjets u hu hu0 hg hg0 a ha t ht eA w hw p hp
  let I := sectionIdeal k s hs v
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  have hy : y ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hyI
  obtain ⟨z,hz⟩ := hy
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme :=
    ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  have hIp : I.ideal U = Ideal.span {g} := sectionIdeal_on_any_frame_s01 k s hs v U eM
  let : (Ideal.span {g}).IsPrime := by
    rw [← hIp]
    exact ideal_prime_of_integral_subscheme I U y hyU hyI
  have hgn : g ≠ 0 := affineCoefficient_ne_zero M U eM _ hne
  have hnu : ¬ IsUnit g := by
    intro h
    have H := h.map (q 0).toRingHom
    change IsUnit (q 0 (affineCoefficient U eM (sectionCombination k s v))) at H
    rw [hg0] at H
    exact not_isUnit_zero H
  obtain ⟨j,n,han,b,hb,hbv,hassoc⟩ := maximal_cartier_extraction_of_iso_s01
    S.structureMap L M d hd E k s hs v hne U eL eM hnu a t ht eA
  let f := affineCoefficient U (localPowerFrame U.1 eL n) b
  have hf : f ∉ Ideal.span {g} := by
    intro h
    apply hbv
    apply (pullback_section_zero_iff_local_coefficient S.structureMap I (L.pow n) b U
      (localPowerFrame U.1 eL n)).mpr
    rw [hIp]
    exact h
  have hker := nodal_branch_kernels hR q hq (hjets 2).2 g hgn u hu hu0 hg
  have hx : restrictX ℂ (bivariateTaylor q hq f) ≠ 0 := by
    intro h
    apply hf
    rw [← hker.1]
    exact h
  have hz : restrictZ ℂ (bivariateTaylor q hq f) ≠ 0 := by
    intro h
    apply hf
    rw [← hker.2]
    exact h
  have hc := nodal_ideal_branch_sum_le_degree_s01 S L hL I hDim (L.pow n) b U y hyU hyI
    (localPowerFrame U.1 eL n) hR q hq hjets g hgn hIp u hu hu0 hg hf
  have hdeg := generated_curveDegree_of_power_iso_s01 S L hL M d E k s hs v hne hDim
  change curveDegree S L (IntegralCurve.ofIdeal S I hDim) = (d:ℤ)*selfIntersection S L at hdeg
  rw [curveDegree_pow_s01 S L hL,hdeg] at hc
  have hbound : (Module.finrank ℂ (Bivariate ℂ ⧸
      intersectionIdeal ℂ (bivariateTaylor q hq f)) : ℝ) ≤
      (n:ℝ)*(d:ℝ)*(selfIntersection S L:ℝ) := by
    rw [nodal_intersection_colength _ _ hx hz]
    change (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat+
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ):ℝ) ≤ _
    dsimp only at hc
    rw [← mul_assoc] at hc
    exact_mod_cast hc
  obtain ⟨u',hu',hg'⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hassoc' := hassoc.map (bivariateTaylor q hq).toMonoidHom
  change Associated ((bivariateTaylor q hq) (g^j*f))
    ((bivariateTaylor q hq) (affineCoefficient U eA t)) at hassoc'
  rw [map_mul,map_pow,hg'] at hassoc'
  exact nodal_associated_quadrilateral_s01 u' (bivariateTaylor q hq f)
    (bivariateTaylor q hq (affineCoefficient U eA t)) j d (selfIntersection S L) w a n
    (by exact_mod_cast hd) (by exact_mod_cast S.selfIntersection_pos L hL) hw
    (by exact_mod_cast ha) hu' hx hz hbound (by exact_mod_cast (by omega : n+j*d=a))
    hassoc' p hp
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01_oai := @OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01_oai
