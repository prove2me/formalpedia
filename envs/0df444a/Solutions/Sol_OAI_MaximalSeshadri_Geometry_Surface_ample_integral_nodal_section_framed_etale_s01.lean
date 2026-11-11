-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:37.393996+00:00
-- url     : https://prove2.me/submissions/af2613c2-33ea-4bfd-b113-7ca0e479a438

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_AnalyticCoordinates_analyticTaylor_exactJets_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_integral_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_powerSection_coefficient_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_exists_centered_rational_jet_in_open_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_dimension_le_one_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_on_any_frame_s01
import Theorems.Thm_OAI_MaximalSeshadri_QuadraticJets_etale_ordinary_node_realization_s01

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

local instance instHasAntidiagonalExponent_2_rc76f7d_1 : Finset.HasAntidiagonal Exponent :=
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
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.InvertibleLocal

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry

theorem invertible_of_affine_equations {X : Scheme} (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    InvertiblePullbackIdeal I (𝟙 X) := by
  apply invertible_of_local_equations
  intro x
  obtain ⟨U, hx, r, hr, he⟩ := hI x
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have hreg : IsLeftRegular (e.symm r) := by
    intro a b hab
    apply e.injective
    apply hr.1
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  refine ⟨U, hx, e.symm r, ⟨hreg, hreg.right_of_commute (fun a => mul_comm _ a)⟩, ?_⟩
  rw [Scheme.IdealSheafData.comap_id, IdealPullback.comap_ι_top, he,
    Ideal.map_span, Set.image_singleton]
  rfl

end
end MaximalSeshadri.InvertibleLocal
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
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma linearEquation_chart (t : σ → R) (i : σ) :
    Away.isLocalizationElem (poly_X_mem (R := R) i) (linearEquation_homogeneous t) =
      ∑ j, chartConstants i (t j) * chartCoordinate i j := by
  apply HomogeneousLocalization.val_injective _
  change (Away.mk _ _ 1 _ _).val = _
  rw [chart_val_mk]
  rw [← HomogeneousLocalization.algebraMap_apply]
  simp only [linearEquation, map_sum, map_mul, pow_one,
    HomogeneousLocalization.algebraMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [chart_val_constants, chart_val_coordinate]
  exact mul_assoc _ _ _

lemma hyperplane_chart_preimage (t : σ → R) (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (linearEquation t) =
      PrimeSpectrum.basicOpen (∑ j, chartConstants i (t j) * chartCoordinate i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (linearEquation_homogeneous t)
    (by decide), linearEquation_chart]

end

end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let ε := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  refine Eq.trans (F.map_comp_assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun morphism => F.map morphism ≫ ε.app N) h) ?_
  refine Eq.trans (F.map_comp_assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (fun morphism => F.map (λ_ M.val).hom ≫ morphism) (ε.naturality g)) ?_
  exact (Category.assoc _ _ _).symm

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_precompose {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
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
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

lemma sectionsMorphism_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : σ) (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ≫ sectionsMorphism k s hcover =
      coordinatesMap U.toScheme (U.ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrameOn (s i) U hU) (restrictSection U.ι (s j)))
        i (sectionFrameOn_normalized (s i) U hU) := by
  conv_lhs => rw [← X.homOfLE_ι hU, Category.assoc, sectionsMorphism_local,
    coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, X.homOfLE_ι]
  · funext j
    exact (sectionFrameOn_coefficient (s i) (s j) U hU).symm

lemma affine_coordinates_factor (U : X.affineOpens) (k : K →+* Γ(U.1.toScheme, ⊤))
    (a : σ → Γ(U.1.toScheme, ⊤)) (i : σ) (hi : a i = 1) :
    U.2.isoSpec.inv ≫ coordinatesMap U.1.toScheme k a i hi =
      fromUnitCoordinate (MvPolynomial.eval₂Hom (U.1.topIso.hom.hom.comp k)
        (fun j => U.1.topIso.hom (a j))) (by decide) (coordinates_X_mem i)
        (by simpa only [MvPolynomial.eval₂Hom_X', hi, map_one] using
          (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
  rw [coordinatesMap, ← Category.assoc]
  have he : U.2.isoSpec.inv ≫ U.1.toScheme.toSpecΓ = Spec.map U.1.topIso.hom := by
    let : IsAffine U.1.toScheme := U.2
    change (Spec.map U.1.topIso.hom ≫ U.1.toScheme.isoSpec.inv) ≫ _ = _
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
  rw [he]
  change Spec.map (CommRingCat.ofHom U.1.topIso.hom.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural _ _ _

lemma evalAway_coordinate {R : Type} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (j : σ) :
    evalAway (MvPolynomial.eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) (chartCoordinate i j) = a j := by
  have hh := evalAway_mk_clear (MvPolynomial.eval₂Hom k a) (poly_X_mem i)
    (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (MvPolynomial.X j)
      (by simpa using (poly_X_mem (R := K) j))
  simpa only [chartCoordinate, MvPolynomial.eval₂Hom_X', hi, one_pow, mul_one] using hh

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_MixedSections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.sectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma mixedPowMap_comp {M N P : X.Modules} (n : ℕ)
    (f : Fin n → (M ⟶ N)) (g : Fin n → (N ⟶ P)) :
    mixedPowMap n (fun i => f i ≫ g i) = mixedPowMap n f ≫ mixedPowMap n g := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change moduleTensorMap (f 0 ≫ g 0) (mixedPowMap n (fun i => f i.succ ≫ g i.succ)) =
      moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
        moduleTensorMap (g 0) (mixedPowMap n (fun i => g i.succ))
    rw [ih, moduleTensorMap_comp]

lemma mixedPowMap_restrict (U : X.Opens) {M N : X.Modules} (n : ℕ)
    (f : Fin n → (M ⟶ N)) :
    (Scheme.Modules.restrictFunctor U.ι).map (mixedPowMap n f) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      mixedPowMap n (fun i => (Scheme.Modules.restrictFunctor U.ι).map (f i)) := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 (structureSheaf U.toScheme)
    exact (congrArg (fun morphism => morphism ≫ (Scheme.Modules.restrictUnitIso U.ι).hom)
      ((Scheme.Modules.restrictFunctor U.ι).map_id (structureSheaf X))).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm)
  | succ n ih =>
    change (Scheme.Modules.restrictFunctor U.ι).map
        (moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ))) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫ _
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, ih]
    simp only [mixedPowMap]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma mixedEnd_value (n : ℕ) (f : Fin n → (structureSheaf X ⟶ structureSheaf X)) :
    endValue (mixedEnd n f) = ∏ i, endValue (f i) := by
  induction n with
  | zero => exact (endValue_id (X := X))
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (endValue_comp (f 0) (mixedEnd n (fun i => f i.succ))).trans
      (congrArg (fun value => endValue (f 0) * value) (ih (fun i => f i.succ)))

lemma mixedPowMap_unitPower (n : ℕ) (f : Fin n → (structureSheaf X ⟶ structureSheaf X)) :
    mixedPowMap n f ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ mixedEnd n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
        ((moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫ (unitPowerIso n).hom) =
      ((moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫ (unitPowerIso n).hom) ≫
        (f 0 ≫ mixedEnd n (fun i => f i.succ))
    calc
      _ = moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap (f 0) ((unitPowerIso n).hom ≫ mixedEnd n (fun i => f i.succ)) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, ih]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap (f 0) (mixedEnd n (fun i => f i.succ)) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f 0 ≫ mixedEnd n (fun i => f i.succ)) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

lemma mixedPowerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    coefficient (globalPowerFrame e n) (mixedPowerSection n s) =
      ∏ i, coefficient e (s i) := by
  have section_power : mixedPowerSection n s ≫ (globalPowerFrame e n).hom =
      mixedEnd n (fun i => s i ≫ e.hom) := by
    change ((unitPowerIso n).inv ≫ mixedPowMap n s) ≫
      (modulePowMap e.hom n ≫ (unitPowerIso n).hom) = _
    rw [Category.assoc, ← mixedPowMap_const, ← Category.assoc (mixedPowMap n s),
      ← mixedPowMap_comp, mixedPowMap_unitPower, Iso.inv_hom_id_assoc]
  exact (congrArg (fun morphism : structureSheaf X ⟶ structureSheaf X =>
    endValue morphism) section_power).trans (mixedEnd_value n (fun i => s i ≫ e.hom))

lemma restrictMixedPowerSection_factor (U : X.Opens) {M : X.Modules}
    (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    restrictSection U.ι (mixedPowerSection n s) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        mixedPowerSection n (fun i => restrictSection U.ι (s i)) := by
  let restriction : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let unitIso : restriction.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  change (unitIso.inv ≫ restriction.map ((unitPowerIso n).inv ≫ mixedPowMap n s)) ≫
      (modulePowRestrict U M n).hom =
    (unitIso.inv ≫ restriction.map (unitPowerIso n).inv ≫
      (modulePowRestrict U (structureSheaf X) n).hom ≫
      modulePowMap unitIso.hom n ≫ (unitPowerIso n).hom) ≫
        ((unitPowerIso n).inv ≫
          mixedPowMap n (fun i => unitIso.inv ≫ restriction.map (s i)))
  rw [restriction.map_comp]
  simp only [Category.assoc]
  rw [mixedPowMap_restrict, Iso.hom_inv_id_assoc, ← mixedPowMap_const,
    ← mixedPowMap_comp]
  simp only [Iso.hom_inv_id_assoc]
  rfl

lemma local_mixedPowerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (mixedPowerSection n s)) =
      endValue (powerRestrictionUnit U n).hom *
        ∏ i, coefficient e (restrictSection U.ι (s i)) := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (mixedPowerSection n s) ≫ (modulePowRestrict U M n).hom) = _
  rw [restrictMixedPowerSection_factor]
  exact (coefficient_precompose (globalPowerFrame e n) (powerRestrictionUnit U n).hom
    (mixedPowerSection n (fun i => restrictSection U.ι (s i)))).trans
      (congrArg (fun value => endValue (powerRestrictionUnit U n).hom * value)
        (mixedPowerSection_coefficient e n (fun i => restrictSection U.ι (s i))))

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_NormalizedMixed
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
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
open AlgebraicGeometry CategoryTheory
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

lemma normalized_mixed_coefficient {M : X.Modules} (s₀ : O X ⟶ M)
    (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen s₀) (n : ℕ)
    (s : Fin n → (O X ⟶ M)) :
    coefficient (sectionFrameOn (powerSection s₀ n) U
        (hU.trans (sectionOpen_le_powerSection s₀ n)))
      (restrictSection U.ι (mixedPowerSection n s)) =
      ∏ i, coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι (s i)) := by
  let e := sectionFrameOn s₀ U hU
  let f := sectionFrameOn (powerSection s₀ n) U
    (hU.trans (sectionOpen_le_powerSection s₀ n))
  let c := frameChange (localPowerFrame U e n) f
  have hc : (c : Γ(U.toScheme, ⊤)) * endValue (powerRestrictionUnit U n).hom = 1 := by
    have hh := coefficient_change (localPowerFrame U e n) f
      (restrictSection U.ι (powerSection s₀ n))
    rw [local_powerSection_coefficient_s01 U e s₀ n,
      sectionFrameOn_normalized (powerSection s₀ n) U
        (hU.trans (sectionOpen_le_powerSection s₀ n)),
      sectionFrameOn_normalized s₀ U hU, one_pow, mul_one] at hh
    exact hh.symm
  change coefficient f _ = _
  rw [coefficient_change (localPowerFrame U e n) f,
    local_mixedPowerSection_coefficient U e n s, ← mul_assoc]
  exact (congrArg (fun value => value * ∏ i,
    coefficient e (restrictSection U.ι (s i))) hc).trans (one_mul _)

lemma quarticSection_normalized {M : X.Modules} (s₀ a b c d : O X ⟶ M)
    (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen s₀) :
    coefficient (sectionFrameOn (powerSection s₀ 4) U
        (hU.trans (sectionOpen_le_powerSection s₀ 4)))
      (restrictSection U.ι (quarticSection a b c d)) =
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι a) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι b) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι c) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι d) := by
  refine (normalized_mixed_coefficient s₀ U hU 4 ![a,b,c,d]).trans ?_
  simp [Fin.prod_univ_succ, mul_assoc]

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LinearRadical
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
open MvPolynomial
variable {K σ : Type*} [Field K]

theorem span_isRadical_of_totalDegree_le_one (p : MvPolynomial σ K)
    (hp : p.totalDegree ≤ 1) : (Ideal.span ({p} : Set (MvPolynomial σ K))).IsRadical := by
  by_cases h0 : p.totalDegree = 0
  · rw [(totalDegree_eq_zero_iff_eq_C (p := p)).mp h0]
    by_cases hc : p.coeff 0 = 0
    · simpa only [hc, C_0, Ideal.span_singleton_zero] using
        (Ideal.isRadical_bot : (⊥ : Ideal (MvPolynomial σ K)).IsRadical)
    · have hu : IsUnit (C (p.coeff 0) : MvPolynomial σ K) :=
        (isUnit_iff_ne_zero.mpr hc).map C
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact le_top
  · have h1 : p.totalDegree = 1 := by omega
    have hirr : Irreducible p := irreducible_of_totalDegree_eq_one h1 (by
      intro x hx
      apply isUnit_iff_ne_zero.mpr
      intro hx0
      have hp0 : p = 0 := by
        ext d
        simpa [hx0, zero_dvd_iff] using hx d
      simp [hp0] at h1)
    exact (Ideal.span_singleton_prime hirr.ne_zero).mpr
      (irreducible_iff_prime.mp hirr) |>.isRadical

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplaneIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} {R : Type} [CommRing R]

lemma vanishingIdeal_comap_open (Z : Closeds Y) (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage f.continuous) := by
  let I := (Scheme.IdealSheafData.vanishingIdeal Z).comap f
  have hs : I.support = Z.preimage f.continuous := by
    ext x
    simp only [I, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [← hs, Scheme.IdealSheafData.vanishingIdeal_support]
  symm
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal]
  change (I.ideal U).radical = I.ideal U
  rw [show I = (Scheme.IdealSheafData.vanishingIdeal Z).comap f from rfl,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical

lemma specIdeal_support (I : Ideal R) :
    ((specIdeal I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  change ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom : Set R) = _
  rw [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

lemma specIdeal_radical_eq (I : Ideal R) (hI : I.IsRadical) :
    (specIdeal I).radical = specIdeal I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.radical_ideal, specIdeal_top]
  let e : R ≃+* Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  change (I.map e.toRingHom).radical = I.map e.toRingHom
  have he : I.map e.toRingHom = I.comap e.symm.toRingHom := Ideal.map_comap_of_equiv e
  rw [he]
  exact (hI.comap e.symm.toRingHom).radical

lemma vanishingIdeal_open_chart (D : X.Opens) (f : Spec (.of R) ⟶ X)
    [IsOpenImmersion f] (a : R)
    (hD : f ⁻¹ᵁ D = PrimeSpectrum.basicOpen a)
    (ha : (Ideal.span ({a} : Set R)).IsRadical) :
    (Scheme.IdealSheafData.vanishingIdeal D.compl).comap f =
      specIdeal (Ideal.span {a}) := by
  rw [vanishingIdeal_comap_open]
  have hs : D.compl.preimage f.continuous = (specIdeal (Ideal.span {a})).support := by
    apply SetLike.coe_injective
    rw [specIdeal_support, PrimeSpectrum.zeroLocus_span]
    change f ⁻¹' ((D : Set X)ᶜ) = PrimeSpectrum.zeroLocus {a}
    have h := congrArg (fun U : (Spec (.of R)).Opens => (U : Set (Spec (.of R)))) hD
    change f ⁻¹' (D : Set X) = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) at h
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at h
    rw [Set.preimage_compl, h]
    exact compl_compl _
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support, specIdeal_radical_eq _ ha]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ]

lemma chart_linear_equation_radical (t : σ → K) (i : σ) :
    (Ideal.span ({∑ j, chartConstants i (t j) * chartCoordinate i j} :
      Set (PolyChart (R := K) i))).IsRadical := by
  classical
  let a : PolyChart (R := K) i := ∑ j, chartConstants i (t j) * chartCoordinate i j
  let e := polynomialChartEquiv (R := K) i
  have hdeg : (e a).totalDegree ≤ 1 := by
    change (chartToPoly i a).totalDegree ≤ 1
    simp only [a, map_sum, map_mul, chartToPoly_constants, chartToPoly_coordinate]
    apply totalDegree_finsetSum_le
    intro j hj
    split_ifs
    · simp
    · apply (totalDegree_mul _ _).trans
      simp
  have hrad := span_isRadical_of_totalDegree_le_one (e a) hdeg
  have he : (Ideal.span ({e a} : Set (MvPolynomial (ChartVariables i) K))).comap
      e.toRingHom = Ideal.span {a} := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  rw [← he]
  exact hrad.comap e.toRingHom

lemma ambientHyperplane_chart (t : σ → K) (i : σ) :
    (ambientHyperplane t).comap
      (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) =
        IdealPullback.specIdeal (Ideal.span {∑ j, chartConstants i (t j) * chartCoordinate i j}) :=
  IdealPullback.vanishingIdeal_open_chart _ _ _ (hyperplane_chart_preimage t i)
    (chart_linear_equation_radical t i)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplanePullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} {R : Type} [CommRing R]

lemma specIdeal_injective : Function.Injective (specIdeal (R := R)) := by
  intro I J h
  have hh := congrArg (fun A => A.ideal ⟨⊤, isAffineOpen_top (Spec (.of R))⟩) h
  simp only [specIdeal_top] at hh
  have hh' := congrArg (Ideal.map (Scheme.ΓSpecIso (.of R)).hom.hom) hh
  have he : (Scheme.ΓSpecIso (.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom = RingHom.id R := by
    exact congrArg CommRingCat.Hom.hom (Iso.inv_hom_id (Scheme.ΓSpecIso (.of R)))
  simpa only [Ideal.map_map, he, Ideal.map_id] using hh'

lemma comap_fromSpec (I : X.IdealSheafData) (U : X.affineOpens) :
    I.comap U.2.fromSpec = specIdeal (I.ideal U) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [← U.2.isoSpec_inv_ι, Scheme.IdealSheafData.comap_comp, comap_top,
    comap_ι_top, U.2.isoSpec_inv_appTop, specIdeal_top]
  rw [Ideal.map_map]
  congr 1
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id_assoc]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma ambientHyperplane_comap_equation
    (h : X ⟶ Proj (PolyGrade K σ)) (v : σ → K) (U : X.affineOpens) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    ((ambientHyperplane v).comap h).ideal U =
      Ideal.span {∑ j, φ (chartConstants i (v j)) * φ (chartCoordinate i j)} := by
  apply specIdeal_injective
  rw [← comap_fromSpec, ← Scheme.IdealSheafData.comap_comp, ← hφ,
    Scheme.IdealSheafData.comap_comp, ambientHyperplane_chart, specIdeal_comap,
    Ideal.map_span, Set.image_singleton]
  simp only [map_sum, map_mul]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionIdeal_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (hU : U.1 ≤ SectionOpens.isoOpen (s i)) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient (sectionFrameOn (s i) U.1 hU)
        (restrictSection U.1.ι (sectionCombination k s v)))} := by
  let e := sectionFrameOn (s i) U.1 hU
  let kU := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  let a (j : σ) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι (s j)))
  have hai : a i = 1 := by simp only [a, e, sectionFrameOn_normalized, map_one]
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) :=
    evalAway (eval₂Hom kU a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hai] using (isUnit_one : IsUnit (1 : Γ(X, U.1))))
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs := by
    rw [← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hs i U.1 hU,
      affine_coordinates_factor]
    rfl
  have hcoord (j : σ) : φ (chartCoordinate i j) = a j := evalAway_coordinate kU a i hai j
  have hconst (c : K) : φ (chartConstants i c) = kU c :=
    RingHom.congr_fun (evalAway_constants kU a i hai) c
  rw [sectionIdeal, ambientHyperplane_comap_equation _ v U i φ hφ]
  congr 2
  simp only [sectionCombination, restrictSection_sum, coefficient_sum, map_sum,
    hconst, hcoord]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_restrict_scalar_comp, map_mul]
  rfl

end
end MaximalSeshadri.Projective
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
-- module Solutions.Q223_SES.Seshadri_Jets_CenteredJetChart
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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

lemma affineSectionRatios_none (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none)) :
    affineSectionRatios s U hU none = 1 := by
  simp only [affineSectionRatios, sectionFrameOn_normalized, map_one]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_CenterPrime
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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

lemma affineSectionRatios_basicOpen (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none)) (j : Option σ) :
    X.basicOpen (affineSectionRatios s U hU j) = U.1 ⊓ SectionOpens.isoOpen (s j) := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv]
  have hh : U.1.topIso.inv (affineSectionRatios s U hU j) =
      coefficient (sectionFrameOn (s none) U.1 hU) (restrictSection U.1.ι (s j)) := by
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id _
  rw [hh, ← preimage_isoOpen]
  ext x
  change (∃ q : U.1.toScheme, q.1 ∈ SectionOpens.isoOpen (s j) ∧ q.1 = x) ↔ _
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.property, hq⟩
  · rintro ⟨hx, hj⟩
    exact ⟨⟨x,hx⟩, hj, rfl⟩

theorem centered_evaluation_kernel (g : X ⟶ Spec (CommRingCat.of K))
    (s : Option σ → (O X ⟶ M)) (p : X)
    (hp : ∀ x : X, x ∉ centeredOpen s ↔ x = p)
    (U : X.affineOpens) (hpU : p ∈ U.1)
    (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (ρ : let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra;
      Γ(X, U.1) →ₐ[K] K)
    (hρ : ∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) :
    RingHom.ker ρ = (U.2.isoSpec.hom ⟨p,hpU⟩).asIdeal := by
  let q : PrimeSpectrum Γ(X, U.1) := ⟨RingHom.ker ρ, RingHom.ker_isPrime ρ⟩
  have hq : U.2.fromSpec q ∉ centeredOpen s := by
    intro h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp h
    have hmem : U.2.fromSpec q ∈ X.basicOpen (affineSectionRatios s U hU (some j)) := by
      rw [affineSectionRatios_basicOpen]
      exact ⟨by rw [← U.2.isoSpec_inv_ι]; exact (U.2.isoSpec.inv q).property, hj⟩
    have hn : q ∈ PrimeSpectrum.basicOpen (affineSectionRatios s U hU (some j)) := by
      rwa [← U.2.fromSpec_preimage_basicOpen]
    exact hn (hρ j)
  have hqp : U.2.fromSpec q = p := (hp _).mp hq
  have heq : q = U.2.isoSpec.hom ⟨p,hpU⟩ := by
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    apply (U.2.fromSpec.isOpenEmbedding.injective)
    rw [hqp]
    change p = (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p,hpU⟩
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  exact congrArg PrimeSpectrum.asIdeal heq

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_effective_cartier [IsIntegral X] (L : LineBundle X)
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    InvertiblePullbackIdeal (sectionIdeal k s hs v) (𝟙 X) := by
  apply MaximalSeshadri.InvertibleLocal.invertible_of_affine_equations
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  obtain ⟨_, ⟨U,hUa,rfl⟩,hxU,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (SectionOpens.isoOpen (s i)).isOpen
  let A : X.affineOpens := ⟨U,hUa⟩
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let e := sectionFrameOn (s i) U hU
  exact ⟨A,hxU,_,L.section_coefficient_regular _ hv A e,
    sectionIdeal_on k s hs v A i hU⟩

lemma idealSheaf_mem_support_of_prime (J : X.IdealSheafData)
    (U : X.affineOpens) (p : X) (hpU : p ∈ U.1)
    (hJ : J.ideal U ≤ (U.2.isoSpec.hom ⟨p,hpU⟩).asIdeal) : p ∈ J.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hpU]
  have hmem : U.2.isoSpec.hom ⟨p,hpU⟩ ∈ PrimeSpectrum.zeroLocus (J.ideal U) := hJ
  rw [← U.2.fromSpec_preimage_zeroLocus] at hmem
  have he : U.2.fromSpec (U.2.isoSpec.hom ⟨p,hpU⟩) = p := by
    change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p,hpU⟩ = p
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  change U.2.fromSpec (U.2.isoSpec.hom ⟨p,hpU⟩) ∈ X.zeroLocus (U := U.1) (J.ideal U) at hmem
  rwa [he] at hmem
end
end MaximalSeshadri.Projective
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
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma local_unramified_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal R) (maximalIdeal S)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  have H : ((maximalIdeal S).height : WithBot ℕ∞) ≤ (maximalIdeal R).height := by exact_mod_cast h
  simpa only [maximalIdeal_height_eq_ringKrullDim] using H

lemma etale_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro q hq
  let := hq
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq := Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have H := local_unramified_dimension_le Rp Sq
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq] at H
  exact H.trans ((ringKrullDim_le_iff_height_le _).mp le_rfl inferInstance)

lemma etale_surface_dimension_le (K S : Type*) [Field K] [CommRing S]
    [Algebra (MvPolynomial (Fin 2) K) S]
    [Algebra.Etale (MvPolynomial (Fin 2) K) S] : ringKrullDim S ≤ 2 := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 2) K) S
  have h := etale_dimension_le (MvPolynomial (Fin 2) K) S
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing] using h

end
end MaximalSeshadri.EtaleDimension
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
-- module Solutions.Q223_SES.Seshadri_Jets_AnalyticFullRank
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

open AlgebraicJets FormalCoordinates MvPolynomial
variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma exactJets_injective [IsNoetherianRing S] [IsDomain S]
    (ρ : S →ₐ[ℂ] ℂ) (τ : S →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hk : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp τ.toRingHom) =
        (RingHom.ker ρ)^n) : Function.Injective τ := by
  apply (injective_iff_map_eq_zero τ).mpr
  intro s hs
  have hm : s ∈ ⨅ n : ℕ, (RingHom.ker ρ)^n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [← hk n]
    change Ideal.Quotient.mk _ (τ s) = 0
    rw [hs, map_zero]
  rwa [Ideal.iInf_pow_eq_bot_of_isDomain (I := RingHom.ker ρ)
    (RingHom.ker_ne_top _)] at hm

end
end MaximalSeshadri.AnalyticCoordinates

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
-- module Solutions.Q223_SES.Seshadri_Jets_QuadraticJets
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.Projective

variable {K A σ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype σ]

lemma coefficientForm_eval (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (l : JetAlgebra (Fin 2) K 3 →ₗ[K] K) (v : QuarticIndex σ → K) :
    aeval v (coefficientForm a τ l) = l (τ (quarticCombination a v)) := by
  simp [coefficientForm, quarticCombination, map_sum, mul_comm, smul_eq_mul]

lemma discriminantPolynomial_eval (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (v : QuarticIndex σ → K) :
    aeval v (discriminantPolynomial a τ) = discriminant (τ (quarticCombination a v)) := by
  simp only [discriminantPolynomial, map_sub, map_pow, map_mul, map_ofNat,
    coefficientForm_eval, discriminant]

lemma quarticCombination_add (a : Option σ → A) (v w : QuarticIndex σ → K) :
    quarticCombination a (v + w) = quarticCombination a v + quarticCombination a w := by
  simp [quarticCombination, add_smul, Finset.sum_add_distrib]

lemma quarticCombination_single [DecidableEq σ] (a : Option σ → A) (j : QuarticIndex σ) (c : K) :
    quarticCombination a (Pi.single j c) = c • quarticValue a j := by
  classical
  simp [quarticCombination, Pi.single_apply, ite_smul]

lemma discriminant_squares :
    discriminant (K := K) (Ideal.Quotient.mk _ ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2)) = -4 := by
  have h01 : (Finsupp.single (0 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have h11a : exponent11 ≠ exponent20 := by
    intro h
    have := DFunLike.congr_fun h 1
    simp [exponent11, exponent20] at this
  have h11b : exponent11 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent11, exponent02] at this
  change (((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent11)^2 -
    4 * ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent20 *
      ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent02 = -4
  change exponent11 ≠ Finsupp.single 0 2 at h11a
  change exponent11 ≠ Finsupp.single 1 2 at h11b
  simp [AddMonoidAlgebra.coeff_add, coeff_X_pow, exponent20, exponent02,
    h01, h01.symm, Ne.symm h11a, Ne.symm h11b]

lemma discriminantPolynomial_ne_zero [CharZero K]
    (a : Option σ → A) (h0 : a none = 1) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (i j : σ)
    (hi : τ (a (some i)) = -Ideal.Quotient.mk _ (X 0))
    (hj : τ (a (some j)) = -Ideal.Quotient.mk _ (X 1)) :
    discriminantPolynomial a τ ≠ 0 := by
  classical
  let v : QuarticIndex σ → K := Pi.single (i,i,none,none) 1 + Pi.single (j,j,none,none) 1
  have hv : τ (quarticCombination a v) =
      Ideal.Quotient.mk _ ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2) := by
    simp only [v, quarticCombination_add, quarticCombination_single, one_smul,
      quarticValue, h0, mul_one, map_add, map_mul, hi, hj]
    simp only [map_pow]
    ring
  intro hz
  have hh := discriminantPolynomial_eval a τ v
  rw [hz, map_zero, hv, discriminant_squares] at hh
  norm_num at hh

lemma quarticCombination_mem_square (a : Option σ → A) (ρ : A →ₐ[K] K)
    (ha : ∀ i : σ, ρ (a (some i)) = 0) (v : QuarticIndex σ → K) :
    quarticCombination a v ∈ (RingHom.ker ρ)^2 := by
  apply Ideal.sum_mem
  intro j hj
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_right
  apply Ideal.mul_mem_right
  rw [pow_two]
  exact Ideal.mul_mem_mul (ha j.1) (ha j.2.1)

end
end MaximalSeshadri.QuadraticJets

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

end
end MaximalSeshadri.AnalyticCoordinates

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_BranchDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem formal_branch_dimension_eq_one {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0)
    [hgp : (Ideal.span {g}).IsPrime]
    (φ : R →+* PowerSeries K) (hφg : φ g = 0)
    (hbranch : ∃ a : R, PowerSeries.constantCoeff (φ a) = 0 ∧ φ a ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {g}) = 1 := by
  apply le_antisymm (principal_curve_dimension_le_one hd g hg)
  have hI : Ideal.span {g} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr hφg
  let ψ := Ideal.Quotient.lift (Ideal.span {g}) φ hI
  let m := RingHom.ker (PowerSeries.constantCoeff.comp ψ)
  have hm : m ≠ ⊥ := by
    obtain ⟨a, ha, han⟩ := hbranch
    intro he
    have ha' : Ideal.Quotient.mk (Ideal.span {g}) a ∈ m := ha
    rw [he, Ideal.mem_bot] at ha'
    have : φ a = 0 := by
      change ψ (Ideal.Quotient.mk (Ideal.span {g}) a) = 0
      rw [ha', map_zero]
    exact han this
  apply Order.one_le_krullDim_iff.mpr
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨m, RingHom.ker_isPrime _⟩, ?_⟩
  change (⊥ : Ideal (R ⧸ Ideal.span {g})) < m
  exact bot_lt_iff_ne_bot.mpr hm

open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.FormalCoordinates
open scoped Topology

lemma nodal_principal_dimension_eq_one {R : Type*} [CommRing R] [Algebra ℂ R]
    [IsDomain R] (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp
      (analyticTaylor q hq).toRingHom))
    (g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    ringKrullDim (R ⧸ Ideal.span {g}) = 1 := by
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hw := (bivariate_branch_witnesses (analyticTaylor q hq) hs).1
  have he (a : R) : (binaryEquiv ℂ) (analyticTaylor q hq a) = bivariateTaylor q hq a := by
    rw [bivariateTaylor_eq]; rfl
  simp only [he] at hw
  apply formal_branch_dimension_eq_one hd g hg0
    ((restrictX ℂ).comp (bivariateTaylor q hq)).toRingHom _ hw
  change restrictX ℂ (bivariateTaylor q hq g) = 0
  simp [hgU, nodeEquation]

end
end MaximalSeshadri.NodalLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace

lemma subscheme_dimension_ge_affine_chart {X : Scheme}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ringKrullDim (Γ(X,U.1) ⧸ I.ideal U) ≤ topologicalKrullDim I.subscheme := by
  let := I.subschemeCover.map_prop U
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (I.subschemeCover.f U).isOpenEmbedding.isInducing.topologicalKrullDim_le

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_OrdinaryQuadraticQuartic
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme} {M : X.Modules}

lemma quarticCombination_coefficient
    (g : X ⟶ Spec (CommRingCat.of K)) (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (U : X.affineOpens)
    (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (hk : ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c)
    (v : QuarticIndex σ → K) :
    let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
    U.1.topIso.hom (coefficient
      (sectionFrameOn (powerSection (s none) 4) U.1
        (hU.trans (sectionOpen_le_powerSection (s none) 4)))
      (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v))) =
      quarticCombination (affineSectionRatios s U hU) v := by
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  simp only [sectionCombination, restrictSection_sum, coefficient_sum,
    map_sum, coefficient_restrict_scalar_comp, map_mul, hk]
  unfold quarticCombination
  apply Finset.sum_congr rfl
  intro j hj
  rw [doublePointQuartics, quarticSection_normalized (s none) _ _ _ _ U.1 hU]
  simp only [map_mul, affineSectionRatios, quarticValue, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra]

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_EtaleNodalDivisor
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_integral_nodal_section_framed_etale_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
          topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1 ∧
          InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs v) (𝟙 S.scheme) ∧
          y ∈ (doublePointQuarticIdeal k s hs v).support ∧
          sectionCombination k (doublePointQuartics s) v ≠ 0 ∧
          Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
            (centeredOpen s).ι ≫ S.structureMap) ∧
          let f := U.1.topIso.hom (coefficient
            (sectionFrameOn (powerSection (s none) 4) U.1
              (hU.trans (sectionOpen_le_powerSection (s none) 4)))
            (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
          ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
            ringKrullDim Γ(S.scheme,U.1) ≤ 2 ∧ (Ideal.span {f}).IsPrime ∧
            f ≠ 0 ∧ q 0 f = 0 ∧
            RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
            ∃ hq : (∀ a, AnalyticAt ℂ (fun z => q z a) 0),
            ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
              (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
              (∃ i : Fin 2 → Fin N, ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
                HasFDerivAt (fun z =>
                  (q z (-affineSectionRatios s U hU (some (i 1))),
                   q z (-affineSectionRatios s U hU (some (i 0)))))
                  (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
              (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                (analyticTaylor q hq).toRingHom) =
                  (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal^n ∧
                Function.Surjective ((Ideal.Quotient.mk
                  (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                  (analyticTaylor q hq).toRingHom)) ∧
              Function.Injective (analyticTaylor q hq) ∧
              ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  obtain ⟨d, hd, N, n, s, hs, e, y, hy, hc, hall⟩ := S.ample_quartic_integral_s01 L hL
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let := hc
  have hbase : sectionsMorphism k s hs ≫ projectiveToSpec = S.structureMap := by
    change _ ≫ projectiveBase = _
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap S.structureMap)
  obtain ⟨W,hyW,⟨eW⟩⟩ := L.locallyRankOne y
  obtain ⟨U, hyU, hUW, hU, i, ρ, τ, hρ, hτ, haug, hi, het, hk⟩ :=
    exists_centered_rational_jet_in_open_s01 S.structureMap k s hs hbase y ((hy y).mpr rfl) W hyW
  let : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
  let a := affineSectionRatios s U hU
  let P := discriminantPolynomial a τ
  have hP : P ≠ 0 := discriminantPolynomial_ne_zero a
    (affineSectionRatios_none s U hU) τ (i 0) (i 1) (hi 0) (hi 1)
  let Q := rename e.symm P
  have hQ : Q ≠ 0 := by
    intro h
    exact hP ((MvPolynomial.renameEquiv ℂ e.symm).injective (by simpa using h))
  obtain ⟨v, hv, hint, hsm⟩ := hall Q hQ
  let f := quarticCombination a (v ∘ e.symm)
  have hf : f ∈ (RingHom.ker ρ)^2 := quarticCombination_mem_square a ρ hρ _
  have hdisc : discriminant (τ f) ≠ 0 := by
    rw [← discriminantPolynomial_eval]
    exact fun hz => hv (by simpa only [Q, P, aeval_rename] using hz)
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) :=
    (eval₂Hom (openScalars S.structureMap U.1) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (openScalars S.structureMap U.1) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) := het
  have hρx (j : Fin 2) : ρ (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) (X j)) = 0 := by
    change ρ ((eval₂Hom _ _) (X j)) = 0
    rw [eval₂Hom_X', map_neg, hρ, neg_zero]
  have hτx (j : Fin 2) : τ (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) (X j)) =
      Ideal.Quotient.mk _ (X j) := by
    change τ ((eval₂Hom _ _) (X j)) = _
    rw [eval₂Hom_X', map_neg, hi, neg_neg]
  obtain ⟨q,hq₀,hq,u,hu,hu₀,heq,⟨E,hE⟩,V,hV,hV₀,hinj⟩ :=
    etale_ordinary_node_realization_s01 ρ hρx τ hτ.ge hτx f hf hdisc
  have hjets := analyticTaylor_exactJets_s01 q hq E hE
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  let : IsNoetherianRing Γ(S.scheme, U.1) := IsLocallyNoetherian.component_noetherian U
  have hinjective : Function.Injective (analyticTaylor q hq) :=
    exactJets_injective (q 0) (analyticTaylor q hq) (fun n => (hjets n).1)
  have hfn : f ≠ 0 := by
    intro he
    apply hdisc
    simp [he, discriminant]
  have hf0 : q 0 f = 0 := by
    rw [hq₀]
    exact (Ideal.pow_le_self (by decide : 2 ≠ 0) hf)
  have hsne : sectionCombination k (doublePointQuartics s) (v ∘ e.symm) ≠ 0 := by
    intro hz
    apply hfn
    dsimp only [f, a]
    rw [← quarticCombination_coefficient S.structureMap k s U hU hk,
      hz, restrictSection_zero, coefficient_zero, map_zero]
  have combination_eq := sectionCombination_extend_zero k (augmentedQuartics s) (v ∘ e.symm)
  have ideal_eq : (doublePointQuarticIdeal k s hs (v ∘ e.symm)).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient
        (sectionFrameOn (powerSection (s none) 4) U.1
          (hU.trans (sectionOpen_le_powerSection (s none) 4)))
        (restrictSection U.1.ι
          (sectionCombination k (doublePointQuartics s) (v ∘ e.symm))))} :=
    (sectionIdeal_on_any_frame_s01 k (augmentedQuartics s) (augmentedQuartics_cover s hs)
      (fun index => index.elim 0 (v ∘ e.symm)) U
      (sectionFrameOn (powerSection (s none) 4) U.1
        (hU.trans (sectionOpen_le_powerSection (s none) 4)))).trans
      (congrArg (fun sectionValue : O S.scheme ⟶ ((L.pow d).pow 4).sheaf =>
        Ideal.span {U.1.topIso.hom (coefficient
          (sectionFrameOn (powerSection (s none) 4) U.1
            (hU.trans (sectionOpen_le_powerSection (s none) 4)))
          (restrictSection U.1.ι sectionValue))}) combination_eq)
  have hcart : InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs (v ∘ e.symm))
      (𝟙 S.scheme) := by
    apply sectionIdeal_effective_cartier ((L.pow d).pow 4)
    intro zero_eq
    exact hsne (combination_eq.symm.trans zero_eq)
  have hsupport : y ∈ (doublePointQuarticIdeal k s hs (v ∘ e.symm)).support := by
    apply idealSheaf_mem_support_of_prime _ U y hyU
    rw [ideal_eq]
    rw [quarticCombination_coefficient S.structureMap k s U hU hk,
      ← centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ]
    apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Ideal.pow_le_self (by decide : 2 ≠ 0) hf
  let : IsIntegral (doublePointQuarticIdeal k s hs (v ∘ e.symm)).subscheme := hint
  have hprime := ideal_prime_of_integral_subscheme
    (doublePointQuarticIdeal k s hs (v ∘ e.symm)) U y hyU hsupport
  rw [ideal_eq] at hprime
  have hdim : topologicalKrullDim
      (doublePointQuarticIdeal k s hs (v ∘ e.symm)).subscheme = 1 := by
    apply le_antisymm
    · let : IsClosedImmersion (show S.scheme ⟶
          Proj (PolyGrade ℂ (Fin (S.embeddingDimension + 1))) from S.embedding) :=
        S.closedImmersion
      apply sectionIdeal_dimension_le_one_s01 S.structureMap S.embedding S.overComplex
        ((L.pow d).pow 4)
      intro zero_eq
      exact hsne (combination_eq.symm.trans zero_eq)
    · have hfp : (Ideal.span {f}).IsPrime := by
        dsimp only [f,a]
        rw [← quarticCombination_coefficient S.structureMap k s U hU hk]
        exact hprime
      let := hfp
      have hd := MaximalSeshadri.NodalLocal.nodal_principal_dimension_eq_one
        (MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ _)
        q hq (hjets 2).2 f hfn u hu hu₀ heq
      have H := subscheme_dimension_ge_affine_chart
        (doublePointQuarticIdeal k s hs (v ∘ e.symm)) U
      rw [ideal_eq] at H
      have he := quarticCombination_coefficient S.structureMap k s U hU hk (v ∘ e.symm)
      have dimension_eq := congrArg (fun coefficientValue : Γ(S.scheme,U.1) =>
        ringKrullDim (Γ(S.scheme,U.1) ⧸ Ideal.span {coefficientValue})) he
      exact (dimension_eq.trans hd) ▸ H
  refine ⟨d, hd, N, s, hs, y, U, hyU, hU, frameOnSmaller eW U.1 hUW, (fun j => -a (some (i j))), het, v ∘ e.symm, hy, hint, hdim, hcart, hsupport, hsne, hsm, q,
    MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ _, hprime, ?_, ?_, ?_,
    hq, u, hu, hu₀, ?_, ⟨i,E,?_⟩, ?_, hinjective, V,hV,hV₀,hinj⟩
  · dsimp only
    rwa [quarticCombination_coefficient S.structureMap k s U hU hk]
  · dsimp only
    rwa [quarticCombination_coefficient S.structureMap k s U hU hk]
  · rw [hq₀]
    exact centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ
  · dsimp only
    rw [quarticCombination_coefficient S.structureMap k s U hU hk]
    exact heq
  · simpa only [RingHom.algebraMap_toAlgebra, eval₂Hom_X'] using hE
  · intro n
    have hn := hjets n
    rw [hq₀, centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ] at hn
    exact hn
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01_oai
