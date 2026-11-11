-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:15.842615+00:00
-- url     : https://prove2.me/submissions/2daba04d-f57f-4d2d-a11f-35ada231426f

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_exists_all_section_quadrilateral_etale_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_germ_jet_test_s01

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

lemma analyticFormal_constantCoeff (f : analyticFunctionAlgebra) :
    constantCoeff (constantCoeff (analyticFormal f)) = f.val (0,0) := by
  have h := analyticCoefficients_eq_derivative f 0 0
  simpa [analyticFormal, biSeries, constantCoeff_mk, iteratedDeriv_zero] using h

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
-- module Solutions.Q223_SES.Seshadri_Jets_PolynomialJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

lemma jetAugment_ker (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := R) n hn) =
      (idealOfVars σ R).map (Ideal.Quotient.mk ((idealOfVars σ R) ^ n)) := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, jetAugment_mk,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    exact ⟨p, by rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker], rfl⟩
  · rintro ⟨f, hf, hfp⟩
    have hd : f - p ∈ (idealOfVars σ R) ^ n := Ideal.Quotient.eq.mp hfp
    have hd' := (mem_pow_idealOfVars_iff' n (f - p)).mp hd 0 (by simpa using hn)
    have hf' : constantCoeff f = 0 := by
      rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker] at hf
    change constantCoeff (f - p) = 0 at hd'
    simpa [map_sub, hf'] using hd'

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma jetAugment_ker_pow (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := S) n hn) ^ n = 0 := by
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end
end MaximalSeshadri.AlgebraicJets


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

variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma analyticTaylor_constantCoeff (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.constantCoeff (analyticTaylor q hq s) = q 0 s := by
  rw [← binaryEquiv_constantCoeff]
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact analyticFormal_constantCoeff _

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma formalTrunc_augment (n : ℕ) (hn : 0 < n) (f : MvPowerSeries σ F) :
    jetAugment n hn (formalTrunc n f) = MvPowerSeries.constantCoeff f := by
  change jetAugment n hn (Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f)) = _
  rw [jetAugment_mk, MvPowerSeries.constantCoeff_truncTotal_eq_ite, ite_eq_left hn]

end
end MaximalSeshadri.AlgebraicJets


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
-- module Solutions.Q223_SES.Seshadri_Jets_JetVanishing
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPowerSeries
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.FormalCoordinates
open scoped Topology

lemma formalTrunc_eq_zero_iff {σ F : Type*} [Finite σ] [Field F]
    (n : ℕ) (f : MvPowerSeries σ F) :
    formalTrunc n f = 0 ↔ ∀ e, e.degree < n → MvPowerSeries.coeff e f = 0 := by
  change Ideal.Quotient.mk _ (f.truncTotal n) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor <;> intro h e he
  · simpa only [MvPowerSeries.coeff_truncTotal f he] using h e he
  · simpa only [MvPowerSeries.coeff_truncTotal f he] using h e he

lemma binaryDegree (a b : ℕ) :
    (Finsupp.cons b (Finsupp.cons a (0 : Fin 0 →₀ ℕ))).degree = a + b := by
  change (Finsupp.cons b (Finsupp.cons a (0 : Fin 0 →₀ ℕ))).sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Fin.sum_univ_zero, add_zero]
  omega

lemma analyticTrunc_zero_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (n : ℕ) (hn : 0 < n) (a : A) (ha : a ∈ (RingHom.ker (q 0))^n) :
    formalTrunc n (analyticTaylor q hq a) = 0 := by
  let ψ := (formalTrunc n).comp (analyticTaylor q hq)
  have hmap : (RingHom.ker (q 0)).map ψ.toRingHom ≤
      RingHom.ker (jetAugment (σ := Fin 2) (R := ℂ) n hn) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change jetAugment n hn (formalTrunc n (analyticTaylor q hq b)) = 0
    rw [formalTrunc_augment n hn, analyticTaylor_constantCoeff]
    exact hb
  have hmapn : ((RingHom.ker (q 0))^n).map ψ.toRingHom ≤ ⊥ := by
    rw [Ideal.map_pow]
    calc
      _ ≤ RingHom.ker (jetAugment (σ := Fin 2) (R := ℂ) n hn)^n :=
        pow_le_pow_left' hmap n
      _ = ⊥ := jetAugment_ker_pow n hn
  exact (Ideal.mem_bot).mp (hmapn (Ideal.mem_map_of_mem _ ha))

theorem mixedDeriv_zero_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (n : ℕ)
    (a : A) (ha : a ∈ (RingHom.ker (q 0))^n)
    (i j : ℕ) (hij : i + j < n) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => q (x,z) a) 0) 0 = 0 := by
  have hz := analyticTrunc_zero_of_ideal_power q hq n (by omega) a ha
  have hc := (formalTrunc_eq_zero_iff n _).mp hz
    (Finsupp.cons j (Finsupp.cons i 0)) (by simpa only [binaryDegree] using hij)
  have hb : biCoeff (analyticFormal (analyticPullback q hq a)) (i,j) = 0 := by
    have hb := binaryEquiv_coeff (analyticTaylor q hq a) i j
    change biCoeff (binaryEquiv ℂ (analyticTaylor q hq a)) (i,j) = _ at hb
    rw [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] at hb
    exact hb.trans hc
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq a) i j
  have hb' : analyticCoefficients (analyticPullback q hq a) (i,j) = 0 := by
    change biCoeff (biSeries (analyticCoefficients (analyticPullback q hq a))) (i,j) = 0 at hb
    rwa [biCoeff_biSeries] at hb
  rw [hb', zero_mul, zero_mul] at hd
  exact hd.symm

lemma mixedDeriv_shift (f : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (i j : ℕ) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (p + (x,z))) 0) 0 =
      iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2 := by
  change iteratedDeriv j (fun z =>
    iteratedDeriv i (fun x => f (p.1 + x, p.2 + z)) 0) 0 = _
  have hx (z : ℂ) : iteratedDeriv i (fun x => f (p.1 + x, p.2 + z)) 0 =
      iteratedDeriv i (fun x => f (x, p.2 + z)) p.1 := by
    exact (congrFun (iteratedDeriv_comp_const_add i
      (fun x => f (x, p.2 + z)) p.1) 0).trans (by rw [add_zero])
  simp_rw [hx]
  exact (congrFun (iteratedDeriv_comp_const_add j
    (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2) 0).trans (by rw [add_zero])

theorem mixedDeriv_zero_at_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (p : ℂ × ℂ)
    (hq : ∀ a, AnalyticAt ℂ (fun z => q (p + z) a) 0)
    (n : ℕ)
    (a : A) (ha : a ∈ (RingHom.ker (q p))^n)
    (i j : ℕ) (hij : i + j < n) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => q (x,z) a) p.1) p.2 = 0 := by
  have hz := mixedDeriv_zero_of_ideal_power (fun z => q (p + z)) hq n
    a (by simpa only [add_zero] using ha) i j hij
  exact (mixedDeriv_shift (fun z => q z a) p i j).symm.trans hz

end
end MaximalSeshadri.AlgebraicJets

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_ActualInterpolation
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MaximalSeshadri.ActualInterpolation
noncomputable section
open scoped Topology
open Filter
open MaximalSeshadri.AnalyticCoordinates

theorem exists_common_representation (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (φ : V →ₗ[ℂ] (ℂ × ℂ → ℂ)) (R : ℝ) (hR : 0 < R)
    (hs : ∀ c ∈ V, DerivativeSummable c R)
    (hrep : ∀ c : V, φ c =ᶠ[𝓝 0] (fun p => seriesEval c p.1 p.2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ∧ ∀ p : ℂ × ℂ, ‖p‖ < ε →
      ∀ c : V, φ c p = seriesEval c p.1 p.2 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ V
  have hh : ∀ᶠ p : ℂ × ℂ in 𝓝 0, ∀ i, φ (b i) p = seriesEval (b i) p.1 p.2 :=
    Filter.eventually_all.mpr (fun i => hrep (b i))
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨min ε R, lt_min hε hR, min_le_right _ _, ?_⟩
  intro p hp c
  have hεp : dist p 0 < ε := by
    simpa only [dist_zero_right] using lt_of_lt_of_le hp (min_le_left _ _)
  have hpR : ‖p‖ < R := lt_of_lt_of_le hp (min_le_right _ _)
  have hx : ‖p.1‖ ≤ R := (norm_fst_le p).trans hpR.le
  have hz : ‖p.2‖ ≤ R := (norm_snd_le p).trans hpR.le
  have hm : (LinearMap.proj p).comp φ = seriesValueMap V R hs p hx hz := by
    apply b.ext
    intro i
    exact heq hεp i
  exact LinearMap.congr_fun hm c

lemma mixedDeriv_congr_on_ball (f g : ℂ × ℂ → ℂ) (ε : ℝ)
    (hfg : ∀ q : ℂ × ℂ, ‖q‖ < ε → f q = g q)
    (p : ℂ × ℂ) (hp : ‖p‖ < ε) (i j : ℕ) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2 =
      iteratedDeriv j (fun z => iteratedDeriv i (fun x => g (x,z)) p.1) p.2 := by
  have hh : (fun z => f (p + z)) =ᶠ[𝓝 0] (fun z => g (p + z)) := by
    have hn : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖p + z‖ < ε := by
      exact (continuous_const.add continuous_id).continuousAt.norm.eventually_lt_const
        (by simpa using hp)
    exact hn.mono (fun z hz => hfg (p + z) hz)
  have hd := mixedDeriv_congr_germ _ _ hh i j
  rw [MaximalSeshadri.AlgebraicJets.mixedDeriv_shift,
    MaximalSeshadri.AlgebraicJets.mixedDeriv_shift] at hd
  exact hd

variable {A M : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup M] [Module ℂ M]

theorem idealPower_test_of_series_test
    (coord : M →ₗ[ℂ] A) (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hinj : Function.Injective (germCoefficients coord q hq))
    [FiniteDimensional ℂ (LinearMap.range (germCoefficients coord q hq))]
    (U : Set (ℂ × ℂ)) (hU : IsOpen U) (h0 : 0 ∈ U) (hqinj : Set.InjOn q U)
    (hqat : ∀ p ∈ U, ∀ a, AnalyticAt ℂ (fun z => q (p + z) a) 0)
    (r m : ℕ) (R : ℝ) (hR : 0 < R)
    (hs : ∀ c ∈ LinearMap.range (germCoefficients coord q hq), DerivativeSummable c R)
    (htest : ∀ ε : ℝ, 0 < ε → ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, ‖(p i).1‖ < min ε R ∧ ‖(p i).2‖ < min ε R) ∧
      Function.Injective (fun c : LinearMap.range (germCoefficients coord q hq) =>
        Interpolation.finiteJetColumn r m p (seriesEval c))) :
    ∃ p : Fin r → A →ₐ[ℂ] ℂ, Function.Injective p ∧
      (∀ i, ∃ z ∈ U, p i = q z) ∧
      ∀ s : M, (∀ i, coord s ∈ (RingHom.ker (p i))^m) → s = 0 := by
  classical
  let C := germCoefficients coord q hq
  let e : M ≃ₗ[ℂ] LinearMap.range C := LinearEquiv.ofInjective C hinj
  let ev : A →ₗ[ℂ] (ℂ × ℂ → ℂ) := LinearMap.pi (fun p => (q p).toLinearMap)
  let φ : LinearMap.range C →ₗ[ℂ] (ℂ × ℂ → ℂ) := ev.comp (coord.comp e.symm.toLinearMap)
  have hrep : ∀ c : LinearMap.range C,
      φ c =ᶠ[𝓝 0] (fun p => seriesEval c p.1 p.2) := by
    intro c
    have hc : C (e.symm c) = (c : Exponent → ℂ) :=
      congrArg Subtype.val (e.apply_symm_apply c)
    have hh := (analyticCoefficients_spec (analyticPullback q hq (coord (e.symm c)))).2
    change (fun p => q p (coord (e.symm c))) =ᶠ[𝓝 0]
      (fun p => seriesEval (C (e.symm c)) p.1 p.2) at hh
    change (fun p => q p (coord (e.symm c))) =ᶠ[𝓝 0] _
    simpa only [hc] using hh
  obtain ⟨ε, hε, _, hεrep⟩ := exists_common_representation
    (LinearMap.range C) φ R hR hs hrep
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨p, hp, hpn, hpjet⟩ := htest (min ε δ) (lt_min hε hδ)
  have hpe (i : Fin r) : ‖p i‖ < ε := by
    rw [Prod.norm_def]
    exact max_lt ((hpn i).1.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      ((hpn i).2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hpU (i : Fin r) : p i ∈ U := by
    apply hδU
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    exact max_lt ((hpn i).1.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      ((hpn i).2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  refine ⟨fun i => q (p i), fun i j hij => hp (hqinj (hpU i) (hpU j) hij),
    fun i => ⟨p i, hpU i, rfl⟩, ?_⟩
  intro s hs0
  apply e.injective
  apply hpjet
  funext j
  simp only [Interpolation.finiteJetColumn]
  split_ifs with hj
  · have hd := AlgebraicJets.mixedDeriv_zero_at_of_ideal_power q (p j.1)
      (hqat (p j.1) (hpU j.1)) m (coord s) (hs0 j.1) j.2.1 j.2.2 hj
    have heq := mixedDeriv_congr_on_ball (φ (e s))
      (fun z => seriesEval (e s) z.1 z.2) ε
      (fun z hz => hεrep z hz (e s)) (p j.1) (hpe j.1) j.2.1 j.2.2
    have hφ : φ (e s) = (fun z => q z (coord s)) := by
      change ev (coord (e.symm (e s))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hφ] at heq
    rw [← heq, hd]
    have he0 : (e 0 : Exponent → ℂ) = 0 := by simp
    rw [he0]
    simp [seriesEval]
  · rfl

end
end MaximalSeshadri.ActualInterpolation

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionGermSystem
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma Surface.sections_finite (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.Finite ℂ (GlobalSections S.scheme M.sheaf) := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite_s01 L hL M
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  exact Module.Finite.equiv (show cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf from
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x })

lemma germCoefficients_eq_bivariate {A M : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) (s : M) :
    germCoefficients coord q hq s = NodalLocal.bivariateCoeff (bivariateTaylor q hq (coord s)) := by
  funext e
  exact (biCoeff_biSeries _ e).symm

lemma germCoefficients_injective_of_taylor {A M : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hc : Function.Injective coord) (ht : Function.Injective (analyticTaylor q hq)) :
    Function.Injective (germCoefficients coord q hq) := by
  intro s t h
  apply hc
  apply ht
  exact congrArg (fun c => (FormalCoordinates.binaryEquiv ℂ).symm (biSeries c)) h
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
-- module Solutions.Q223_SES.Seshadri_Interpolation_GermInterpolation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

theorem exists_node_weight_range (d H : ℝ) (hd : 0 < d) (hH : 0 < H) :
    ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2 := by
  refine ⟨d ^ 2 * H + 2, ?_, ?_⟩
  · have hpos : 0 < d ^ 2 * H := mul_pos (sq_pos_of_pos hd) hH
    linarith
  intro t ht
  have hpos : 0 < d ^ 2 * H := mul_pos (sq_pos_of_pos hd) hH
  have ht0 : 0 < t := by linarith
  nlinarith [mul_pos ht0 (sub_pos.mpr ht)]

end MaximalSeshadri.Interpolation

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_UniformAnalyticAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem exists_uniform_analytic_neighborhood
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ p ∈ U, ∀ a, AnalyticAt ℂ (fun z => q (p+z) a) 0 := by
  classical
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := ℂ) (A := A)
  let U : Set (ℂ × ℂ) := ⋂ a ∈ s, {p | AnalyticAt ℂ (fun z => q z a) p}
  have hU : IsOpen U := isOpen_biInter_finset fun a ha => isOpen_analyticAt ℂ _
  have h0 : (0 : ℂ × ℂ) ∈ U := by simp only [U, Set.mem_iInter]; exact fun a ha => hq a
  refine ⟨U,hU,h0,?_⟩
  intro p hp a
  have hall : AnalyticAt ℂ (fun z => q z a) p := by
    have ha : a ∈ Algebra.adjoin ℂ (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp a) ha)
    | algebraMap c =>
      convert (analyticAt_const (𝕜 := ℂ) (v := c) (x := p)) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      exact (q z).commutes c
    | add a b ha hb ia ib =>
      convert ia.add ib using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      exact map_add (q z) a b
    | mul a b ha hb ia ib =>
      have he : (fun z => q z (a*b)) = (fun z => q z a * q z b) :=
        funext fun z => map_mul (q z) a b
      rw [he]
      exact ia.mul ib
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ => p+z) 0 := analyticAt_const.add analyticAt_id
  have hall' : AnalyticAt ℂ (fun z => q z a) (p+0) := by simpa using hall
  exact hall'.comp hh
end
end MaximalSeshadri.AnalyticCoordinates

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleAffineTest
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
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

theorem Surface.eventual_etale_affine_section_test_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ U : S.scheme.affineOpens, ∃ eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
      (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r → ∀ k m : ℕ,
        0 < k → 0 < m → (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
        ∃ p : Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ), Function.Injective p ∧
          ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
            (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
              (RingHom.ker (p i))^m) → s = 0 := by
  classical
  obtain ⟨d,hd,y,U,hyU,eL,t,het,q,hq0,hq,hjets,htinj,⟨V,hV,hV0,hqinj⟩,hbound⟩ :=
    S.exists_all_section_quadrilateral_etale_s01 L hL
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  have hft : (openScalars S.structureMap U.1).FiniteType := by
    exact (S.structureMap.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).surjective)
  let : Algebra.FiniteType ℂ Γ(S.scheme,U.1) := (RingHom.finiteType_algebraMap.mp hft)
  obtain ⟨W,hW,hW0,hqat⟩ := exists_uniform_analytic_neighborhood q hq
  let : ∀ k : ℕ, Module ℂ (GlobalSections S.scheme (modulePow S.scheme L.sheaf k)) :=
    fun k => complexSectionModule S.structureMap (L.pow k).sheaf
  let coord (k : ℕ) := affineCoefficientLinear S.structureMap U (localPowerFrame U.1 eL k)
  let C (k : ℕ) := germCoefficients (coord k) q hq
  have hci (k : ℕ) : Function.Injective (C k) :=
    germCoefficients_injective_of_taylor (coord k) q hq
      (affineCoefficientLinear_injective S.structureMap (L.pow k) U _) htinj
  let F (k : ℕ) := LinearMap.range (C k)
  let : ∀ k : ℕ, FiniteDimensional ℂ (F k) := fun k =>
    @Module.Finite.range ℂ _ _ _ _ (complexSectionModule S.structureMap (L.pow k).sheaf)
      _ _ (S.sections_finite L hL (L.pow k)) (C k)
  have hconv : ∀ k c, c ∈ F k → ConvergentSeries c := by
    rintro k c ⟨s,rfl⟩
    exact (analyticCoefficients_spec (analyticPullback q hq (coord k s))).1
  have hH : 0 < (selfIntersection S L:ℝ) := by exact_mod_cast S.selfIntersection_pos L hL
  obtain ⟨T,hT,hweight⟩ := Interpolation.exists_node_weight_range (d:ℝ)
    (selfIntersection S L:ℝ) (by exact_mod_cast hd) hH
  have hbound' : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ Interpolation.initialExponentSet (F k) t,
      ((e.1:ℝ),(e.2:ℝ)) ∈ Interpolation.nodeQuadrilateral
        ((k:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*t/(1+t)))
        ((k:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+t))) ((k:ℝ)/d) := by
    intro k hk t ht e he
    obtain ⟨c,⟨s,hs⟩,hc⟩ := he
    have heq := germCoefficients_eq_bivariate (coord k) q hq s
    have hsne : s ≠ 0 := by
      intro hs0
      have hc0 : c = 0 := by rw [← hs,hs0,map_zero]
      exact hc.1 (by rw [hc0]; rfl)
    have HH := hbound k hk s hsne (localPowerFrame U.1 eL k) t (by linarith) e
    apply HH
    change LexInitial (NodalLocal.bivariateCoeff
      (bivariateTaylor q hq (coord k s))) t e
    rw [← heq,hs]
    exact hc
  obtain ⟨r₀,hr₀,htest⟩ := Interpolation.eventual_germ_jet_test_s01 (d:ℝ)
    (selfIntersection S L:ℝ) T (by exact_mod_cast hd) hH hT hweight F hconv hbound'
  refine ⟨U,eL,t,het,r₀,hr₀,?_⟩
  intro r hr k m hk hm hkm
  obtain ⟨R,hR,hs,ht⟩ := htest r hr k m hk hm hkm
  obtain ⟨p,hp,-,hzero⟩ := idealPower_test_of_series_test (coord k) q hq (hci k)
    (V ∩ W) (hV.inter hW) ⟨hV0,hW0⟩ (hqinj.mono Set.inter_subset_left)
    (fun z hz => hqat z hz.2) r m R hR hs ht
  exact ⟨p,hp,hzero⟩
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01_oai
