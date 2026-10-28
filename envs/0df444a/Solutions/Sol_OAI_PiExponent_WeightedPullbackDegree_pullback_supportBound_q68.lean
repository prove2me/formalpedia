-- Prove2me | solution 1 for OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:47:56.51318+00:00
-- url     : https://prove2.me/submissions/f27717c9-4532-4359-93f0-600d9e179d54

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_GlobalPolynomialWeightedBound_coefficient_bound_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

theorem SupportBound.mono {ρ : σ → ℝ} {M N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hMN : M ≤ N) : SupportBound ρ N p :=
  fun d hd => (hp d hd).trans hMN

theorem supportBound_zero (ρ : σ → ℝ) (N : ℝ) :
    SupportBound ρ N (0 : MvPolynomial σ E) := by
  intro d hd
  simp at hd

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

theorem SupportBound.pow {ρ : σ → ℝ} {N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (m : ℕ) : SupportBound ρ ((m : ℝ) * N) (p ^ m) := by
  induction m with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem supportBound_prod {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : α → ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ (N i) (p i)) :
    SupportBound ρ (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_sum {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ N (p i)) :
    SupportBound ρ N (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supportBound_zero ρ N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_aeval_monomial (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (d : ι →₀ ℕ) (c : C) :
    SupportBound κ (Finsupp.weight ρ d) (MvPolynomial.aeval g (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hC : SupportBound κ 0 (algebraMap C (MvPolynomial σ E) c) :=
    supportBound_C κ (algebraMap C E c)
  have hprod := supportBound_prod d.support κ (fun i => g i ^ d i)
    (fun i => (d i : ℝ) * ρ i) (fun i _ => (hg i).pow (d i))
  have h := hC.mul hprod
  simpa only [zero_add, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finsupp.prod] using h

theorem supportBound_aeval (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound κ N (MvPolynomial.aeval g p) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum p, map_sum]
  exact supportBound_sum p.support κ _ N
    (fun d hd => (supportBound_aeval_monomial ρ κ g hg d (p.coeff d)).mono (hp d hd))

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedChartRingEvaluation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedChartRingEvaluation
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponentSeshadri.Frames PiExponentSeshadri
open PiExponent.WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

section Generic
variable {X : Scheme} {K σ A : Type} [CommRing K] [CommRing A]
variable (M : X.Modules) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
  (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
  (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
  (i : σ) (v : PolyChart (R := K) i →+* A)
  (g : Spec (CommRingCat.of A) ⟶ (SectionOpens.isoOpen (s i)).toScheme)
  (hg : g ≫ (coordinateSectionChartIso M k s hc f hf i).hom =
    Spec.map (CommRingCat.ofHom v))

include hg

theorem chart_pullback (q : MvPolynomial (ChartVariables i) K) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop ((SectionOpens.isoOpen (s i)).topIso.inv
        ((coordinateSectionRingEquiv M k s hc f hf i).symm q))) = v (polyToChart i q) := by
  let U := SectionOpens.isoOpen (s i)
  let e := coordinateSectionChartIso M k s hc f hf i
  have hcancel (x : Γ(U.toScheme, ⊤)) : U.topIso.inv (U.topIso.hom x) = x :=
    CategoryTheory.congr_fun U.topIso.hom_inv_id x
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g.appTop (U.topIso.inv (U.topIso.hom
      (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv
        (polyToChart i q)))))) = _
  rw [hcancel]
  change (e.hom.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, hg, Scheme.ΓSpecIso_naturality]
  change v ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q))) = _
  exact congrArg v (CategoryTheory.congr_fun
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv_hom_id _)
end Generic

variable {R ι σ : Type} [CommRing R]

theorem evalAway_polyToChart (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (q : MvPolynomial (ChartVariables z) R) :
    evalAway (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz])
      (polyToChart z q) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  have ha : monomial (a z) (1 : R) = (1 : MvPolynomial ι R) := by simp [hz]
  have he :
      (evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz])).comp (polyToChart z) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
      exact evalAway_constants z C (fun j => monomial (a j) (1 : R)) ha r
    · intro j
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
      exact evalAway_coordinate z C (fun j => monomial (a j) (1 : R)) ha j.val
  exact RingHom.congr_fun he q

theorem chartFactor_comp (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      chartFactor a z hz coordinate hcoordinate ≫ (ambientOpen (R := R) z).ι := by
  have he := coordinateSectionChartIso_hom_away
    (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at he
  rw [affineChartMap_comp_projectiveMonomialMap]
  unfold chartFactor fromUnitCoordinate
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem ambient_chart_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (g : Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme)
    (hg : g ≫ (ambientOpen (R := R) z).ι =
      affineChartMap a z hz coordinate hcoordinate ≫ projectiveMonomialMap a)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      (g.appTop ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  let v : PolyChart (R := R) z →+* MvPolynomial ι R := evalAway (affineMonomialMap (R := R) a) (X z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz])
  have hfactor : g ≫
      (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
        ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
        (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).hom =
      Spec.map (CommRingCat.ofHom v) := by
    apply (cancel_mono (Proj.awayι (PolyGrade R σ) (X z) (poly_X_mem z) (by decide))).mp
    rw [Category.assoc, coordinateSectionChartIso_hom_away,
      ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id, hg,
      affineChartMap_comp_projectiveMonomialMap]
    rfl
  exact (chart_pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z v g hfactor q).trans
      (evalAway_polyToChart a z hz q)

theorem chartFactor_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      ((chartFactor a z hz coordinate hcoordinate).appTop
        ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q :=
  ambient_chart_pullback a z hz coordinate hcoordinate
    (chartFactor a z hz coordinate hcoordinate) (chartFactor_comp a z hz coordinate hcoordinate).symm q

end
end PiExponent.WeightedChartRingEvaluation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveRepresentedCoefficient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.FlasqueCohomology FreeOpenUnit Frames


variable {X : Scheme} (U : X.Opens) (M : X.Modules)

theorem freeOpenEquiv_freeTop_comp (b : structureSheaf X ⟶ M) :
    freeOpenEquiv X.ringCatSheaf M ⊤ ((freeTopIso X.ringCatSheaf).hom ≫ b) =
      globalHomEquiv X.ringCatSheaf M b := by
  erw [freeOpenEquiv_comp]
  change b.val.app (op ⊤)
    (freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤
      ((freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤).symm
        (globalHomEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem framedHomCoefficientsEquiv_globalSection
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (b : structureSheaf X ⟶ M) :
    framedHomCoefficientsEquiv U M e
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b) =
      U.topIso.hom (coefficient e (restrictSection U.ι b)) := by
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv
    (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b)))) = _
  erw [freeOpenEquiv_naturality X.ringCatSheaf M
    (homOfLE (show U ≤ ⊤ from le_top)) ((freeTopIso X.ringCatSheaf).hom ≫ b),
    freeOpenEquiv_freeTop_comp]
  apply congrArg U.topIso.hom
  change e.hom.app ⊤
      (M.presheaf.map (eqToHom U.ι_image_top).op
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))))) =
    e.hom.app ⊤ (b.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤))))
  apply congrArg (e.hom.app ⊤)
  rw [show (U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)) =
    (1 : Γ(X, U.ι ''ᵁ ⊤)) from map_one _]
  change (M.presheaf.map _ ≫ M.presheaf.map _) (b.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [← Functor.map_comp]
  rw [show (homOfLE (show U ≤ ⊤ from le_top)).op ≫ (eqToHom U.ι_image_top).op =
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op from Subsingleton.elim _ _]
  have hb := CategoryTheory.congr_fun (b.mapPresheaf.naturality
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change b.app (U.ι ''ᵁ ⊤)
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op 1) =
    M.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))) at hb
  simpa only [map_one] using hb.symm

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomials
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveTwistCech ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveCoordinateAcyclicity GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
variable (L : X.Modules) (s : σ → (structureSheaf X ⟶ L)) (k : R →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc = f.hom)

omit [Fintype σ] in

lemma coordinateChartPolynomial_coefficient (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    coordinateChartPolynomial L s k hc f hf n i b =
      coordinateSectionRingEquiv L k s hc f hf i
        ((PiExponentSeshadri.SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (coordinatePowerFrame (s i) n)
            (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen (s i)).ι b))) := by
  change coordinateSectionRingEquiv L k s hc f hf i
    (framedHomCoefficientsEquiv _ _ (coordinatePowerFrame (s i) n)
      (freeOpenMap X.ringCatSheaf (homOfLE le_top) ≫
        (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)) = _
  rw [framedHomCoefficientsEquiv_globalSection]


end
end PiExponent.ProjectiveGlobalPolynomials

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GlobalPolynomialCoefficientLaw
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialCoefficientLaw
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinate_law {Y : Scheme} {R σ : Type} [CommRing R]
    (M : Y.Modules) (s : σ → (structureSheaf Y ⟶ M)) (k : R →+* Γ(Y,⊤))
    (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
    (f : Y ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc=f.hom)
    (n : ℕ) (z : σ) :
    CoefficientLaw (PiExponentSeshadri.SectionOpens.isoOpen (s z))
      (coordinatePowerFrame (s z) n) (coordinateSectionRingEquiv M k s hc f hf z)
      (ProjectiveGlobalPolynomials.coordinateChartPolynomial M s k hc f hf n z) :=
  fun b => ProjectiveGlobalPolynomials.coordinateChartPolynomial_coefficient M s k hc f hf n z b

end PiExponent.GlobalPolynomialCoefficientLaw
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveIntrinsicCoefficientLaw
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveIntrinsicCoefficientLaw
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

namespace CoordinateData
variable {R σ : Type} [CommRing R] (D : CoordinateData R σ)

theorem law (n : ℕ) (z : σ) : D.Law n z :=
  GlobalPolynomialCoefficientLaw.coordinate_law D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

end CoordinateData

attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateSection
  ProjectiveO1.scalars ProjectiveO1.coordinateCocycle sectionsMorphism
  CoordinateAtlas.morphism atlasOfFramedSections
  CoordinateData.chartOpen CoordinateData.Sections CoordinateData.Frame
  CoordinateData.frame CoordinateData.ringEquiv CoordinateData.polynomial CoordinateData.Law

variable {R σ : Type} [CommRing R]

attribute [local semireducible] CoordinateData.Sections CoordinateData.chartOpen
  CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_polynomial (n : ℕ) (z : σ) :
    (intrinsicData (R := R) (σ := σ)).polynomial n z =
      ProjectiveO1.globalSectionChartPolynomial (R := R) (σ := σ) n z := rfl

theorem intrinsic_ringEquiv (z : σ) :
    (intrinsicData (R := R) (σ := σ)).ringEquiv z =
      WeightedChartRingEvaluation.ambientRingEquiv (R := R) z := rfl

attribute [local irreducible] intrinsicData intrinsicBundle
  CoordinateData.Sections CoordinateData.chartOpen CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_law (n : ℕ) (z : σ) : (intrinsicData (R := R) (σ := σ)).Law n z :=
  CoordinateData.law _ n z

end
end PiExponent.ProjectiveIntrinsicCoefficientLaw

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedHomogeneousSubstitution
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedHomogeneousSubstitution
noncomputable section
open scoped BigOperators
open MvPolynomial
open WeightedSliceDegree
open PiExponentSeshadri.Projective


variable {σ ι K : Type*}

theorem supportBound_substitution [Field K] (ρ : ι → ℝ) (B : ℝ)
    (a : σ → ι →₀ ℕ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B)
    (n : ℕ) (p : MvPolynomial.homogeneousSubmodule σ K n) :
    SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p.val) := by
  classical
  refine supportBound_aeval (fun _ : σ => B) ρ
    (fun j => MvPolynomial.monomial (a j) (1 : K)) ?_ ((n : ℝ) * B) p.val ?_
  · intro j b hb
    have he : b = a j := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    simpa only [he] using ha j
  · intro b hb
    have hd : b.degree = n := by
      exact (p.property.degree_eq_sum_deg_support hb).symm
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      ← Finset.sum_mul, ← Nat.cast_sum, ← Finsupp.degree_apply, hd, le_refl]

theorem dehomogenize_substitution [CommRing K] (a : σ → ι →₀ ℕ)
    (z : σ) (hz : a z = 0) (p : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j : ChartVariables z => MvPolynomial.monomial (a j.val) (1 : K))
      (dehomogenize z p) =
    MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p := by
  classical
  have he :
      (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K))).toRingHom.comp (dehomogenize (R := K) z) =
      (MvPolynomial.aeval (R := K) (fun j => MvPolynomial.monomial (a j) (1 : K))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenize]
    · intro j
      by_cases hj : j = z
      · subst j
        simp [dehomogenize, hz]
      · simp [dehomogenize, hj]
  exact RingHom.congr_fun he p

end
end PiExponent.WeightedHomogeneousSubstitution

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedPullbackDegree
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedPullbackDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound_q68_oai (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  let D := ProjectiveIntrinsicCoefficientLaw.intrinsicData (R := K) (σ := σ)
  let ev : MvPolynomial (ChartVariables z) K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
      MvPolynomial.monomial (a j.val) (1 : K))).toRingHom
  have hbound : SupportBound ρ ((n : ℝ) * B) (ev (D.polynomial n z (ProjectiveSectionInterface.sectionHom
      (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s))) := by
    dsimp only [D]
    rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_polynomial]
    rw [← hp]
    change SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K)) (dehomogenize z p.val))
    rw [WeightedHomogeneousSubstitution.dehomogenize_substitution a z hz]
    exact WeightedHomogeneousSubstitution.supportBound_substitution ρ B a ha n p
  exact GlobalPolynomialWeightedBound.coefficient_bound_q68
    (X := Proj (imageGrade (R := K) a)) (Y := D.scheme) (K := K) (ι := ι)
    (B := MvPolynomial (ChartVariables z) K)
    (ProjectiveIntrinsicCoefficientLaw.intrinsicBundle (R := K) (σ := σ))
    (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate)
    (D.chartOpen z) (WeightedChartRingEvaluation.chartFactor (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.chartFactor_comp (R := K) a z hz coordinate hcoordinate) n
    (D.frame n z) (D.ringEquiv z) (D.polynomial n z)
    (ProjectiveIntrinsicCoefficientLaw.intrinsic_law (R := K) n z) ev
    (by
      intro q
      dsimp only [D]
      rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_ringEquiv]
      exact WeightedChartRingEvaluation.chartFactor_pullback (R := K) a z hz coordinate hcoordinate q)
    ρ ((n : ℝ) * B) e s hbound

end PiExponent.WeightedPullbackDegree
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68_oai := @OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68_oai
