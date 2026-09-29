-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevelRam.DRResolvedModelChartsLevelRam.exists_chartPresentation_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cdbe795f-bde9-5849-8d36-d67438afa539

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevelRam_DRResolvedModelChartsLevelRam_exists_chartPresentation_stalk
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient ModularCurve
open IsLocalRing

noncomputable section

universe u

namespace ChartAtLevelAux

private abbrev cgerm (R : CommRingCat.{u}) (q : ↥(Spec R)) (c : R) : (Spec R).presheaf.stalk q :=
  ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv.hom c)

private abbrev stalkAlg (R : CommRingCat.{u}) (q : ↥(Spec R)) : Algebra R ((Spec R).presheaf.stalk q) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.stalk q))

private theorem isLocalizationAtPrime_stalk (R : CommRingCat.{u}) (q : ↥(Spec R)) :
    letI := stalkAlg R q
    IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk q) q.asIdeal)

private theorem cgerm_eq_algebraMap (R : CommRingCat.{u}) (q : ↥(Spec R)) (c : R) :
    cgerm R q c = @algebraMap R ((Spec R).presheaf.stalk q) _ _ (stalkAlg R q) c := rfl

private theorem cgerm_mul (R : CommRingCat.{u}) (q : ↥(Spec R)) (c d : R) :
    cgerm R q (c * d) = cgerm R q c * cgerm R q d := by
  simp only [cgerm, map_mul]

private theorem cgerm_pow (R : CommRingCat.{u}) (q : ↥(Spec R)) (c : R) (m : ℕ) :
    cgerm R q (c ^ m) = cgerm R q c ^ m := by
  simp only [cgerm, map_pow]

private theorem cgerm_natCast (R : CommRingCat.{u}) (q : ↥(Spec R)) (m : ℕ) : cgerm R q (m : R) = (m : _) := by
  simp only [cgerm, map_natCast]

private theorem cgerm_mem_maximalIdeal (R : CommRingCat.{u}) (q : ↥(Spec R)) (c : R) (hc : c ∈ q.asIdeal) :
    cgerm R q c ∈ maximalIdeal ((Spec R).presheaf.stalk q) := by
  letI := stalkAlg R q
  haveI := isLocalizationAtPrime_stalk R q
  rw [cgerm_eq_algebraMap, ← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal ((Spec R).presheaf.stalk q)]
  exact Ideal.mem_map_of_mem _ hc

private theorem span_cgerm_eq_maximalIdeal (R : CommRingCat.{u}) (q : ↥(Spec R)) (s : Set R)
    (hs : q.asIdeal = Ideal.span s) :
    Ideal.span (cgerm R q '' s) = maximalIdeal ((Spec R).presheaf.stalk q) := by
  letI := stalkAlg R q
  haveI := isLocalizationAtPrime_stalk R q
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal ((Spec R).presheaf.stalk q), hs, Ideal.map_span]
  rfl

private theorem asIdeal_eq_span_of_U_mem_of_V_mem {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    (P : PrimeSpectrum (CrossingQuotient O (ϖ ^ e)))
    (hU : CrossingQuotient.U (ϖ ^ e) ∈ P.asIdeal) (hV : CrossingQuotient.V (ϖ ^ e) ∈ P.asIdeal) :
    P.asIdeal = Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e),
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} := by
  classical
  set B := CrossingQuotient O (ϖ ^ e) with hB
  have ht : algebraMap O B ϖ ∈ P.asIdeal := by
    have hmem : (algebraMap O B ϖ) ^ e ∈ P.asIdeal := by
      rw [← map_pow, ← CrossingQuotient.U_mul_V]; exact Ideal.mul_mem_left _ _ hV
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance e hmem
  let N : Ideal B := Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e), algebraMap O B ϖ}
  have hNP : N ≤ P.asIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl | rfl)
    exacts [hU, hV, ht]
  have hUN : CrossingQuotient.U (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have hVN : CrossingQuotient.V (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have htN : algebraMap O B ϖ ∈ N := Ideal.subset_span (by simp)
  let θ : O →+* B ⧸ N := (Ideal.Quotient.mk N).comp (algebraMap O B)
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective
      (I := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ e)}) b
    induction r using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add r s hr hs =>
      obtain ⟨a, ha⟩ := hr
      obtain ⟨b, hb⟩ := hs
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
    | mul_X r i hr =>
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      fin_cases i
      · exact hUN
      · exact hVN
  have hNtop : N ≠ ⊤ := fun h => P.2.ne_top (top_le_iff.mp (h ▸ hNP))
  have hker : RingHom.ker θ = maximalIdeal O := by
    symm
    haveI : Nontrivial (B ⧸ N) := Ideal.Quotient.nontrivial_iff.mpr hNtop
    refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top θ) ?_
    rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr htN
  have hmax : N.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have e₁ := RingHom.quotientKerEquivOfSurjective hsurj
    have hF : IsField (O ⧸ RingHom.ker θ) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (hker ▸ IsLocalRing.maximalIdeal.isMaximal O)
    exact MulEquiv.isField hF e₁.symm.toMulEquiv
  exact (hmax.eq_of_le P.2.ne_top hNP).symm

private theorem map_stalkMap_maximalIdeal {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X) :
    Ideal.map (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f.base x))) = maximalIdeal (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  haveI : IsLocalHom (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  haveI : Algebra.EssFiniteType (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  haveI : Algebra.FormallyUnramified (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  exact Algebra.FormallyUnramified.map_maximalIdeal

private theorem isNoetherianRing_stalk_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X)
    [IsNoetherianRing (S.presheaf.stalk (f.base x))] : IsNoetherianRing (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  haveI : Algebra.EssFiniteType (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  exact Algebra.EssFiniteType.isNoetherianRing (S.presheaf.stalk (f.base x)) _

private theorem exists_mul_mem_of_mem_span_map
    (R : CommRingCat.{u}) (q : ↥(Spec R)) {A : Type u} [CommRing A]
    (τ : (Spec R).presheaf.stalk q →+* A) (hτ : ∀ I : Ideal ((Spec R).presheaf.stalk q), (I.map τ).comap τ = I)
    (x a b : R) (h : τ (cgerm R q x) ∈ Ideal.span {τ (cgerm R q a), τ (cgerm R q b)}) :
    ∃ c ∉ q.asIdeal, c * x ∈ Ideal.span {a, b} := by
  letI := stalkAlg R q
  haveI := isLocalizationAtPrime_stalk R q
  have h1 : cgerm R q x ∈ Ideal.span {cgerm R q a, cgerm R q b} := by
    have e1 : Ideal.span {τ (cgerm R q a), τ (cgerm R q b)} = (Ideal.span {cgerm R q a, cgerm R q b}).map τ := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [e1] at h
    rw [← hτ (Ideal.span {cgerm R q a, cgerm R q b}), Ideal.mem_comap]
    exact h
  have h2 : Ideal.span {cgerm R q a, cgerm R q b} =
      (Ideal.span {a, b}).map (algebraMap R ((Spec R).presheaf.stalk q)) := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [h2, cgerm_eq_algebraMap, IsLocalization.mem_map_algebraMap_iff q.asIdeal.primeCompl] at h1
  obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, hx⟩ := h1
  dsimp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists q.asIdeal.primeCompl] at hx
  obtain ⟨⟨d, hd⟩, hdx⟩ := hx
  dsimp only at hdx
  refine ⟨d * c, fun hmem => (q.2.mem_or_mem hmem).elim hd hc, ?_⟩
  have e3 : d * c * x = d * i := by rw [mul_assoc, mul_comm c x]; exact hdx
  rw [e3]
  exact Ideal.mul_mem_left _ _ hi

private theorem le_asIdeal_of_mem_support_of_comap_eq {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (I : (Resolution t e).IdealSheafData) (i : Fin e) (K : Ideal (CrossingQuotient W t))
    (hI : I.comap (Resolution.ι t e i) = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom K))
    (y : chartScheme t) (hy : (Resolution.ι t e i).base y ∈ I.support) : K ≤ y.asIdeal := by
  have hy' : y ∈ (I.comap (Resolution.ι t e i)).support := by
    rw [Scheme.IdealSheafData.support_comap]; exact hy
  rw [hI] at hy'
  have hy'' : y ∈ (chartScheme t).zeroLocus (U := ⊤)
      ((Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom K :
        Ideal Γ(chartScheme t, ⊤)) : Set Γ(chartScheme t, ⊤)) := by
    rw [← Scheme.IdealSheafData.coe_support_ofIdealTop]; exact hy'
  rw [Scheme.mem_zeroLocus_iff] at hy''
  intro c hc
  have h := hy'' _ (Ideal.mem_map_of_mem _ hc)
  rw [basicOpen_eq_of_affine] at h
  by_contra hcy
  exact h hcy

private theorem toCrossing_ι_asIdeal {W : Type u} [CommRing W] (t : W) (e : ℕ) (i : Fin e) (y : chartScheme t) :
    ((Resolution.toCrossing t e).base ((Resolution.ι t e i).base y)).asIdeal =
      Ideal.comap (resolutionChart t e i).toRingHom y.asIdeal := by
  have h : (Resolution.toCrossing t e).base ((Resolution.ι t e i).base y) =
      (Resolution.ι t e i ≫ Resolution.toCrossing t e).base y := rfl
  rw [h, Resolution.ι_toCrossing]
  rfl

private theorem stalkClosedPointTo_stalkSpecializes_congr {X : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    {g₁ g₂ : Spec (CommRingCat.of O) ⟶ X} (hg : g₁ = g₂) {x : X}
    (h₁ : g₁.base (closedPoint O) = x) (h₂ : g₂.base (closedPoint O) = x) (a : X.presheaf.stalk x) :
    (Scheme.stalkClosedPointTo g₁).hom ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom a) =
      (Scheme.stalkClosedPointTo g₂).hom ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom a) := by
  subst hg; rfl

private theorem stalkClosedPointTo_cgerm_congr {R : CommRingCat.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    {g₁ g₂ : Spec (CommRingCat.of O) ⟶ Spec R} (hg : g₁ = g₂) (c : R) :
    (Scheme.stalkClosedPointTo g₁).hom (cgerm R (g₁.base (closedPoint O)) c) =
      (Scheme.stalkClosedPointTo g₂).hom (cgerm R (g₂.base (closedPoint O)) c) := by
  subst hg; rfl

section ChainPos

variable {node : Type} (width : node → ℕ) (n : node)

private def posOf (c : X0MqComponents width) : ℕ :=
  match c with
  | Sum.inl i => if i = 0 then 0 else width n
  | Sum.inr q => q.2.val + 1

private theorem chainPos_of_eq_zero : DRResolvedModelPackageLevel.chainPos width n 0 = Sum.inl 0 := by
  simp [DRResolvedModelPackageLevel.chainPos]

private theorem chainPos_of_pos_of_lt {d : ℕ} (h0 : d ≠ 0) (h : d < width n) :
    DRResolvedModelPackageLevel.chainPos width n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  simp [DRResolvedModelPackageLevel.chainPos, h0, h]

private theorem chainPos_of_le {d : ℕ} (h0 : d ≠ 0) (h : width n ≤ d) :
    DRResolvedModelPackageLevel.chainPos width n d = Sum.inl 1 := by
  simp [DRResolvedModelPackageLevel.chainPos, h0, not_lt.mpr h]

private theorem posOf_chainPos (he : 1 ≤ width n) {k : ℕ} (hk : k ≤ width n) :
    posOf width n (DRResolvedModelPackageLevel.chainPos width n k) = k := by
  by_cases h0 : k = 0
  · subst h0; rw [chainPos_of_eq_zero]; simp [posOf]
  · by_cases hlt : k < width n
    · rw [chainPos_of_pos_of_lt width n h0 hlt]; simp [posOf]; omega
    · rw [chainPos_of_le width n h0 (not_lt.mp hlt)]; simp [posOf]; omega

private theorem chainPos_injOn (he : 1 ≤ width n) {k₁ k₂ : ℕ} (h₁ : k₁ ≤ width n) (h₂ : k₂ ≤ width n)
    (h : DRResolvedModelPackageLevel.chainPos width n k₁ = DRResolvedModelPackageLevel.chainPos width n k₂) : k₁ = k₂ := by
  rw [← posOf_chainPos width n he h₁, ← posOf_chainPos width n he h₂, h]

private theorem chainPos_ne_inr {m : node} (hm : m ≠ n) (i : Fin (width m - 1)) (k : ℕ) :
    DRResolvedModelPackageLevel.chainPos width n k ≠ Sum.inr ⟨m, i⟩ := by
  by_cases h0 : k = 0
  · subst h0; rw [chainPos_of_eq_zero]; exact Sum.inl_ne_inr
  · by_cases hlt : k < width n
    · rw [chainPos_of_pos_of_lt width n h0 hlt]
      intro h
      have := (Sum.inr_injective h)
      exact hm (congrArg Sigma.fst this).symm
    · rw [chainPos_of_le width n h0 (not_lt.mp hlt)]; exact Sum.inl_ne_inr

private theorem chainPos_cases (he : 1 ≤ width n) (c : X0MqComponents width) :
    (∃ k : ℕ, k ≤ width n ∧ c = DRResolvedModelPackageLevel.chainPos width n k) ∨
      (∃ (m : node) (i : Fin (width m - 1)), m ≠ n ∧ c = Sum.inr ⟨m, i⟩) := by
  classical
  rcases c with i | ⟨m, i⟩
  · left
    fin_cases i
    · exact ⟨0, Nat.zero_le _, (chainPos_of_eq_zero width n).symm⟩
    · exact ⟨width n, le_rfl, (chainPos_of_le width n (by omega) le_rfl).symm⟩
  · by_cases hm : m = n
    · subst hm
      left
      refine ⟨i.val + 1, by omega, ?_⟩
      rw [chainPos_of_pos_of_lt width m (Nat.succ_ne_zero _) (by omega)]
      congr
    · right
      exact ⟨m, i, hm, rfl⟩

end ChainPos

private theorem maximalIdeal_eq_span_of_map_eq {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (φ : R →+* A) (hmap : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal A)
    (r₁ r₂ r₃ : R) (hR : IsLocalRing.maximalIdeal R = Ideal.span {r₁, r₂, r₃}) :
    IsLocalRing.maximalIdeal A = Ideal.span {φ r₁, φ r₂, φ r₃} := by
  rw [← hmap, hR, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

section Principal

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

private theorem exists_eq_unit_mul_pow_of_maximalIdeal_eq_span {ϖ : A} (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    {x : A} (hx : x ≠ 0) : ∃ (n : ℕ) (u : Aˣ), x = u * ϖ ^ n := by
  classical
  have hKrull : ⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hex : ∃ n : ℕ, x ∉ (IsLocalRing.maximalIdeal A) ^ n := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n := Ideal.mem_iInf.mpr h
    rwa [hKrull, Ideal.mem_bot] at this
  set N := Nat.find hex with hNdef
  have hN : x ∉ (IsLocalRing.maximalIdeal A) ^ N := Nat.find_spec hex
  have hmin : ∀ m < N, x ∈ (IsLocalRing.maximalIdeal A) ^ m := fun m hm => by
    have := Nat.find_min hex hm
    simpa using this
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  have hxn : x ∈ Ideal.span {ϖ ^ n} := by
    have := hmin n (by omega)
    rwa [hϖ, Ideal.span_singleton_pow] at this
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hxn
  have hyu : IsUnit y := by
    by_contra hyu
    have hym : y ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal y).mpr hyu
    rw [hϖ, Ideal.mem_span_singleton'] at hym
    obtain ⟨z, rfl⟩ := hym
    apply hN
    rw [hn, hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

private theorem noZeroDivisors_of_maximalIdeal_eq_span {ϖ : A} (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hnil : ∀ n : ℕ, ϖ ^ n ≠ 0) : NoZeroDivisors A := by
  refine ⟨fun {x y} hxy => ?_⟩
  by_contra h
  push_neg at h
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_pow_of_maximalIdeal_eq_span hϖ h.1
  obtain ⟨m, w, rfl⟩ := exists_eq_unit_mul_pow_of_maximalIdeal_eq_span hϖ h.2
  apply hnil (n + m)
  have : ((u * w : Aˣ) : A) * ϖ ^ (n + m) = 0 := by
    rw [← hxy, Units.val_mul, pow_add]; ring
  simpa using (Units.mul_right_eq_zero (u * w)).mp this

private theorem eq_bot_or_eq_maximalIdeal_of_maximalIdeal_eq_span {ϖ : A} (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal A) [h𝔔 : 𝔔.IsPrime] : 𝔔 = ⊥ ∨ 𝔔 = IsLocalRing.maximalIdeal A := by
  classical
  by_cases h : 𝔔 = ⊥
  · exact Or.inl h
  · right
    apply le_antisymm (IsLocalRing.le_maximalIdeal h𝔔.ne_top)
    obtain ⟨x, hx𝔔, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_pow_of_maximalIdeal_eq_span hϖ hx0
    have hϖn : ϖ ^ n ∈ 𝔔 := by
      have := 𝔔.mul_mem_left ((u⁻¹ : Aˣ) : A) hx𝔔
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this
    have hϖ𝔔 : ϖ ∈ 𝔔 := h𝔔.mem_of_pow_mem n hϖn
    rw [hϖ, Ideal.span_singleton_le_iff_mem]
    exact hϖ𝔔

end Principal

section Branch

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

private theorem isPrime_span_pair_and_forall (t a b : A)
    (hmax : Ideal.span {t, a, b} = IsLocalRing.maximalIdeal A) (hbn : ∀ m : ℕ, b ^ m ∉ Ideal.span ({t, a} : Set A)) :
    (Ideal.span ({t, a} : Set A)).IsPrime ∧ Ideal.span ({t, a} : Set A) ≠ IsLocalRing.maximalIdeal A ∧
      ∀ 𝔓 : Ideal A, 𝔓.IsPrime → Ideal.span ({t, a} : Set A) ≤ 𝔓 →
        𝔓 = Ideal.span ({t, a} : Set A) ∨ 𝔓 = IsLocalRing.maximalIdeal A := by
  classical
  set I : Ideal A := Ideal.span ({t, a} : Set A) with hI

  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hmax, hI]
    apply Ideal.span_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hItop : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hIle))
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hmapmax : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (A ⧸ I) := by
    have hne : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) ≠ ⊤ := by
      intro htop
      apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      have hcm := congrArg (Ideal.comap (Ideal.Quotient.mk I)) htop
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hIle] at hcm
      exact hcm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (IsLocalRing.maximalIdeal.isMaximal A) with h | h
    · exact absurd h hne
    · exact IsLocalRing.eq_maximalIdeal h
  have hbar : IsLocalRing.maximalIdeal (A ⧸ I) = Ideal.span {Ideal.Quotient.mk I b} := by
    rw [← hmapmax, ← hmax, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    have ht0 : Ideal.Quotient.mk I t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have ha0 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [ht0, ha0, Set.insert_eq_of_mem (Set.mem_insert _ _)]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z hz
      rcases hz with rfl | rfl
      · exact Ideal.zero_mem _
      · exact Ideal.subset_span rfl
    · exact Ideal.span_mono (Set.subset_insert _ _)
  have hnil : ∀ n : ℕ, (Ideal.Quotient.mk I b) ^ n ≠ 0 := fun n h =>
    hbn n (by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h)

  haveI : NoZeroDivisors (A ⧸ I) := noZeroDivisors_of_maximalIdeal_eq_span hbar hnil
  haveI : IsDomain (A ⧸ I) := NoZeroDivisors.to_isDomain _
  have hprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  refine ⟨hprime, ?_, ?_⟩
  · intro h
    apply hbn 1
    rw [pow_one, h, ← hmax]
    exact Ideal.subset_span (by simp)
  · intro 𝔓 h𝔓 hI𝔓
    haveI := h𝔓
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔓 := by rw [Ideal.mk_ker]; exact hI𝔓
    haveI : (𝔓.map (Ideal.Quotient.mk I)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hback : (𝔓.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = 𝔓 := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left]
      intro z hz
      exact hker hz
    rcases eq_bot_or_eq_maximalIdeal_of_maximalIdeal_eq_span hbar (𝔓.map (Ideal.Quotient.mk I)) with h | h
    · left
      rw [← hback, h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    · right
      apply le_antisymm (IsLocalRing.le_maximalIdeal h𝔓.ne_top)
      rw [← hmax]
      rw [Ideal.span_le]
      have hb𝔓 : b ∈ 𝔓 := by
        rw [← hback, Ideal.mem_comap, h, hbar]
        exact Ideal.subset_span rfl
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hI𝔓 (Ideal.subset_span (by simp))
      · exact hI𝔓 (Ideal.subset_span (by simp))
      · exact hb𝔓

private theorem branchIdeals_of_crossing (t a b : A) (e : ℕ) (he : 1 ≤ e) (hab : a * b = t ^ e)
    (hmax : Ideal.span {t, a, b} = IsLocalRing.maximalIdeal A)
    (hbn : ∀ m : ℕ, b ^ m ∉ Ideal.span ({t, a} : Set A)) (han : ∀ m : ℕ, a ^ m ∉ Ideal.span ({t, b} : Set A)) :
    (Ideal.span ({t, a} : Set A)).IsPrime ∧ (Ideal.span ({t, b} : Set A)).IsPrime ∧
      Ideal.span ({t, a} : Set A) ≠ IsLocalRing.maximalIdeal A ∧ Ideal.span ({t, b} : Set A) ≠ IsLocalRing.maximalIdeal A ∧
      Ideal.span ({t, a} : Set A) ≠ Ideal.span ({t, b} : Set A) ∧
      ∀ 𝔓 : Ideal A, 𝔓.IsPrime → t ∈ 𝔓 →
        𝔓 = IsLocalRing.maximalIdeal A ∨ 𝔓 = Ideal.span ({t, a} : Set A) ∨ 𝔓 = Ideal.span ({t, b} : Set A) := by
  have hmax' : Ideal.span {t, b, a} = IsLocalRing.maximalIdeal A := by
    rw [← hmax]; congr 1; ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨hPa, hPa_ne, hPa_all⟩ := isPrime_span_pair_and_forall t a b hmax hbn
  obtain ⟨hPb, hPb_ne, hPb_all⟩ := isPrime_span_pair_and_forall t b a hmax' han
  refine ⟨hPa, hPb, hPa_ne, hPb_ne, ?_, ?_⟩
  · intro h
    apply hbn 1
    rw [pow_one, h]
    exact Ideal.subset_span (by simp)
  · intro 𝔓 h𝔓 ht
    haveI := h𝔓
    have habP : a * b ∈ 𝔓 := by rw [hab]; exact 𝔓.pow_mem_of_mem ht e he
    rcases h𝔓.mem_or_mem habP with ha𝔓 | hb𝔓
    · have hle : Ideal.span ({t, a} : Set A) ≤ 𝔓 := by
        rw [Ideal.span_le]; rintro z hz; rcases hz with rfl | rfl; exacts [ht, ha𝔓]
      rcases hPa_all 𝔓 h𝔓 hle with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · have hle : Ideal.span ({t, b} : Set A) ≤ 𝔓 := by
        rw [Ideal.span_le]; rintro z hz; rcases hz with rfl | rfl; exacts [ht, hb𝔓]
      rcases hPb_all 𝔓 h𝔓 hle with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

end Branch

private theorem comap_map_eq_of_flat_of_isLocalHom {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (φ : R →+* A) (hφ : φ.Flat) [IsLocalHom φ] (I : Ideal R) : (I.map φ).comap φ = I := by
  letI := φ.toAlgebra
  haveI : Module.Flat R A := hφ
  haveI : IsLocalHom (algebraMap R A) := ‹IsLocalHom φ›
  haveI : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

private theorem isNoetherianRing_of_essFiniteType {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A) (hφ : φ.EssFiniteType)
    [IsNoetherianRing R] : IsNoetherianRing A := by
  letI := φ.toAlgebra
  haveI : Algebra.EssFiniteType R A := hφ
  exact Algebra.EssFiniteType.isNoetherianRing R A

section Crossing

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem span_U_V_algebraMap_isMaximal (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) :
    (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e),
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e))).IsMaximal ∨
    (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e),
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e))) = ⊤ := by
  classical
  set B := CrossingQuotient O (ϖ ^ e) with hB
  let N : Ideal B := Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e), algebraMap O B ϖ}
  show N.IsMaximal ∨ N = ⊤
  have hUN : CrossingQuotient.U (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have hVN : CrossingQuotient.V (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have htN : algebraMap O B ϖ ∈ N := Ideal.subset_span (by simp)
  let θ : O →+* B ⧸ N := (Ideal.Quotient.mk N).comp (algebraMap O B)
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective
      (I := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ e)}) b
    induction r using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add r s hr hs =>
      obtain ⟨a, ha⟩ := hr
      obtain ⟨b, hb⟩ := hs
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
    | mul_X r i hr =>
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      fin_cases i
      · exact hUN
      · exact hVN
  by_cases hNtop : N = ⊤
  · exact Or.inr hNtop
  left
  have hker : RingHom.ker θ = IsLocalRing.maximalIdeal O := by
    symm
    haveI : Nontrivial (B ⧸ N) := Ideal.Quotient.nontrivial_iff.mpr hNtop
    refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top θ) ?_
    rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr htN
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  have e₁ := RingHom.quotientKerEquivOfSurjective hsurj
  have hF : IsField (O ⧸ RingHom.ker θ) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (hker ▸ IsLocalRing.maximalIdeal.isMaximal O)
  exact MulEquiv.isField hF e₁.symm.toMulEquiv

private theorem mul_U_pow_notMem_span_algebraMap_V (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (c : CrossingQuotient O (ϖ ^ e))
    (hc : c ∉ (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e),
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e)))) :
    c * CrossingQuotient.U (ϖ ^ e) ^ m ∉
      (Ideal.span {algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ, CrossingQuotient.V (ϖ ^ e)} :
        Ideal (CrossingQuotient O (ϖ ^ e))) := by
  classical
  haveI hprime : (Ideal.span {ϖ}).IsPrime := hϖ ▸ (IsLocalRing.maximalIdeal.isMaximal O).isPrime
  let k := O ⧸ Ideal.span {ϖ}
  have hk0 : algebraMap O (Polynomial k) (ϖ ^ e) = 0 := by
    rw [map_pow, IsScalarTower.algebraMap_apply O k (Polynomial k), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_pow (by omega)]

  let φ : CrossingQuotient O (ϖ ^ e) →ₐ[O] Polynomial k := CrossingQuotient.lift (ϖ ^ e) Polynomial.X (0 : Polynomial k) (by rw [mul_zero, hk0])
  have hφU : φ (CrossingQuotient.U (ϖ ^ e)) = Polynomial.X := CrossingQuotient.lift_U _ _ _ _
  have hφV : φ (CrossingQuotient.V (ϖ ^ e)) = 0 := CrossingQuotient.lift_V _ _ _ _
  have hφt : φ (algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ) = 0 := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O k (Polynomial k), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]

  have hker : (Ideal.span {algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ, CrossingQuotient.V (ϖ ^ e)} : Ideal (CrossingQuotient O (ϖ ^ e))) ≤ RingHom.ker φ.toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl)
    · exact hφt
    · exact hφV
  intro hmem
  have h0 : φ c * Polynomial.X ^ m = 0 := by
    have := hker hmem
    rw [RingHom.mem_ker] at this
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow φ (CrossingQuotient.U (ϖ ^ e)) m, hφU] at this
  have hφc : φ c = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (pow_ne_zero m Polynomial.X_ne_zero)

  apply hc
  let ψ : CrossingQuotient O (ϖ ^ e) →+* k := (Polynomial.evalRingHom 0).comp φ.toRingHom
  have hψN : (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e), algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e)))
      ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl | rfl)
    · show (Polynomial.evalRingHom 0) (φ (CrossingQuotient.U (ϖ ^ e))) = 0
      rw [hφU]; simp
    · show (Polynomial.evalRingHom 0) (φ (CrossingQuotient.V (ϖ ^ e))) = 0
      rw [hφV, map_zero]
    · show (Polynomial.evalRingHom 0) (φ (algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ)) = 0
      rw [hφt, map_zero]
  have hψc : c ∈ RingHom.ker ψ := by
    show (Polynomial.evalRingHom 0) (φ c) = 0
    rw [hφc, map_zero]
  rcases span_U_V_algebraMap_isMaximal ϖ hϖ e with hmax | htop
  · have heq := hmax.eq_of_le (RingHom.ker_ne_top ψ) hψN
    rw [heq]; exact hψc
  · rw [htop]; exact Submodule.mem_top

private theorem mul_V_pow_notMem_span_algebraMap_U (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (c : CrossingQuotient O (ϖ ^ e))
    (hc : c ∉ (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e),
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e)))) :
    c * CrossingQuotient.V (ϖ ^ e) ^ m ∉
      (Ideal.span {algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ, CrossingQuotient.U (ϖ ^ e)} :
        Ideal (CrossingQuotient O (ϖ ^ e))) := by
  classical
  haveI hprime : (Ideal.span {ϖ}).IsPrime := hϖ ▸ (IsLocalRing.maximalIdeal.isMaximal O).isPrime
  let k := O ⧸ Ideal.span {ϖ}
  have hk0 : algebraMap O (Polynomial k) (ϖ ^ e) = 0 := by
    rw [map_pow, IsScalarTower.algebraMap_apply O k (Polynomial k), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_pow (by omega)]
  let φ : CrossingQuotient O (ϖ ^ e) →ₐ[O] Polynomial k := CrossingQuotient.lift (ϖ ^ e) (0 : Polynomial k) Polynomial.X (by rw [zero_mul, hk0])
  have hφU : φ (CrossingQuotient.U (ϖ ^ e)) = 0 := CrossingQuotient.lift_U _ _ _ _
  have hφV : φ (CrossingQuotient.V (ϖ ^ e)) = Polynomial.X := CrossingQuotient.lift_V _ _ _ _
  have hφt : φ (algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ) = 0 := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O k (Polynomial k), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]
  have hker : (Ideal.span {algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ, CrossingQuotient.U (ϖ ^ e)} : Ideal (CrossingQuotient O (ϖ ^ e))) ≤ RingHom.ker φ.toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl)
    · exact hφt
    · exact hφU
  intro hmem
  have h0 : φ c * Polynomial.X ^ m = 0 := by
    have := hker hmem
    rw [RingHom.mem_ker] at this
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow φ (CrossingQuotient.V (ϖ ^ e)) m, hφV] at this
  have hφc : φ c = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (pow_ne_zero m Polynomial.X_ne_zero)
  apply hc
  let ψ : CrossingQuotient O (ϖ ^ e) →+* k := (Polynomial.evalRingHom 0).comp φ.toRingHom
  have hψN : (Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e), algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ} : Ideal (CrossingQuotient O (ϖ ^ e)))
      ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl | rfl)
    · show (Polynomial.evalRingHom 0) (φ (CrossingQuotient.U (ϖ ^ e))) = 0
      rw [hφU, map_zero]
    · show (Polynomial.evalRingHom 0) (φ (CrossingQuotient.V (ϖ ^ e))) = 0
      rw [hφV]; simp
    · show (Polynomial.evalRingHom 0) (φ (algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ)) = 0
      rw [hφt, map_zero]
  have hψc : c ∈ RingHom.ker ψ := by
    show (Polynomial.evalRingHom 0) (φ c) = 0
    rw [hφc, map_zero]
  rcases span_U_V_algebraMap_isMaximal ϖ hϖ e with hmax | htop
  · have heq := hmax.eq_of_le (RingHom.ker_ne_top ψ) hψN
    rw [heq]; exact hψc
  · rw [htop]; exact Submodule.mem_top

end Crossing

private theorem exists_lift_of_closedPoint_mem {X : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    (t : Spec (CommRingCat.of O) ⟶ X) (W : X.Opens) (h : t.base (IsLocalRing.closedPoint O) ∈ W) :
    ∃ t' : Spec (CommRingCat.of O) ⟶ W, t' ≫ W.ι = t := by
  have hrange : Set.range t.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hsp : t.base y ⤳ t.base (IsLocalRing.closedPoint O) :=
      (IsLocalRing.specializes_closedPoint y).map t.base.hom.continuous
    exact hsp.mem_open W.isOpen h
  exact ⟨IsOpenImmersion.lift W.ι t hrange, IsOpenImmersion.lift_fac W.ι t hrange⟩

private theorem stalkClosedPointTo_cgerm (R : CommRingCat.{u}) {O : Type u} [CommRing O] [IsLocalRing O]
    (φ : R ⟶ CommRingCat.of O) (c : R) :
    (Scheme.stalkClosedPointTo (Spec.map φ)).hom (cgerm R ((Spec.map φ).base (IsLocalRing.closedPoint O)) c) = φ.hom c := by
  have h := Scheme.germ_stalkClosedPointTo_Spec (S := CommRingCat.of O) φ
  have h' := congrArg (fun f => f.hom ((Scheme.ΓSpecIso R).inv.hom c)) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [cgerm]
  erw [h']
  change φ.hom ((Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom c)) = φ.hom c
  congr 1
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso R) c

private theorem natCast_mem_maximalIdeal_stalk_of_map {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) (m : ℕ)
    (hm : (m : X.presheaf.stalk x) = 0) : (m : Y.presheaf.stalk (g.base x)) ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' : IsUnit ((g.stalkMap x).hom (m : Y.presheaf.stalk (g.base x))) := hu.map _
  rw [map_natCast, hm] at hu'
  exact not_isUnit_zero hu'

private theorem natCast_stalk_eq_zero_of_charP {X : Scheme.{u}} {K : Type u} [Field K] (q : ℕ) [CharP K q]
    (π : X ⟶ Spec (CommRingCat.of K)) (x : X) : (q : X.presheaf.stalk x) = 0 := by
  have h1 : (q : (Spec (CommRingCat.of K)).presheaf.stalk (π.base x)) = 0 := by
    have := map_natCast (((Spec (CommRingCat.of K)).presheaf.germ ⊤ (π.base x) trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) q
    rw [← this]
    have hK : ((q : ℕ) : (CommRingCat.of K)) = 0 := CharP.cast_eq_zero K q
    rw [hK, map_zero]
  have := map_natCast (π.stalkMap x).hom q
  rw [← this, h1, map_zero]

end ChartAtLevelAux

open ChartAtLevelAux

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

private theorem ChartAtLevelAux.exists_chartPresentation_stalk_ram
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackageLevelRam N₀ q 𝔛 O ρO ((q : ℕ) : O) k toκ)
    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((q : ℕ) : O) e).IdealSheafData) (hF : ∀ (e : ℕ) (i : Fin e) (k' : Fin (e + 1)), (Fc e k').comap (Resolution.ι ((q : ℕ) : O) e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O)))).inv.hom
          (if (k' : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((q : ℕ) : O)} else if (k' : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((q : ℕ) : O)}
            else ⊤)))
    (ch : 𝔛reg.DRResolvedModelChartsLevelRam Fc)
    (n : 𝔛reg.node) :
    haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
    ∃ (hspInf : ((𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)))
      (hspZero : ((𝔛.comp k (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)))
      (u v w₀ : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))),
      IsUnit w₀ ∧
      u * v = ((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))) ^ (𝔛reg.width n) * w₀ ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), u, v} = IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))) ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), u} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _) ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), v} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _) ∧
      (∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
      ∀ (htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))),
      ∀ d : ℕ,
        IsDiscreteValuationRing.addVal O
          ((Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR))
            (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom v)) = d →
        ∀ c : X0MqComponents 𝔛reg.width,
          t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
            c = DRResolvedModelPackageLevel.chainPos 𝔛reg.width n d) := by

  haveI hint0 : IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  let XO := pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
  let xn : ↥XO := (pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)
  have hxn : xn = 𝔛reg.crossingPt n := rfl
  have he : 1 ≤ 𝔛reg.width n := 𝔛reg.one_le_width n
  let y : ↥(ch.U n) := ⟨xn, ch.mem_U n⟩
  let B : CommRingCat.{0} := CommRingCat.of (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n))
  let f : (ch.U n).toScheme ⟶ Spec B := ch.f n
  let s : ↥(Spec B) := f.base y
  let US : B := CrossingQuotient.U (((q : ℕ) : O) ^ 𝔛reg.width n)
  let VS : B := CrossingQuotient.V (((q : ℕ) : O) ^ 𝔛reg.width n)
  let ϖB : B := algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n)) (q : O)

  let ι₁ : (Spec B).presheaf.stalk s →+* (ch.U n).toScheme.presheaf.stalk y := (f.stalkMap y).hom
  let ι₂ : (ch.U n).toScheme.presheaf.stalk y ≃+* XO.presheaf.stalk xn := ((ch.U n).stalkIso y).commRingCatIsoToRingEquiv
  let τ : (Spec B).presheaf.stalk s →+* XO.presheaf.stalk xn := ι₂.toRingHom.comp ι₁
  let u : XO.presheaf.stalk xn := τ (cgerm B s VS)
  let v : XO.presheaf.stalk xn := τ (cgerm B s US)

  have hsUV : US ∈ s.asIdeal ∧ VS ∈ s.asIdeal := by
    have hx' : ¬ (f.base y ∈ ((PrimeSpectrum.basicOpen US : (crossingScheme (((q : ℕ) : O) ^ 𝔛reg.width n)).Opens) ⊔
        (PrimeSpectrum.basicOpen VS : (crossingScheme (((q : ℕ) : O) ^ 𝔛reg.width n)).Opens))) := by
      rw [ch.f_mem_Vc_iff]; exact fun h => h rfl
    constructor
    · by_contra h; exact hx' (TopologicalSpace.Opens.mem_sup.mpr (Or.inl ((PrimeSpectrum.mem_basicOpen _ _).mpr h)))
    · by_contra h; exact hx' (TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((PrimeSpectrum.mem_basicOpen _ _).mpr h)))
  have hs : s.asIdeal = Ideal.span {US, VS, ϖB} :=
    asIdeal_eq_span_of_U_mem_of_V_mem (q : O) hϖO (𝔛reg.width n) he s hsUV.1 hsUV.2

  have hτq : τ (cgerm B s ϖB) = ((q : ℕ) : XO.presheaf.stalk xn) := by
    have : ϖB = ((q : ℕ) : B) := map_natCast (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n))) q
    rw [this, cgerm_natCast, map_natCast]

  have hmapτ : (maximalIdeal ((Spec B).presheaf.stalk s)).map τ = maximalIdeal (XO.presheaf.stalk xn) := by
    rw [← Ideal.map_map, map_stalkMap_maximalIdeal f y]
    exact IsLocalRing.map_ringEquiv_maximalIdeal ι₂
  have h𝔪S : maximalIdeal ((Spec B).presheaf.stalk s) = Ideal.span {cgerm B s ϖB, cgerm B s VS, cgerm B s US} := by
    rw [← span_cgerm_eq_maximalIdeal B s {ϖB, VS, US}, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [hs]
    congr 1
    ext b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h𝔪 : Ideal.span {((q : ℕ) : XO.presheaf.stalk xn), u, v} = maximalIdeal (XO.presheaf.stalk xn) := by
    rw [maximalIdeal_eq_span_of_map_eq τ hmapτ _ _ _ h𝔪S, hτq]

  have huv : u * v = ((q : ℕ) : XO.presheaf.stalk xn) ^ 𝔛reg.width n := by
    have hUV : VS * US = ((q ^ 𝔛reg.width n : ℕ) : B) := by
      rw [mul_comm]
      change CrossingQuotient.U _ * CrossingQuotient.V _ = _
      rw [CrossingQuotient.U_mul_V]
      simp only [map_pow, map_natCast, Nat.cast_pow]
    change τ (cgerm B s VS) * τ (cgerm B s US) = _
    rw [← map_mul, ← cgerm_mul, hUV, cgerm_natCast, map_natCast, Nat.cast_pow]

  have hX0 := ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt N₀ q hqN 𝔛 O ρO k toκ
    (𝔛reg.nodeEquiv n)
  have hspInf : ((𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ xn :=
    hX0.1
  have hspZero : ((𝔛.comp k (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ xn :=
    hX0.2

  haveI hBnoeth : IsNoetherianRing ((Spec B).presheaf.stalk s) := by
    letI := stalkAlg B s
    haveI := isLocalizationAtPrime_stalk B s
    exact IsLocalization.isNoetherianRing s.asIdeal.primeCompl _ (inferInstance : IsNoetherianRing B)
  haveI hUnoeth : IsNoetherianRing ((ch.U n).toScheme.presheaf.stalk y) := isNoetherianRing_stalk_of_etale f y
  haveI hAnoeth : IsNoetherianRing (XO.presheaf.stalk xn) := isNoetherianRing_of_ringEquiv _ ι₂

  have hτcomap : ∀ I : Ideal ((Spec B).presheaf.stalk s), (I.map τ).comap τ = I := by
    intro I
    haveI : IsLocalHom ι₁ := f.toLRSHom.prop y
    have e2 : ∀ J : Ideal ((ch.U n).toScheme.presheaf.stalk y), (J.map ι₂.toRingHom).comap ι₂.toRingHom = J := by
      intro J
      refine le_antisymm ?_ Ideal.le_comap_map
      intro z hz
      rw [Ideal.mem_comap] at hz
      have hz' := Ideal.mem_map_of_mem ι₂.symm.toRingHom hz
      rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id] at hz'
      simpa using hz'
    change ((I.map (ι₂.toRingHom.comp ι₁)).comap (ι₂.toRingHom.comp ι₁)) = I
    rw [← Ideal.map_map, ← Ideal.comap_comap, e2]
    exact comap_map_eq_of_flat_of_isLocalHom ι₁ (Flat.stalkMap f y) I
  have hbn : ∀ m : ℕ, v ^ m ∉ Ideal.span ({((q : ℕ) : XO.presheaf.stalk xn), u} : Set _) := by
    intro m hm
    have hm' : τ (cgerm B s (US ^ m)) ∈ Ideal.span {τ (cgerm B s ϖB), τ (cgerm B s VS)} := by
      rw [cgerm_pow, map_pow, hτq]; exact hm
    obtain ⟨c, hc, hcm⟩ := exists_mul_mem_of_mem_span_map B s τ hτcomap (US ^ m) ϖB VS hm'
    rw [hs] at hc
    exact mul_U_pow_notMem_span_algebraMap_V (q : O) hϖO (𝔛reg.width n) he m c hc hcm
  have han : ∀ m : ℕ, u ^ m ∉ Ideal.span ({((q : ℕ) : XO.presheaf.stalk xn), v} : Set _) := by
    intro m hm
    have hm' : τ (cgerm B s (VS ^ m)) ∈ Ideal.span {τ (cgerm B s ϖB), τ (cgerm B s US)} := by
      rw [cgerm_pow, map_pow, hτq]; exact hm
    obtain ⟨c, hc, hcm⟩ := exists_mul_mem_of_mem_span_map B s τ hτcomap (VS ^ m) ϖB US hm'
    rw [hs] at hc
    exact mul_V_pow_notMem_span_algebraMap_U (q : O) hϖO (𝔛reg.width n) he m c hc hcm
  obtain ⟨hPu, hPv, hu𝔪, hv𝔪, huv_ne, htri⟩ :=
    branchIdeals_of_crossing ((q : ℕ) : XO.presheaf.stalk xn) u v (𝔛reg.width n) he huv h𝔪 hbn han

  set P : Ideal (XO.presheaf.stalk xn) := Ideal.comap (XO.presheaf.stalkSpecializes hspInf).hom (maximalIdeal _) with hPdef
  set Q : Ideal (XO.presheaf.stalk xn) := Ideal.comap (XO.presheaf.stalkSpecializes hspZero).hom (maximalIdeal _) with hQdef
  have h76 := ModularCurve.DRModelPackageLevel.not_branchIdeal_le_branchIdeal_crossingPt N₀ q hqN 𝔛 O ρO hϖO k toκ
    (𝔛reg.nodeEquiv n) hspInf hspZero
  have hQP' : ¬ Q ≤ P := h76.1
  have hPQ' : ¬ P ≤ Q := h76.2
  have hP𝔪 : P ≠ maximalIdeal _ := fun h => hQP' (h ▸ IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hQ𝔪 : Q ≠ maximalIdeal _ := fun h => hPQ' (h ▸ IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hQP : Q ≠ P := fun h => hQP' h.le

  have hp0 : ((q : ℕ) : (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)).presheaf.stalk (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) = 0 :=
    natCast_stalk_eq_zero_of_charP q (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) _
  have hpP : ((q : ℕ) : XO.presheaf.stalk xn) ∈ P := by
    rw [hPdef, Ideal.mem_comap, map_natCast]
    exact natCast_mem_maximalIdeal_stalk_of_map (𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ) _ q hp0
  have hpQ : ((q : ℕ) : XO.presheaf.stalk xn) ∈ Q := by
    rw [hQdef, Ideal.mem_comap, map_natCast]
    exact natCast_mem_maximalIdeal_stalk_of_map (𝔛.comp k (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ) _ q hp0

  have hor : u ∈ P := by

    obtain ⟨eC, heC, -, heq⟩ := 𝔛reg.strict_iso 0
    let ξ : ↥XO := (𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))
    let z := (inv eC).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))
    let y₀ : ↥𝔛reg.Y := (pullback.fst ((𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toBase)
      (Spec.map (CommRingCat.ofHom toκ)) ≫ (𝔛reg.comp (Sum.inl 0)).subschemeι).base z
    have hy₀ξ : 𝔛reg.toDR.base y₀ = ξ := by
      show 𝔛reg.toDR.base ((pullback.fst ((𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toBase)
        (Spec.map (CommRingCat.ofHom toκ)) ≫ (𝔛reg.comp (Sum.inl 0)).subschemeι).base
          ((inv eC).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) = ξ
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← heq, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
    have hy₀supp : y₀ ∈ (𝔛reg.comp (Sum.inl 0)).support := by
      have : y₀ ∈ ((𝔛reg.comp (Sum.inl 0)).support : Set 𝔛reg.Y) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
      exact this

    have hξU : ξ ∈ ch.U n := hspInf.mem_open (ch.U n).isOpen (ch.mem_U n)
    have hy₀U : y₀ ∈ 𝔛reg.toDR ⁻¹ᵁ (ch.U n) := by
      show 𝔛reg.toDR.base y₀ ∈ ch.U n
      rw [hy₀ξ]; exact hξU
    let y₀' : ↥(𝔛reg.toDR ⁻¹ᵁ (ch.U n)) := ⟨y₀, hy₀U⟩

    let d0 : Fin (𝔛reg.width n + 1) := ⟨0, Nat.succ_pos _⟩
    have hcp : DRResolvedModelPackageLevel.chainPos 𝔛reg.width n (d0 : ℕ) = Sum.inl 0 := by
      simp [DRResolvedModelPackageLevel.chainPos, d0]
    have hlab := ch.label n d0
    have hgw : (ch.g n).base y₀' ∈ (Fc (𝔛reg.width n) d0).support := by
      have h1 : y₀' ∈ ((Fc (𝔛reg.width n) d0).comap (ch.g n)).support := by
        rw [← hlab, Scheme.IdealSheafData.support_comap, hcp]
        exact hy₀supp
      rw [Scheme.IdealSheafData.support_comap] at h1
      exact h1

    obtain ⟨i, zc, hzc⟩ := Resolution.exists_ι_apply_eq ((q : ℕ) : O) (𝔛reg.width n) ((ch.g n).base y₀')
    have hle := le_asIdeal_of_mem_support_of_comap_eq ((q : ℕ) : O) (𝔛reg.width n) (Fc _ d0) i _
      (hF (𝔛reg.width n) i d0) zc (by rw [hzc]; exact hgw)
    simp only [d0] at hle
    have hi0 : (i : ℕ) = 0 := by
      by_contra hi
      rw [if_neg (Ne.symm hi), if_neg (by omega)] at hle
      exact zc.2.ne_top (top_le_iff.mp hle)
    have hVz : CrossingQuotient.V ((q : ℕ) : O) ∈ zc.asIdeal := by
      rw [if_pos hi0.symm] at hle; exact hle (Ideal.subset_span rfl)

    let ξU : ↥(ch.U n) := ⟨ξ, hξU⟩
    let qq := (ch.Φ n).inv.base y₀'
    have hfst : (pullback.fst (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n))).base qq = ξU := by
      show (pullback.fst (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n))).base ((ch.Φ n).inv.base y₀') = ξU
      rw [← Scheme.Hom.comp_apply, ← ch.Φ_fst n, Iso.inv_hom_id_assoc]
      apply Subtype.ext
      rw [morphismRestrict_base_coe]
      exact hy₀ξ
    have hsnd : (pullback.snd (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n))).base qq =
        (ch.g n).base y₀' := by
      show (pullback.snd (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n))).base ((ch.Φ n).inv.base y₀') = _
      rw [← Scheme.Hom.comp_apply, ← ch.Φ_snd n, Iso.inv_hom_id_assoc]
    have hfξ : (ch.f n).base ξU = (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n)).base
        ((Resolution.ι ((q : ℕ) : O) (𝔛reg.width n) i).base zc) := by
      rw [← hfst, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hsnd, hzc]
    have hVS : VS ∈ ((ch.f n).base ξU).asIdeal := by
      rw [hfξ, toCrossing_ι_asIdeal, Ideal.mem_comap]
      change resolutionChart ((q : ℕ) : O) (𝔛reg.width n) i (CrossingQuotient.V _) ∈ zc.asIdeal
      rw [resolutionChart_V]
      exact Ideal.mul_mem_left _ _ hVz

    have hspU : ξU ⤳ y := (subtype_specializes_iff ξU y).mpr hspInf
    have hspS : (ch.f n).base ξU ⤳ s := hspU.map (ch.f n).continuous
    have e1 : ((Spec B).presheaf.stalkSpecializes hspS).hom (cgerm B s VS) = cgerm B ((ch.f n).base ξU) VS := by
      change ((Spec B).presheaf.germ ⊤ s trivial ≫ (Spec B).presheaf.stalkSpecializes hspS).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    have e2 : ((ch.U n).toScheme.presheaf.stalkSpecializes hspU).hom (ι₁ (cgerm B s VS)) =
        ((ch.f n).stalkMap ξU).hom (cgerm B ((ch.f n).base ξU) VS) := by
      rw [← e1]
      change ((ch.f n).stalkMap y ≫ (ch.U n).toScheme.presheaf.stalkSpecializes hspU).hom _ =
        ((Spec B).presheaf.stalkSpecializes hspS ≫ (ch.f n).stalkMap ξU).hom _
      rw [Scheme.Hom.stalkSpecializes_stalkMap]
    have e3 : ((ch.U n).stalkIso y).hom ≫ XO.presheaf.stalkSpecializes hspInf =
        (ch.U n).toScheme.presheaf.stalkSpecializes hspU ≫ ((ch.U n).stalkIso ξU).hom := by
      have h3 := Scheme.Hom.stalkSpecializes_stalkMap (ch.U n).ι ξU y hspU
      rw [← Scheme.Opens.stalkIso_inv, ← Scheme.Opens.stalkIso_inv] at h3
      have h4 := (Iso.eq_inv_comp _).mp h3
      rw [← Category.assoc] at h4
      exact (Iso.comp_inv_eq _).mp h4
    have key : (XO.presheaf.stalkSpecializes hspInf).hom u =
        ((ch.U n).stalkIso ξU).hom.hom (((ch.f n).stalkMap ξU).hom (cgerm B ((ch.f n).base ξU) VS)) := by
      change (((ch.U n).stalkIso y).hom ≫ XO.presheaf.stalkSpecializes hspInf).hom (ι₁ (cgerm B s VS)) = _
      rw [e3]
      change ((ch.U n).stalkIso ξU).hom.hom (((ch.U n).toScheme.presheaf.stalkSpecializes hspU).hom (ι₁ (cgerm B s VS))) = _
      rw [e2]
    rw [hPdef, Ideal.mem_comap, key]
    have m1 : cgerm B ((ch.f n).base ξU) VS ∈ maximalIdeal _ := cgerm_mem_maximalIdeal B _ VS hVS
    have m2 : ((ch.f n).stalkMap ξU).hom (cgerm B ((ch.f n).base ξU) VS) ∈ maximalIdeal _ := by
      haveI : IsLocalHom ((ch.f n).stalkMap ξU).hom := (ch.f n).toLRSHom.prop ξU
      exact map_nonunit _ _ m1
    have m3 : ((ch.U n).stalkIso ξU).commRingCatIsoToRingEquiv
        (((ch.f n).stalkMap ξU).hom (cgerm B ((ch.f n).base ξU) VS)) ∈ maximalIdeal _ := by
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal ((ch.U n).stalkIso ξU).commRingCatIsoToRingEquiv]
      exact Ideal.mem_map_of_mem _ m2
    exact m3
  have hP : P = Ideal.span {((q : ℕ) : XO.presheaf.stalk xn), u} := by
    rcases htri P inferInstance hpP with h | h | h
    · exact absurd h hP𝔪
    · exact h
    · exfalso
      apply hv𝔪
      refine le_antisymm (IsLocalRing.le_maximalIdeal hPv.ne_top) ?_
      rw [← h𝔪, ← h]
      refine Ideal.span_le.mpr ?_
      rintro b (rfl | rfl | rfl)
      · exact hpP
      · exact hor
      · rw [h]; exact Ideal.subset_span (by simp)
  have hQ : Q = Ideal.span {((q : ℕ) : XO.presheaf.stalk xn), v} := by
    rcases htri Q inferInstance hpQ with h | h | h
    · exact absurd h hQ𝔪
    · exact absurd (h.trans hP.symm) hQP
    · exact h
  refine ⟨hspInf, hspZero, u, v, 1, isUnit_one, by rw [mul_one]; exact huv, h𝔪, hP.symm, hQ.symm, ?_⟩

  intro t ht htx d hd c
  let W : 𝔛reg.Y.Opens := 𝔛reg.toDR ⁻¹ᵁ (ch.U n)

  have htW : t.base (IsLocalRing.closedPoint O) ∈ W := by
    show 𝔛reg.toDR.base (t.base (IsLocalRing.closedPoint O)) ∈ ch.U n
    rw [← Scheme.Hom.comp_apply, htx]; exact ch.mem_U n
  obtain ⟨t', ht'⟩ := exists_lift_of_closedPoint_mem t W htW

  let tU : Spec (CommRingCat.of O) ⟶ (ch.U n).toScheme := t' ≫ (𝔛reg.toDR ∣_ ch.U n)
  let r : Spec (CommRingCat.of O) ⟶ Resolution ((q : ℕ) : O) (𝔛reg.width n) := t' ≫ ch.g n
  let σ : Spec (CommRingCat.of O) ⟶ Spec B := tU ≫ ch.f n
  have htDR : t ≫ 𝔛reg.toDR = tU ≫ (ch.U n).ι := by
    rw [← ht', Category.assoc, Category.assoc, ← morphismRestrict_ι]
  have hq1 : (t' ≫ (ch.Φ n).inv) ≫ pullback.fst (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n)) = tU := by
    rw [Category.assoc, ← ch.Φ_fst n, Iso.inv_hom_id_assoc]
  have hq2 : (t' ≫ (ch.Φ n).inv) ≫ pullback.snd (ch.f n) (Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n)) = r := by
    rw [Category.assoc, ← ch.Φ_snd n, Iso.inv_hom_id_assoc]
  have hσ : r ≫ Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n) = σ := by
    rw [← hq2, Category.assoc, ← pullback.condition, ← Category.assoc, hq1]
  have hσO : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n)))) = 𝟙 _ := by
    change ((t' ≫ (𝔛reg.toDR ∣_ ch.U n)) ≫ ch.f n) ≫ _ = _
    simp only [Category.assoc]
    rw [ch.f_over n, morphismRestrict_ι_assoc, 𝔛reg.toDR_over, ← Category.assoc, ht']
    exact ht
  have hr : r ≫ Resolution.toSpec ((q : ℕ) : O) (𝔛reg.width n) = 𝟙 _ := by
    change r ≫ (Resolution.toCrossing _ _ ≫ Spec.map _) = _
    rw [← Category.assoc, hσ]; exact hσO
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective σ
  let ψ : CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n) →+* O := ψ'.hom
  have hψ : r ≫ Resolution.toCrossing ((q : ℕ) : O) (𝔛reg.width n) = Spec.map (CommRingCat.ofHom ψ) := by
    rw [hσ, ← hψ']; rfl
  have hψO : ∀ o : O, ψ (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n)) o) = o := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ 𝔛reg.width n))) ≫ ψ') =
        Spec.map (𝟙 _) := by
      rw [Spec.map_comp, hψ', Spec.map_id]; exact hσO
    have h2 := Spec.map_injective h1
    intro o
    exact congrArg (fun φ : CommRingCat.of O ⟶ CommRingCat.of O => φ.hom o) h2

  have H := fun k' => MvPolynomial.CrossingQuotient.Resolution.mem_support_iff_eq_addVal_of_comp_toCrossing_eq
    ((q : ℕ) : O) hϖO (𝔛reg.width n) (Fc (𝔛reg.width n)) (hF (𝔛reg.width n)) r hr ψ hψ k'

  have htx₂ : (tU ≫ (ch.U n).ι).base (IsLocalRing.closedPoint O) = xn := by rw [← htDR]; exact htx
  have htUc : tU.base (IsLocalRing.closedPoint O) = y := by
    apply Subtype.ext
    rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, htx₂]
  have hread : (Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR)).hom
      ((XO.presheaf.stalkSpecializes (specializes_of_eq htx)).hom v) = ψ US := by
    rw [stalkClosedPointTo_stalkSpecializes_congr htDR htx htx₂ v]
    have hspy : tU.base (IsLocalRing.closedPoint O) ⤳ y := specializes_of_eq htUc
    have hspS' : (ch.f n).base (tU.base (IsLocalRing.closedPoint O)) ⤳ s := hspy.map (ch.f n).continuous

    let m : (Spec B).presheaf.stalk s := cgerm B s US
    let b : (ch.U n).toScheme.presheaf.stalk y := ((ch.f n).stalkMap y).hom m
    have hv : v = ((ch.U n).stalkIso y).hom.hom b := rfl

    have step1 : ∀ w, (Scheme.stalkClosedPointTo (tU ≫ (ch.U n).ι)).hom w =
        (Scheme.stalkClosedPointTo tU).hom (((ch.U n).ι.stalkMap (tU.base (IsLocalRing.closedPoint O))).hom w) :=
      fun w => congrArg (fun φ => φ.hom w) (Scheme.stalkClosedPointTo_comp tU (ch.U n).ι)

    have step2 : ∀ w, ((ch.U n).ι.stalkMap (tU.base (IsLocalRing.closedPoint O))).hom
        ((XO.presheaf.stalkSpecializes (specializes_of_eq htx₂)).hom w) =
        ((ch.U n).toScheme.presheaf.stalkSpecializes hspy).hom (((ch.U n).ι.stalkMap y).hom w) :=
      fun w => Scheme.Hom.stalkSpecializes_stalkMap_apply (ch.U n).ι _ y hspy w

    have step3 : ((ch.U n).ι.stalkMap y).hom (((ch.U n).stalkIso y).hom.hom b) = b := by
      rw [← Scheme.Opens.stalkIso_inv]
      exact congrArg (fun φ => φ.hom b) ((ch.U n).stalkIso y).hom_inv_id

    have step4 : ((ch.U n).toScheme.presheaf.stalkSpecializes hspy).hom b =
        ((ch.f n).stalkMap (tU.base (IsLocalRing.closedPoint O))).hom (((Spec B).presheaf.stalkSpecializes hspS').hom m) :=
      (Scheme.Hom.stalkSpecializes_stalkMap_apply (ch.f n) _ y hspy m).symm

    have step5 : ((Spec B).presheaf.stalkSpecializes hspS').hom m = cgerm B ((ch.f n).base (tU.base (IsLocalRing.closedPoint O))) US := by
      change ((Spec B).presheaf.germ ⊤ s trivial ≫ (Spec B).presheaf.stalkSpecializes hspS').hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]

    have step6 : ∀ w, (Scheme.stalkClosedPointTo tU).hom (((ch.f n).stalkMap (tU.base (IsLocalRing.closedPoint O))).hom w) =
        (Scheme.stalkClosedPointTo (tU ≫ ch.f n)).hom w :=
      fun w => (congrArg (fun φ => φ.hom w) (Scheme.stalkClosedPointTo_comp tU (ch.f n))).symm
    rw [hv, step1, step2, step3, step4, step5, step6]
    change (Scheme.stalkClosedPointTo σ).hom (cgerm B (σ.base (IsLocalRing.closedPoint O)) US) = _
    rw [stalkClosedPointTo_cgerm_congr hψ'.symm US]
    exact stalkClosedPointTo_cgerm B ψ' US
  have hd' : IsDiscreteValuationRing.addVal O (ψ US) = d := by rw [← hread]; exact hd

  have hde : d ≤ 𝔛reg.width n := by
    have hprod : ψ US * ψ VS = (q : O) ^ 𝔛reg.width n := by
      rw [← map_mul]
      change ψ (CrossingQuotient.U _ * CrossingQuotient.V _) = _
      rw [CrossingQuotient.U_mul_V, hψO]
    have hirr : Irreducible (q : O) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖO
    have hval := congrArg (IsDiscreteValuationRing.addVal O) hprod
    rw [AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hirr, hd'] at hval
    have hle : ((d : ℕ) : ℕ∞) ≤ (𝔛reg.width n : ℕ∞) := by
      rw [nsmul_eq_mul, mul_one] at hval
      rw [← hval]; exact le_self_add
    exact_mod_cast hle

  have hchain : ∀ (k' : ℕ) (hk' : k' ≤ 𝔛reg.width n),
      t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (DRResolvedModelPackageLevel.chainPos 𝔛reg.width n k')).support ↔ k' = d := by
    intro k' hk'
    let kf : Fin (𝔛reg.width n + 1) := ⟨k', Nat.lt_succ_of_le hk'⟩
    have hlab := ch.label n kf
    have e0 : t.base (IsLocalRing.closedPoint O) = W.ι.base (t'.base (IsLocalRing.closedPoint O)) := by rw [← ht']; rfl
    have h1 : t'.base (IsLocalRing.closedPoint O) ∈ ((𝔛reg.comp (DRResolvedModelPackageLevel.chainPos 𝔛reg.width n k')).comap W.ι).support ↔
        t'.base (IsLocalRing.closedPoint O) ∈ ((Fc (𝔛reg.width n) kf).comap (ch.g n)).support := by
      rw [← hlab]
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at h1
    rw [e0]
    refine h1.trans ?_
    refine (H kf).trans ?_
    rw [hd']
    exact Nat.cast_inj

  have hoff : ∀ (m : 𝔛reg.node) (i : Fin (𝔛reg.width m - 1)), m ≠ n →
      t.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp (Sum.inr ⟨m, i⟩)).support := by
    intro m i hm hmem
    have h1 := 𝔛reg.exc_image m i _ hmem
    have h2 : 𝔛reg.toDR.base (t.base (IsLocalRing.closedPoint O)) = xn := htx
    apply ch.not_mem_U n m hm
    change (pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv m) ∈ ch.U n
    rw [← h1, h2]
    exact ch.mem_U n

  rcases chainPos_cases 𝔛reg.width n he c with ⟨k', hk', rfl⟩ | ⟨m, i, hm, rfl⟩
  · rw [hchain k' hk']
    constructor
    · rintro rfl; rfl
    · intro h; exact chainPos_injOn 𝔛reg.width n he hk' hde h
  · constructor
    · intro h; exact absurd h (hoff m i hm)
    · intro h; exact absurd h.symm (chainPos_ne_inr 𝔛reg.width n hm i d)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackageLevel N₀ q 𝔛 O ρO k toκ)
    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((q : ℕ) : O) e).IdealSheafData) (hF : ∀ (e : ℕ) (i : Fin e) (k' : Fin (e + 1)), (Fc e k').comap (Resolution.ι ((q : ℕ) : O) e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O)))).inv.hom
          (if (k' : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((q : ℕ) : O)} else if (k' : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((q : ℕ) : O)}
            else ⊤)))
    (ch : (DRResolvedModelPackageLevelRam.ofUnramified 𝔛reg).DRResolvedModelChartsLevelRam Fc)
    (n : 𝔛reg.node) :
    haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
    ∃ (hspInf : ((𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)))
      (hspZero : ((𝔛.comp k (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)))
      (u v w₀ : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))),
      IsUnit w₀ ∧
      u * v = ((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))) ^ (𝔛reg.width n) * w₀ ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), u, v} = IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))) ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), u} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _) ∧
      Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))), v} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _) ∧
      (∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
      ∀ (htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.comp k (toκ.comp ρO) 0) (𝔛.comp k (toκ.comp ρO) 1) ≫ 𝔛.comp k (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))),
      ∀ d : ℕ,
        IsDiscreteValuationRing.addVal O
          ((Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR))
            (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom v)) = d →
        ∀ c : X0MqComponents 𝔛reg.width,
          t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
            c = DRResolvedModelPackageLevel.chainPos 𝔛reg.width n d) :=
  ChartAtLevelAux.exists_chartPresentation_stalk_ram N₀ q hqN 𝔛 O ρO hϖO toκ
    (DRResolvedModelPackageLevelRam.ofUnramified 𝔛reg) Fc hF ch n

end

end S_ModularCurve_DRResolvedModelPackageLevelRam_DRResolvedModelChartsLevelRam_exists_chartPresentation_stalk
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevelRam_DRResolvedModelChartsLevelRam_exists_chartPresentation_stalk (solution)
