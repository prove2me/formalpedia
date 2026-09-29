-- Prove2me | solution 1 for ModularCurve.DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b3ee7a13-8a46-50ee-b71f-e4d10fe4c214

import Mathlib
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve Topology NeronModelInfra

noncomputable section

namespace DICTPack

variable (p : ℕ) [Fact p.Prime]

abbrev A : Type := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

abbrev ιF : Spec (CommRingCat.of (A p)) ⟶ DRModel p :=
  TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev Fk (k : Type) [Field k] : Scheme.{0} :=
  pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))

abbrev fk (k : Type) [Field k] : Fk p k ⟶ DRModel p :=
  pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))

def T : Set ↥(DRModel p) := {x | ((DRModel.toBase p).base x).asIdeal = Ideal.span {(p : ℤ)}}

def xpt (Q : PrimeSpectrum (A p)) : ↥(DRModel p) := (ιF p).base Q

omit [Fact p.Prime] in
theorem ker_algebraMap_int (k : Type) [Field k] [CharP k p] :
    RingHom.ker (algebraMap ℤ k) = Ideal.span {(p : ℤ)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast]
  exact CharP.intCast_eq_zero_iff k p a

theorem asIdeal_eq_bot {k : Type} [Field k] (z : PrimeSpectrum k) : z.asIdeal = ⊥ :=
  (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top

theorem specMap_base_apply {R S : CommRingCat} (φ : R ⟶ S) (z : PrimeSpectrum S) :
    (Spec.map φ).base z = PrimeSpectrum.comap φ.hom z := rfl

omit [Fact p.Prime] in
theorem asIdeal_specMap_algebraMap (k : Type) [Field k] [CharP k p] (z : ↥(Spec (CommRingCat.of k))) :
    ((Spec.map (CommRingCat.ofHom (algebraMap ℤ k))).base z).asIdeal = Ideal.span {(p : ℤ)} := by
  rw [specMap_base_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, asIdeal_eq_bot,
    ← RingHom.ker_eq_comap_bot, ker_algebraMap_int]

omit [Fact p.Prime] in

theorem mem_range_specMap_iff (k : Type) [Field k] [CharP k p] (s : ↥(Spec (CommRingCat.of ℤ))) :
    s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))).base ↔ s.asIdeal = Ideal.span {(p : ℤ)} := by
  constructor
  · rintro ⟨z, rfl⟩
    exact asIdeal_specMap_algebraMap p k z
  · intro hs
    refine ⟨default, PrimeSpectrum.ext ?_⟩
    rw [asIdeal_specMap_algebraMap, hs]

theorem mem_range_fk_iff (k : Type) [Field k] [CharP k p] (x : ↥(DRModel p)) :
    x ∈ Set.range (fk p k).base ↔ x ∈ T p := by
  rw [Scheme.Pullback.range_fst]
  exact mem_range_specMap_iff p k _

theorem fk_mem_T (k : Type) [Field k] [CharP k p] (y : ↥(Fk p k)) : (fk p k).base y ∈ T p :=
  (mem_range_fk_iff p k _).mp ⟨y, rfl⟩

theorem toBase_xpt (Q : PrimeSpectrum (A p)) :
    (DRModel.toBase p).base (xpt p Q) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ (A p)))).base Q := by
  have h := TwoChartIntegralModel.ιFin_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  have h' := congrArg (fun g => g.base Q) h
  exact h'

theorem xpt_mem_T_iff (Q : PrimeSpectrum (A p)) : xpt p Q ∈ T p ↔ (p : A p) ∈ Q.asIdeal := by
  change ((DRModel.toBase p).base (xpt p Q)).asIdeal = _ ↔ _
  rw [toBase_xpt, specMap_base_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
  constructor
  · intro h
    have : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (A p)) Q.asIdeal := by rw [h]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  · intro h
    symm
    refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.mem_comap] using h

theorem exists_xpt_of_specializes {x : ↥(DRModel p)} {Q : PrimeSpectrum (A p)} (h : x ⤳ xpt p Q) :
    ∃ Q', x = xpt p Q' := by
  obtain ⟨Q', hQ'⟩ := (ιF p).isOpenEmbedding.isOpen_range.stableUnderGeneralization h ⟨Q, rfl⟩
  exact ⟨Q', hQ'.symm⟩

theorem le_of_xpt_specializes {Q' Q : PrimeSpectrum (A p)} (h : xpt p Q' ⤳ xpt p Q) :
    Q'.asIdeal ≤ Q.asIdeal := by
  have h' : Q' ⤳ Q := ((ιF p).isOpenEmbedding.isInducing.specializes_iff).mp h
  exact (PrimeSpectrum.le_iff_specializes Q' Q).mpr h'

theorem xpt_injective : Function.Injective (xpt p) := (ιF p).isOpenEmbedding.injective

theorem eq_xpt_of_mem_T_of_specializes {x : ↥(DRModel p)} (hx : x ∈ T p) {Q : PrimeSpectrum (A p)}
    (hQ : Q.asIdeal ∈ (Ideal.span {(p : A p)}).minimalPrimes) (h : x ⤳ xpt p Q) : x = xpt p Q := by
  obtain ⟨Q', rfl⟩ := exists_xpt_of_specializes p h
  have hle : Q'.asIdeal ≤ Q.asIdeal := le_of_xpt_specializes p h
  have hp : (p : A p) ∈ Q'.asIdeal := (xpt_mem_T_iff p Q').mp hx
  have hge : Q.asIdeal ≤ Q'.asIdeal :=
    hQ.2 ⟨Q'.isPrime, (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))⟩ hle
  rw [PrimeSpectrum.ext (le_antisymm hle hge)]

theorem xpt_mem_T_of_mem_minimalPrimes {Q : PrimeSpectrum (A p)}
    (hQ : Q.asIdeal ∈ (Ideal.span {(p : A p)}).minimalPrimes) : xpt p Q ∈ T p :=
  (xpt_mem_T_iff p Q).mpr (hQ.1.2 (Ideal.mem_span_singleton_self _))

section TwoPoints

variable {P : Fin 2 → Ideal (A p)} {hP : ∀ i, (P i).IsPrime}

theorem mem_minimalPrimes_of_hmin
    (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (i : Fin 2) :
    P i ∈ (Ideal.span {(p : A p)}).minimalPrimes := by
  rw [hmin]
  fin_cases i <;> simp

theorem xpt_ne_of_ne (hne : P 0 ≠ P 1) : xpt p ⟨P 0, hP 0⟩ ≠ xpt p ⟨P 1, hP 1⟩ := fun h =>
  hne (congrArg PrimeSpectrum.asIdeal (xpt_injective p h))

theorem eq_xptP_of_specializes (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (i : Fin 2)
    {x : ↥(DRModel p)} (hx : x ∈ T p) (h : x ⤳ xpt p ⟨P i, hP i⟩) : x = xpt p ⟨P i, hP i⟩ :=
  eq_xpt_of_mem_T_of_specializes p hx (mem_minimalPrimes_of_hmin p hmin i) h

theorem xptP_mem_range_fk (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (i : Fin 2)
    (k : Type) [Field k] [CharP k p] : xpt p ⟨P i, hP i⟩ ∈ Set.range (fk p k).base :=
  (mem_range_fk_iff p k _).mpr (xpt_mem_T_of_mem_minimalPrimes p (mem_minimalPrimes_of_hmin p hmin i))

theorem le_of_xptP_specializes (j : Fin 2) (𝔮 : PrimeSpectrum (A p)) (h : xpt p ⟨P j, hP j⟩ ⤳ xpt p 𝔮) :
    P j ≤ 𝔮.asIdeal :=
  le_of_xpt_specializes p h

end TwoPoints

theorem match_two {F X : Type*} [TopologicalSpace F] [TopologicalSpace X] (f : F → X) (hf : Continuous f)
    (a b : F) (hab : ∀ z, a ⤳ z ∨ b ⤳ z) (T : Set X) (hT : ∀ z, f z ∈ T)
    (x₀ x₁ : X) (hne : x₀ ≠ x₁) (h₀ : x₀ ∈ Set.range f) (h₁ : x₁ ∈ Set.range f)
    (hmax₀ : ∀ x ∈ T, x ⤳ x₀ → x = x₀) (hmax₁ : ∀ x ∈ T, x ⤳ x₁ → x = x₁) :
    (f a = x₀ ∧ f b = x₁) ∨ (f a = x₁ ∧ f b = x₀) := by
  obtain ⟨z₀, rfl⟩ := h₀
  obtain ⟨z₁, rfl⟩ := h₁
  have key : ∀ (c : F) (z : F), c ⤳ z → (∀ x ∈ T, x ⤳ f z → x = f z) → f c = f z :=
    fun c z hcz hmax => hmax (f c) (hT c) (hcz.map hf)
  rcases hab z₀ with ha₀ | hb₀ <;> rcases hab z₁ with ha₁ | hb₁
  · exact absurd ((key a z₀ ha₀ hmax₀).symm.trans (key a z₁ ha₁ hmax₁)) hne
  · exact Or.inl ⟨key a z₀ ha₀ hmax₀, key b z₁ hb₁ hmax₁⟩
  · exact Or.inr ⟨key a z₁ ha₁ hmax₁, key b z₀ hb₀ hmax₀⟩
  · exact absurd ((key b z₀ hb₀ hmax₀).symm.trans (key b z₁ hb₁ hmax₁)) hne

theorem match_fibre {P : Fin 2 → Ideal (A p)} {hP : ∀ i, (P i).IsPrime}
    (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    (k : Type) [Field k] [CharP k p] (a b : ↥(Fk p k)) (hab : ∀ z, a ⤳ z ∨ b ⤳ z) :
    ((fk p k).base a = xpt p ⟨P 0, hP 0⟩ ∧ (fk p k).base b = xpt p ⟨P 1, hP 1⟩) ∨
      ((fk p k).base a = xpt p ⟨P 1, hP 1⟩ ∧ (fk p k).base b = xpt p ⟨P 0, hP 0⟩) :=
  match_two (fk p k).base (fk p k).continuous a b hab (T p) (fk_mem_T p k) _ _ (xpt_ne_of_ne p hne)
    (xptP_mem_range_fk p hmin 0 k) (xptP_mem_range_fk p hmin 1 k)
    (fun _ hx h => eq_xptP_of_specializes p hmin 0 hx h) (fun _ hx h => eq_xptP_of_specializes p hmin 1 hx h)

section Rho

variable {K k : Type} [Field K] [Field k] (σ : K →+* k)

theorem comp_algebraMap_int : σ.comp (algebraMap ℤ K) = algebraMap ℤ k := RingHom.ext_int _ _

theorem specMap_σ_comp :
    Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ K)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, comp_algebraMap_int]

def ρ : Fk p k ⟶ Fk p K :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ))
    (by rw [pullback.condition, Category.assoc, specMap_σ_comp])

@[reassoc (attr := simp)]
theorem ρ_fst : ρ p σ ≫ fk p K = fk p k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ρ_snd : ρ p σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ) :=
  pullback.lift_snd _ _ _

theorem fk_ρ_apply (y : ↥(Fk p k)) : (fk p K).base ((ρ p σ).base y) = (fk p k).base y := by
  change (ρ p σ ≫ fk p K) y = _
  rw [ρ_fst]

theorem sectionFibre_ρ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)) :
    DRModel.sectionFibre ε (algebraMap ℤ k) ≫ ρ p σ =
      Spec.map (CommRingCat.ofHom σ) ≫ DRModel.sectionFibre ε (algebraMap ℤ K) := by
  apply pullback.hom_ext
  · rw [Category.assoc, ρ_fst, DRModel.sectionFibre, DRModel.sectionFibre, pullback.lift_fst, Category.assoc,
      pullback.lift_fst, ← Category.assoc, specMap_σ_comp]
  · rw [Category.assoc, ρ_snd, DRModel.sectionFibre, DRModel.sectionFibre, pullback.lift_snd_assoc, Category.assoc,
      pullback.lift_snd, Category.id_comp, Category.comp_id]

theorem ρ_sectionFibre_apply (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    (z : ↥(Spec (CommRingCat.of k))) (z' : ↥(Spec (CommRingCat.of K))) :
    (ρ p σ).base ((DRModel.sectionFibre ε (algebraMap ℤ k)).base z) =
      (DRModel.sectionFibre ε (algebraMap ℤ K)).base z' := by
  change (DRModel.sectionFibre ε (algebraMap ℤ k) ≫ ρ p σ) z = _
  rw [sectionFibre_ρ, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

end Rho

noncomputable def σ₀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k] : AlgebraicClosure (ZMod p) →+* k :=
  letI := ZMod.algebra k p
  (IsAlgClosed.lift (R := ZMod p) (M := k) (S := AlgebraicClosure (ZMod p))).toRingHom

section Upstairs

variable (𝔛 : DRModelPackage p)

noncomputable def ηInf (k : Type) [Field k] [CharP k p] [IsAlgClosed k] : ↥(Fk p k) :=
  (𝔛.compInf k).base (genericPoint ↥((𝔛.ratModel k).C))

noncomputable def ηZero (k : Type) [Field k] [CharP k p] [IsAlgClosed k] : ↥(Fk p k) :=
  (𝔛.compZero k).base (genericPoint ↥((𝔛.ratModel k).C))

noncomputable def ePt (k : Type) [Field k] : ↥(Fk p k) :=
  (DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k)

theorem mem_range_iff_specializes_of_isClosed {C Y : Type*} [TopologicalSpace C] [TopologicalSpace Y]
    [QuasiSober C] [IrreducibleSpace C] (g : C → Y) (hg : Continuous g) (hcl : IsClosed (Set.range g)) (y : Y) :
    y ∈ Set.range g ↔ g (genericPoint C) ⤳ y := by
  constructor
  · rintro ⟨c, rfl⟩
    exact (genericPoint_specializes c).map hg
  · intro h
    rw [specializes_iff_mem_closure] at h
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) h

section U
variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

theorem mem_range_compInf_iff (y : ↥(Fk p k)) : y ∈ Set.range (𝔛.compInf k).base ↔ ηInf p 𝔛 k ⤳ y := by
  haveI := 𝔛.compInf_isClosedImmersion k
  exact mem_range_iff_specializes_of_isClosed (𝔛.compInf k).base (𝔛.compInf k).continuous
    (𝔛.compInf k).isClosedEmbedding.isClosed_range y

theorem mem_range_compZero_iff (y : ↥(Fk p k)) : y ∈ Set.range (𝔛.compZero k).base ↔ ηZero p 𝔛 k ⤳ y := by
  haveI := 𝔛.compZero_isClosedImmersion k
  exact mem_range_iff_specializes_of_isClosed (𝔛.compZero k).base (𝔛.compZero k).continuous
    (𝔛.compZero k).isClosedEmbedding.isClosed_range y

theorem cover (y : ↥(Fk p k)) : ηInf p 𝔛 k ⤳ y ∨ ηZero p 𝔛 k ⤳ y := by
  rcases 𝔛.comp_jointly_surjective k y with h | h
  · exact Or.inl ((mem_range_compInf_iff p 𝔛 k y).mp h)
  · exact Or.inr ((mem_range_compZero_iff p 𝔛 k y).mp h)

theorem ηInf_specializes_ePt : ηInf p 𝔛 k ⤳ ePt p 𝔛 k :=
  (mem_range_compInf_iff p 𝔛 k _).mp (𝔛.εinf_mem_compInf k ⟨IsLocalRing.closedPoint k, rfl⟩)

omit [CharP k p] [IsAlgClosed k] in

theorem fk_ePt_mem_smoothLocus : (fk p k).base (ePt p 𝔛 k) ∈ 𝔛.smoothLocus := by
  apply 𝔛.εinf_mem_smoothLocus
  refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap ℤ k))).base (IsLocalRing.closedPoint k), ?_⟩
  have h : DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k) ≫ fk p k =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ 𝔛.εinf.1 := pullback.lift_fst _ _ _
  rw [ePt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

theorem not_ηZero_specializes_ePt : ¬ ηZero p 𝔛 k ⤳ ePt p 𝔛 k := by
  intro h0
  have hsm : ePt p 𝔛 k ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus) :=
    fk_ePt_mem_smoothLocus p 𝔛 k
  exact (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
    p 𝔛 k (ePt p 𝔛 k)).mp hsm
    ⟨(mem_range_compInf_iff p 𝔛 k _).mpr (ηInf_specializes_ePt p 𝔛 k),
      (mem_range_compZero_iff p 𝔛 k _).mpr h0⟩

end U

section K

variable {P : Fin 2 → Ideal (A p)} {hP : ∀ i, (P i).IsPrime}

theorem exists_index (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    ∃ i : Fin 2, (fk p k).base (ηInf p 𝔛 k) = xpt p ⟨P i, hP i⟩ ∧
      ∀ j, j ≠ i → (fk p k).base (ηZero p 𝔛 k) = xpt p ⟨P j, hP j⟩ := by
  rcases match_fibre p (hP := hP) hmin hne k (ηInf p 𝔛 k) (ηZero p 𝔛 k) (cover p 𝔛 k) with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · refine ⟨0, h0, fun j hj => ?_⟩
    obtain rfl : j = 1 := by fin_cases j <;> simp_all
    exact h1
  · refine ⟨1, h1, fun j hj => ?_⟩
    obtain rfl : j = 0 := by fin_cases j <;> simp_all
    exact h0

include hP in

theorem fk_ηInf_eq (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    (fk p k).base (ηInf p 𝔛 k) =
      (fk p (AlgebraicClosure (ZMod p))).base (ηInf p 𝔛 (AlgebraicClosure (ZMod p))) := by

  have h1 : (ρ p (σ₀ p k)).base (ηInf p 𝔛 k) ⤳ ePt p 𝔛 (AlgebraicClosure (ZMod p)) := by
    have := (ηInf_specializes_ePt p 𝔛 k).map (ρ p (σ₀ p k)).continuous
    rwa [ePt, ρ_sectionFibre_apply p (σ₀ p k) 𝔛.εinf (IsLocalRing.closedPoint k)
      (IsLocalRing.closedPoint (AlgebraicClosure (ZMod p)))] at this

  have h2 : ηInf p 𝔛 (AlgebraicClosure (ZMod p)) ⤳ (ρ p (σ₀ p k)).base (ηInf p 𝔛 k) := by
    rcases cover p 𝔛 (AlgebraicClosure (ZMod p)) ((ρ p (σ₀ p k)).base (ηInf p 𝔛 k)) with h | h
    · exact h
    · exact absurd (h.trans h1) (not_ηZero_specializes_ePt p 𝔛 (AlgebraicClosure (ZMod p)))

  have h3 : (fk p (AlgebraicClosure (ZMod p))).base (ηInf p 𝔛 (AlgebraicClosure (ZMod p))) ⤳
      (fk p k).base (ηInf p 𝔛 k) := by
    have := h2.map (fk p (AlgebraicClosure (ZMod p))).continuous
    rwa [fk_ρ_apply] at this
  obtain ⟨i, hi, -⟩ := exists_index p 𝔛 (hP := hP) hmin hne k
  rw [hi] at h3 ⊢
  exact (eq_xptP_of_specializes p hmin i (fk_mem_T p (AlgebraicClosure (ZMod p)) _) h3).symm

theorem goal_of_index (i : Fin 2) (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (hi : ∀ j, j ≠ i → (fk p k).base (ηZero p 𝔛 k) = xpt p ⟨P j, hP j⟩)
    (y : ↥(Fk p k)) (𝔮 : PrimeSpectrum (A p)) (hy : (fk p k).base y = xpt p 𝔮)
    (h𝔮 : ∀ j : Fin 2, j ≠ i → ¬ P j ≤ 𝔮.asIdeal) :
    y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hy0 : y ∉ Set.range (𝔛.compZero k).base := by
    intro hy0
    have hsp : (fk p k).base (ηZero p 𝔛 k) ⤳ (fk p k).base y :=
      ((mem_range_compZero_iff p 𝔛 k y).mp hy0).map (fk p k).continuous
    rw [hi j hj, hy] at hsp
    exact h𝔮 j hj (le_of_xptP_specializes p j 𝔮 hsp)
  exact ⟨(𝔛.comp_jointly_surjective k y).resolve_right hy0, hy0⟩

end K

end Upstairs

end DICTPack

namespace DICTPack

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)

section Desc

variable {P : Fin 2 → Ideal (A p)} {hP : ∀ i, (P i).IsPrime}
variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

omit [IsAlgClosed k] in

theorem flat_ρ_castHom : Flat (ρ p (ZMod.castHom (dvd_refl p) k)) := by
  have big : IsPullback (ρ p (ZMod.castHom (dvd_refl p) k) ≫ fk p (ZMod p)) (pullback.snd _ _) (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p)))) := by
    convert IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) using 1
    · exact ρ_fst p _
    · exact specMap_σ_comp _
  have sq : IsPullback (ρ p (ZMod.castHom (dvd_refl p) k)) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) k))) :=
    IsPullback.of_right big (ρ_snd p _) (IsPullback.of_hasPullback _ _)
  have hσ : (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) k)).hom.Flat := by
    show (ZMod.castHom (dvd_refl p) k).Flat
    unfold RingHom.Flat
    infer_instance
  haveI : Flat (Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) k))) := Flat.SpecMap_iff.mpr hσ
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance

omit [Fact p.Prime] in

theorem isClosedImmersion_fk_zmod [Fact p.Prime] : IsClosedImmersion (fk p (ZMod p)) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p)))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  exact MorphismProperty.pullback_fst _ _ inferInstance

include hP in

theorem P_ne (hne : P 0 ≠ P 1) {i j : Fin 2} (hji : j ≠ i)
    (heq : xpt p ⟨P j, hP j⟩ = xpt p ⟨P i, hP i⟩) : False := by
  have hPji : P j = P i := by simpa using congrArg PrimeSpectrum.asIdeal (xpt_injective p heq)
  apply hne
  fin_cases i <;> fin_cases j <;> simp_all

include hP in

theorem mem_range_compInf_of_specializes (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1})
    (hne : P 0 ≠ P 1) (y : ↥(Fk p k))
    (h : (fk p k).base (ηInf p 𝔛 k) ⤳ (fk p k).base y) : y ∈ Set.range (𝔛.compInf k).base := by
  haveI := flat_ρ_castHom p k
  haveI := isClosedImmersion_fk_zmod p

  have h1 : (ρ p (ZMod.castHom (dvd_refl p) k)).base (ηInf p 𝔛 k) ⤳ (ρ p (ZMod.castHom (dvd_refl p) k)).base y := by
    rw [← (fk p (ZMod p)).isClosedEmbedding.isInducing.specializes_iff, fk_ρ_apply, fk_ρ_apply]
    exact h

  obtain ⟨y', hy', hρ⟩ := Flat.generalizingMap (ρ p (ZMod.castHom (dvd_refl p) k)) h1
  rcases cover p 𝔛 k y' with h' | h'
  · exact (mem_range_compInf_iff p 𝔛 k y).mpr (h'.trans hy')
  · exfalso
    obtain ⟨i, hi, hj⟩ := exists_index p 𝔛 (hP := hP) hmin hne k
    obtain ⟨j, hji⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
    have hfk : (fk p k).base y' = (fk p k).base (ηInf p 𝔛 k) := by
      rw [← fk_ρ_apply p (ZMod.castHom (dvd_refl p) k) y', hρ, fk_ρ_apply]
    have hsp : xpt p ⟨P j, hP j⟩ ⤳ xpt p ⟨P i, hP i⟩ := by
      rw [← hj j hji, ← hi, ← hfk]
      exact h'.map (fk p k).continuous
    exact P_ne p (hP := hP) hne hji (eq_xptP_of_specializes p hmin i
      (xpt_mem_T_of_mem_minimalPrimes p (mem_minimalPrimes_of_hmin p hmin j)) hsp)

include hP in

theorem mem_range_compZero_of_specializes (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1})
    (hne : P 0 ≠ P 1) (y : ↥(Fk p k))
    (h : (fk p k).base (ηZero p 𝔛 k) ⤳ (fk p k).base y) : y ∈ Set.range (𝔛.compZero k).base := by
  haveI := flat_ρ_castHom p k
  haveI := isClosedImmersion_fk_zmod p
  have h1 : (ρ p (ZMod.castHom (dvd_refl p) k)).base (ηZero p 𝔛 k) ⤳ (ρ p (ZMod.castHom (dvd_refl p) k)).base y := by
    rw [← (fk p (ZMod p)).isClosedEmbedding.isInducing.specializes_iff, fk_ρ_apply, fk_ρ_apply]
    exact h
  obtain ⟨y', hy', hρ⟩ := Flat.generalizingMap (ρ p (ZMod.castHom (dvd_refl p) k)) h1
  rcases cover p 𝔛 k y' with h' | h'
  · exfalso
    obtain ⟨i, hi, hj⟩ := exists_index p 𝔛 (hP := hP) hmin hne k
    obtain ⟨j, hji⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
    have hfk : (fk p k).base y' = (fk p k).base (ηZero p 𝔛 k) := by
      rw [← fk_ρ_apply p (ZMod.castHom (dvd_refl p) k) y', hρ, fk_ρ_apply]
    have hsp : xpt p ⟨P i, hP i⟩ ⤳ xpt p ⟨P j, hP j⟩ := by
      rw [← hj j hji, ← hi, ← hfk]
      exact h'.map (fk p k).continuous
    exact P_ne p (hP := hP) hne hji (eq_xptP_of_specializes p hmin j
      (xpt_mem_T_of_mem_minimalPrimes p (mem_minimalPrimes_of_hmin p hmin i)) hsp).symm
  · exact (mem_range_compZero_iff p 𝔛 k y).mpr (h'.trans hy')

include hP in

theorem preimage_closure_image_compInf (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1})
    (hne : P 0 ≠ P 1) :
    (fk p k).base ⁻¹' closure ((fk p k).base '' Set.range (𝔛.compInf k).base) = Set.range (𝔛.compInf k).base := by
  apply Set.Subset.antisymm
  · intro y hy
    apply mem_range_compInf_of_specializes p 𝔛 (hP := hP) k hmin hne y
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure hy
    rintro _ ⟨w, hw, rfl⟩
    exact specializes_iff_mem_closure.mp (((mem_range_compInf_iff p 𝔛 k w).mp hw).map (fk p k).continuous)
  · exact (Set.subset_preimage_image _ _).trans (Set.preimage_mono subset_closure)

include hP in

theorem preimage_closure_image_compZero (hmin : (Ideal.span {(p : A p)}).minimalPrimes = {P 0, P 1})
    (hne : P 0 ≠ P 1) :
    (fk p k).base ⁻¹' closure ((fk p k).base '' Set.range (𝔛.compZero k).base) = Set.range (𝔛.compZero k).base := by
  apply Set.Subset.antisymm
  · intro y hy
    apply mem_range_compZero_of_specializes p 𝔛 (hP := hP) k hmin hne y
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure hy
    rintro _ ⟨w, hw, rfl⟩
    exact specializes_iff_mem_closure.mp (((mem_range_compZero_iff p 𝔛 k w).mp hw).map (fk p k).continuous)
  · exact (Set.subset_preimage_image _ _).trans (Set.preimage_mono subset_closure)

end Desc

theorem preimage_closure_image_eq_of_comp {O : Type} [CommRing O] {k : Type} [Field k]
    (bc : Fk p k ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (hbc₁ : bc ≫ pullback.fst _ _ = fk p k) (C : Set ↥(Fk p k))
    (hC : (fk p k).base ⁻¹' closure ((fk p k).base '' C) = C) :
    bc.base ⁻¹' closure (bc.base '' C) = C := by
  apply Set.Subset.antisymm
  · intro y hy
    have e : ∀ z, (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (bc.base z) =
        (fk p k).base z := fun z => by
      show (bc ≫ pullback.fst _ _).base z = _; rw [hbc₁]
    have h1 := closure_subset_preimage_closure_image (s := bc.base '' C)
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).continuous hy
    rw [Set.mem_preimage, Set.image_image, e y, funext e] at h1
    have h2 : y ∈ (fk p k).base ⁻¹' closure ((fk p k).base '' C) := h1
    rwa [hC] at h2
  · exact (Set.subset_preimage_image _ _).trans (Set.preimage_mono subset_closure)

end DICTPack

open DICTPack in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _) :
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.compInf κ).base) = Set.range (𝔛.compInf κ).base ∧
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.compZero κ).base) = Set.range (𝔛.compZero κ).base := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨-, hcard, -, -⟩ := ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int p
  obtain ⟨P₀, P₁, hne, hmin⟩ := Set.ncard_eq_two.mp hcard
  have hmin' : (Ideal.span {(p : A p)}).minimalPrimes = {(![P₀, P₁] : Fin 2 → Ideal (A p)) 0, (![P₀, P₁] : Fin 2 → Ideal (A p)) 1} := by
    simpa using hmin
  have hne' : (![P₀, P₁] : Fin 2 → Ideal (A p)) 0 ≠ (![P₀, P₁] : Fin 2 → Ideal (A p)) 1 := by simpa using hne
  have hP : ∀ i, ((![P₀, P₁] : Fin 2 → Ideal (A p)) i).IsPrime := fun i => (mem_minimalPrimes_of_hmin p hmin' i).1.1
  exact ⟨preimage_closure_image_eq_of_comp p bc hbc₁ _ (preimage_closure_image_compInf p 𝔛 (hP := hP) κ hmin' hne'),
    preimage_closure_image_eq_of_comp p bc hbc₁ _ (preimage_closure_image_compZero p 𝔛 (hP := hP) κ hmin' hne')⟩

end

end S_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq (solution)
