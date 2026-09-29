-- Prove2me | solution 1 for ModularCurve.relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1e00d489-97f7-5f97-810e-9d447c1f594d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_relfinrank_eq_sub_one_x1FunctionField_mul_x1x0
import Theorems.Thm_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace CycDiamondAux

theorem isGalois_and_isCyclic {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    {G : Type*} [Group G] [IsCyclic G] (τ : G →* (E ≃ₐ[k] E))
    (h : Module.finrank k E ≤ Nat.card τ.range) : IsGalois k E ∧ IsCyclic (E ≃ₐ[k] E) := by
  classical
  have hfix : Module.finrank (IntermediateField.fixedField τ.range) E = Nat.card τ.range :=
    IntermediateField.finrank_fixedField_eq_card τ.range
  have htower := Module.finrank_mul_finrank k (↥(IntermediateField.fixedField τ.range)) E
  have hEpos : 0 < Module.finrank (↥(IntermediateField.fixedField τ.range)) E := Module.finrank_pos
  have h1 : Module.finrank k (↥(IntermediateField.fixedField τ.range)) = 1 := by
    have hle : Module.finrank k (↥(IntermediateField.fixedField τ.range)) *
        Module.finrank (↥(IntermediateField.fixedField τ.range)) E ≤
        1 * Module.finrank (↥(IntermediateField.fixedField τ.range)) E := by
      rw [htower, one_mul, hfix]; exact h
    have := Nat.le_of_mul_le_mul_right hle hEpos
    have hkpos : 0 < Module.finrank k (↥(IntermediateField.fixedField τ.range)) := Module.finrank_pos
    omega
  have hbot : IntermediateField.fixedField τ.range = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  have hgal : IsGalois k E := by
    refine IsGalois.of_fixedField_eq_bot k E (le_bot_iff.mp ?_)
    rw [← hbot]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun φ _ => hx φ (Subgroup.mem_top φ)
  haveI := hgal
  refine ⟨hgal, ?_⟩
  have hcard : Nat.card (E ≃ₐ[k] E) = Module.finrank k E := IsGalois.card_aut_eq_finrank k E
  have htop : τ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm (Subgroup.card_le_card_group _) (hcard ▸ h)
  exact isCyclic_of_surjective τ (MonoidHom.range_eq_top.mp htop)

theorem natCard_range_le {G X Y : Type*} [Group G] [Group X] [Group Y] [Finite G]
    (a : G →* X) (b : G →* Y) (h : b.ker ≤ a.ker) : Nat.card a.range ≤ Nat.card b.range := by
  rw [← Subgroup.index_ker, ← Subgroup.index_ker]
  haveI : b.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) (Subgroup.index_dvd_of_le h)

theorem natCard_range_eq_finrank {F₀ A : Type*} [Field F₀] [Field A] [Algebra F₀ A] {G : Type*} [Group G]
    [Finite G] (δ : G →* (A ≃ₐ[F₀] A)) :
    Nat.card δ.range = Module.finrank (↥(IntermediateField.fixedField δ.range)) A := by
  classical
  haveI : Finite ↥δ.range := Finite.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective
  haveI : Fintype ↥δ.range := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (FixedPoints.finrank_eq_card (↥δ.range) A).symm

theorem finrank_transport {R₀ S₀ R₁ S₁ : Type*} [Field R₀] [Field S₀] [Algebra R₀ S₀] [Field R₁] [Field S₁]
    [Algebra R₁ S₁] (i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁) (hc : ∀ r : R₀, algebraMap R₁ S₁ (i r) = j (algebraMap R₀ S₀ r)) :
    Module.finrank R₀ S₀ = Module.finrank R₁ S₁ :=
  Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext hc)

theorem natCard_range_eq_finrank_extendScalars {k V : Type*} [Field k] [Field V] [Algebra k V]
    {F₁ F : IntermediateField k V} (h₁ : F₁ ≤ F) {G : Type*} [Group G] [Finite G]
    {F₀ : Type*} [Field F₀] {algF : Algebra F₀ ↥F}
    (δ : G →* (↥F ≃ₐ[F₀] ↥F)) (hfix : ∀ x : ↥F, (x : V) ∈ F₁ ↔ ∀ u : G, δ u x = x) :
    Nat.card ↥δ.range = Module.finrank ↥F₁ ↥(IntermediateField.extendScalars h₁) := by
  rw [natCard_range_eq_finrank δ]
  exact finrank_transport
    { toFun := fun s => ⟨((s.1 : ↥F) : V),
        (hfix s.1).2 fun u => (IntermediateField.mem_fixedField_iff _ _).1 s.2 (δ u) ⟨u, rfl⟩⟩
      invFun := fun z => ⟨⟨z.1, h₁ z.2⟩, (IntermediateField.mem_fixedField_iff _ _).2 (by
        rintro _ ⟨u, rfl⟩
        exact (hfix _).1 z.2 u)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
    (fun _ => rfl)

theorem eq_one_of_cast_eq_one {M p : ℕ} [NeZero (M * p)] (h : Nat.Coprime M p) (x : ZMod (M * p))
    (h1 : (ZMod.castHom (dvd_mul_right M p) (ZMod M)) x = 1)
    (h2 : (ZMod.castHom (dvd_mul_left p M) (ZMod p)) x = 1) : x = 1 := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val x, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h1 h2
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩

theorem isCyclic_ker_unitsMap (M p : ℕ) [NeZero M] [Fact p.Prime] (h : Nat.Coprime M p) :
    IsCyclic ↥(ZMod.unitsMap (dvd_mul_right M p)).ker := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : ↥(ZMod.unitsMap (dvd_mul_right M p)).ker →* (ZMod p)ˣ :=
    (ZMod.unitsMap (dvd_mul_left p M)).comp (ZMod.unitsMap (dvd_mul_right M p)).ker.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ hfu
    rw [MonoidHom.mem_ker, ZMod.unitsMap_def] at hu
    change ZMod.unitsMap (dvd_mul_left p M) u = 1 at hfu
    rw [ZMod.unitsMap_def] at hfu
    have h1 := congrArg Units.val hu
    have h2 := congrArg Units.val hfu
    rw [Units.coe_map, Units.val_one] at h1 h2
    have : (u : ZMod (M * p)) = 1 := eq_one_of_cast_eq_one h u h1 h2
    exact Subtype.ext (Units.ext this)
  exact isCyclic_of_injective f hf

def restrictHom {k V : Type*} [Field k] [Field V] [Algebra k V] {A B : IntermediateField k V} (hAB : A ≤ B)
    {G : Type*} [Group G] (ρ : G →* (↥B ≃ₐ[k] ↥B))
    (hρ : ∀ (g : G) (y : V) (hy : y ∈ A), (ρ g ⟨y, hAB hy⟩ : V) = y) :
    G →* (↥(IntermediateField.extendScalars hAB) ≃ₐ[↥A] ↥(IntermediateField.extendScalars hAB)) where
  toFun g :=
    { toFun := fun x => ⟨(ρ g ⟨x.1, x.2⟩ : V), (ρ g ⟨x.1, x.2⟩).2⟩
      invFun := fun x => ⟨((ρ g).symm ⟨x.1, x.2⟩ : V), ((ρ g).symm ⟨x.1, x.2⟩).2⟩
      left_inv := fun x => Subtype.ext (by
        change (((ρ g).symm (ρ g ⟨x.1, x.2⟩)) : V) = x.1
        rw [AlgEquiv.symm_apply_apply])
      right_inv := fun x => Subtype.ext (by
        change ((ρ g ((ρ g).symm ⟨x.1, x.2⟩)) : V) = x.1
        rw [AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => Subtype.ext (by
        change ((ρ g (⟨x.1, x.2⟩ * ⟨y.1, y.2⟩)) : V) = (ρ g ⟨x.1, x.2⟩ : V) * (ρ g ⟨y.1, y.2⟩ : V)
        rw [map_mul]; rfl)
      map_add' := fun x y => Subtype.ext (by
        change ((ρ g (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩)) : V) = (ρ g ⟨x.1, x.2⟩ : V) + (ρ g ⟨y.1, y.2⟩ : V)
        rw [map_add]; rfl)
      commutes' := fun a => Subtype.ext (hρ g a.1 a.2) }
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by
    change ((ρ 1 ⟨x.1, x.2⟩) : V) = x.1
    rw [map_one]; rfl)
  map_mul' g g' := AlgEquiv.ext fun x => Subtype.ext (by
    change ((ρ (g * g') ⟨x.1, x.2⟩) : V) = (ρ g (ρ g' ⟨x.1, x.2⟩) : V)
    rw [map_mul]; rfl)

theorem fixes_adjoin {k V : Type*} [Field k] [Field V] [Algebra k V] {B : IntermediateField k V} {S : Set V}
    (hS : ∀ z ∈ S, z ∈ B) {G : Type*} [Group G] (ρ : G →* (↥B ≃ₐ[k] ↥B))
    (hρS : ∀ (g : G) (z : V) (hz : z ∈ S), (ρ g ⟨z, hS z hz⟩ : V) = z)
    (g : G) (y : V) (hy : y ∈ IntermediateField.adjoin k S) (hyB : y ∈ B) : (ρ g ⟨y, hyB⟩ : V) = y := by
  have hle : IntermediateField.adjoin k S ≤ IntermediateField.lift (IntermediateField.fixedField ρ.range) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    show ((⟨z, hS z hz⟩ : ↥B) : V) ∈ _
    rw [SetLike.mem_coe, IntermediateField.mem_lift, IntermediateField.mem_fixedField_iff]
    rintro _ ⟨g', rfl⟩
    exact Subtype.ext (hρS g' z hz)
  have hw := (IntermediateField.mem_lift (⟨y, hyB⟩ : ↥B)).1 (hle hy)
  rw [IntermediateField.mem_fixedField_iff] at hw
  exact congrArg Subtype.val (hw (ρ g) ⟨g, rfl⟩)

theorem isGalois_and_isCyclic_of_restrict {k V : Type*} [Field k] [Field V] [Algebra k V]
    {A B : IntermediateField k V} (hAB : A ≤ B) {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (ρ : G →* (↥B ≃ₐ[k] ↥B)) (hρ : ∀ (g : G) (y : V) (hy : y ∈ A), (ρ g ⟨y, hAB hy⟩ : V) = y)
    {X : Type*} [Group X] (δ : G →* X) (hker : ∀ g : G, (∀ y : ↥B, (ρ g y : V) = y) → δ g = 1)
    (hcard : Module.finrank ↥A ↥(IntermediateField.extendScalars hAB) ≤ Nat.card ↥δ.range)
    (hpos : 0 < Module.finrank ↥A ↥(IntermediateField.extendScalars hAB)) :
    IsGalois ↥A ↥(IntermediateField.extendScalars hAB) ∧
      IsCyclic (↥(IntermediateField.extendScalars hAB) ≃ₐ[↥A] ↥(IntermediateField.extendScalars hAB)) := by
  haveI : FiniteDimensional ↥A ↥(IntermediateField.extendScalars hAB) := Module.finite_of_finrank_pos hpos
  have hk : (restrictHom hAB ρ hρ).ker ≤ δ.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    refine hker g fun y => ?_
    have := congrArg (fun φ => ((φ ⟨(y : V), y.2⟩ : ↥(IntermediateField.extendScalars hAB)) : V)) hg
    beta_reduce at this
    exact this
  exact isGalois_and_isCyclic (restrictHom hAB ρ hρ) (hcard.trans (natCard_range_le δ _ hk))

theorem coeffEmb_rat (x : LaurentSeries ℚ) (inst : Algebra ℚ ℚ) : @ModularCurve.coeffEmb ℚ _ inst x = x := by
  have h : @algebraMap ℚ ℚ _ _ inst = RingHom.id ℚ := Subsingleton.elim _ _
  unfold ModularCurve.coeffEmb
  rw [h, ModularCurve.coeffMap_id]

theorem laurentBaseChange_rat (X : IntermediateField ℚ (LaurentSeries ℚ)) (inst : Algebra ℚ ℚ) :
    @ModularCurve.laurentBaseChange ℚ _ inst X = X := by
  have hS : (⇑(@ModularCurve.coeffEmb ℚ _ inst)) '' (X : Set (LaurentSeries ℚ)) = X := by
    ext y
    simp only [Set.mem_image, coeffEmb_rat, exists_eq_right, SetLike.mem_coe]
  unfold ModularCurve.laurentBaseChange
  rw [hS, IntermediateField.adjoin_self]

theorem x1x0FunctionFieldC_le_x1FunctionField (M p : ℕ) :
    ModularCurve.x1x0FunctionFieldC ℚ M p ≤ ModularCurve.x1FunctionField (M * p) := by
  refine ModularCurve.qExpFunctionFieldC_mono ℚ (le_inf (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M p)) ?_)
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CongruenceSubgroup.Gamma0_mem]
  have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) hA.2.2
  rwa [map_intCast, map_zero] at this

end CycDiamondAux

open CycDiamondAux in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K) :
    IntermediateField.relfinrank K₁ K = p - 1 ∧
      IsGalois ↥K₁ ↥(IntermediateField.extendScalars hle) ∧
      IsCyclic (↥(IntermediateField.extendScalars hle) ≃ₐ[↥K₁] ↥(IntermediateField.extendScalars hle)) := by
  classical

  have hdeg : IntermediateField.relfinrank K₁ K = p - 1 :=
    ModularCurve.relfinrank_eq_sub_one_x1FunctionField_mul_x1x0 p M hM hpM L K hK K₁ hK₁ hle
  refine ⟨hdeg, ?_⟩

  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime M p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM).symm
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt

  obtain ⟨δ, -, hfix⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff M p hcop
    (fun d hd => ModularCurve.exists_isDiamondAut (M * p) hd)
  have h₁ : ModularCurve.x1x0FunctionFieldC ℚ M p ≤ ModularCurve.x1FunctionField (M * p) :=
    x1x0FunctionFieldC_le_x1FunctionField M p

  have hdegQ : IntermediateField.relfinrank (ModularCurve.x1x0FunctionFieldC ℚ M p)
      (ModularCurve.x1FunctionField (M * p)) = p - 1 :=
    ModularCurve.relfinrank_eq_sub_one_x1FunctionField_mul_x1x0 p M hM hpM ℚ _ (laurentBaseChange_rat _ _).symm
      _ (laurentBaseChange_rat _ _).symm h₁
  rw [IntermediateField.relfinrank_eq_finrank_of_le h₁] at hdegQ
  have hcardQ : Nat.card ↥δ.range = p - 1 :=
    (natCard_range_eq_finrank_extendScalars h₁ δ hfix).trans hdegQ

  subst hK
  subst hK₁
  obtain ⟨δL, hδL⟩ := ModularCurve.exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb L
    (ModularCurve.x1FunctionField (M * p)) _ δ
  have hρ : ∀ (g : ↥(ZMod.unitsMap (dvd_mul_right M p)).ker) (y : LaurentSeries L)
      (hy : y ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)),
      (δL g ⟨y, hle hy⟩ : LaurentSeries L) = y := fun g y hy =>
    fixes_adjoin (k := L) (S := ⇑(ModularCurve.coeffEmb L) '' (ModularCurve.x1x0FunctionFieldC ℚ M p : Set (LaurentSeries ℚ)))
      (fun z hz => hle (IntermediateField.subset_adjoin L _ hz)) δL
      (by
        rintro g _ ⟨z, hz, rfl⟩
        exact (hδL g ⟨z, h₁ hz⟩ _).trans
          (congrArg (fun y : ↥(ModularCurve.x1FunctionField (M * p)) => ModularCurve.coeffEmb L (y : LaurentSeries ℚ))
            ((hfix ⟨z, h₁ hz⟩).1 hz g)))
      g y hy (hle hy)

  have hker : ∀ g : ↥(ZMod.unitsMap (dvd_mul_right M p)).ker,
      (∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))),
        (δL g y : LaurentSeries L) = y) → δ g = 1 := fun g hg =>
    AlgEquiv.ext fun x => Subtype.ext ((ModularCurve.coeffEmb L).injective
      ((hδL g x (ModularCurve.coeffEmb_mem_laurentBaseChange L x.2)).symm.trans (hg _)))

  have hfin : Module.finrank ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
      ↥(IntermediateField.extendScalars hle) = p - 1 := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hle]; exact hdeg
  haveI : IsCyclic ↥(ZMod.unitsMap (dvd_mul_right M p)).ker := isCyclic_ker_unitsMap M p hcop
  exact isGalois_and_isCyclic_of_restrict hle δL hρ δ hker (by rw [hfin, hcardQ]) (by rw [hfin]; exact hp1)

end S_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
end P2MW
export P2MW.S_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0 (solution)
