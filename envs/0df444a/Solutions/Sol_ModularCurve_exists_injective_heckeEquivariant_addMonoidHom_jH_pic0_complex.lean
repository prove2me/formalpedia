-- Prove2me | solution 1 for ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1f8959b5-8827-556f-87d0-c8a0a991dbcb

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve"

open scoped TensorProduct Pointwise

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaHBar coe_heckeAlphaHBar HeckeBetaHDefined heckeBetaHBar coe_heckeBetaHBar HeckeAlphaHBarIntegral HeckeBetaHBarIntegral HeckeInputsHAlong heckeOperatorHAlong heckeOperatorHAlong_eq translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHTopFunctionFieldC xHFunctionFieldBar JH Gamma1_le_of_dvd qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace K1HBC
p2m_open "ModularCurve"

local notation "Qb" => AlgebraicClosure ℚ

local notation "FQ" F₀:max => laurentBaseChange (AlgebraicClosure ℚ) F₀

local notation "FC" F₀:max => laurentBaseChange ℂ F₀

def HFG (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Prop :=
  ∃ x : ↥(laurentBaseChange L F₀), Transcendental L x ∧
    FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥(laurentBaseChange L F₀))) ↥(laurentBaseChange L F₀)

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance gammaH_inf_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := CongruenceSubgroup.Gamma1 (M * ℓ))
    (le_inf ?_ (CongruenceSubgroup.Gamma1_in_Gamma0 _))
  exact (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)

theorem T_mem_inf (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [ModularGroup.T]

scoped instance fact_hfg_xH (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Fact (HFG L (xHFunctionField M H)) :=
  ⟨ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H)⟩

scoped instance fact_hfg_xHTop (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : ℕ) [NeZero ℓ] : Fact (HFG L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
  ⟨ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (T_mem_inf M H ℓ)⟩

def sigmaR : Qb →+* ℂ := (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom

theorem sigmaR_comp_algebraMap : sigmaR.comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ :=
  complexEmbedding.comp_algebraMap

theorem coeffMap_sigma_algebraMap (a : Qb) :
    coeffMap sigmaR (algebraMap Qb (LaurentSeries Qb) a) = algebraMap ℂ (LaurentSeries ℂ) (sigmaR a) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_sigma_coeffEmb (z : LaurentSeries ℚ) : coeffMap sigmaR (coeffEmb Qb z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr sigmaR_comp_algebraMap z

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

section Field

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_sigma_mem {x : LaurentSeries Qb} (hx : x ∈ FQ F₀) : coeffMap sigmaR x ∈ FC F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_sigma_algebraMap]
        exact (laurentBaseChange ℂ _).algebraMap_mem _
      · rw [coeffMap_sigma_coeffEmb]
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def phi : (FQ F₀) →+* (FC F₀) where
  toFun x := ⟨coeffMap sigmaR (x : LaurentSeries Qb), coeffMap_sigma_mem F₀ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_phi (x : FQ F₀) : (phi F₀ x : LaurentSeries ℂ) = coeffMap sigmaR x := rfl

theorem phi_algebraMap (a : Qb) : phi F₀ (algebraMap Qb (FQ F₀) a) = algebraMap ℂ (FC F₀) (sigmaR a) :=
  Subtype.ext (coeffMap_sigma_algebraMap a)

theorem phi_injective : Function.Injective (phi F₀) := (phi F₀).injective

theorem phi_ne_zero {f : FQ F₀} (hf : f ≠ 0) : phi F₀ f ≠ 0 := (map_ne_zero_iff _ (phi_injective F₀)).2 hf

@[reducible] def algQbC : Algebra Qb ℂ := sigmaR.toAlgebra

@[reducible] def algF : Algebra (FQ F₀) (FC F₀) := (phi F₀).toAlgebra

@[reducible] def algQbFC : Algebra Qb (FC F₀) := ((algebraMap ℂ (FC F₀)).comp sigmaR).toAlgebra

attribute [local instance] algQbC algF algQbFC

theorem algebraMap_FQ_FC : algebraMap (FQ F₀) (FC F₀) = phi F₀ := rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem isScalarTower_Qb_C_FC : IsScalarTower Qb ℂ (FC F₀) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem isScalarTower_Qb_FQ_FC : IsScalarTower Qb (FQ F₀) (FC F₀) :=
  IsScalarTower.of_algebraMap_eq fun a => (phi_algebraMap F₀ a).symm

attribute [local instance] isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC

theorem hfgQ [h : Fact (HFG Qb F₀)] : ∃ x : FQ F₀, Transcendental Qb x ∧
    FiniteDimensional (IntermediateField.adjoin Qb ({x} : Set (FQ F₀))) (FQ F₀) := h.out

theorem hfgC [h : Fact (HFG ℂ F₀)] : ∃ x : FC F₀, Transcendental ℂ x ∧
    FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set (FC F₀))) (FC F₀) := h.out

theorem isCurveOverQ [Fact (HFG Qb F₀)] : IsCurveOver Qb (FQ F₀) := by
  obtain ⟨x, hx, hfd⟩ := hfgQ F₀
  haveI := hfd
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

theorem isCurveOverC [Fact (HFG ℂ F₀)] : IsCurveOver ℂ (FC F₀) := by
  obtain ⟨x, hx, hfd⟩ := hfgC F₀
  haveI := hfd
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

attribute [local instance] isCurveOverQ isCurveOverC

theorem adjoin_range_phi : IntermediateField.adjoin ℂ (Set.range (phi F₀)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hle : (FC F₀) ≤ IntermediateField.lift (IntermediateField.adjoin ℂ (Set.range (phi F₀))) := by
    rw [IntermediateField.lift_adjoin]
    change IntermediateField.adjoin ℂ _ ≤ _
    refine IntermediateField.adjoin.mono ℂ _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨phi F₀ ⟨coeffEmb Qb z, coeffEmb_mem_laurentBaseChange _ hz⟩, ⟨_, rfl⟩, coeffMap_sigma_coeffEmb z⟩
  exact (IntermediateField.mem_lift y).1 (hle y.2)

theorem adjoin_range_algebraMap : IntermediateField.adjoin ℂ (Set.range (algebraMap (FQ F₀) (FC F₀))) = ⊤ :=
  adjoin_range_phi F₀

end Field

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_eq_zero_of_mem_of_inv_mem {f : F} (hf : f ∈ v.toValuationSubring)
    (hfi : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have h1 := ord_nonneg_of_mem v hf
  have h2 := ord_nonneg_of_mem v hfi
  rw [Place.ord_inv] at h2
  omega

theorem exists_not_mem : ∃ g : F, g ∉ v.toValuationSubring := by
  by_contra h
  push Not at h
  exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => h x⟩)

theorem exists_ord_eq_one : ∃ f : F, v.ord f = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨π, v.ord_coe_irreducible hπ⟩

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K F] (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one]
  refine Finsupp.sum_congr fun v _ => ?_
  simp

theorem mem_smul_place_iff (g : SemilinearAut K F) (x : F) :
    x ∈ (g • v).toValuationSubring ↔ g⁻¹ • x ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

end PlaceHelpers

section Field2

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [Fact (HFG Qb F₀)] [Fact (HFG ℂ F₀)]

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

theorem exists_liftPlace (v : Place Qb (FQ F₀)) :
    ∃ P' : Place ℂ (FC F₀),
      P'.toValuationSubring.comap (phi F₀) = v.toValuationSubring ∧
      (∀ f, P'.ord (phi F₀ f) = v.ord f) ∧
      ∀ Q' : Place ℂ (FC F₀), Q'.toValuationSubring.comap (phi F₀) = v.toValuationSubring → Q' = P' :=
  Place.exists_comap_algebraMap_eq_of_constantFieldExtension Qb (FQ F₀) ℂ (FC F₀)
    (hfgQ F₀) (hfgC F₀) (adjoin_range_algebraMap F₀) v

def liftPlace (v : Place Qb (FQ F₀)) : Place ℂ (FC F₀) := (exists_liftPlace F₀ v).choose

theorem liftPlace_comap (v : Place Qb (FQ F₀)) :
    (liftPlace F₀ v).toValuationSubring.comap (phi F₀) = v.toValuationSubring :=
  (exists_liftPlace F₀ v).choose_spec.1

theorem mem_liftPlace_iff (v : Place Qb (FQ F₀)) (f : FQ F₀) :
    phi F₀ f ∈ (liftPlace F₀ v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [← liftPlace_comap F₀ v]
  exact Iff.rfl

theorem ord_liftPlace (v : Place Qb (FQ F₀)) (f : FQ F₀) : (liftPlace F₀ v).ord (phi F₀ f) = v.ord f :=
  (exists_liftPlace F₀ v).choose_spec.2.1 f

theorem liftPlace_unique {v : Place Qb (FQ F₀)} {Q' : Place ℂ (FC F₀)}
    (h : Q'.toValuationSubring.comap (phi F₀) = v.toValuationSubring) : Q' = liftPlace F₀ v :=
  (exists_liftPlace F₀ v).choose_spec.2.2 Q' h

theorem liftPlace_injective : Function.Injective (liftPlace F₀) := fun v w h =>
  Place.ext (by rw [← liftPlace_comap F₀ v, ← liftPlace_comap F₀ w, h])

theorem exists_eq_liftPlace {w' : Place ℂ (FC F₀)} (hwx : ∃ y : FQ F₀, phi F₀ y ∉ w'.toValuationSubring) :
    ∃ v, w' = liftPlace F₀ v := by
  obtain ⟨x, _, hfd⟩ := hfgQ F₀
  haveI := hfd
  obtain ⟨v, hv⟩ := Place.exists_toValuationSubring_eq_comap_ringHom (K := Qb) x (phi F₀)
    w'.toValuationSubring (fun a => by rw [phi_algebraMap]; exact w'.algebraMap_mem' _) hwx
  exact ⟨v, liftPlace_unique F₀ hv.symm⟩

theorem ord_phi_of_forall_ne {w' : Place ℂ (FC F₀)} (hoff : ∀ v, w' ≠ liftPlace F₀ v) (f : FQ F₀) :
    w'.ord (phi F₀ f) = 0 := by
  have hall : ∀ y : FQ F₀, phi F₀ y ∈ w'.toValuationSubring := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_eq_liftPlace F₀ h
    exact hoff v hv
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact ord_eq_zero_of_mem_of_inv_mem w' (hall f) (by rw [← map_inv₀]; exact hall f⁻¹)

theorem forall_ne_liftPlace_of_comap_ne {w' : Place ℂ (FC F₀)}
    (h : ∀ v : Place Qb (FQ F₀), w'.toValuationSubring.comap (algebraMap (FQ F₀) (FC F₀)) ≠ v.toValuationSubring) :
    ∀ v, w' ≠ liftPlace F₀ v := fun v hv =>
  h v (by rw [hv]; exact liftPlace_comap F₀ v)

theorem forall_comap_ne_of_ne_liftPlace {w' : Place ℂ (FC F₀)} (h : ∀ v, w' ≠ liftPlace F₀ v)
    (v : Place Qb (FQ F₀)) :
    w'.toValuationSubring.comap (algebraMap (FQ F₀) (FC F₀)) ≠ v.toValuationSubring := fun hv =>
  h v (liftPlace_unique F₀ hv)

def conorm : Divisor Qb (FQ F₀) →+ Divisor ℂ (FC F₀) :=
  Finsupp.mapDomain.addMonoidHom (liftPlace F₀)

theorem conorm_apply (D : Divisor Qb (FQ F₀)) : conorm F₀ D = Finsupp.mapDomain (liftPlace F₀) D := rfl

@[scoped simp] theorem conorm_apply_liftPlace (D : Divisor Qb (FQ F₀)) (v : Place Qb (FQ F₀)) :
    conorm F₀ D (liftPlace F₀ v) = D v := by
  rw [conorm_apply]
  exact Finsupp.mapDomain_apply (liftPlace_injective F₀) D v

theorem conorm_apply_of_forall_ne (D : Divisor Qb (FQ F₀)) {w' : Place ℂ (FC F₀)}
    (h : ∀ v, w' ≠ liftPlace F₀ v) : conorm F₀ D w' = 0 := by
  rw [conorm_apply]
  exact Finsupp.mapDomain_notin_range D w' (by rintro ⟨v, rfl⟩; exact h v rfl)

@[scoped simp] theorem conorm_single (v : Place Qb (FQ F₀)) (n : ℤ) :
    conorm F₀ (Finsupp.single v n) = Finsupp.single (liftPlace F₀ v) n := by
  rw [conorm_apply, Finsupp.mapDomain_single]

theorem degree_conorm (D : Divisor Qb (FQ F₀)) : Divisor.degree (conorm F₀ D) = Divisor.degree D := by
  rw [degree_eq_sum, degree_eq_sum, conorm_apply]
  exact Finsupp.sum_mapDomain_index_inj (liftPlace_injective F₀)

theorem isPrincipal_conorm {D : Divisor Qb (FQ F₀)} (hD : D.IsPrincipal) : (conorm F₀ D).IsPrincipal := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨phi F₀ f, phi_ne_zero F₀ hf, fun w' => ?_⟩
  by_cases h : ∃ v, w' = liftPlace F₀ v
  · obtain ⟨v, rfl⟩ := h
    rw [conorm_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at h
    rw [conorm_apply_of_forall_ne F₀ D h, ord_phi_of_forall_ne F₀ h]

theorem conorm_mem_degZero {D : Divisor Qb (FQ F₀)} (hD : D ∈ Divisor.degZero (K := Qb) (F := FQ F₀)) :
    conorm F₀ D ∈ Divisor.degZero (K := ℂ) (F := FC F₀) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [degree_conorm, hD]

def conormDegZero : Divisor.degZero (K := Qb) (F := FQ F₀) →+ Divisor.degZero (K := ℂ) (F := FC F₀) :=
  ((conorm F₀).domRestrict _).codRestrict _ fun D => conorm_mem_degZero F₀ D.2

@[scoped simp] theorem coe_conormDegZero (D : Divisor.degZero (K := Qb) (F := FQ F₀)) :
    (conormDegZero F₀ D : Divisor ℂ (FC F₀)) = conorm F₀ D := rfl

def iota : Pic0 Qb (FQ F₀) →+ Pic0 ℂ (FC F₀) :=
  QuotientAddGroup.map _ _ (conormDegZero F₀) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_conorm F₀ hD)

theorem iota_mk (D : Divisor.degZero (K := Qb) (F := FQ F₀)) : iota F₀ (Pic0.mk D) = Pic0.mk (conormDegZero F₀ D) :=
  rfl

theorem mk_eq_zero_iff {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (D : Divisor.degZero (K := K') (F := F')) : Pic0.mk D = 0 ↔ (D : Divisor K' F').IsPrincipal := by
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

theorem mk_eq_mk_of_add_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (A B C : Divisor.degZero (K := K') (F := F')) (hC : Pic0.mk C = 0) (h : A + C = B) :
    Pic0.mk A = Pic0.mk B := by
  rw [← h, Pic0.mk_add, hC, add_zero]

theorem iota_injective : Function.Injective (iota F₀) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [iota_mk, mk_eq_zero_iff, coe_conormDegZero] at hx
  rw [mk_eq_zero_iff]
  exact Divisor.isPrincipal_of_constantFieldExtension Qb (FQ F₀) ℂ (FC F₀) (hfgQ F₀) (hfgC F₀)
    (adjoin_range_algebraMap F₀) D (conorm F₀ D)
    (fun v' v h => by rw [liftPlace_unique F₀ h, conorm_apply_liftPlace])
    (fun v' h => conorm_apply_of_forall_ne F₀ _ (forall_ne_liftPlace_of_comap_ne F₀ h)) hx

set_option synthInstance.maxHeartbeats 1600000 in
theorem mem_range_iota_of_isOfFinAddOrder {z : Pic0 ℂ (FC F₀)} (hz : IsOfFinAddOrder z) : z ∈ (iota F₀).range := by
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective z
  set n : ℕ := addOrderOf (Pic0.mk D') with hn_def
  have hn : n ≠ 0 := (hz.addOrderOf_pos).ne'
  have hnD : ((n • D' : Divisor.degZero (K := ℂ) (F := FC F₀)) : Divisor ℂ (FC F₀)).IsPrincipal := by
    rw [← mk_eq_zero_iff, Pic0.mk, QuotientAddGroup.mk_nsmul]
    exact addOrderOf_nsmul_eq_zero (Pic0.mk D')
  obtain ⟨g', hg', hg'D⟩ := hnD
  have hD'tors : ∃ g' : FC F₀, g' ≠ 0 ∧ ∀ v', (n : ℤ) * (D' : Divisor ℂ (FC F₀)) v' = v'.ord g' :=
    ⟨g', hg', fun v' => by
      have := hg'D v'
      rwa [AddSubgroupClass.coe_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this⟩
  obtain ⟨D, h', hh', _, hover, hoff⟩ :=
    Divisor.exists_torsion_descent_of_constantFieldExtension Qb (FQ F₀) ℂ (FC F₀) (hfgQ F₀) (hfgC F₀)
      (adjoin_range_algebraMap F₀) n hn (D' : Divisor ℂ (FC F₀)) hD'tors
  obtain ⟨E', hE', hE'0⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) h' hh'
  have hsplit : ∀ w', (D' : Divisor ℂ (FC F₀)) w' = conorm F₀ D w' + E' w' := by
    intro w'
    by_cases h : ∃ v, w' = liftPlace F₀ v
    · obtain ⟨v, rfl⟩ := h
      rw [conorm_apply_liftPlace, hE', hover v (liftPlace F₀ v) (liftPlace_comap F₀ v)]
    · push Not at h
      rw [conorm_apply_of_forall_ne F₀ D h, hE', zero_add, hoff w' (forall_comap_ne_of_ne_liftPlace F₀ h)]
  have hD0 : D ∈ Divisor.degZero (K := Qb) (F := FQ F₀) := by
    rw [Divisor.mem_degZero, ← degree_conorm F₀ D]
    have hcon : conorm F₀ D = (D' : Divisor ℂ (FC F₀)) - E' := by
      ext w'
      rw [Finsupp.sub_apply, hsplit]
      ring
    rw [hcon, map_sub, Divisor.mem_degZero.mp D'.2, hE'0, sub_zero]
  have hE'deg : E' ∈ Divisor.degZero (K := ℂ) (F := FC F₀) := Divisor.mem_degZero.mpr hE'0
  refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
  rw [iota_mk]
  have hE'P : Pic0.mk ⟨E', hE'deg⟩ = 0 := by
    rw [mk_eq_zero_iff]
    exact ⟨h', hh', hE'⟩
  have hsum : conormDegZero F₀ ⟨D, hD0⟩ + ⟨E', hE'deg⟩ = D' :=
    Subtype.ext <| Finsupp.ext fun w' => by
      simp only [AddSubgroup.coe_add, Finsupp.add_apply, coe_conormDegZero, hsplit w']
  exact mk_eq_mk_of_add_eq _ _ _ hE'P hsum

theorem smul_liftPlace (g : SemilinearAut Qb (FQ F₀)) (g' : SemilinearAut ℂ (FC F₀))
    (hc : ∀ y, g' • phi F₀ y = phi F₀ (g • y)) (v : Place Qb (FQ F₀)) :
    g' • liftPlace F₀ v = liftPlace F₀ (g • v) := by
  refine liftPlace_unique F₀ ?_
  ext y
  show phi F₀ y ∈ (g' • liftPlace F₀ v).toValuationSubring ↔ y ∈ (g • v).toValuationSubring
  have hinv : g'⁻¹ • phi F₀ y = phi F₀ (g⁻¹ • y) := by
    rw [inv_smul_eq_iff, hc, smul_inv_smul]
  rw [mem_smul_place_iff, mem_smul_place_iff, hinv, mem_liftPlace_iff]

theorem conorm_smul (g : SemilinearAut Qb (FQ F₀)) (g' : SemilinearAut ℂ (FC F₀))
    (hc : ∀ y, g' • phi F₀ y = phi F₀ (g • y)) (D : Divisor Qb (FQ F₀)) :
    conorm F₀ (g • D) = g' • conorm F₀ D := by
  rw [conorm_apply, conorm_apply, SemilinearAut.divisor_smul_def, SemilinearAut.divisor_smul_def,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext v
  exact (smul_liftPlace F₀ g g' hc v).symm

theorem iota_smul (g : SemilinearAut Qb (FQ F₀)) (g' : SemilinearAut ℂ (FC F₀))
    (hc : ∀ y, g' • phi F₀ y = phi F₀ (g • y)) (x : Pic0 Qb (FQ F₀)) : iota F₀ (g • x) = g' • iota F₀ x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, iota_mk, iota_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [coe_conormDegZero, SemilinearAut.coe_degZeroSMulHom]
  exact conorm_smul F₀ g g' hc D

theorem exists_algEquiv_extend_of_constantFieldExtension (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (σ : F ≃ₐ[K] F) :
    ∃ σ' : F' ≃ₐ[K'] F', ∀ y : F, σ' (algebraMap F F' y) = algebraMap F F' (σ y) := by
  classical

  let μ : K' ⊗[K] F →ₐ[K'] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' F') (IsScalarTower.toAlgHom K F F')
      (fun _ _ => Commute.all _ _)
  have hμ_tmul : ∀ (a : K') (y : F), μ (a ⊗ₜ y) = algebraMap K' F' a * algebraMap F F' y :=
    fun a y => by simp [μ]

  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    let bF := Module.Free.chooseBasis K F
    let B := Algebra.TensorProduct.basis K' bF
    have hli : LinearIndependent K' (fun i => algebraMap F F' (bF i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen
        bF.linearIndependent
    have hcomp : (μ.toLinearMap : K' ⊗[K] F → F') ∘ (B : _ → K' ⊗[K] F) =
        fun i => algebraMap F F' (bF i) := by
      funext i
      simp [B, Algebra.TensorProduct.basis_apply, hμ_tmul]
    have hz' : Finsupp.linearCombination K' (fun i => algebraMap F F' (bF i)) (B.repr z) = 0 := by
      rw [← hcomp, ← Finsupp.apply_linearCombination, B.linearCombination_repr]
      exact hz
    have hrepr : B.repr z = 0 := linearIndependent_iff.mp hli _ hz'
    simpa using hrepr

  set S : Subalgebra K' F' := μ.range with hS
  let e : (K' ⊗[K] F) ≃ₐ[K'] S := AlgEquiv.ofInjective μ hμ
  have he : ∀ z, ((e z : S) : F') = μ z := fun z => AlgEquiv.ofInjective_apply μ hμ z
  haveI : FaithfulSMul S F' := (faithfulSMul_iff_algebraMap_injective S F').mpr Subtype.val_injective
  have hFS : ∀ y : F, algebraMap F F' y ∈ S := fun y =>
    ⟨1 ⊗ₜ y, show μ (1 ⊗ₜ y) = _ by rw [hμ_tmul, map_one, one_mul]⟩
  have hadj : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact hFS y)
  haveI : IsFractionRing S F' := by
    refine IsFractionRing.of_field S F' fun z => ?_
    have hz : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
      rw [hgen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := K')).mp hz
    exact ⟨⟨r, hadj hr⟩, ⟨s, hadj hs⟩, hrs⟩

  let θ : K' ⊗[K] F ≃ₐ[K'] K' ⊗[K] F := Algebra.TensorProduct.congr (AlgEquiv.refl : K' ≃ₐ[K'] K') σ
  have hθ : ∀ (a : K') (y : F), θ (a ⊗ₜ y) = a ⊗ₜ σ y := fun a y => by
    simp [θ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  let ΦS : S ≃+* S := (e.symm.toRingEquiv.trans θ.toRingEquiv).trans e.toRingEquiv
  have hΦS : ∀ z, ΦS (e z) = e (θ z) := fun z => by simp [ΦS]
  let Φ : F' ≃+* F' := IsFractionRing.ringEquivOfRingEquiv ΦS
  have hΦ : ∀ s : S, Φ (s : F') = ((ΦS s : S) : F') := fun s =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ΦS s
  have hΦμ : ∀ z, Φ (μ z) = μ (θ z) := fun z => by rw [← he, hΦ, hΦS, he]
  have hΦK : ∀ a : K', Φ (algebraMap K' F' a) = algebraMap K' F' a := fun a => by
    have h1 : algebraMap K' F' a = μ (a ⊗ₜ 1) := by rw [hμ_tmul, map_one, mul_one]
    rw [h1, hΦμ, hθ, map_one]
  have hΦF : ∀ y : F, Φ (algebraMap F F' y) = algebraMap F F' (σ y) := fun y => by
    have h1 : algebraMap F F' y = μ (1 ⊗ₜ y) := by rw [hμ_tmul, map_one, one_mul]
    rw [h1, hΦμ, hθ, hμ_tmul, map_one, one_mul]
  exact ⟨AlgEquiv.ofRingEquiv (f := Φ) hΦK, hΦF⟩

theorem exists_extend (σ : (FQ F₀) ≃ₐ[Qb] (FQ F₀)) :
    ∃ σ' : (FC F₀) ≃ₐ[ℂ] (FC F₀), ∀ y, σ' (phi F₀ y) = phi F₀ (σ y) :=
  exists_algEquiv_extend_of_constantFieldExtension Qb (FQ F₀) ℂ (FC F₀) (hfgQ F₀) (hfgC F₀)
    (adjoin_range_algebraMap F₀) σ

end Field2

theorem inertiaDegAlong_eq_one {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := Place.deg_restrict_mul_inertiaDeg (F := F) w
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

section Compat

variable {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
  [Fact (HFG Qb F₀)] [Fact (HFG ℂ F₀)] [Fact (HFG Qb F₁)] [Fact (HFG ℂ F₁)]

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

variable (ψQ : FQ F₀ →ₐ[Qb] FQ F₁) (ψC : FC F₀ →ₐ[ℂ] FC F₁)
  (hψQ : ψQ.toRingHom.IsIntegral) (hψC : ψC.toRingHom.IsIntegral)
  (hc : ∀ f, phi F₁ (ψQ f) = ψC (phi F₀ f))

include hψQ hψC hc

theorem restrictAlong_liftPlace (W : Place Qb (FQ F₁)) :
    (liftPlace F₁ W).restrictAlong ψC hψC = liftPlace F₀ (W.restrictAlong ψQ hψQ) := by
  refine liftPlace_unique F₀ ?_
  ext f
  show ψC (phi F₀ f) ∈ (liftPlace F₁ W).toValuationSubring ↔ ψQ f ∈ W.toValuationSubring
  rw [← hc, mem_liftPlace_iff]

theorem ramificationIndexAlong_liftPlace (W : Place Qb (FQ F₁)) :
    (liftPlace F₁ W).ramificationIndexAlong ψC = W.ramificationIndexAlong ψQ := by
  obtain ⟨f, hf⟩ := exists_ord_eq_one (W.restrictAlong ψQ hψQ)
  have hQ := Place.ord_restrictAlong ψQ hψQ W f
  have hC := Place.ord_restrictAlong ψC hψC (liftPlace F₁ W) (phi F₀ f)
  rw [restrictAlong_liftPlace ψQ ψC hψQ hψC hc, ord_liftPlace, hf, mul_one, ← hc, ord_liftPlace,
    hQ, hf, mul_one] at hC
  exact_mod_cast hC.symm

omit hψQ hc in
theorem mem_restrictAlong_C_iff (W' : Place ℂ (FC F₁)) (x : FC F₀) :
    x ∈ (W'.restrictAlong ψC hψC).toValuationSubring ↔ ψC x ∈ W'.toValuationSubring :=
  Iff.rfl

theorem exists_eq_liftPlace_of_restrictAlong {v : Place Qb (FQ F₀)} {W' : Place ℂ (FC F₁)}
    (hW' : W'.restrictAlong ψC hψC = liftPlace F₀ v) : ∃ W, W' = liftPlace F₁ W := by
  obtain ⟨g, hg⟩ := exists_not_mem v
  refine exists_eq_liftPlace F₁ ⟨ψQ g, fun hmem => hg ?_⟩
  rw [hc, ← mem_restrictAlong_C_iff ψC hψC W' (phi F₀ g), hW'] at hmem
  exact (mem_liftPlace_iff F₀ v g).1 hmem

theorem fiberAlong_liftPlace (v : Place Qb (FQ F₀)) :
    Place.fiberAlong ψC hψC (liftPlace F₀ v) =
      (Place.fiberAlong ψQ hψQ v).map ⟨liftPlace F₁, liftPlace_injective F₁⟩ := by
  ext W'
  rw [Place.mem_fiberAlong, Finset.mem_map]
  constructor
  · intro hW'
    obtain ⟨W, rfl⟩ := exists_eq_liftPlace_of_restrictAlong ψQ ψC hψQ hψC hc hW'
    refine ⟨W, ?_, rfl⟩
    rw [Place.mem_fiberAlong]
    apply liftPlace_injective F₀
    rw [← restrictAlong_liftPlace ψQ ψC hψQ hψC hc W]
    exact hW'
  · rintro ⟨W, hW, rfl⟩
    rw [Place.mem_fiberAlong] at hW
    rw [Function.Embedding.coeFn_mk, restrictAlong_liftPlace ψQ ψC hψQ hψC hc, hW]

end Compat

section HeckeLevel

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

theorem phi_heckeAlphaHBar (f : FQ (xHFunctionField M H)) :
    phi (xHTopFunctionFieldC ℚ M H (M * ℓ)) (heckeAlphaHBar Qb M H ℓ f) =
      heckeAlphaHBar ℂ M H ℓ (phi (xHFunctionField M H) f) :=
  Subtype.ext (by simp only [coe_phi, coe_heckeAlphaHBar])

theorem phi_heckeBetaHBar (h0 : HeckeBetaHDefined M H ℓ) (f : FQ (xHFunctionField M H)) :
    phi (xHTopFunctionFieldC ℚ M H (M * ℓ)) (heckeBetaHBar Qb M H ℓ f) =
      heckeBetaHBar ℂ M H ℓ (phi (xHFunctionField M H) f) :=
  Subtype.ext (by simp only [coe_phi, coe_heckeBetaHBar M H ℓ h0, coeffMap_qExpand])

theorem conorm_heckeDivHBar (h0 : HeckeBetaHDefined M H ℓ)
    (hαQ : HeckeAlphaHBarIntegral Qb M H ℓ) (hβQ : HeckeBetaHBarIntegral Qb M H ℓ)
    (hαC : HeckeAlphaHBarIntegral ℂ M H ℓ) (hβC : HeckeBetaHBarIntegral ℂ M H ℓ)
    (D : Divisor Qb (FQ (xHFunctionField M H))) :
    conorm (xHFunctionField M H)
        (Divisor.correspondence (heckeBetaHBar Qb M H ℓ) (heckeAlphaHBar Qb M H ℓ) hβQ hαQ D) =
      Divisor.correspondence (heckeBetaHBar ℂ M H ℓ) (heckeAlphaHBar ℂ M H ℓ) hβC hαC
        (conorm (xHFunctionField M H) D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D E hD hE => simp only [map_add, hD, hE]
  | single v n =>
    simp only [Divisor.correspondence_apply, conorm_single, Divisor.pullbackAlong_single, map_sum,
      Divisor.pushforwardAlong_single,
      fiberAlong_liftPlace _ _ hβQ hβC (phi_heckeBetaHBar M H ℓ h0),
      Finset.sum_map, Function.Embedding.coeFn_mk,
      ramificationIndexAlong_liftPlace _ _ hβQ hβC (phi_heckeBetaHBar M H ℓ h0),
      restrictAlong_liftPlace _ _ hαQ hαC (phi_heckeAlphaHBar M H ℓ),
      inertiaDegAlong_eq_one, Nat.cast_one, mul_one]

theorem iota_heckeOperatorHAlong (hQ : HeckeInputsHAlong Qb M H ℓ) (hC : HeckeInputsHAlong ℂ M H ℓ)
    (x : Pic0 Qb (FQ (xHFunctionField M H))) :
    iota (xHFunctionField M H) (heckeOperatorHAlong Qb M H ℓ x) =
      heckeOperatorHAlong ℂ M H ℓ (iota (xHFunctionField M H) x) := by
  obtain ⟨h0, hαQ, hβQ, hPQ, hfinQ, hFIQ, hNQ⟩ := hQ
  obtain ⟨_, hαC, hβC, hPC, hfinC, hFIC, hNC⟩ := hC
  rw [heckeOperatorHAlong_eq h0 hαQ hβQ hFIQ hfinQ hNQ, heckeOperatorHAlong_eq h0 hαC hβC hFIC hfinC hNC]
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  change Pic0.mk (conormDegZero _ (Pic0.degZeroCorrespondence _ _ hβQ hαQ hFIQ D)) =
    Pic0.mk (Pic0.degZeroCorrespondence _ _ hβC hαC hFIC (conormDegZero _ D))
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [coe_conormDegZero, Pic0.coe_degZeroCorrespondence]
  exact conorm_heckeDivHBar M H ℓ h0 hαQ hβQ hαC hβC D

end HeckeLevel

end ModularCurve.K1HBC
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve.K1HBC"
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve"

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (φ : ↥(ModularCurve.xHFunctionFieldBar M H) →+*
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
      (ι : ModularCurve.JH M H →+
          AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
      (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H),
        ((φ y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) =
          ModularCurve.coeffMap (complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
            (y : LaurentSeries (AlgebraicClosure ℚ))) ∧
      Function.Injective ι ∧
      (∀ z, IsOfFinAddOrder z → z ∈ ι.range) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ],
        ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ →
        ModularCurve.HeckeInputsHAlong ℂ M H ℓ →
        ∀ x : ModularCurve.JH M H,
          ι (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeOperatorHAlong ℂ M H ℓ (ι x)) ∧
      (∀ (g : AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
        (g' : AlgebraicCurve.SemilinearAut ℂ
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), g' • φ y = φ (g • y)) →
        ∀ x : ModularCurve.JH M H, ι (g • x) = g' • ι x) ∧
      ∀ σ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H),
        ∃ σ' : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)),
          ∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), σ' (φ y) = φ (σ y) :=
  ⟨ModularCurve.K1HBC.phi (ModularCurve.xHFunctionField M H),
    ModularCurve.K1HBC.iota (ModularCurve.xHFunctionField M H),
    fun _ => rfl,
    ModularCurve.K1HBC.iota_injective _,
    fun _ hz => ModularCurve.K1HBC.mem_range_iota_of_isOfFinAddOrder _ hz,
    fun ℓ _ hQ hC x => ModularCurve.K1HBC.iota_heckeOperatorHAlong M H ℓ hQ hC x,
    fun g g' hc x => ModularCurve.K1HBC.iota_smul _ g g' hc x,
    fun σ => ModularCurve.K1HBC.exists_extend _ σ⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.ModularCurve.K1HBC"

end S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
end P2MW
export P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex (solution)
