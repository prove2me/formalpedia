-- Prove2me | solution 1 for ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aa446ccd-10f7-5e5f-a552-d1fde47aaafa

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_comap_algebraMap_ne_top
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

namespace RationalForm

variable {K : Type} [Field K]

noncomputable def formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) :=
  letI := ι₀.toAlgebra
  have hmem : ∀ x : ↥(qExpFunctionFieldC k Γ), coeffMap (algebraMap k K) (x : LaurentSeries k) ∈ qExpFunctionFieldC K Γ := by
    intro x
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩
  { toFun := fun x => ⟨coeffMap (algebraMap k K) (x : LaurentSeries k), hmem x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun x y => Subtype.ext (by simp) }

theorem coe_formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC k Γ)) :
    (formEmb ι₀ Γ x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries k) := rfl

theorem formEmb_algebraMap {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) (a : k) :
    formEmb ι₀ Γ (algebraMap k ↥(qExpFunctionFieldC k Γ) a) = algebraMap K ↥(qExpFunctionFieldC K Γ) (ι₀ a) := by
  apply Subtype.ext
  change coeffMap ι₀ (algebraMap k (LaurentSeries k) a) = algebraMap K (LaurentSeries K) (ι₀ a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem adjoin_range_formEmb_eq_top {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    IntermediateField.adjoin K (Set.range (formEmb ι₀ Γ)) = ⊤ := by
  letI := ι₀.toAlgebra
  apply IntermediateField.lift_injective (qExpFunctionFieldC K Γ)
  have e1 := IntermediateField.lift_adjoin K (qExpFunctionFieldC K Γ) (Set.range (formEmb ι₀ Γ))
  have e2 := IntermediateField.lift_top K (qExpFunctionFieldC K Γ)
  refine e1.trans (Eq.trans ?_ e2.symm)
  conv_rhs => rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨formEmb ι₀ Γ ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

theorem isAlgebraic_of_adjoin_range_eq_top {k K' F F' : Type*} [Field k] [Field K'] [Field F] [Field F']
    [Algebra k K'] [Algebra K' F'] [Algebra F F'] [Algebra k F] [Algebra.IsAlgebraic k K']
    (hcomp : ∀ a : k, algebraMap F F' (algebraMap k F a) = algebraMap K' F' (algebraMap k K' a))
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    Algebra.IsAlgebraic F F' := by
  letI : Algebra k F' := ((algebraMap K' F').comp (algebraMap k K')).toAlgebra
  haveI : IsScalarTower k K' F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq (fun a => (hcomp a).symm)
  set S : IntermediateField F F' := IntermediateField.adjoin F (Set.range (algebraMap K' F')) with hS
  have hSalg : Algebra.IsAlgebraic F S := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro _ ⟨a, rfl⟩
    have ha : IsIntegral k a := (Algebra.IsAlgebraic.isAlgebraic (R := k) a).isIntegral
    exact (ha.map (IsScalarTower.toAlgHom k K' F')).tower_top
  have hStop : S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ (⊤ : IntermediateField K' F') := IntermediateField.mem_top
    rw [← hgen] at hy
    have h1 : (IntermediateField.adjoin K' (Set.range (algebraMap F F'))).toSubfield =
        Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range (algebraMap F F')) :=
      IntermediateField.adjoin_toSubfield _ _
    have h2 : S.toSubfield = Subfield.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap K' F')) :=
      IntermediateField.adjoin_toSubfield _ _
    change y ∈ S.toSubfield
    rw [h2, Set.union_comm, ← h1]
    exact hy
  refine ⟨fun y => ?_⟩
  have hy : y ∈ S := hStop ▸ IntermediateField.mem_top
  exact IntermediateField.isAlgebraic_iff.mp (hSalg.isAlgebraic ⟨y, hy⟩)

theorem isAlgebraic_formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ))
    (halg : @Algebra.IsAlgebraic k K _ _ ι₀.toAlgebra) :
    @Algebra.IsAlgebraic ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) _ _ (formEmb ι₀ Γ).toAlgebra := by
  letI : Algebra k K := ι₀.toAlgebra
  letI : Algebra ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := (formEmb ι₀ Γ).toAlgebra
  exact isAlgebraic_of_adjoin_range_eq_top (k := k) (K' := K) (fun a => formEmb_algebraMap ι₀ Γ a) (adjoin_range_formEmb_eq_top ι₀ Γ)

theorem exists_tracePlace {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ))
    (halg : @Algebra.IsAlgebraic k K _ _ ι₀.toAlgebra)
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    ∃ v : Place k ↥(qExpFunctionFieldC k Γ), v.toValuationSubring = w.toValuationSubring.comap (formEmb ι₀ Γ) := by
  letI : Algebra ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := (formEmb ι₀ Γ).toAlgebra
  haveI : Algebra.IsAlgebraic ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := isAlgebraic_formEmb ι₀ Γ halg
  haveI : Algebra.IsIntegral ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›
  refine AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (formEmb ι₀ Γ) w (fun a => ?_) ?_
  · rw [formEmb_algebraMap]
    exact w.algebraMap_mem' _
  · exact AlgebraicCurve.Place.comap_algebraMap_ne_top w

end RationalForm

open RationalForm in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    ∃ (m : ℕ) (_ : 0 < m) (ι₀ : GaloisField p m →+* K)
      (ι : ↥(qExpFunctionFieldC (GaloisField p m) Γ) →+* ↥(qExpFunctionFieldC K Γ))
      (_ : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ),
        (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries (GaloisField p m)))
      (P : Place (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ)),
      P.toValuationSubring = w.toValuationSubring.comap ι ∧ P.deg = 1 := by
  classical
  have hp : p.Prime := Fact.out

  have halgK : ∀ (k : Type) [Field k] (j : k →+* K), @Algebra.IsAlgebraic k K _ _ j.toAlgebra := by
    intro k _ j
    letI := j.toAlgebra
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn, ha⟩ := halg a
    have h1 : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.X, FiniteField.X_pow_card_sub_X_ne_zero _ h1, ?_⟩
    simp [ha]

  set j₁ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hj₁
  obtain ⟨P₁, hP₁⟩ := exists_tracePlace j₁ Γ (halgK (ZMod p) j₁) w
  set xj : ↥(qExpFunctionFieldC (ZMod p) Γ) :=
    ⟨jqModC (ZMod p), intFormRatiosC_subset (ZMod p) Γ (ModularCurve.jqModC_mem_intFormRatiosC (ZMod p) Γ)⟩ with hxj
  have hxjt : Transcendental (ZMod p) xj := by
    intro halgj
    apply ModularCurve.transcendental_jqModC (ZMod p)
    exact halgj.algebraMap (A := LaurentSeries (ZMod p))
  obtain ⟨hfdj, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (ZMod p) Γ hT Γ le_rfl
    (fun γ hγ => Or.inl hγ) xj rfl
  haveI := hfdj
  have hm0 : P₁.deg ≠ 0 := AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin xj hxjt P₁
  have hmpos : 0 < P₁.deg := Nat.pos_of_ne_zero hm0

  letI : Algebra (ZMod p) K := j₁.toAlgebra
  haveI : Algebra.IsAlgebraic (ZMod p) K := halgK (ZMod p) j₁
  haveI : Fintype (GaloisField p P₁.deg) := Fintype.ofFinite _
  let φ : GaloisField p P₁.deg →ₐ[ZMod p] K := IsAlgClosed.lift
  set ι₀ : GaloisField p P₁.deg →+* K := φ.toRingHom with hι₀
  obtain ⟨P, hP⟩ := exists_tracePlace ι₀ Γ (halgK (GaloisField p P₁.deg) ι₀) w
  have hdeg : P.deg = 1 :=
    ModularCurve.deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd K p halg Γ hT w
      (formEmb j₁ Γ) (fun x => coe_formEmb j₁ Γ x) P₁ hP₁ P₁.deg hmpos ι₀ (formEmb ι₀ Γ) (fun x => coe_formEmb ι₀ Γ x)
      P hP (dvd_refl _)
  exact ⟨P₁.deg, hmpos, ι₀, formEmb ι₀ Γ, fun x => coe_formEmb ι₀ Γ x, P, hP, hdeg⟩

end S_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
end P2MW
export P2MW.S_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one (solution)
