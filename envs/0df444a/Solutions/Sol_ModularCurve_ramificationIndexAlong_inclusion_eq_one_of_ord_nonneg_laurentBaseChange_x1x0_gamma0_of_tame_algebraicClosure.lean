-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a1ce5be9-151c-5cf5-bc1a-bd6a4360fd09

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
import Theorems.Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset x1x0FunctionFieldC jq coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC"
namespace TowerUnramAux
p2m_open "ModularCurve"

section PlaceLemmas

variable {Ω : Type*} {F : Type*} [Field Ω] [Field F] [Algebra Ω F]

theorem mem_of_ord_nonneg' (v : Place Ω F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact v.toValuationSubring.zero_mem
  · exact v.mem_of_ord_nonneg hf h

theorem inv_mem_of_ord_le_zero (v : Place Ω F) {f : F} (hf : f ≠ 0) (h : v.ord f ≤ 0) :
    f⁻¹ ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg (inv_ne_zero hf) (by rw [v.ord_inv]; linarith)

theorem exists_ord_sub_algebraMap_pos [IsAlgClosed Ω] (v : Place Ω F) (t : F)
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin Ω ({t} : Set F)) F] (ht : 0 ≤ v.ord t) :
    ∃ a : Ω, 0 < v.ord (t - algebraMap Ω F a) := by
  by_contra hcon
  push Not at hcon
  have htO : t ∈ v.toValuationSubring := mem_of_ord_nonneg' v ht

  let Ov : Subalgebra Ω F :=
    { v.toValuationSubring.toSubring with
      algebraMap_mem' := v.algebraMap_mem' }
  have hOv : ∀ x, x ∈ Ov ↔ x ∈ v.toValuationSubring := fun _ => Iff.rfl
  have haeval : ∀ r : Polynomial Ω, Polynomial.aeval t r ∈ v.toValuationSubring := by
    intro r
    have : Polynomial.aeval t r = Ov.val (Polynomial.aeval (⟨t, htO⟩ : ↥Ov) r) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [this]
    exact (Polynomial.aeval (⟨t, htO⟩ : ↥Ov) r).2

  have hpoly : ∀ (n : ℕ) (p : Polynomial Ω), p.natDegree = n → p ≠ 0 →
      (Polynomial.aeval t p)⁻¹ ∈ v.toValuationSubring := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hn hp0
      by_cases hdeg : p.natDegree = 0
      · obtain ⟨c, rfl⟩ : ∃ c, p = Polynomial.C c := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
        rw [Polynomial.aeval_C, ← map_inv₀]
        exact v.algebraMap_mem' _
      · have hdeg' : p.degree ≠ 0 := fun h => hdeg (Polynomial.natDegree_eq_of_degree_eq_some h)
        obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg'
        have hsplit : (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) = p :=
          Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
        have hq0 : p /ₘ (Polynomial.X - Polynomial.C a) ≠ 0 := by
          intro h0; apply hp0; rw [← hsplit, h0, mul_zero]
        have hqdeg : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree < n := by
          rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C a), Polynomial.natDegree_X_sub_C, ← hn]
          omega
        rw [← hsplit, map_mul, mul_inv]
        refine mul_mem ?_ (ih _ hqdeg _ rfl hq0)
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
        by_cases h0 : t - algebraMap Ω F a = 0
        · rw [h0, inv_zero]; exact zero_mem _
        · exact inv_mem_of_ord_le_zero v h0 (hcon a)

  have hadj : ∀ x ∈ IntermediateField.adjoin Ω ({t} : Set F), x ∈ v.toValuationSubring := by
    intro x hx
    rw [IntermediateField.mem_adjoin_simple_iff] at hx
    obtain ⟨r, s, rfl⟩ := hx
    by_cases hs : s = 0
    · rw [hs, map_zero, div_zero]; exact zero_mem _
    · rw [div_eq_mul_inv]
      exact mul_mem (haeval r) (hpoly _ s rfl hs)

  have hall : ∀ x : F, x ∈ v.toValuationSubring := by
    intro x
    have hx : IsIntegral ↥(IntermediateField.adjoin Ω ({t} : Set F)) x :=
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    let φ : ↥(IntermediateField.adjoin Ω ({t} : Set F)) →+* ↥v.toValuationSubring :=
      { toFun := fun r => ⟨r, hadj r r.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hxV : IsIntegral ↥v.toValuationSubring x := hx.map_of_comp_eq φ (RingHom.id F) (by ext; rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxV
    rw [← hy]
    exact y.2
  exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => hall x⟩)

end PlaceLemmas

end ModularCurve.TowerUnramAux

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure.ModularCurve ModularCurve.TowerUnramAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (K₁ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (J : ↥K₁) (hJ : ((J : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (x : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥K₁) (hx : 0 ≤ x.ord J)
    (h0 : 0 < x.ord J → p % 3 ≠ 1 ∧ (p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1))
    (h1728 : 0 < x.ord (J - 1728) → p % 4 ≠ 1 ∧ (p = 2 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1)) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) x = 1  := by
  classical
  have hK₁' : K₁ = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)) := by
    rw [hK₁]; rfl
  subst hK₁'
  subst hK₂

  set j := J with hjdef
  set P := x with hPdef
  have hj : ((j : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq := hJ
  have hP : 0 ≤ P.ord j := hx

  let ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) := IntermediateField.inclusion hle
  have hjq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hj'mem : coeffEmb (AlgebraicClosure ℚ) jq ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) := by
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 (M * p))
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let j' : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := ⟨coeffEmb (AlgebraicClosure ℚ) jq, hj'mem⟩
  have hιj' : ι j' = j := Subtype.ext hj.symm
  have hyK : ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := hj.trans hjq
  have hyK' : ((j' : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := hjq

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]
    · rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have hΓ1 : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p := by
    intro A hA
    obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hA
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h00
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h11
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h10
    · rw [CongruenceSubgroup.Gamma0_mem]
      simpa using congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h10
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) hT1 (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) rfl j hj
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 (M * p)) hT0 (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) rfl j' rfl

  letI algK : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  letI algE : Algebra ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    (ι.toRingHom.comp (algebraMap ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))).toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmap : (IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))).map ι = IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)))) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hιj']
  let e₁ : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ≃ₐ[AlgebraicClosure ℚ] ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))))) :=
    (IntermediateField.equivMap (IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ι).trans (IntermediateField.equivOfEq hmap)
  haveI := hFD
  haveI hfinE : Module.Finite ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    Module.Finite.of_equiv_equiv e₁.symm.toRingEquiv (RingEquiv.refl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)))) (by
      refine RingHom.ext fun y => ?_
      obtain ⟨z, rfl⟩ := e₁.surjective y
      show ι ((e₁.symm (e₁ z) : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) = ((e₁ z : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)))))) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))))
      rw [e₁.symm_apply_apply]
      rfl)
  haveI hfinK : Module.Finite ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) :=
    Module.Finite.of_restrictScalars_finite ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)))
  haveI : Algebra.IsIntegral ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) := Algebra.IsIntegral.of_finite _ _
  have hι : ι.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) x

  obtain ⟨hub0, hub1728, hubgen⟩ :=
    ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
      (M * p) (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) hΓ1 j hyK P
  obtain ⟨hlb0', hlb1728'⟩ :=
    ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic (AlgebraicClosure ℚ) (M * p) j' hyK'

  have hp : p.Prime := Fact.out
  have hν3 : 0 < P.ord j → (9 ∣ M * p ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M * p ∧ ℓ % 3 = 2) := by
    intro hpos
    obtain ⟨hp3, hp3'⟩ := h0 hpos
    by_cases hp3e : p = 3
    · obtain ⟨ℓ, hℓ, hℓM, hℓ3⟩ := hp3' hp3e
      have hℓne3 : ℓ ≠ 3 := fun h => hpM (by rw [hp3e]; exact h ▸ hℓM)
      have : ℓ % 3 ≠ 0 := fun h => hℓne3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp (Nat.dvd_of_mod_eq_zero h)).symm
      exact Or.inr ⟨ℓ, hℓ, dvd_mul_of_dvd_left hℓM p, by omega⟩
    · have : p % 3 ≠ 0 := fun h => hp3e ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
      exact Or.inr ⟨p, hp, dvd_mul_left p M, by clear hp3' hpos; omega⟩
  have hν2 : 0 < P.ord (j - 1728) → (4 ∣ M * p ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M * p ∧ ℓ % 4 = 3) := by
    intro hpos
    obtain ⟨hp4, hp4'⟩ := h1728 hpos
    by_cases hp2e : p = 2
    · obtain ⟨ℓ, hℓ, hℓM, hℓ4⟩ := hp4' hp2e
      have hℓne2 : ℓ ≠ 2 := fun h => hpM (by rw [hp2e]; exact h ▸ hℓM)
      have hodd : ℓ % 2 = 1 := Nat.odd_iff.mp (hℓ.odd_of_ne_two hℓne2)
      exact Or.inr ⟨ℓ, hℓ, dvd_mul_of_dvd_left hℓM p, by omega⟩
    · have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2e)
      exact Or.inr ⟨p, hp, dvd_mul_left p M, by clear hp4' hpos; omega⟩

  have he1 : 1 ≤ Place.ramificationIndexAlong ι P := Place.one_le_ramificationIndexAlong ι hι P
  have hord : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))), P.ord (ι f) =
      (Place.ramificationIndexAlong ι P : ℤ) * (P.restrictAlong ι hι).ord f :=
    fun f => Place.ord_restrictAlong ι hι P f
  have he1' : (1 : ℤ) ≤ (Place.ramificationIndexAlong ι P : ℤ) := by exact_mod_cast he1

  have hP' : 0 ≤ (P.restrictAlong ι hι).ord j' := by
    have h := hord j'
    rw [hιj'] at h
    rw [h] at hP
    exact nonneg_of_mul_nonneg_right hP (by linarith)

  haveI := hFD'
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨a, ha⟩ := exists_ord_sub_algebraMap_pos (P.restrictAlong ι hι) j' hP'
  have hkey := hord (j' - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) a)
  rw [map_sub, hιj', AlgHom.commutes] at hkey

  suffices hle1 : (Place.ramificationIndexAlong ι P : ℤ) ≤ 1 by
    have : Place.ramificationIndexAlong ι P ≤ 1 := by exact_mod_cast hle1
    exact le_antisymm this he1
  rcases eq_or_ne a 0 with rfl | ha0
  · simp only [map_zero, sub_zero] at ha hkey
    have hposP : 0 < P.ord j := by rw [hkey]; exact mul_pos (by linarith) ha
    have h3 : (P.restrictAlong ι hι).ord j' = 3 := hlb0' (hν3 hposP) (P.restrictAlong ι hι) ha
    rw [h3] at hkey
    have : (Place.ramificationIndexAlong ι P : ℤ) * 3 ≤ 3 := hkey ▸ hub0
    linarith
  · rcases eq_or_ne a 1728 with rfl | ha1728
    · have h1728K : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) 1728 = 1728 := map_ofNat _ 1728
      have h1728K' : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) 1728 = 1728 := map_ofNat _ 1728
      rw [h1728K'] at ha hkey
      rw [h1728K] at hkey
      have hposP : 0 < P.ord (j - 1728) := by rw [hkey]; exact mul_pos (by linarith) ha
      have h2 : (P.restrictAlong ι hι).ord (j' - 1728) = 2 := hlb1728' (hν2 hposP) (P.restrictAlong ι hι) ha
      rw [h2] at hkey
      have : (Place.ramificationIndexAlong ι P : ℤ) * 2 ≤ 2 := hkey ▸ hub1728
      linarith
    · have h1 : P.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p))) a) ≤ 1 := hubgen a ha0 ha1728
      rw [hkey] at h1
      nlinarith

end
end S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure (solution)
