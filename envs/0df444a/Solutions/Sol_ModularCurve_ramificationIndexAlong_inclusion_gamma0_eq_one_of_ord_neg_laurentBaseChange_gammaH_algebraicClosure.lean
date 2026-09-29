-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_neg_laurentBaseChange_gammaH_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ca855169-f209-5b29-b3f8-6898385d596c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion_forall_le
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq
import Theorems.Thm_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level
import Theorems.Thm_ModularCurve_LevelN_Descent_fixer_le_gamma0
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_neg_laurentBaseChange_gammaH_algebraicClosure
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~mem_restrictAlong_iff P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_neg_laurentBaseChange_gammaH_algebraicClosure.ModularCurve"
open scoped MatrixGroups IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset qExpand jq jGen coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH jqModC jqModC_rat map_jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion_forall_le LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq LevelN.exists_place_ord_jGen_le_two_three_level LevelN.Descent.fixer_le_gamma0 JOneES.exists_transcendental_finiteDimensional_laurentBaseChange finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC"
namespace CuspUnramAux
p2m_open "ModularCurve~mem_restrictAlong_iff"

theorem isDomain_levelN_ring (N : ℕ) [NeZero N] : IsDomain ↥(ModularCurve.LevelN.ring N) := by
  have h := WLight.levelN_structure_package N (fun τ => PeriodPair.ofTau τ) (fun τ => ⟨rfl, rfl⟩)
    (ModularCurve.LevelN.wp N) (fun v τ => rfl) (ModularCurve.LevelN.fricke N) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := h
  haveI : NoZeroDivisors ↥(ModularCurve.LevelN.ring N) := ⟨fun {a b} hab => by
    have := hdom a b a.2 b.2 (by rw [← Subalgebra.coe_mul, hab]; rfl)
    rcases this with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0⟩
  haveI : Nontrivial ↥(ModularCurve.LevelN.ring N) := inferInstance
  exact NoZeroDivisors.to_isDomain _

theorem mem_sup_zpowers_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ H ∨ -g ∈ H := by
  haveI hN : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute ((-1 : SL(2, ℤ)) ^ k) g := (Commute.neg_one_left g).zpow_left k
    rw [← hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  have hpm : ∀ n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)), n = 1 ∨ n = -1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_ofNat]
      simp
    · right
      rw [zpow_add, zpow_mul, zpow_ofNat, zpow_one]
      simp
  constructor
  · intro hg
    have hg' : g ∈ ((H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨h, hh, n, hn, rfl⟩ := Set.mem_mul.mp hg'
    rcases hpm n hn with rfl | rfl
    · left; simpa using hh
    · right; simpa using hh
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have : g = (-g) * (-1) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem dvd_of_T_zpow_mem (N : ℕ) [NeZero N] (k : ℤ)
    (h : ModularGroup.T ^ k ∈ CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) : (N : ℤ) ∣ k := by
  rw [mem_sup_zpowers_neg_one_iff] at h
  have hT : ((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, k; 0, 1] := ModularGroup.coe_T_zpow k
  rcases h with h | h
  · have h01 := (CongruenceSubgroup.Gamma_mem.mp h).2.1
    rw [show ((ModularGroup.T ^ k : SL(2, ℤ)) 0 1 : ℤ) = k by
      change ((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = k; rw [hT]; rfl] at h01
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k N).mp h01
  · have h01 := (CongruenceSubgroup.Gamma_mem.mp h).2.1
    rw [show ((-(ModularGroup.T ^ k) : SL(2, ℤ)) 0 1 : ℤ) = -k by
      change ((-(ModularGroup.T ^ k) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -k
      rw [Matrix.SpecialLinearGroup.coe_neg, hT]; rfl] at h01
    rw [Int.cast_neg, neg_eq_zero] at h01
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k N).mp h01

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem]
  have hT : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow N
  have e : ∀ i j, ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) i j : ℤ) = !![(1 : ℤ), (N : ℤ); 0, 1] i j := fun i j => by
    change ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _; rw [hT]
  rw [e 0 0, e 0 1, e 1 0, e 1 1]
  simp

theorem ramificationIndexAlong_eq_one_of_ord_eq {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F)
    (hpos : 0 < w.ord (φ f)) (heq : w.ord (φ f) = (w.restrictAlong φ hφ).ord f) :
    Place.ramificationIndexAlong φ w = 1 := by
  have h := Place.ord_restrictAlong φ hφ w f
  rw [← heq] at h
  have h1 : ((Place.ramificationIndexAlong φ w : ℕ) : ℤ) = 1 := by
    have : w.ord (φ f) * ((Place.ramificationIndexAlong φ w : ℕ) : ℤ) = w.ord (φ f) * 1 := by rw [mul_one, mul_comm]; exact h.symm
    exact mul_left_cancel₀ hpos.ne' this
  exact_mod_cast h1

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact Place.mem_restrict_iff (w := w) (F := F)

theorem restrictAlong_restrictAlong {K F₁ F₂ F₃ : Type*} [Field K] [Field F₁] [Field F₂] [Field F₃]
    [Algebra K F₁] [Algebra K F₂] [Algebra K F₃]
    (φ : F₁ →ₐ[K] F₂) (ψ : F₂ →ₐ[K] F₃) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψφ : (ψ.comp φ).toRingHom.IsIntegral) (w : Place K F₃) :
    (w.restrictAlong ψ hψ).restrictAlong φ hφ = w.restrictAlong (ψ.comp φ) hψφ := by
  apply Place.ext
  ext f
  rw [mem_restrictAlong_iff, mem_restrictAlong_iff, mem_restrictAlong_iff]
  rfl

section Inclusion

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isIntegral_inclusion
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L)) (K₁ : IntermediateField L (LaurentSeries L)) (hle : K₁ ≤ K)
    (j : ↥K) (hjK₁ : ((j : LaurentSeries L)) ∈ K₁)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  haveI := hFD
  set E := IntermediateField.adjoin L ({j} : Set ↥K) with hE

  have hEK₁ : ∀ x : ↥E, (((x : ↥K) : LaurentSeries L)) ∈ K₁ := by
    have hle' : E ≤ IntermediateField.comap K.val K₁ := by
      rw [hE, IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hjK₁
    intro x
    exact hle' x.2
  let ψ : ↥E →+* ↥K₁ :=
    { toFun := fun x => ⟨((x : ↥K) : LaurentSeries L), hEK₁ x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hψ : (IntermediateField.inclusion hle).toRingHom.comp ψ = algebraMap ↥E ↥K := by
    ext x
    rfl
  intro y
  have hy : IsIntegral ↥E y := Algebra.IsIntegral.isIntegral y
  refine ⟨(minpoly ↥E y).map ψ, (minpoly.monic hy).map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ, ← Polynomial.aeval_def, minpoly.aeval]

end Inclusion

end ModularCurve.CuspUnramAux

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset qExpand jq jGen coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH jqModC jqModC_rat map_jqModC LevelN.wp LevelN.fricke LevelN.jAnalytic LevelN.ring LevelN.jGen exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion_forall_le LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.exists_place_ord_neg_forall_smul_eq LevelN.exists_place_ord_jGen_le_two_three_level LevelN.Descent.fixer_le_gamma0 JOneES.exists_transcendental_finiteDimensional_laurentBaseChange finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC" namespace CuspUnramAux end ModularCurve.CuspUnramAux
p2m_open_scoped "ModularCurve" in
open ModularCurve.CuspUnramAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in
theorem ModularCurve.CuspUnramAux.main
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ (γ : SL(2, ℤ)) (k : ℤ), γ * ModularGroup.T ^ k * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N →
      γ * ModularGroup.T ^ k * γ⁻¹ ∈ CohCarrier.GammaH N H)
    (hle : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) ≤
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)))
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)))) (hP : P.ord y < 0) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) P = 1 := by
  classical
  haveI : IsDomain ↥(ModularCurve.LevelN.ring N) := isDomain_levelN_ring N
  let K : Type := FractionRing ↥(ModularCurve.LevelN.ring N)
  letI algCK : Algebra ℂ K := inferInstance
  haveI : IsScalarTower ℂ ↥(ModularCurve.LevelN.ring N) K := inferInstance
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    constructor
    intro x
    obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
    refine ⟨p, hp0, ?_⟩
    rw [Polynomial.aeval_def] at hp ⊢
    convert hp using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  let ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom

  have hH0 : CohCarrier.GammaH N H ≤ CongruenceSubgroup.Gamma0 N := CohCarrier.GammaH_le_Gamma0 H
  have hTH : ModularGroup.T ∈ CohCarrier.GammaH N H := ModularCurve.translation_mem_GammaH N H
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := hH0 hTH
  have hΓH : CongruenceSubgroup.Gamma N ≤ CohCarrier.GammaH N H := by
    intro γ hγ
    obtain ⟨h00, -, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0_mem).mpr h10
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hγ0, ?_⟩
    have : CohCarrier.gamma0Units N ⟨γ, hγ0⟩ = 1 := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      exact h11
    rw [this]
    exact one_mem H
  haveI : (CohCarrier.GammaH N H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH N H)
  haveI : (CongruenceSubgroup.Gamma0 N).FiniteIndex := inferInstance

  obtain ⟨Φ, E', hE'j, hE'Φ, hΦc, hΦy, hΦfix, hΦfix'⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion_forall_le N
      (CohCarrier.GammaH N H) hΓH hTH ι K

  obtain ⟨hst, σ, hσ, hker, hfix, htr, hfd, hdeg, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N K

  obtain ⟨W, hWneg, hWT⟩ := ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq N K (hst ModularGroup.T⁻¹)
  obtain ⟨-, -, ⟨W₁, hW₁neg, hW₁ge⟩⟩ := ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level N K
  let t : K := algebraMap ↥(ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)
  have ht0 : t ≠ 0 := fun h => by
    have : W.ord t < 0 := hWneg
    rw [h, Place.ord_zero] at this
    exact lt_irrefl _ this
  let t' : K := t⁻¹
  have hadj : IntermediateField.adjoin ℂ ({t'} : Set K) = IntermediateField.adjoin ℂ ({t} : Set K) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have : t = t'⁻¹ := (inv_inv t).symm
      rw [this]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t')
  have hfd' : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := by rw [hadj]; exact hfd
  have hgal' : IsGalois ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := by rw [hadj]; exact hgal
  have hdeg' : Module.finrank ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K =
      (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by rw [hadj]; exact hdeg
  have hfixL : ∀ (d : SL(2, ℤ)), ∀ z ∈ IntermediateField.adjoin ℂ ({t'} : Set K), σ d z = z := fun d z hz => by
    rw [hadj, ← hfix] at hz
    exact (IntermediateField.mem_fixedField_iff _ z).mp hz _ ⟨d, rfl⟩
  have hy0 : y ≠ 0 := fun h => by rw [h, Place.ord_zero] at hP; exact lt_irrefl _ hP
  have hΦy' : Φ y = t := hΦy y hy
  have hΦy'' : Φ y⁻¹ = t' := by rw [map_inv₀, hΦy']

  let incl : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) := IntermediateField.inclusion hle
  have hinclcoe : ∀ u, ((incl u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)))) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun u => IntermediateField.coe_inclusion hle u
  let Φ₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) →+* K := Φ.comp incl.toRingHom
  have hΦ₀ : ∀ u, Φ₀ u = Φ (incl u) := fun _ => rfl
  let E : IntermediateField ℂ K := IntermediateField.adjoin ℂ (Set.range Φ)
  let E₀ : IntermediateField ℂ K := IntermediateField.adjoin ℂ (Set.range Φ₀)
  have hE₀E : E₀ ≤ E := by
    refine IntermediateField.adjoin.mono ℂ _ _ ?_
    rintro _ ⟨u, rfl⟩; exact ⟨incl u, rfl⟩
  have hΦmem : ∀ f, Φ f ∈ E := fun f => IntermediateField.subset_adjoin ℂ _ ⟨f, rfl⟩
  have hΦ₀mem : ∀ f, Φ₀ f ∈ E₀ := fun f => IntermediateField.subset_adjoin ℂ _ ⟨f, rfl⟩
  let ΦE : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) →+* ↥E := Φ.codRestrict E hΦmem
  let ΦE₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) →+* ↥E₀ := Φ₀.codRestrict E₀ hΦ₀mem
  have hΦE : ∀ f, ((ΦE f : ↥E) : K) = Φ f := fun f => RingHom.codRestrict_apply Φ E hΦmem f
  have hΦE₀ : ∀ f, ((ΦE₀ f : ↥E₀) : K) = Φ₀ f := fun f => RingHom.codRestrict_apply Φ₀ E₀ hΦ₀mem f
  let inclE : ↥E₀ →ₐ[ℂ] ↥E := IntermediateField.inclusion hE₀E
  have hsqE : ∀ u, inclE (ΦE₀ u) = ΦE (incl u) := fun u => Subtype.ext (by
    rw [IntermediateField.coe_inclusion, hΦE₀, hΦE, hΦ₀])
  have hcoeC : ∀ z : ℂ, ((algebraMap ℂ ↥E z : ↥E) : K) = algebraMap ℂ K z := fun _ => rfl
  have hcoeC₀ : ∀ z : ℂ, ((algebraMap ℂ ↥E₀ z : ↥E₀) : K) = algebraMap ℂ K z := fun _ => rfl
  letI algFE : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ↥E := ΦE.toAlgebra
  letI algFE₀ : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) ↥E₀ := ΦE₀.toAlgebra
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQE : Algebra (AlgebraicClosure ℚ) ↥E := ((algebraMap ℂ ↥E).comp ι).toAlgebra
  letI algQE₀ : Algebra (AlgebraicClosure ℚ) ↥E₀ := ((algebraMap ℂ ↥E₀).comp ι).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥E₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ↥E := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (by
      change ((algebraMap ℂ ↥E (ι c) : ↥E) : K) = ((ΦE (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) c) : ↥E) : K)
      rw [hcoeC, hΦE, hΦc])
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) ↥E₀ := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (by
      change ((algebraMap ℂ ↥E₀ (ι c) : ↥E₀) : K) = ((ΦE₀ (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) c) : ↥E₀) : K)
      rw [hcoeC₀, hΦE₀, hΦ₀]
      have : incl (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) c) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) c := incl.commutes c
      rw [this, hΦc])

  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) (CohCarrier.GammaH N H) hTH
  obtain ⟨x₁, hx₁tr, hx₁fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma0 N) hT0
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) := isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) := isCurveOver_of_transcendental_of_perfectField hx₁tr hx₁fd

  have hy₀mem : (y : LaurentSeries (AlgebraicClosure ℚ)) ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) := by
    have hjq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
      rw [coeffEmb, ← jqModC_rat]
      exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [hy, ← hjq]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 N)
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let y₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) := ⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hy₀mem⟩
  have hincly₀ : incl y₀ = y := Subtype.ext (IntermediateField.coe_inclusion hle y₀)
  have hΦ₀y : Φ₀ y₀ = t := by rw [hΦ₀, hincly₀, hΦy']
  have hy₀0 : y₀ ≠ 0 := fun h => hy0 (by rw [← hincly₀, h, map_zero])

  have htrE : Transcendental ℂ (ΦE y⁻¹) := fun h => htr (by
    have h' := IntermediateField.isAlgebraic_iff.mp h
    rw [hΦE, hΦy''] at h'
    have h'' : IsAlgebraic ℂ (t'⁻¹) := h'.inv
    rwa [inv_inv] at h'')
  have htrE₀ : Transcendental ℂ (ΦE₀ y₀⁻¹) := fun h => htr (by
    have h' := IntermediateField.isAlgebraic_iff.mp h
    rw [hΦE₀, map_inv₀, hΦ₀y] at h'
    have h'' : IsAlgebraic ℂ (t⁻¹⁻¹) := h'.inv
    rwa [inv_inv] at h'')
  haveI := hfd'
  have hvalE : ((ΦE y⁻¹ : ↥E) : K) = t' := by rw [hΦE, hΦy'']
  have hvalE₀ : ((ΦE₀ y₀⁻¹ : ↥E₀) : K) = t' := by rw [hΦE₀, map_inv₀, hΦ₀y]
  have hleCt : IntermediateField.adjoin ℂ ({t'} : Set K) ≤ E₀ :=
    IntermediateField.adjoin_simple_le_iff.mpr (hvalE₀ ▸ (ΦE₀ y₀⁻¹).2)
  have hleCtE : IntermediateField.adjoin ℂ ({t'} : Set K) ≤ E := hleCt.trans hE₀E

  have hEfd_of : ∀ (M : IntermediateField ℂ K) (x : ↥M), ((x : ↥M) : K) = t' →
      FiniteDimensional ↥(IntermediateField.adjoin ℂ ({x} : Set ↥M)) ↥M := by
    intro M x hx
    have hlift : IntermediateField.lift (IntermediateField.adjoin ℂ ({x} : Set ↥M)) = IntermediateField.adjoin ℂ ({t'} : Set K) := by
      rw [IntermediateField.lift_adjoin_simple, hx]
    have hle' : IntermediateField.adjoin ℂ ({t'} : Set K) ≤ M := by rw [← hlift]; exact IntermediateField.lift_le _
    let M₂ : IntermediateField ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := IntermediateField.extendScalars hle'
    haveI hM₂ : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥M₂ := inferInstance
    let e₁ : ↥(IntermediateField.adjoin ℂ ({x} : Set ↥M)) ≃ₐ[ℂ] ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) :=
      (IntermediateField.liftAlgEquiv _).trans (IntermediateField.equivOfEq hlift)
    let e₂ : ↥M₂ ≃+* ↥M := RingEquiv.refl _
    exact Module.Finite.of_equiv_equiv e₁.symm.toRingEquiv e₂ (by
      refine RingHom.ext fun w => Subtype.ext ?_
      have h1 : ∀ v : ↥(IntermediateField.adjoin ℂ ({x} : Set ↥M)), ((e₁ v : ↥(IntermediateField.adjoin ℂ ({t'} : Set K))) : K) = ((v : ↥M) : K) := fun v => rfl
      have h2 := congrArg (fun u : ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) => (u : K)) (e₁.apply_symm_apply w)
      simp only [h1] at h2
      exact h2)
  have hEfd : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({ΦE y⁻¹} : Set ↥E)) ↥E := hEfd_of E _ hvalE
  have hE₀fd : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({ΦE₀ y₀⁻¹} : Set ↥E₀)) ↥E₀ := hEfd_of E₀ _ hvalE₀
  have hgen_of : ∀ (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F] (Ψ : F →+* K) (M : IntermediateField ℂ K)
      (hM : M = IntermediateField.adjoin ℂ (Set.range Ψ)) (hΨ : ∀ f, Ψ f ∈ M),
      letI := (Ψ.codRestrict M hΨ).toAlgebra
      IntermediateField.adjoin ℂ (Set.range (algebraMap F ↥M)) = ⊤ := by
    intro F _ _ Ψ M hM hΨ
    letI := (Ψ.codRestrict M hΨ).toAlgebra
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have : Subtype.val '' Set.range (algebraMap F ↥M) = Set.range Ψ := by
      ext w
      constructor
      · rintro ⟨_, ⟨f, rfl⟩, rfl⟩; exact ⟨f, (RingHom.codRestrict_apply Ψ M hΨ f).symm⟩
      · rintro ⟨f, rfl⟩; exact ⟨Ψ.codRestrict M hΨ f, ⟨f, rfl⟩, RingHom.codRestrict_apply Ψ M hΨ f⟩
    rw [this]; exact hM.symm
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ↥E)) = ⊤ := hgen_of _ Φ E rfl hΦmem
  have hgen₀ : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) ↥E₀)) = ⊤ := hgen_of _ Φ₀ E₀ rfl hΦ₀mem

  obtain ⟨P', hP'comap, hP'ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ℂ ↥E ⟨x₀, hx₀tr, hx₀fd⟩ ⟨ΦE y⁻¹, htrE, hEfd⟩ hgen P

  have hFD : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CohCarrier.GammaH N H) hTH
      (AlgebraicClosure ℚ) _ rfl y (by rw [hy, coeffEmb, ← jqModC_rat]; exact (map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm)
  have hincl : incl.toRingHom.IsIntegral := isIntegral_inclusion (AlgebraicClosure ℚ) _ _ hle y hy₀mem hFD
  have hinclE : inclE.toRingHom.IsIntegral := by

    letI algRS : Algebra ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E := (IntermediateField.inclusion hleCtE).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E :=
      Module.Finite.of_injective (IsScalarTower.toAlgHom ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E K).toLinearMap (fun a b h => Subtype.ext h)
    haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E := Algebra.IsIntegral.of_finite _ _
    intro x
    have hx : IsIntegral ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) x := Algebra.IsIntegral.isIntegral x
    let ψ : ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) →+* ↥E₀ := (IntermediateField.inclusion hleCt).toRingHom
    have hψ : inclE.toRingHom.comp ψ = algebraMap ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥E := by ext z; rfl
    refine ⟨(minpoly ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) x).map ψ, (minpoly.monic hx).map ψ, ?_⟩
    rw [Polynomial.eval₂_map, hψ, ← Polynomial.aeval_def, minpoly.aeval]

  let Q' : Place ℂ ↥E₀ := P'.restrictAlong inclE hinclE
  let P₀ : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) := P.restrictAlong incl hincl
  obtain ⟨Q₀, -, hQ₀ord, hQ₀uniq⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) ℂ ↥E₀ ⟨x₁, hx₁tr, hx₁fd⟩ ⟨ΦE₀ y₀⁻¹, htrE₀, hE₀fd⟩ hgen₀ P₀

  have hQ' : Q' = Q₀ := by
    apply hQ₀uniq
    ext u
    rw [ValuationSubring.mem_comap, mem_restrictAlong_iff, mem_restrictAlong_iff]
    change (inclE (ΦE₀ u) : ↥E) ∈ P'.toValuationSubring ↔ incl u ∈ P.toValuationSubring
    rw [hsqE, ← hP'comap, ValuationSubring.mem_comap]
    rfl

  have hW' : 0 < W.ord (t' - algebraMap ℂ K 0) := by
    rw [map_zero, sub_zero, Place.ord_inv]; linarith
  have hW₁' : 0 < W₁.ord (t' - algebraMap ℂ K 0) := by
    rw [map_zero, sub_zero, Place.ord_inv]; linarith

  have hint_of : ∀ (F' : Type) [Field F'] [Algebra ℂ F'] (x : F') (ψ : F' →ₐ[ℂ] K), ψ x = t' → ψ.toRingHom.IsIntegral := by
    intro F' _ _ x ψ hψ
    let S : Subalgebra ℂ K := ψ.range
    have hleS : (IntermediateField.adjoin ℂ ({t'} : Set K)).toSubalgebra ≤ S := by
      have : IntermediateField.adjoin ℂ ({t'} : Set K) ≤ ψ.fieldRange :=
        IntermediateField.adjoin_simple_le_iff.mpr ⟨x, hψ⟩
      intro w hw
      exact (AlgHom.mem_fieldRange.mp (this hw))
    letI algRS : Algebra ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥S := (Subalgebra.inclusion hleS).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) ↥S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ↥S K := Module.Finite.of_restrictScalars_finite ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) _ _
    haveI : Algebra.IsIntegral ↥S K := Algebra.IsIntegral.of_finite _ _
    have hS : (algebraMap ↥S K).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥S) x
    let e : F' ≃ₐ[ℂ] ↥S := AlgEquiv.ofInjective ψ ψ.toRingHom.injective
    have he : ψ.toRingHom = (algebraMap ↥S K).comp e.toAlgHom.toRingHom := by
      refine RingHom.ext fun x => ?_
      change ψ x = ((e x : ↥S) : K)
      rw [AlgEquiv.ofInjective_apply]
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective e.toAlgHom.toRingHom e.surjective) hS

  have hordW_le : W.ord (t' - algebraMap ℂ K 0) ≤ N := by
    obtain ⟨-, -, h3K, -, -⟩ := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ t' t' (0 : ℂ) (AlgHom.id ℂ K) rfl
      hfd' hgal' (hint_of K t') W₁ hW₁'
    obtain ⟨ψ, hψ, hWψ⟩ := h3K W hW'
    have h := Place.ord_restrictAlong ψ (hint_of K t' ψ hψ) W₁ (t' - algebraMap ℂ K 0)
    rw [hWψ, map_sub, AlgHom.commutes, hψ] at h
    have hb : W₁.ord (t' - algebraMap ℂ K 0) ≤ N := by rw [map_zero, sub_zero, Place.ord_inv]; linarith
    have he : (1 : ℤ) ≤ (Place.ramificationIndexAlong ψ W₁ : ℤ) := by
      rcases Nat.eq_zero_or_pos (Place.ramificationIndexAlong ψ W₁) with h0 | h0
      · exfalso; rw [h0, Nat.cast_zero, zero_mul] at h; exact hW₁'.ne' h
      · exact_mod_cast h0
    nlinarith

  have hσsub : ∀ d : SL(2, ℤ), ∃ g : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K), g.restrictScalars ℂ = σ d := fun d =>
    ⟨{ (σ d).toRingEquiv with commutes' := fun z => hfixL d z z.2 }, AlgEquiv.ext fun _ => rfl⟩
  let rSH : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K) →* (K ≃ₐ[ℂ] K) :=
    { toFun := fun g => g.restrictScalars ℂ
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hrSH : ∀ g z, rSH g z = g z := fun _ _ => rfl
  have hrSH' : ∀ g, rSH g = g.restrictScalars ℂ := fun _ => rfl
  have rSH_inj : Function.Injective rSH := fun g h hgh => AlgEquiv.ext fun z => by
    have := congrArg (fun f : K ≃ₐ[ℂ] K => f z) hgh
    exact this
  haveI := hfd'
  haveI := hgal'
  have hrange : σ.range = rSH.range := by
    have hle' : σ.range ≤ rSH.range := by
      rintro _ ⟨d, rfl⟩
      obtain ⟨g, hg⟩ := hσsub d
      exact ⟨g, hg⟩
    haveI : Finite rSH.range := inferInstance
    refine Subgroup.eq_of_le_of_card_ge hle' (le_of_eq ?_)
    show Nat.card rSH.range = Nat.card σ.range
    rw [← Subgroup.index_ker σ, hker, ← hdeg', ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective rSH_inj).toEquiv).symm
  obtain ⟨gT, hgT⟩ := hσsub ModularGroup.T
  have hgTW : SemilinearAut.ofAlgAut (gT.restrictScalars ℂ) • W = W := by
    rw [hgT]; exact hWT (σ ModularGroup.T) (hσ ModularGroup.T)

  let Stab : Subgroup (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K) :=
    { carrier := {g | SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W}
      mul_mem' := fun {a b} ha hb => by
        change SemilinearAut.ofAlgAut ((a * b).restrictScalars ℂ) • W = W
        rw [show (a * b).restrictScalars ℂ = a.restrictScalars ℂ * b.restrictScalars ℂ from AlgEquiv.ext fun _ => rfl,
          map_mul, mul_smul, hb, ha]
      one_mem' := by
        change SemilinearAut.ofAlgAut ((1 : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K)).restrictScalars ℂ) • W = W
        rw [show (1 : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K)).restrictScalars ℂ = 1 from AlgEquiv.ext fun _ => rfl, map_one, one_smul]
      inv_mem' := fun {a} ha => by
        change SemilinearAut.ofAlgAut (a⁻¹.restrictScalars ℂ) • W = W
        rw [show a⁻¹.restrictScalars ℂ = (a.restrictScalars ℂ)⁻¹ from AlgEquiv.ext fun _ => rfl, map_inv,
          inv_smul_eq_iff, ha] }
  have hmemStab : ∀ g : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K), g ∈ Stab ↔ SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W := fun _ => Iff.rfl

  have hgT_zpow : ∀ k : ℤ, gT ^ k = 1 ↔ (N : ℤ) ∣ k := by
    intro k
    have hrk : rSH (gT ^ k) = σ (ModularGroup.T ^ k) := by rw [map_zpow, map_zpow, hrSH', hgT]
    constructor
    · intro h
      apply dvd_of_T_zpow_mem N k
      rw [← hker, MonoidHom.mem_ker, ← hrk, h, map_one]
    · rintro ⟨m, rfl⟩
      apply rSH_inj
      rw [map_one, hrk, ← MonoidHom.mem_ker, hker, zpow_mul]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (T_pow_mem_Gamma N) m)
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have horder : orderOf gT = N := by
    refine (orderOf_eq_iff hN).mpr ⟨?_, fun m hm hm0 h => ?_⟩
    · have := (hgT_zpow (N : ℤ)).mpr (dvd_refl _)
      rwa [zpow_natCast] at this
    · have h' : gT ^ (m : ℤ) = 1 := by rw [zpow_natCast]; exact h
      have hd : N ∣ m := by exact_mod_cast (hgT_zpow (m : ℤ)).mp h'
      exact absurd (Nat.le_of_dvd hm0 hd) (not_le.mpr hm)

  have hvalE' : E.val (ΦE y⁻¹) = t' := by rw [IntermediateField.coe_val]; exact hvalE
  obtain ⟨h1, -, h3, h4, h5⟩ := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ (ΦE y⁻¹) t' (0 : ℂ) E.val hvalE'
    hfd' hgal' (hint_of ↥E (ΦE y⁻¹)) W hW'
  have hStab_eq : Subgroup.zpowers gT = Stab := by
    have hle' : Subgroup.zpowers gT ≤ Stab := (Subgroup.zpowers_le (G := (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K))).mpr hgTW
    haveI : Finite ↥Stab := inferInstance
    refine Subgroup.eq_of_le_of_card_ge hle' ?_
    have hc1 : Nat.card ↥Stab = Nat.card {g : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K) // SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W} :=
      Nat.card_congr (Equiv.refl _)
    have hc2 : Nat.card ↥(Subgroup.zpowers gT) = N := by rw [Nat.card_zpowers, horder]
    rw [hc1, hc2]
    have hle'' := hordW_le
    rw [h1] at hle''
    exact_mod_cast hle''
  have hD : ∀ g : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K), SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W → ∃ k : ℤ, g.restrictScalars ℂ = σ (ModularGroup.T ^ k) := by
    intro g hg
    have hg' : g ∈ Subgroup.zpowers gT := by rw [hStab_eq]; exact hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    refine ⟨k, ?_⟩
    rw [← hrSH', map_zpow, hrSH', hgT, map_zpow]

  have hE'Φ₀ : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))), E' (Φ₀ u) = ModularCurve.qExpand ℂ N (ModularCurve.coeffMap ι (u : LaurentSeries (AlgebraicClosure ℚ))) := by
    intro u; rw [hΦ₀, hE'Φ, hinclcoe]
  have hy₀' : (y₀ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) := hy
  have hΦ₀fix : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ u, σ γ (Φ₀ u) = Φ₀ u := by
    intro γ hγ u
    have hu : ((incl u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) := by
      rw [hinclcoe]; exact u.2
    rw [hΦ₀]
    exact hΦfix' (CongruenceSubgroup.Gamma0 N) hH0 γ hγ (hst γ⁻¹) (σ γ) (hσ γ) (incl u) hu
  have hΦfixσ : ∀ γ ∈ CohCarrier.GammaH N H, ∀ u, σ γ (Φ u) = Φ u :=
    fun γ hγ u => hΦfix γ hγ (hst γ⁻¹) (σ γ) (hσ γ) u
  have hclaim : ∀ (ψ : ↥E →ₐ[ℂ] K), ψ (ΦE y⁻¹) = t' → ∀ g : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K),
      SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W →
      (∀ e₀ : ↥E₀, g (ψ (inclE e₀)) = ψ (inclE e₀)) → ∀ e : ↥E, g (ψ e) = ψ e := by
    intro ψ hψ g hgW hgψ
    obtain ⟨k, hk⟩ := hD g hgW

    have hψfix : ∀ (z : K) (hz : z ∈ IntermediateField.adjoin ℂ ({t'} : Set K)), ψ ⟨z, hleCtE hz⟩ = z := by
      intro z hz
      let T : IntermediateField ℂ ↥E := (AlgHom.equalizer ψ E.val).toIntermediateField (fun x hx => by
        rw [AlgHom.mem_equalizer] at hx ⊢
        rw [map_inv₀, map_inv₀, hx])
      have hTle : IntermediateField.adjoin ℂ ({ΦE y⁻¹} : Set ↥E) ≤ T := by
        rw [IntermediateField.adjoin_simple_le_iff]
        show ψ (ΦE y⁻¹) = E.val (ΦE y⁻¹)
        rw [hψ, hvalE']
      have hzmem : (⟨z, hleCtE hz⟩ : ↥E) ∈ IntermediateField.adjoin ℂ ({ΦE y⁻¹} : Set ↥E) := by
        rw [← IntermediateField.mem_lift (⟨z, hleCtE hz⟩ : ↥E), IntermediateField.lift_adjoin_simple, hvalE]
        exact hz
      exact hTle hzmem

    let E₂ : IntermediateField ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := IntermediateField.extendScalars hleCtE
    let ψ₂ : ↥E₂ →ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K :=
      { ψ.toRingHom with
        commutes' := fun z => hψfix z z.2 }
    haveI : Normal ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := inferInstance
    let φ' : K →ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K := ψ₂.liftNormal K
    have hφ' : ∀ e : ↥E, φ' (e : K) = ψ e := fun e => by
      have := AlgHom.liftNormal_commutes ψ₂ K (e : ↥E₂)
      exact this
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℂ ({t'} : Set K)) K := Algebra.IsAlgebraic.of_finite _ _
    let g' : (K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K) := AlgEquiv.ofBijective φ' (Algebra.IsAlgebraic.algHom_bijective φ')
    have hg' : ∀ e : ↥E, g' (e : K) = ψ e := fun e => (AlgEquiv.ofBijective_apply φ' _ (e : K)).trans (hφ' e)
    obtain ⟨δ', hδ'⟩ : rSH g' ∈ σ.range := by rw [hrange]; exact ⟨g', rfl⟩

    set η : SL(2, ℤ) := δ'⁻¹ * ModularGroup.T ^ k * δ' with hη
    have hσg : rSH g = σ (ModularGroup.T ^ k) := by rw [hrSH']; exact hk
    have hση : σ η = rSH (g'⁻¹ * g * g') := by
      rw [hη, map_mul, map_mul, map_inv, hδ', map_mul, map_mul, map_inv, hσg]
    have hηfix₀ : ∀ u, σ η (Φ₀ u) = Φ₀ u := by
      intro u
      rw [hση, hrSH, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      have hmem : Φ₀ u ∈ E := hE₀E (hΦ₀mem u)
      have h1 : g' (Φ₀ u) = ψ ⟨Φ₀ u, hmem⟩ := hg' ⟨Φ₀ u, hmem⟩
      have h2 : (⟨Φ₀ u, hmem⟩ : ↥E) = inclE (ΦE₀ u) := Subtype.ext (by rw [IntermediateField.coe_inclusion, hΦE₀])
      rw [h1, h2, hgψ, ← h2, ← h1]
      exact g'.symm_apply_apply _

    have hηmem := ModularCurve.LevelN.Descent.fixer_le_gamma0 N K t σ hker hfd hgal hdeg ι Φ₀ E' hE'j hE'Φ₀ y₀ hy₀' hΦ₀y hΦ₀fix η hηfix₀
    rw [mem_sup_zpowers_neg_one_iff] at hηmem
    have hηmem' : η ∈ CongruenceSubgroup.Gamma0 N := by
      rcases hηmem with h | h
      · exact h
      · have h' : -(-η) ∈ CongruenceSubgroup.Gamma0 N := by
          rw [CongruenceSubgroup.Gamma0_mem] at h ⊢
          rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h, neg_zero]
        simpa using h'
    have hηH : η ∈ CohCarrier.GammaH N H := by
      have hη' : δ'⁻¹ * ModularGroup.T ^ k * δ'⁻¹⁻¹ = η := by rw [inv_inv, hη]
      have := hH δ'⁻¹ k (by rw [hη']; exact hηmem')
      rw [hη'] at this
      exact this

    have hηfix : ∀ u, σ η (Φ u) = Φ u := hΦfixσ η hηH
    intro e
    have hcfix : (g'⁻¹ * g * g') (e : K) = (e : K) := by
      let cK : K →ₐ[ℂ] K := ((rSH (g'⁻¹ * g * g') : K ≃ₐ[ℂ] K) : K →ₐ[ℂ] K)
      let T : IntermediateField ℂ K := (AlgHom.equalizer cK (AlgHom.id ℂ K)).toIntermediateField (fun x hx => by
        rw [AlgHom.mem_equalizer] at hx ⊢
        rw [map_inv₀, map_inv₀, hx])
      have hET : E ≤ T := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨u, rfl⟩
        change (rSH (g'⁻¹ * g * g')) (Φ u) = Φ u
        rw [← hση]; exact hηfix u
      exact hET e.2
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg'] at hcfix
    have h2 := congrArg g' hcfix
    have h3 : g' (g'⁻¹ (g (ψ e))) = g (ψ e) := g'.apply_symm_apply _
    rw [h3, hg'] at h2
    exact h2

  have h0E : P'.ord (ΦE y⁻¹) = P.ord y⁻¹ := by rw [← hP'ord (y⁻¹)]; rfl
  have hPpos : 0 < P.ord y⁻¹ := by rw [Place.ord_inv]; linarith
  have hP'pos : 0 < P'.ord (ΦE y⁻¹ - algebraMap ℂ ↥E 0) := by rw [map_zero, sub_zero, h0E]; exact hPpos
  obtain ⟨ψ, hψ, hψP⟩ := h3 P' hP'pos

  have hinclx : inclE (ΦE₀ y₀⁻¹) = ΦE y⁻¹ := by rw [hsqE, map_inv₀ incl y₀, hincly₀]
  let ψ₀ : ↥E₀ →ₐ[ℂ] K := ψ.comp inclE
  have hψ₀ : ψ₀ (ΦE₀ y₀⁻¹) = t' := by rw [AlgHom.comp_apply, hinclx, hψ]
  have hvalE₀' : E₀.val (ΦE₀ y₀⁻¹) = t' := by rw [IntermediateField.coe_val]; exact hvalE₀
  obtain ⟨-, -, -, h4₀, h5₀⟩ := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ (ΦE₀ y₀⁻¹) t' (0 : ℂ) E₀.val hvalE₀'
    hfd' hgal' (hint_of ↥E₀ (ΦE₀ y₀⁻¹)) W hW'
  have hint := hint_of ↥E (ΦE y⁻¹)
  have hint₀ := hint_of ↥E₀ (ΦE₀ y₀⁻¹)
  have hQ'ψ₀ : Q' = W.restrictAlong ψ₀ (hint₀ ψ₀ hψ₀) := by
    change P'.restrictAlong inclE hinclE = _
    rw [← hψP]
    exact restrictAlong_restrictAlong inclE ψ hinclE (hint ψ hψ) (hint₀ ψ₀ hψ₀) W

  have hcompx : ∀ ψ' : ↥E →ₐ[ℂ] K, ψ' (ΦE y⁻¹) = t' → (ψ'.comp inclE) (ΦE₀ y₀⁻¹) = t' := fun ψ' h => by
    rw [AlgHom.comp_apply, hinclx, h]
  let R : {ψ' : {ψ' : ↥E →ₐ[ℂ] K // ψ' (ΦE y⁻¹) = t'} //
        W.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W.restrictAlong ψ (hint ψ hψ)} →
      {ψ' : {ψ' : ↥E₀ →ₐ[ℂ] K // ψ' (ΦE₀ y₀⁻¹) = t'} //
        W.restrictAlong ψ'.1 (hint₀ ψ'.1 ψ'.2) = W.restrictAlong ψ₀ (hint₀ ψ₀ hψ₀)} := fun a =>
    ⟨⟨a.1.1.comp inclE, hcompx a.1.1 a.1.2⟩, by
      change W.restrictAlong (a.1.1.comp inclE) _ = W.restrictAlong (ψ.comp inclE) _
      rw [← restrictAlong_restrictAlong inclE a.1.1 hinclE (hint a.1.1 a.1.2), a.2,
        restrictAlong_restrictAlong inclE ψ hinclE (hint ψ hψ)]⟩
  have hRsurj : Function.Surjective R := by
    rintro ⟨⟨ψ₀', hψ₀'⟩, heq⟩
    obtain ⟨g, hg, hgeq⟩ := (h4₀ ψ₀ ψ₀' hψ₀ hψ₀').mp heq.symm
    have hga : (((g : K →ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K).restrictScalars ℂ).comp ψ) (ΦE y⁻¹) = t' := by
      rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hψ]
      exact g.commutes (⟨t', IntermediateField.mem_adjoin_simple_self ℂ t'⟩ : ↥(IntermediateField.adjoin ℂ ({t'} : Set K)))
    refine ⟨⟨⟨((g : K →ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K).restrictScalars ℂ).comp ψ, hga⟩, ((h4 ψ _ hψ hga).mpr ⟨g, hg, rfl⟩).symm⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change (((g : K →ₐ[↥(IntermediateField.adjoin ℂ ({t'} : Set K))] K).restrictScalars ℂ).comp ψ).comp inclE = ψ₀'
    rw [hgeq]; rfl
  have hRinj : Function.Injective R := by
    rintro ⟨⟨ψ₁, hψ₁⟩, heq₁⟩ ⟨⟨ψ₂, hψ₂⟩, heq₂⟩ hR
    have hR' : ψ₁.comp inclE = ψ₂.comp inclE := by
      have := congrArg (fun b => b.1.1) hR
      exact this
    obtain ⟨g₁, hg₁, rfl⟩ := (h4 ψ ψ₁ hψ hψ₁).mp heq₁.symm
    obtain ⟨g₂, hg₂, rfl⟩ := (h4 ψ ψ₂ hψ hψ₂).mp heq₂.symm
    have hg : ∀ e : ↥E, (g₂⁻¹ * g₁) (ψ e) = ψ e := by
      refine hclaim ψ hψ (g₂⁻¹ * g₁) ?_ ?_
      · rw [show (g₂⁻¹ * g₁).restrictScalars ℂ = (g₂.restrictScalars ℂ)⁻¹ * g₁.restrictScalars ℂ from
          AlgEquiv.ext fun _ => rfl, map_mul, map_inv, mul_smul, hg₁, inv_smul_eq_iff, hg₂]
      · intro e₀
        have h12 : g₁ (ψ (inclE e₀)) = g₂ (ψ (inclE e₀)) := by
          have := congrArg (fun f : ↥E₀ →ₐ[ℂ] K => f e₀) hR'
          exact this
        rw [AlgEquiv.mul_apply, h12]
        exact g₂.symm_apply_apply _
    apply Subtype.ext; apply Subtype.ext
    apply AlgHom.ext
    intro e
    change g₁ (ψ e) = g₂ (ψ e)
    have h1 := hg e
    rw [AlgEquiv.mul_apply] at h1
    have h2 := congrArg g₂ h1
    have h3 : g₂ (g₂⁻¹ (g₁ (ψ e))) = g₁ (ψ e) := g₂.apply_symm_apply _
    rw [h3] at h2
    exact h2
  have hcount : P'.ord (ΦE y⁻¹ - algebraMap ℂ ↥E 0) = Q'.ord (ΦE₀ y₀⁻¹ - algebraMap ℂ ↥E₀ 0) := by
    rw [← hψP, h5 ψ hψ, hQ'ψ₀, h5₀ ψ₀ hψ₀]
    exact_mod_cast Nat.card_eq_of_bijective R ⟨hRinj, hRsurj⟩

  rw [map_zero, sub_zero, map_zero, sub_zero, h0E, hQ'] at hcount
  have h0E₀ : Q₀.ord (ΦE₀ y₀⁻¹) = P₀.ord y₀⁻¹ := by rw [← hQ₀ord (y₀⁻¹)]; rfl
  rw [h0E₀] at hcount
  have hinv : incl y₀⁻¹ = y⁻¹ := by rw [map_inv₀, hincly₀]
  exact ramificationIndexAlong_eq_one_of_ord_eq incl hincl P y₀⁻¹ (by rw [hinv]; exact hPpos) (by rw [hinv]; exact hcount)

open ModularCurve.CuspUnramAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

    (hH : ∀ (γ : SL(2, ℤ)) (k : ℤ), γ * ModularGroup.T ^ k * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N →
      γ * ModularGroup.T ^ k * γ⁻¹ ∈ CohCarrier.GammaH N H)
    (K : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK : K = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)))
    (K₀ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)))
    (hle : K₀ ≤ K)
    (j : ↥K) (hj : ((j : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥K) (hP : P.ord j < 0) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) P = 1 := by
  subst hK
  subst hK₀
  have hy : (j : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
    rw [hj, ModularCurve.coeffEmb, ← ModularCurve.jqModC_rat]
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  exact ModularCurve.CuspUnramAux.main N H hH hle j hy P hP

end
end S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_neg_laurentBaseChange_gammaH_algebraicClosure
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_neg_laurentBaseChange_gammaH_algebraicClosure (solution)
