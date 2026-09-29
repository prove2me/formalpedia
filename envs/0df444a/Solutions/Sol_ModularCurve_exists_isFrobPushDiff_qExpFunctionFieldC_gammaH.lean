-- Prove2me | solution 1 for ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/bb47aa67-7e22-5af3-a20f-26e95bf9ffca

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve AlgebraicCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke HahnSeries KaehlerDifferential
open scoped MatrixGroups

namespace FPX

theorem coeffMap_frobenius_qEuler (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h : LaurentSeries K) :
    ModularCurve.coeffMap (frobenius K p) (ModularCurve.qEuler K h) =
      ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) h) := by
  ext n
  simp only [coeffMap_coeff, qEuler_coeff, map_mul, map_intCast]

theorem smul_eq_coe_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (f : F)
    (y : LaurentSeries K) : f • y = (f : LaurentSeries K) * y := rfl

theorem exists_diffQExp_eq_coeffMap_frobenius (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (Γ : Subgroup SL(2, ℤ)) (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) :
    ∃ ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K],
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) ω' =
        ModularCurve.coeffMap (frobenius K p)
          (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) ω) := by
  have hmem : ω ∈ Submodule.span (qExpFunctionFieldC K Γ)
      (Set.range (D K (qExpFunctionFieldC K Γ))) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine ⟨D K (qExpFunctionFieldC K Γ) (qExpArithFrobC p K Γ • g), ?_⟩
    rw [diffQExp_D, diffQExp_D, coe_qExpArithFrobC_smul, coeffMap_frobenius_qEuler]
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, map_add, map_add, hx', hy']⟩
  | smul f x _ hx =>
    obtain ⟨x', hx'⟩ := hx
    refine ⟨(qExpArithFrobC p K Γ • f) • x', ?_⟩
    rw [map_smul, map_smul, smul_eq_coe_mul, smul_eq_coe_mul, hx', coe_qExpArithFrobC_smul, map_mul]

section Generic

variable {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))

theorem diffQExp_smul_algebraMap (a : K) (ω : Ω[F⁄K]) :
    diffQExp F (a • ω) = single 0 a * diffQExp F ω := by
  have h1 : a • ω = (algebraMap K F a) • ω := (algebraMap_smul F a ω).symm
  rw [h1, map_smul]
  show ((algebraMap K F a : F) : LaurentSeries K) * diffQExp F ω = _
  congr 1
  exact algebraMap_laurentSeries_eq_single K a

variable (p : ℕ) [NeZero p]

theorem qDecimate_single_zero_mul (a : K) (x : LaurentSeries K) :
    qDecimate K p (single 0 a * x) = single 0 a * qDecimate K p x := by
  ext k
  simp only [coeff_qDecimate, coeff_single_zero_mul]

end Generic

theorem coeff_qEuler_jqModC_neg_one (K : Type*) [Field K] :
    (qEuler K (jqModC K)).coeff (-1 : ℤ) = -1 := by
  rw [qEuler_coeff, coeff_jqModC_neg_one, mul_one, Int.cast_neg, Int.cast_one]

theorem qEuler_jqModC_ne_zero (K : Type*) [Field K] : qEuler K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1 : ℤ)) h
  simp only [coeff_qEuler_jqModC_neg_one, HahnSeries.coeff_zero, neg_eq_zero, one_ne_zero] at h1

section Main

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
  (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)

local notation "Γ" => CohCarrier.GammaH N H'
local notation "F" => qExpFunctionFieldC K (CohCarrier.GammaH N H')

theorem exists_diffQExp_eq_qDecimate (ω : Ω[F⁄K]) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ ω' : Ω[F⁄K], diffQExp F ω' = qDecimate K p (diffQExp F ω) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  haveI : PerfectField K := inferInstance
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : (Γ).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H')
  have hT : ModularGroup.T ∈ Γ := translation_mem_GammaH N H'
  obtain ⟨t, ht, htr, hfd⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI := hfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  have hj : jqModC K ∈ F := ht ▸ t.2
  have htt : (⟨jqModC K, hj⟩ : F) = t := Subtype.ext ht.symm
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : F)} : Set F)) F := by
    rw [htt]; infer_instance
  have hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
    have h := isSeparable_adjoin_jqModC_of_isAlgebraic K F hj
    rw [htt] at h
    exact h
  haveI : IsCurveOver K F := isCurveOver_of_transcendental_of_isSeparable K F t htr hfd hsepK

  have hdt : KaehlerDifferential.D K F t ≠ 0 := fun h0 =>
    qEuler_jqModC_ne_zero K (by rw [← ht, ← diffQExp_D F t, h0, map_zero])
  have hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤ :=
    kw_cart_hspan_of_isCurveOver (K := K) hdt
  have hsep : ∀ y : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield y :=
    kw_pke_hsep_of_isSeparable_adjoin (K := K) (ℓ := p) t hsepK
  have hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p :=
    kw_cart_minpoly_natDegree_eq (K := K) (ℓ := p) hdt

  set C₀ := kw_cart_C (K := K) (ℓ := p) t hdt hspan hsep hdeg with hC₀
  have hlaw : ∀ n : ℤ, (diffQExp F (C₀ ω)).coeff n ^ p = (diffQExp F ω).coeff (n * p) := by
    intro n
    have h := coeff_qExpansionDiffAlong_kw_cart_C_pow p F t hdt hspan hsep hdeg ω n
    rwa [qExpansionDiffAlong_val_eq_diffQExp, qExpansionDiffAlong_val_eq_diffQExp] at h

  obtain ⟨ω', hω'⟩ := exists_diffQExp_eq_coeffMap_frobenius K p Γ (C₀ ω)
  refine ⟨ω', ?_⟩
  rw [hω']
  ext n
  rw [coeffMap_coeff, frobenius_def, hlaw n, coeff_qDecimate, mul_comm]

def frobPush (ω : Ω[F⁄K]) : Ω[F⁄K] := (exists_diffQExp_eq_qDecimate p K N H' ω).choose

theorem diffQExp_frobPush (ω : Ω[F⁄K]) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    diffQExp F (frobPush p K N H' ω) = qDecimate K p (diffQExp F ω) :=
  (exists_diffQExp_eq_qDecimate p K N H' ω).choose_spec

theorem injective_diffQExp : Function.Injective (diffQExp F) := by
  haveI : (Γ).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H')
  exact diffQExp_qExpFunctionFieldC_injective K Γ (translation_mem_GammaH N H')

def frobPushLin :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] where
  toFun := frobPush p K N H'
  map_add' ω₁ ω₂ := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    apply injective_diffQExp K N H'
    rw [map_add, diffQExp_frobPush, diffQExp_frobPush, diffQExp_frobPush, map_add, map_add]
  map_smul' a ω := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    apply injective_diffQExp K N H'
    rw [RingHom.id_apply, diffQExp_smul_algebraMap, diffQExp_frobPush, diffQExp_frobPush,
      diffQExp_smul_algebraMap, qDecimate_single_zero_mul]

theorem isFrobPushDiff_frobPushLin :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsFrobPushDiff K (CohCarrier.GammaH N H') p (frobPushLin p K N H') := by
  intro ω
  exact diffQExp_frobPush p K N H' ω

end Main

end FPX

end

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K],
      ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH N H') p C :=
  ⟨FPX.frobPushLin p K N H', FPX.isFrobPushDiff_frobPushLin p K N H'⟩

end S_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
end P2MW
export P2MW.S_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH (solution)
