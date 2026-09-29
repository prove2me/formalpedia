-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_map_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b15fcd44-0cef-5557-b0a3-a7c4d8c80f1e

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_map_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve Polynomial

namespace GaussPencil
namespace SST

theorem mem_ssJSet_of_algebraMap_mem {q : ℕ} {k K : Type*} [Field k] [Field K] [Algebra k K] [DecidableEq k] [DecidableEq K]
    (b : k) (h : algebraMap k K b ∈ ssJSet q K) : b ∈ ssJSet q k := by
  intro W _ hj P hP
  let P₀ : (W.baseChange k).toAffine.Point := P
  let φ := WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId k K)
  have hjK : (W.map (algebraMap k K)).j = algebraMap k K b := by
    rw [WeierstrassCurve.map_j, hj]
  let Q : (W.map (algebraMap k K)).toAffine.Point := φ P₀
  have hQ : q • Q = 0 := by
    show q • φ P₀ = 0
    rw [← map_nsmul]
    have : q • P₀ = 0 := hP
    rw [this, map_zero]
  have h1 : φ P₀ = 0 := h (W.map (algebraMap k K)) hjK Q hQ
  have h2 : P₀ = 0 := WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId k K) (h1.trans (map_zero φ).symm)
  exact h2

theorem mem_range_of_pow_eq {q : ℕ} [Fact q.Prime] {k₀ K : Type*} [Field k₀] [Field K] [CharP k₀ q] [IsAlgClosed k₀]
    (ψ : k₀ →+* K) (x : K) (hx : ∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x) : x ∈ ψ.range := by
  classical
  obtain ⟨n, hn, hxn⟩ := hx
  have hq : 1 < q ^ n := Nat.one_lt_pow (by omega) (Fact.out : q.Prime).one_lt
  set f : k₀[X] := X ^ (q ^ n) - X with hf
  have hfmap : f.map ψ = X ^ (q ^ n) - X := by rw [hf, Polynomial.map_sub, Polynomial.map_pow, map_X]
  have hne : f.map ψ ≠ 0 := by rw [hfmap]; exact FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hroot : x ∈ (f.map ψ).roots := by
    rw [mem_roots hne, IsRoot, hfmap, eval_sub, eval_pow, eval_X, hxn, sub_self]
  rw [← roots_map_of_injective_of_card_eq_natDegree ψ.injective (splits_iff_card_roots.mp (IsAlgClosed.splits f))] at hroot
  obtain ⟨x₀, -, rfl⟩ := Multiset.mem_map.mp hroot
  exact ⟨x₀, rfl⟩

end GaussPencil.SST

theorem solution
    {q : ℕ} [Fact q.Prime] {k₀ k : Type*} [Field k₀] [Field k] [CharP k₀ q] [CharP k q]
    [IsAlgClosed k₀] [DecidableEq k₀] [DecidableEq k]
    (θ : k₀ →+* k) (a : k₀) (ha : a ∈ ssJSet q k₀) : θ a ∈ ssJSet q k := by
  classical
  by_cases hq2 : q = 2
  ·
    subst hq2
    have ha4 : a ^ (2 ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet 2 ha
    have ha0 : a = 0 := ModularCurve.eq_zero_of_mem_ssJSet_two a ha ha4
    rw [ha0, map_zero]
    exact ModularCurve.zero_mem_ssJSet_of_lt_five (by norm_num)
  ·
    let K := AlgebraicClosure k
    letI : Algebra k₀ K := ((algebraMap k K).comp θ).toAlgebra
    haveI : CharP K q := (RingHom.charP_iff_charP (algebraMap k K) q).mp inferInstance
    have hk : ∀ x : K, (∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x) → x ∈ (algebraMap k₀ K).range :=
      fun x hx => GaussPencil.SST.mem_range_of_pow_eq (algebraMap k₀ K) x hx
    have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha
    have hK : algebraMap k₀ K a ∈ ssJSet q K := ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_two hq2 hk a ha ha2
    have hK' : algebraMap k K (θ a) ∈ ssJSet q K := hK
    exact GaussPencil.SST.mem_ssJSet_of_algebraMap_mem (θ a) hK'

end S_ModularCurve_mem_ssJSet_map_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_map_of_isAlgClosed (solution)
