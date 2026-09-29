-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_reduceFst_residue_jFun_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/77a8a22e-c245-57f7-824a-abb6d832e0dd

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one.AlgebraicCurve IsLocalRing ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring residueInv_algebraMap evalAt evalAt_of_mem"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_e15 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_e15"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_e15 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_e15"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_e15 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_e15"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_e15 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_e15"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_e15 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_e15"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_e15 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm

  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_e15 hsub h0]
    have hnn := v.ord_nonneg_of_mem_e15 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_export "AlgebraicCurve.Place" "hasValue_iff_eq_or_ord_sub_pos_e15"

theorem div_mem_of_ord_le_e15 {r t : F} (ht : t ≠ 0) (h : v.ord t ≤ v.ord r) :
    r / t ∈ v.toValuationSubring := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · apply v.mem_of_ord_nonneg_e15 (div_ne_zero hr ht)
    rw [div_eq_mul_inv, v.ord_mul hr (inv_ne_zero ht), v.ord_inv]
    omega

theorem tExpansion_coeff_unique_e15 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
    (hc : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c i) * t ^ i) / t ^ m ∈
      v.toValuationSubring)
    (hc' : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c' i) * t ^ i) / t ^ m ∈
      v.toValuationSubring) :
    c = c' := by
  classical
  have ht0 : t ≠ 0 := v.ne_zero_of_ord_pos_e15 ht
  by_contra hne
  have hex : ∃ m, c m ≠ c' m := by
    by_contra hall
    exact hne (funext fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm, hmin⟩ : ∃ m, c m ≠ c' m ∧ ∀ i < m, c i = c' i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  set e : K := c m - c' m with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hm

  have hdiff : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) / t ^ (m + 1) -
      (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) / t ^ (m + 1) =
      algebraMap K F e / t := by
    rw [← sub_div]
    have hnum : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) -
        (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) =
        algebraMap K F e * t ^ m := by
      have hs : ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i -
          ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i =
          algebraMap K F e * t ^ m := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
          ← sub_mul, ← map_sub]
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hmin i hi, sub_self]
      rw [← hs]; ring
    rw [hnum, pow_succ, mul_comm (t ^ m) t, mul_div_mul_right _ _ (pow_ne_zero m ht0)]
  have hmem : algebraMap K F e / t ∈ v.toValuationSubring := by
    rw [← hdiff]; exact sub_mem (hc' (m + 1)) (hc (m + 1))
  have hord : v.ord (algebraMap K F e / t) < 0 := by
    have hae : algebraMap K F e ≠ 0 := (_root_.map_ne_zero _).mpr he0
    rw [div_eq_mul_inv, v.ord_mul hae (inv_ne_zero ht0), v.ord_inv, v.ord_algebraMap_e15]
    omega
  exact absurd (v.ord_nonneg_of_mem_e15 hmem) (not_le.mpr hord)

end Place
end AlgebraicCurve

open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : P.ProlongationTuple)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (j₀ : A) (hj₀ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ)))
    (a : k) (ha : (P.reduceFst Q).evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (h : (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ)) ∈ R.R₁.integers) :
    (P.reduceFst Q).ord (R.residue₁ ⟨_, h⟩) = 1 := by
  classical
  obtain ⟨h₁, -, -, -, E₁, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN j₀

  have hE : R.residue₁ ⟨_, h⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀) := E₁

  have hpos : 0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀)) :=
    P.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos Q j₀ hj₀
  have hne : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀) ≠ 0 :=
    (P.reduceFst Q).ne_zero_of_ord_pos_e15 hpos
  have hmem : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀) ∈
      (P.reduceFst Q).toValuationSubring := (P.reduceFst Q).mem_of_ord_nonneg_e15 hne hpos.le
  have hj : jGeomGen k N ∈ (P.reduceFst Q).toValuationSubring := by
    simpa using add_mem hmem ((P.reduceFst Q).algebraMap_mem' (red j₀))
  have hval : (P.reduceFst Q).HasValue (jGeomGen k N) (red j₀) :=
    ((P.reduceFst Q).hasValue_iff_eq_or_ord_sub_pos_e15 hj (red j₀)).mpr (Or.inr hpos)
  have hev : (P.reduceFst Q).evalAt (jGeomGen k N) = red j₀ := by
    rw [(P.reduceFst Q).evalAt_of_mem hj, hval.residue_eq, (P.reduceFst Q).residueInv_algebraMap]

  have hja : red j₀ = a := hev.symm.trans ha

  rw [hE, hja]
  exact ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q k N hqN (P.reduceFst Q) a ha h0 h1728

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_reduceFst_residue_jFun_sub_eq_one (solution)
