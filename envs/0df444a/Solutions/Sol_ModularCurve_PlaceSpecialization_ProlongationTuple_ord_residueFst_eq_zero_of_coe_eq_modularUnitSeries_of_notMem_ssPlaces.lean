-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/04e4be85-2836-5cb1-8e83-81f7fc08603e

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

namespace J3UresN

section Series

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

private theorem ps_map_map_j3 (g : S →+* T) (f : R →+* S) (φ : PowerSeries R) :
    PowerSeries.map g (PowerSeries.map f φ) = PowerSeries.map (g.comp f) φ := by
  rw [PowerSeries.map_comp, RingHom.comp_apply]

private theorem coeffMap_injective_j3 {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simpa only [coeffMap_coeff] using this

end Series

section Frobenius

variable {k : Type*} [CommRing k] {q : ℕ} [Fact q.Prime] [CharP k q]

private theorem coeff_pow_char_j3 (g : PowerSeries k) (M : ℕ) :
    PowerSeries.coeff M (g ^ q) =
      if q ∣ M then frobenius k q (PowerSeries.coeff (M / q) g) else 0 := by
  have hq : 0 < q := (Fact.out : q.Prime).pos

  have ht := PowerSeries.trunc_trunc_pow g (M + 1) q
  have hc := congrArg (fun p : Polynomial k => p.coeff M) ht
  simp only [PowerSeries.coeff_trunc, lt_add_one, if_true] at hc
  rw [← hc, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_frobenius_expand q,
    Polynomial.coeff_map, Polynomial.coeff_expand hq]
  split_ifs with hd
  · rw [PowerSeries.coeff_trunc, if_pos]
    exact Nat.lt_succ_of_le (Nat.div_le_self M q)
  · exact map_zero _

private theorem ofPowerSeries_pow_char_j3 (g : PowerSeries k) :
    (ofPowerSeries ℤ k g) ^ q = qExpand k q (ofPowerSeries ℤ k (g.map (frobenius k q))) := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  rw [← map_pow]
  ext n
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_natCast, coeff_pow_char_j3 g M]
    by_cases hd : q ∣ M
    · obtain ⟨m, rfl⟩ := hd
      rw [if_pos (dvd_mul_right q m), Nat.mul_div_cancel_left m hq,
        Nat.cast_mul q m, qExpand_coeff_mul,
        PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_natCast, PowerSeries.coeff_map]
    · rw [if_neg hd, qExpand_coeff_of_not_dvd (N := q)]
      exact fun h => hd (Int.natCast_dvd_natCast.mp h)
  ·
    rw [PowerSeries.coeff_coe, if_pos hn]
    by_cases hd : (q : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m < 0 := by
        by_contra hm
        push Not at hm
        exact absurd (mul_nonneg (by exact_mod_cast hq.le) hm) (not_le.mpr hn)
      rw [qExpand_coeff_mul, PowerSeries.coeff_coe, if_pos hm]
    · rw [qExpand_coeff_of_not_dvd (N := q) _ hd]

private theorem ofPowerSeries_intCast_pow_char_j3 (h : PowerSeries ℤ) :
    (ofPowerSeries ℤ k (h.map (Int.castRingHom k))) ^ q =
      qExpand k q (ofPowerSeries ℤ k (h.map (Int.castRingHom k))) := by
  rw [ofPowerSeries_pow_char_j3, ps_map_map_j3,
    RingHom.ext_int ((frobenius k q).comp (Int.castRingHom k)) (Int.castRingHom k)]

end Frobenius

section Delta

private noncomputable def dser (R : Type*) [CommRing R] : LaurentSeries R :=
  single (1 : ℤ) 1 * ofPowerSeries ℤ R (dedekindEtaUnit.map (Int.castRingHom R))

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_dser (f : R →+* S) : coeffMap f (dser R) = dser S := by
  unfold dser
  rw [map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries, ps_map_map_j3,
    RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]

private theorem deltaSeries_eq_dser : deltaSeries = dser ℚ := rfl

private theorem deltaSeriesN_eq (p : ℕ) [NeZero p] : deltaSeriesN p = qExpand ℚ p (dser ℚ) := rfl

private theorem dser_eq_ofPowerSeries (k : Type*) [CommRing k] :
    dser k = ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k)
      (PowerSeries.X * dedekindEtaUnit)) := by
  unfold dser
  rw [map_mul (PowerSeries.map (Int.castRingHom k)), PowerSeries.map_X, map_mul, ofPowerSeries_X]

private theorem dser_pow_char (k : Type*) [CommRing k] (q : ℕ) [Fact q.Prime] [CharP k q] :
    dser k ^ q = qExpand k q (dser k) := by
  unfold dser
  rw [mul_pow, single_pow, ofPowerSeries_intCast_pow_char_j3, map_mul (qExpand k q),
    qExpand_single]
  simp only [nsmul_eq_mul, mul_one, one_pow]

private theorem dser_coeff_one (k : Type*) [CommRing k] : (dser k).coeff 1 = 1 := by
  unfold dser
  have h := coeff_single_mul_add (r := (1 : k))
    (x := ofPowerSeries ℤ k (dedekindEtaUnit.map (Int.castRingHom k))) (a := (0 : ℤ)) (b := 1)
  rw [zero_add] at h
  rw [h, one_mul, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_dedekindEtaUnit, map_one]

private theorem dser_ne_zero (k : Type*) [CommRing k] [Nontrivial k] : dser k ≠ 0 := by
  intro h
  have h1 := dser_coeff_one k
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

end Delta

section Places

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f n
  rwa [zpow_natCast] at this

private theorem ord_sub_algebraMap_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) {c₀ a : K}
    (hc : 0 < v.ord (f - algebraMap K F c₀)) (hne : a ≠ c₀) :
    v.ord (f - algebraMap K F a) = 0 := by
  have hmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' a)
  have hmem₀ : f - algebraMap K F c₀ ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' c₀)
  have hnn := v.ord_nonneg_of_mem hmem
  rcases hnn.lt_or_eq with hpos | h0
  · exfalso
    have h1 := v.mk_mem_maximalIdeal_of_ord_pos hmem hpos
    have h2 := v.mk_mem_maximalIdeal_of_ord_pos hmem₀ hc
    have h3 := Ideal.sub_mem _ h2 h1
    have hac : a - c₀ ≠ 0 := sub_ne_zero.mpr hne
    have heq : (⟨f - algebraMap K F c₀, hmem₀⟩ : v.toValuationSubring) - ⟨f - algebraMap K F a, hmem⟩
        = ⟨algebraMap K F (a - c₀), v.algebraMap_mem' (a - c₀)⟩ := by
      apply Subtype.ext
      show (f - algebraMap K F c₀) - (f - algebraMap K F a) = algebraMap K F (a - c₀)
      rw [map_sub]
      ring
    rw [heq] at h3
    have hunit : IsUnit (⟨algebraMap K F (a - c₀), v.algebraMap_mem' (a - c₀)⟩ :
        v.toValuationSubring) := by
      refine ⟨⟨⟨algebraMap K F (a - c₀), v.algebraMap_mem' _⟩,
        ⟨algebraMap K F (a - c₀)⁻¹, v.algebraMap_mem' _⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        show algebraMap K F (a - c₀) * algebraMap K F (a - c₀)⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hac, map_one]
      · apply Subtype.ext
        show algebraMap K F (a - c₀)⁻¹ * algebraMap K F (a - c₀) = 1
        rw [← map_mul, inv_mul_cancel₀ hac, map_one]
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) hunit
  · exact h0.symm

private theorem ord_prod_pow_eq_zero {ι : Type*} (s : Finset ι) (g : ι → F) (m : ι → ℕ)
    (hg : ∀ i ∈ s, g i ≠ 0) (h0 : ∀ i ∈ s, v.ord (g i) = 0) :
    v.ord (∏ i ∈ s, g i ^ m i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Place.ord_one]
  | insert a s ha ih =>
    have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : ∏ i ∈ s, g i ^ m i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hgs i hi)
    rw [Finset.prod_insert ha, v.ord_mul (pow_ne_zero _ hga) hprod, ord_pow' v, h0 a
      (Finset.mem_insert_self a s), ih hgs fun i hi => h0 i (Finset.mem_insert_of_mem hi)]
    simp

private theorem coe_prod_jGeomGen_sub_pow (N : ℕ) [NeZero N] (s : Finset K) (m : K → ℕ) :
    ((∏ a ∈ s, (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) ^ m a :
        modularFunctionFieldC K N) : LaurentSeries K)
      = ∏ a ∈ s, (jqModC K - HahnSeries.C a) ^ m a := by
  refine (IntermediateField.algebraMap_apply _ _).symm.trans ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_pow, map_sub, IntermediateField.algebraMap_apply, coe_jGeomGen,
    ← IsScalarTower.algebraMap_apply]
  congr 2

  rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

end Places

section Residue

open ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem residue_mul_dser_pow
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) (h₁ : u ∈ R.R₁.integers) :
    ((R.residue₁ ⟨u, h₁⟩ : modularFunctionFieldC k N) : LaurentSeries k) * dser k ^ q
      = dser k := by
  obtain ⟨h₁', -, y, hy1, hy2, -⟩ :=
    PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
      P R u hu

  have hseries : ((R.residue₁ ⟨u, h₁⟩ : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffMap red y := by
    show ((R.ι (R.R₁.residue ⟨u, h₁⟩) : modularFunctionFieldC k N) : LaurentSeries k) = _
    rw [R.ι_coe, hy2, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => (RingHom.comp_apply _ _ a).trans
      (R.redBar_residue a)) y

  have hA : y * qExpand A q (dser A) = dser A := by
    apply coeffMap_injective_j3 (f := A.subtype) Subtype.coe_injective
    rw [map_mul, coeffMap_qExpand, coeffMap_dser, hy1, hu]
    have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) (modularUnitSeries_mul_deltaSeriesN q)
    rw [map_mul, deltaSeriesN_eq, deltaSeries_eq_dser] at h
    unfold coeffEmb at h
    rw [coeffMap_qExpand, coeffMap_dser] at h
    exact h

  have hk := congrArg (coeffMap red) hA
  rw [map_mul, coeffMap_qExpand, coeffMap_dser] at hk
  rw [hseries, dser_pow_char k q]
  exact hk

end Residue

end J3UresN

open J3UresN ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k N))
    (haff : IsAffineGeomPlace k N v) (hord : v ∉ ssPlaces q N k) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = 0 := by
  classical
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have h1q : 1 ≤ q := hq

  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hrat : v.IsRational := by
    haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
    haveI : Algebra.IsIntegral k v.ResidueField := Algebra.IsIntegral.of_finite k v.ResidueField
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := v.ResidueField)).2
  have hcen := exists_isCentreOf_of_isRational hrat haff
  have hc₀ : v.evalAt (jGeomGen k N) ∉ ssJSet q k := fun h => hord ⟨hrat, haff, h⟩

  have hja : ∀ a ∈ ssJSet q k,
      v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) = 0 := by
    intro a ha
    refine J3UresN.ord_sub_algebraMap_eq_zero v haff.1 hcen.1 ?_
    rintro rfl
    exact hc₀ ha

  have hser := J3UresN.residue_mul_dser_pow P R u hu h₁
  have hD := J3UresN.dser_ne_zero k
  set X := ((R.residue₁ ⟨u, h₁⟩ : modularFunctionFieldC k N) : LaurentSeries k) with hXdef
  rcases le_or_gt 5 q with hq5 | hq5'
  ·
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset k, ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k :=
      ⟨(ModularCurve.ssJSet_finite q k).toFinset, fun a => (ModularCurve.ssJSet_finite q k).mem_toFinset⟩
    have hid := ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one q hq5 k S₀ hS₀
    rw [← J3UresN.dser_eq_ofPowerSeries] at hid
    have hX1 : X * dser k ^ (q - 1) = 1 := by
      have h : X * dser k ^ (q - 1) * dser k = 1 * dser k := by
        rw [one_mul, mul_assoc, ← pow_succ, Nat.sub_add_cancel h1q]
        exact hser
      exact mul_right_cancel₀ hD h
    have hX : X = ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) := by
      calc X = X * (dser k ^ (q - 1) *
            ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a)) := by rw [hid, mul_one]
        _ = (X * dser k ^ (q - 1)) *
            ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) := by rw [mul_assoc]
        _ = ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) := by rw [hX1, one_mul]
    have hxC : R.residue₁ ⟨u, h₁⟩ =
        ∏ a ∈ S₀, (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) ^ (12 / jWidth a) := by
      apply Subtype.ext
      rw [← hXdef, hX, J3UresN.coe_prod_jGeomGen_sub_pow]
    rw [hxC]
    refine J3UresN.ord_prod_pow_eq_zero v S₀ _ _ (fun a _ => jGeomGen_sub_algebraMap_ne_zero k N a)
      fun a ha => hja a ((hS₀ a).mp ha)
  ·
    have hq5 : q < 5 := hq5'
    have hp : q.Prime := Fact.out
    have hq23 : q = 2 ∨ q = 3 := by
      have h2 := hp.two_le
      have h4 : q ≠ 4 := by
        intro h
        rw [h] at hp
        exact absurd hp (by decide)
      omega
    have hdvd : q ∣ 240 := by
      rcases hq23 with h | h <;> rw [h] <;> decide
    have h240 : ((240 : ℤ) : k) = 0 := by
      have : ((240 : ℕ) : k) = 0 := (CharP.cast_eq_zero_iff k q 240).mpr hdvd
      exact_mod_cast this
    have hE4 : eisenstein4.map (Int.castRingHom k) = 1 := by
      ext n
      rw [PowerSeries.coeff_map, show eisenstein4 = PowerSeries.mk fun n =>
        if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3 from rfl,
        PowerSeries.coeff_mk, PowerSeries.coeff_one]
      split_ifs with hn
      · exact map_one _
      · rw [map_mul, eq_intCast, h240, zero_mul]
    have hjD : jqModC k * dser k = 1 := by
      unfold jqModC J3UresN.dser
      rw [show jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv from rfl, map_mul, map_pow, hE4,
        one_pow, one_mul, mul_mul_mul_comm, single_mul_single, ← map_mul, ← map_mul,
        mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, map_one, map_one]
      simp
    have hX : X = jqModC k ^ (q - 1) := by
      have hDj : dser k * jqModC k = 1 := by rw [mul_comm]; exact hjD
      calc X = X * (dser k * jqModC k) ^ q := by rw [hDj, one_pow, mul_one]
        _ = (X * dser k ^ q) * jqModC k ^ q := by rw [mul_pow, mul_assoc]
        _ = dser k * jqModC k ^ q := by rw [hser]
        _ = dser k * jqModC k * jqModC k ^ (q - 1) := by
            rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel h1q]
        _ = jqModC k ^ (q - 1) := by rw [hDj, one_mul]
    have hxC : R.residue₁ ⟨u, h₁⟩ = jGeomGen k N ^ (q - 1) := by
      apply Subtype.ext
      rw [← hXdef, hX, SubmonoidClass.coe_pow, coe_jGeomGen]
    have h0 : (0 : k) ∈ ssJSet q k := ModularCurve.zero_mem_ssJSet_of_lt_five hq5
    have hj0 := hja 0 h0
    rw [map_zero, sub_zero] at hj0
    rw [hxC, J3UresN.ord_pow' v, hj0, mul_zero]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces (solution)
