-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_ringHom_tExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7f395539-e85f-534e-a374-31281b720531

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_residue_jFun_sub_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_algebraMap_mem_smoothLocalRingFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_tExpansion_of_mem_smoothLocalRingFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow rec algebraMap_mem' toValuationSubring mk"
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

private theorem _root_.AlgebraicCurve.Place.tExpansion_coeff_unique_e15 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
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

p2m_export "AlgebraicCurve.Place" "tExpansion_coeff_unique_e15"
end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "rec subtype ext mk map" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_e15 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_e15"
namespace ValuationSubring p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff algebraMap_apply ext zero_mem rec mem_nonunits_iff mk mul_mem one_mem add_mem valuation LiesOverPrime" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_e15 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_e15"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow rec algebraMap_mem' toValuationSubring mk"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem exists_tExpansion_e15 {ι : Type*} (e : ι → K) (O : Subring F) {t : F} (ht0 : t ≠ 0)
    (hval : ∀ s : F, s ∈ O → ∃ a : ι, v.HasValue s (e a))
    (hdiv : ∀ s : F, s ∈ O → 0 < v.ord s → s / t ∈ O)
    (hC : ∀ a : ι, algebraMap K F (e a) ∈ O)
    (r : F) (hr : r ∈ O) :
    ∃ c : ℕ → ι, ∀ m : ℕ,
      (r - ∑ i ∈ Finset.range m, algebraMap K F (e (c i)) * t ^ i) / t ^ m ∈ O := by
  classical
  have step : ∀ s : ↥O, ∃ a : ι, ((s : F) - algebraMap K F (e a)) / t ∈ O := by
    intro s
    obtain ⟨a, ha⟩ := hval s s.2
    refine ⟨a, ?_⟩
    rcases (v.hasValue_iff_eq_or_ord_sub_pos_e15 ha.mem (e a)).mp ha with hEq | hpos
    · rw [hEq, sub_self, zero_div]; exact O.zero_mem
    · exact hdiv _ (O.sub_mem s.2 (hC a)) hpos
  choose coef hcoef using step
  let next : ↥O → ↥O := fun s => ⟨((s : F) - algebraMap K F (e (coef s))) / t, hcoef s⟩
  let seq : ℕ → ↥O := fun n => Nat.rec (motive := fun _ => ↥O) ⟨r, hr⟩ (fun _ s => next s) n
  refine ⟨fun n => coef (seq n), ?_⟩
  have hseq : ∀ m : ℕ, ((seq m : ↥O) : F) =
      (r - ∑ i ∈ Finset.range m, algebraMap K F (e (coef (seq i))) * t ^ i) / t ^ m := by
    intro m
    induction m with
    | zero =>
      show r = _
      simp
    | succ m ih =>
      have h1 : ((seq (m + 1) : ↥O) : F) =
          (((seq m : ↥O) : F) - algebraMap K F (e (coef (seq m)))) / t := rfl
      rw [h1, ih, Finset.sum_range_succ, div_sub' (hc := pow_ne_zero m ht0), div_div, ← pow_succ]
      congr 1
      ring
  intro m
  rw [← hseq m]
  exact (seq m).2

end Place
end AlgebraicCurve

section CauchyE15

variable {S : Type*} [CommRing S]

theorem sum_antidiagonal_eq_sum_filter_e15 (f : ℕ → ℕ → S) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, f p.1 p.2 =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, if i + j < m then f i j else 0 := by
  rw [Finset.sum_sigma', ← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun x => x.2) (fun p => (⟨p.1 + p.2, p⟩ : (_ : ℕ) × (ℕ × ℕ)))
  · rintro ⟨k, p⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal, and_true]
    omega
  · rintro ⟨k, p⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    obtain ⟨-, rfl⟩ := hx
    rfl
  · intro p hp
    rfl
  · intro x hx
    rfl

theorem sum_mul_sum_eq_cauchy_add_e15 (a b : ℕ → S) (t : S) (m : ℕ) :
    (∑ i ∈ Finset.range m, a i * t ^ i) * (∑ j ∈ Finset.range m, b j * t ^ j) =
      ∑ k ∈ Finset.range m, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) * t ^ k +
        t ^ m * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (if m ≤ i + j then a i * b j * t ^ (i + j - m) else 0) := by
  rw [Finset.sum_mul_sum]
  have h1 : ∑ k ∈ Finset.range m, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) * t ^ k =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if i + j < m then a i * b j * t ^ (i + j) else 0) := by
    rw [← sum_antidiagonal_eq_sum_filter_e15 (fun i j => a i * b j * t ^ (i + j)) m]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [h1, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i + j < m
  · rw [if_pos h, if_neg (by omega), mul_zero, add_zero]
    ring
  · rw [if_neg h, if_pos (by omega), zero_add,
      show t ^ m * (a i * b j * t ^ (i + j - m)) = a i * b j * (t ^ m * t ^ (i + j - m)) by ring,
      ← pow_add, Nat.add_sub_cancel' (by omega : m ≤ i + j)]
    ring

theorem cauchy_remainder_mem_e15 {F : Type*} [Field F] (O : Subring F) {t : F} (ht0 : t ≠ 0) (htO : t ∈ O)
    (a b : ℕ → F) (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) (r s : F) (m : ℕ)
    (hr : (r - ∑ i ∈ Finset.range m, a i * t ^ i) / t ^ m ∈ O)
    (hs : (s - ∑ i ∈ Finset.range m, b i * t ^ i) / t ^ m ∈ O) :
    (r * s - ∑ k ∈ Finset.range m, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) * t ^ k) / t ^ m ∈ O := by
  have htm : t ^ m ≠ 0 := pow_ne_zero m ht0
  have hPa : ∑ i ∈ Finset.range m, a i * t ^ i ∈ O :=
    O.sum_mem fun i _ => O.mul_mem (ha i) (O.pow_mem htO i)
  have hPb : ∑ i ∈ Finset.range m, b i * t ^ i ∈ O :=
    O.sum_mem fun i _ => O.mul_mem (hb i) (O.pow_mem htO i)
  have hH : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (if m ≤ i + j then a i * b j * t ^ (i + j - m) else 0) ∈ O := by
    refine O.sum_mem fun i _ => O.sum_mem fun j _ => ?_
    split_ifs
    · exact O.mul_mem (O.mul_mem (ha i) (hb j)) (O.pow_mem htO _)
    · exact O.zero_mem
  have hc := sum_mul_sum_eq_cauchy_add_e15 a b t m
  have key : (r * s - ∑ k ∈ Finset.range m, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) * t ^ k) / t ^ m =
      (r - ∑ i ∈ Finset.range m, a i * t ^ i) / t ^ m * ∑ i ∈ Finset.range m, b i * t ^ i +
      (∑ i ∈ Finset.range m, a i * t ^ i) * ((s - ∑ i ∈ Finset.range m, b i * t ^ i) / t ^ m) +
      t ^ m * ((r - ∑ i ∈ Finset.range m, a i * t ^ i) / t ^ m) *
        ((s - ∑ i ∈ Finset.range m, b i * t ^ i) / t ^ m) +
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if m ≤ i + j then a i * b j * t ^ (i + j - m) else 0) := by
    have hC : ∑ k ∈ Finset.range m, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) * t ^ k =
        (∑ i ∈ Finset.range m, a i * t ^ i) * (∑ j ∈ Finset.range m, b j * t ^ j) -
          t ^ m * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
            (if m ≤ i + j then a i * b j * t ^ (i + j - m) else 0) := by
      rw [hc]; ring
    rw [hC]
    field_simp
    ring
  rw [key]
  exact O.add_mem (O.add_mem (O.add_mem (O.mul_mem hr hPb) (O.mul_mem hPa hs))
    (O.mul_mem (O.mul_mem (O.pow_mem htO m) hr) hs)) hH

end CauchyE15

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow rec algebraMap_mem' toValuationSubring mk"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.exists_ringHom_tExpansion_e15 {Aᵣ : Type*} [CommRing Aᵣ] (e : Aᵣ →+* K)
    (he : Function.Injective e) (O : Subring F) {t : F} (ht : 0 < v.ord t)
    (hOv : ∀ s : F, s ∈ O → s ∈ v.toValuationSubring) (htO : t ∈ O)
    (hC : ∀ a : Aᵣ, algebraMap K F (e a) ∈ O)
    (hex : ∀ r : F, r ∈ O → ∃ c : ℕ → Aᵣ, ∀ m : ℕ,
      (r - ∑ i ∈ Finset.range m, algebraMap K F (e (c i)) * t ^ i) / t ^ m ∈ O) :
    ∃ φ : ↥O →+* PowerSeries Aᵣ,
      (∀ (r : ↥O) (m : ℕ), ((r : F) - ∑ i ∈ Finset.range m,
          algebraMap K F (e (PowerSeries.coeff i (φ r))) * t ^ i) / t ^ m ∈ O) ∧
      φ ⟨t, htO⟩ = PowerSeries.X ∧
      ∀ a : Aᵣ, φ ⟨algebraMap K F (e a), hC a⟩ = PowerSeries.C a := by
  classical
  have ht0 : t ≠ 0 := v.ne_zero_of_ord_pos_e15 ht

  let Good : F → (ℕ → Aᵣ) → Prop := fun r c =>
    ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (e (c i)) * t ^ i) / t ^ m ∈ O
  have uniq : ∀ (r : F) (c c' : ℕ → Aᵣ), Good r c → Good r c' → c = c' := by
    intro r c c' hc hc'
    have h := v.tExpansion_coeff_unique_e15 ht r (fun i => e (c i)) (fun i => e (c' i))
      (fun m => hOv _ (hc m)) (fun m => hOv _ (hc' m))
    funext i
    exact he (congrFun h i)
  choose cf hcf using hex
  let φf : ↥O → PowerSeries Aᵣ := fun r => PowerSeries.mk (cf r r.2)
  have hφ : ∀ r : ↥O, Good r (fun i => PowerSeries.coeff i (φf r)) := by
    intro r m
    simp only [φf, PowerSeries.coeff_mk]
    exact hcf r r.2 m
  have hchar : ∀ (r : ↥O) (c : ℕ → Aᵣ), Good r c → φf r = PowerSeries.mk c := by
    intro r c hc
    have h := congrFun (uniq r _ c (hφ r) hc)
    ext i
    have hi := h i
    simp only [φf, PowerSeries.coeff_mk] at hi ⊢
    exact hi

  have good_C : ∀ a : Aᵣ, Good (algebraMap K F (e a))
      (fun i => PowerSeries.coeff i (PowerSeries.C a : PowerSeries Aᵣ)) := by
    intro a m
    beta_reduce
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
      exact hC a
    · rw [Finset.sum_eq_single 0
        (fun i _ hi => by rw [PowerSeries.coeff_C, if_neg hi, map_zero, map_zero, zero_mul])
        (fun h => absurd (Finset.mem_range.mpr hm) h)]
      rw [PowerSeries.coeff_C, if_pos rfl, pow_zero, mul_one, sub_self, zero_div]
      exact O.zero_mem
  have good_X : Good t (fun i => PowerSeries.coeff i (PowerSeries.X : PowerSeries Aᵣ)) := by
    intro m
    beta_reduce
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
        exact htO
      · rw [Finset.sum_range_one, PowerSeries.coeff_X, if_neg (by decide), map_zero, map_zero, zero_mul,
          sub_zero, pow_one, div_self ht0]
        exact O.one_mem
    · rw [Finset.sum_eq_single 1
        (fun i _ hi => by rw [PowerSeries.coeff_X, if_neg hi, map_zero, map_zero, zero_mul])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      rw [PowerSeries.coeff_X, if_pos rfl, map_one, map_one, one_mul, pow_one, sub_self, zero_div]
      exact O.zero_mem
  have good_add : ∀ (r s : F) (c d : ℕ → Aᵣ), Good r c → Good s d → Good (r + s) (c + d) := by
    intro r s c d hc hd m
    have h : (r + s - ∑ i ∈ Finset.range m, algebraMap K F (e ((c + d) i)) * t ^ i) / t ^ m =
        (r - ∑ i ∈ Finset.range m, algebraMap K F (e (c i)) * t ^ i) / t ^ m +
        (s - ∑ i ∈ Finset.range m, algebraMap K F (e (d i)) * t ^ i) / t ^ m := by
      rw [← add_div]
      congr 1
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [h]
    exact O.add_mem (hc m) (hd m)
  have good_mul : ∀ (r s : F) (c d : ℕ → Aᵣ), Good r c → Good s d →
      Good (r * s) (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2) := by
    intro r s c d hc hd m
    have h := cauchy_remainder_mem_e15 O ht0 htO (fun i => algebraMap K F (e (c i)))
      (fun i => algebraMap K F (e (d i))) (fun i => hC _) (fun i => hC _) r s m (hc m) (hd m)
    show (r * s - ∑ i ∈ Finset.range m,
      algebraMap K F (e (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, c p.1 * d p.2)) * t ^ i) / t ^ m ∈ O
    simp only [map_sum, map_mul]
    exact h

  let φ : ↥O →+* PowerSeries Aᵣ :=
    { toFun := φf
      map_one' := by
        have hg := good_C 1
        simp only [map_one] at hg
        rw [hchar 1 _ hg]
        ext i
        simp only [PowerSeries.coeff_mk, map_one]
      map_mul' := fun r s => by
        rw [hchar (r * s) _ (good_mul _ _ _ _ (hφ r) (hφ s))]
        ext n
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
      map_zero' := by
        have hg := good_C 0
        simp only [map_zero] at hg
        rw [hchar 0 _ hg]
        ext i
        simp only [PowerSeries.coeff_mk, map_zero]
      map_add' := fun r s => by
        rw [hchar (r + s) _ (good_add _ _ _ _ (hφ r) (hφ s))]
        ext n
        simp only [PowerSeries.coeff_mk, Pi.add_apply, map_add] }
  refine ⟨φ, fun r m => hφ r m, ?_, ?_⟩
  · show φf ⟨t, htO⟩ = PowerSeries.X
    rw [hchar ⟨t, htO⟩ _ good_X]
    ext i
    simp only [PowerSeries.coeff_mk]
  · intro a
    show φf ⟨algebraMap K F (e a), hC a⟩ = PowerSeries.C a
    rw [hchar ⟨algebraMap K F (e a), hC a⟩ _ (good_C a)]
    ext i
    simp only [PowerSeries.coeff_mk]

p2m_export "AlgebraicCurve.Place" "exists_ringHom_tExpansion_e15"
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow rec algebraMap_mem' toValuationSubring mk"
p2m_open "AlgebraicCurve.Place"

theorem hasValue_iff_mem_and_eq_or_ord_sub_pos_e15
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_e15 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_e15 hg c).mpr h
end Place
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar ModularPolynomialData algebraMap_laurentSeries_eq_single PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun redFst IsStrictTypeOne mk rec"
p2m_open "ModularCurve.PlaceSpecialization"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "smoothLocalRingFst mem_smoothLocalRingFst_iff IsModel rec ι mk exists_mem_integers_residue_jFun_sub_ne_zero algebraMap_mem_smoothLocalRingFst"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]

theorem coe_algebraMap_intermediateField_laurent_e15 {L : Type*} [Field L]
    (E : IntermediateField L (LaurentSeries L)) (x : L) :
    ((algebraMap L ↥E x : ↥E) : LaurentSeries L) = HahnSeries.single 0 x := by
  rw [← algebraMap_laurentSeries_eq_single, IsScalarTower.algebraMap_apply L ↥E (LaurentSeries L) x]
  rfl

theorem liesOverPrime_of_red_e15 (red' : A →+* k) : A.LiesOverPrime q := by
  unfold ValuationSubring.LiesOverPrime
  have hq : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
  rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (red' (q : A)) := hu.map red'
  rw [map_natCast, CharP.cast_eq_zero k q] at h1
  exact not_isUnit_zero h1

end LevelOneProlongationPair
end PlaceSpecialization
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.ModularCurve.PlaceSpecialization.LevelOneProlongationPair in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ))) :
    ∃ φ : ↥(R.smoothLocalRingFst (P.redFst Q)) →+* PowerSeries ↥A,
      (∀ (r : ↥(R.smoothLocalRingFst (P.redFst Q))) (m : ℕ),
        ((r : ↥(modularFunctionFieldBar (1 * q))) - ∑ i ∈ Finset.range m,
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
              ((PowerSeries.coeff (R := ↥A) i (φ r) : A) : AlgebraicClosure ℚ) *
              (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ i) /
          (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ m ∈
        R.smoothLocalRingFst (P.redFst Q)) ∧
      (∀ ht : (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈
          R.smoothLocalRingFst (P.redFst Q), φ ⟨_, ht⟩ = PowerSeries.X) ∧
      (∀ (a : A) (ha : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈
          R.smoothLocalRingFst (P.redFst Q)), φ ⟨_, ha⟩ = PowerSeries.C (R := ↥A) a) := by
  obtain ⟨h3a1, h3a2⟩ := hR.ord_jFun_sub_eq_one_of_isStrictTypeOne hQ j₀ hj₀
  obtain ⟨htint, -⟩ := R.exists_mem_integers_residue_jFun_sub_ne_zero j₀
  set t := (jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) with ht_def
  have ht0 : t ≠ 0 := Q.ne_zero_of_ord_pos_e15 hj₀
  have htO : t ∈ R.smoothLocalRingFst (P.redFst Q) := by
    rw [mem_smoothLocalRingFst_iff]
    refine ⟨htint, fun W hW hWv => ?_⟩
    by_cases hWQ : W = Q
    · rw [hWQ]; exact Q.mem_of_ord_nonneg_e15 ht0 (by omega)
    · exact W.mem_of_ord_nonneg_e15 ht0 (h3a2 W hW hWv hWQ).ge
  obtain ⟨φ, h1, h2, h3⟩ := Q.exists_ringHom_tExpansion_e15 A.subtype (fun x y h => Subtype.ext h)
    (R.smoothLocalRingFst (P.redFst Q)) hj₀
    (fun s hs => ((R.mem_smoothLocalRingFst_iff _ _).mp hs).2 Q hQ rfl) htO
    (fun a => R.algebraMap_mem_smoothLocalRingFst (P.redFst Q) a)
    (fun r hr => hR.exists_tExpansion_of_mem_smoothLocalRingFst hQ j₀ hj₀ r hr)
  exact ⟨φ, h1, fun ht => h2, fun a ha => h3 a⟩

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion (solution)
