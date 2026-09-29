-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_redFst_residue_jFun_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b7c13505-f511-59c0-9be0-9c795b1af8c0

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_algebraMap_eq_red
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_congrRingEquiv Place.congrEquiv_apply RationalFunctionField.ord_placeOfPoint_algebraMap"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ord_congrRingEquiv congrEquiv_apply"
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

theorem hasValue_iff_eq_or_ord_sub_pos_e15 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
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

namespace Subring p2m_export "Subring" "ext map" end Subring
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
namespace ValuationSubring p2m_export "ValuationSubring" "coe_mem_nonunits_iff algebraMap_apply ext mem_nonunits_iff mul_mem valuation LiesOverPrime" end ValuationSubring
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
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC coeffMap_jqModC"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun redFst d0_j redFst_eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve.PlaceSpecialization"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply ι_coe R₁ residue_jFun_jqFun residue_algebraMap_eq_red"
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

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC coeffMap_jqModC"
p2m_open "ModularCurve"

theorem ord_charLGeomPlaceOfPoint_jq_sub_e15 (K : Type*) [Field K] (c : K) :
    (charLGeomPlaceOfPoint K c).ord
      ((⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) -
        algebraMap K ↥(modularFunctionFieldC K 1) c) = 1 := by
  rw [charLGeomPlaceOfPoint, charLGeomPlaceEquiv, AlgebraicCurve.Place.congrEquiv_apply]
  have hX : (((ratFuncEquivCharLOneC K) (RatFunc.X : RatFunc K) : ↥(modularFunctionFieldC K 1)) :
      LaurentSeries K) = jqModC K := by
    simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
    exact RatFunc.algEquivOfTranscendental_X _ _
  have hX' : (ratFuncEquivCharLOneC K) (RatFunc.X : RatFunc K) =
      (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) := Subtype.ext hX
  have hCc : (RatFunc.C c : RatFunc K) = algebraMap K (RatFunc K) c := by
    rw [RatFunc.algebraMap_eq_C]
  have hf : ((⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) -
        algebraMap K ↥(modularFunctionFieldC K 1) c) =
      (ratFuncEquivCharLOneC K).toRingEquiv
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C c)) := by
    rw [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, map_sub, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, map_sub, hX', hCc, AlgEquiv.commutes]
  rw [hf, AlgebraicCurve.Place.ord_congrRingEquiv,
    AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap c (Polynomial.X_sub_C_ne_zero c),
    Polynomial.rootMultiplicity_X_sub_C_self, Nat.cast_one]

end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one.ModularCurve.PlaceSpecialization.LevelOneProlongationPair in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)))
    (h : (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈ R.R₁.integers) :
    (P.redFst Q).ord (R.residue₁ ⟨_, h⟩) = 1 := by

  have hj : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) :=
    Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)
  have hQ' := P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos Q j₀ (by rw [hj]; exact hj₀)

  have hA : A.LiesOverPrime q := liesOverPrime_of_red_e15 (q := q) red
  obtain ⟨hj1, -, -, -, hres, -⟩ := residue_jFun_jqFun hA R
  have hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr j₀.2
  have hsub : (⟨_, h⟩ : R.R₁.integers) = ⟨jFun (q := q), hj1⟩ - ⟨_, hc⟩ := rfl
  have hrest : R.residue₁ ⟨_, h⟩ =
      (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) -
        algebraMap k ↥(modularFunctionFieldC k 1) (red j₀) := by
    rw [hsub, map_sub, R.residue_algebraMap_eq_red j₀ hc]
    congr 1
    apply Subtype.ext
    rw [residue₁_apply, R.ι_coe, hres, coeffMap_jqModC]

  rw [hQ', hrest]
  exact ord_charLGeomPlaceOfPoint_jq_sub_e15 k (red j₀)

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one (solution)
