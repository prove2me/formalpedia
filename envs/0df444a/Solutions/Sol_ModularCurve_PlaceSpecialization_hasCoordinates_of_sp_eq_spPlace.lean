-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.hasCoordinates_of_sp_eq_spPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5c7b00a7-477b-573d-ade5-ee32daa790a2

import Definitions.Def_ModularCurve_ChartSemicontinuity
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piInf_range_localizes_of_not_affine
import Theorems.Thm_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.ModularCurve ModularCurve.CharPModel ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

private theorem penC_FIN
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring) :
    (∀ b : fm.BFin, fm.piFin b ∈ v.toValuationSubring) ∧
      ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
        ∃ b b' : fm.BFin, ¬ v.HasValue (fm.piFin b') (0 : k) ∧ g * fm.piFin b' = fm.piFin b :=
  ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem N A ℓ hℓN k red fm v hv

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen jq_mem_full coeff_jqModC_neg_one CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin mem_integralCoeffs_of_integral_affineBaseInf CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.FibreModel.piInf_range_localizes_of_not_affine CharPReduction.mem_modularLocalized_of_eval2_monic CharPReduction.modularRedLocHom_eq_coeffRed CharPReduction.modularRedLocHom_mem relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi adjoin_jBar_jNBar_eq_top"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "fibreReduction HasCoordinates sp d0_j d0_j_pole"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.ord_nonneg_of_mem_pn" "AlgebraicCurve.Place.ord_nonneg_of_mem_pn"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.mem_of_ord_nonneg_pn" "AlgebraicCurve.Place.mem_of_ord_nonneg_pn"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.ord_algebraMap_pn" "AlgebraicCurve.Place.ord_algebraMap_pn"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn" "AlgebraicCurve.Place.ne_zero_of_ord_pos_pn"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn" "AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
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
  · rw [v.isUnit_iff_ord_eq_zero_pn hsub h0]
    have hnn := v.ord_nonneg_of_mem_pn hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn h) h.le
  have hg : g ∈ v.toValuationSubring := by
    have h' := add_mem hsub (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at h'
  exact (v.hasValue_iff_eq_or_ord_sub_pos_pn hg c).mpr (Or.inr h)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn"
private theorem pnN_coe_algebraMap {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))
    (x : L) : ((algebraMap L E x : E) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
  rw [IsScalarTower.algebraMap_apply L E (LaurentSeries L) x]
  rfl

private theorem pnN_const_mem (a : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red := by
  rw [pnN_coe_algebraMap]
  exact CharPReduction.subring_le_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    (CharPReduction.constSeries_mem_modularRing N A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩)

private theorem penC_residue_surjective [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N)) :
    Function.Surjective (algebraMap k v.ResidueField) := by
  have h1 : Module.finrank k v.ResidueField = 1 := place_deg_eq_one_of_isAlgClosed k N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem penC_exists_j_value (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a₀ : A, 0 < w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a₀ : AlgebraicClosure ℚ)) := by
  by_contra hcon
  have hle : ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
    fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
  have hpole := P.d0_j_pole w hle
  rw [hw] at hpole
  have hnn : (0 : ℤ) ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem_pn hv1
  exact absurd hnn (not_le.mpr hpole)

private theorem penC_sub_mem_nonunits_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : u.HasValue g c) :
    g - algebraMap K F c ∈ u.toValuationSubring.nonunits := by
  have hmem : g - algebraMap K F c ∈ u.toValuationSubring := sub_mem h.mem (u.algebraMap_mem' c)
  have hres : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = 0 := by
    have e : (⟨g - algebraMap K F c, hmem⟩ : u.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K u.toValuationSubring c := rfl
    rw [e, map_sub, h.residue_eq, u.residue_algebraMap, sub_self]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)

private theorem penC_hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : g - algebraMap K F c ∈ u.toValuationSubring.nonunits) :
    u.HasValue g c := by
  by_cases hgc : g = algebraMap K F c
  · rw [hgc]
    exact u.hasValue_algebraMap c
  · have hne : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hgc
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact u.hasValue_of_ord_sub_pos_pn ((u.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax)

private theorem penC_red_eq_zero_of_mem_maximalIdeal (hred : Function.Surjective red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]
  exact ha

private theorem coeffMap_qExpand_g {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hm
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

private theorem coeffEmb_jq_eq_jqModC_g :
    coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  have hmap : jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = jNum.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : m = (-1 : ℤ) <;> simp [hm]
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, ← hmap,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega), map_zero]

private theorem h1_coe_mem_adjoin (t : modularFunctionFieldBar N) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} := by
  have htop := adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have ht : t ∈ (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := trivial
  rw [← htop] at ht
  have hmap : (modularFunctionFieldBar N).val t ∈
      (IntermediateField.adjoin (AlgebraicClosure ℚ) _).map (modularFunctionFieldBar N).val := ⟨t, ht, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton] at hmap
  have h1 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = jqModC (AlgebraicClosure ℚ) :=
    coeffEmb_jq_eq_jqModC_g
  have h2 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ =
        jqNModC (AlgebraicClosure ℚ) N := by
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N
    rw [jqNModC, ← coeffEmb_jq_eq_jqModC_g, coeffEmb, coeffMap_qExpand_g]
  rw [h1, h2] at hmap
  exact hmap

private theorem penC_bfin_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value v hv1 _ hw

  have hreg : fm.piFin b ∈ v.toValuationSubring := (penC_FIN N A q hqN k red fm v hv1).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BFin := b - ⟨CharPModel.constantsHom N A a₁, fm.constFin_mem a₁⟩ with hb₁
  have hpi : (fm.piFin b₁ : modularFunctionFieldC k N)
      = fm.piFin b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piFin_const]
  have hnu : (fm.piFin b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep _ a₀ ha₀ b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    penC_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

private theorem w2_jqModC_inv_mem_localized :
    (jqModC (AlgebraicClosure ℚ))⁻¹ ∈ CharPReduction.modularLocalized N A.toSubring red := by
  have hj0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h1 := coeff_jqModC_neg_one (AlgebraicClosure ℚ)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hj : (⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing N A.toSubring⟩ :
      CharPReduction.modularRing N A.toSubring) ∉
        CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
          (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff]
    intro h0
    have h1 := congrArg (fun x : LaurentSeries k => x.coeff (-1 : ℤ)) h0
    simp only [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_zero] at h1
    have h2 : ∀ h : (jqModC (AlgebraicClosure ℚ)).coeff (-1 : ℤ) ∈ A.toSubring,
        (⟨(jqModC (AlgebraicClosure ℚ)).coeff (-1 : ℤ), h⟩ : A.toSubring) = 1 :=
      fun _ => Subtype.ext (coeff_jqModC_neg_one (AlgebraicClosure ℚ))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  refine ⟨1, ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing N A.toSubring⟩, hj, ?_⟩
  show (jqModC (AlgebraicClosure ℚ))⁻¹ * jqModC (AlgebraicClosure ℚ) = 1
  exact inv_mul_cancel₀ hj0

private theorem w2_bfin_mem_localized (fm : FibreModel N A q k red) (dataN : ModularPolynomialData N)
    (hqN : ¬ q ∣ N) (b : fm.BFin) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
  have hle : CharPModel.affineBaseFin N A ≤
      (CharPReduction.modularLocalized N A.toSubring red).comap
        (modularFunctionFieldBar N).val.toRingHom := by
    rw [CharPModel.affineBaseFin, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · refine Subring.mem_comap.mpr ?_
      exact pnN_const_mem a
    · refine Subring.mem_comap.mpr ?_
      show coeffEmb (AlgebraicClosure ℚ) jq ∈ CharPReduction.modularLocalized N A.toSubring red
      rw [coeffEmb_jq_eq_jqModC_g]
      exact CharPReduction.subring_le_localizedAtKer A.toSubring red
        (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
        (CharPReduction.jqModC_mem_modularRing N A.toSubring)
  obtain ⟨p, hp, hpb⟩ := fm.integralFin b
  let ι : CharPModel.affineBaseFin N A →+* CharPReduction.modularLocalized N A.toSubring red :=
    ((modularFunctionFieldBar N).val.toRingHom.comp (CharPModel.affineBaseFin N A).subtype).codRestrict _
      (fun x => hle x.2)
  have hcomp : (CharPReduction.modularLocalized N A.toSubring red).subtype.comp ι
      = (modularFunctionFieldBar N).val.toRingHom.comp (CharPModel.affineBaseFin N A).subtype :=
    RingHom.ext fun _ => rfl
  refine CharPReduction.mem_modularLocalized_of_eval2_monic A red N dataN
    (relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN)
    (h1_coe_mem_adjoin (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hp.map ι) ?_
  rw [Polynomial.eval₂_map, hcomp]
  have h := Polynomial.hom_eval₂ p (CharPModel.affineBaseFin N A).subtype
    (modularFunctionFieldBar N).val.toRingHom
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  rw [hpb, map_zero] at h
  exact h.symm

private theorem w2_binf_mem_localized (fm : FibreModel N A q k red) (dataN : ModularPolynomialData N)
    (hqN : ¬ q ∣ N) (b : fm.BInf) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
  have hle : CharPModel.affineBaseInf N A ≤
      (CharPReduction.modularLocalized N A.toSubring red).comap
        (modularFunctionFieldBar N).val.toRingHom := by
    rw [CharPModel.affineBaseInf, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · refine Subring.mem_comap.mpr ?_
      exact pnN_const_mem a
    · refine Subring.mem_comap.mpr ?_
      show (((CharPModel.jBar N)⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized N A.toSubring red
      rw [IntermediateField.coe_inv,
        show ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
          = jqModC (AlgebraicClosure ℚ) from coeffEmb_jq_eq_jqModC_g]
      exact w2_jqModC_inv_mem_localized
  obtain ⟨p, hp, hpb⟩ := fm.integralInf b
  let ι : CharPModel.affineBaseInf N A →+* CharPReduction.modularLocalized N A.toSubring red :=
    ((modularFunctionFieldBar N).val.toRingHom.comp (CharPModel.affineBaseInf N A).subtype).codRestrict _
      (fun x => hle x.2)
  have hcomp : (CharPReduction.modularLocalized N A.toSubring red).subtype.comp ι
      = (modularFunctionFieldBar N).val.toRingHom.comp (CharPModel.affineBaseInf N A).subtype :=
    RingHom.ext fun _ => rfl
  refine CharPReduction.mem_modularLocalized_of_eval2_monic A red N dataN
    (relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN)
    (h1_coe_mem_adjoin (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hp.map ι) ?_
  rw [Polynomial.eval₂_map, hcomp]
  have h := Polynomial.hom_eval₂ p (CharPModel.affineBaseInf N A).subtype
    (modularFunctionFieldBar N).val.toRingHom
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  rw [hpb, map_zero] at h
  exact h.symm

private theorem w2_piFin_glue (fm : FibreModel N A q k red) (b : fm.BFin)
    (hb : ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    CharPReduction.modularRedLocHom N A.toSubring red
        ⟨((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
          LaurentSeries (AlgebraicClosure ℚ)), hb⟩
      = ((fm.piFin b : modularFunctionFieldC k N) : LaurentSeries k) := by
  have hint : ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
    mem_integralCoeffs_of_integral_affineBaseFin A N _ (fm.integralFin b)
  rw [CharPReduction.modularRedLocHom_eq_coeffRed A.toSubring red N _ hint,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

private theorem w2_piInf_glue (fm : FibreModel N A q k red) (hc : fm.CuspChart)
    (dataN : ModularPolynomialData N)
    (hsep : (((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)) (b : fm.BInf)
    (hb : ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    CharPReduction.modularRedLocHom N A.toSubring red
        ⟨((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
          LaurentSeries (AlgebraicClosure ℚ)), hb⟩
      = ((fm.piInf b : modularFunctionFieldC k N) : LaurentSeries k) := by
  have hint : ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
    mem_integralCoeffs_of_integral_affineBaseInf A N _ (fm.integralInf b)
  rw [CharPReduction.modularRedLocHom_eq_coeffRed A.toSubring red N _ hint,
    FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A q k red fm hc dataN hsep b hint]

private theorem w2_j_no_value (v : Place k (modularFunctionFieldC k N))
    (hv : jGeomGen k N ∉ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
  intro a
  by_contra hlt
  have hpos := P.d0_j w a (not_le.mp hlt)
  rw [hw] at hpos
  apply hv
  have hsub : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red a) ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn hpos) hpos.le
  have h := add_mem hsub (v.algebraMap_mem' (red a))
  rwa [sub_add_cancel] at h

private theorem w2_binf_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∉ v.toValuationSubring) (b : fm.BInf)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piInf b) (red a) := by
  have hpole := w2_j_no_value v hv w hw

  have hreg : fm.piInf b ∈ v.toValuationSubring :=
    (ModularCurve.CharPModel.FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v
      (fun h => hv h.1)).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BInf := b - ⟨CharPModel.constantsHom N A a₁, fm.constInf_mem a₁⟩ with hb₁
  have hpi : (fm.piInf b₁ : modularFunctionFieldC k N)
      = fm.piInf b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piInf_const]
  have hnu : (fm.piInf b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    penC_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

private theorem w2_clause_of_model (v : Place k (modularFunctionFieldC k N)) (hred : Function.Surjective red)
    (B : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (π : B →+* modularFunctionFieldC k N)
    (hloc : ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
      ∃ b b' : B, ¬ v.HasValue (π b') (0 : k) ∧ g * π b' = π b)
    (hB : ∀ b : B, ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hπ : ∀ b : B, CharPReduction.modularRedLocHom N A.toSubring red
        ⟨((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
          LaurentSeries (AlgebraicClosure ℚ)), hB b⟩
      = ((π b : modularFunctionFieldC k N) : LaurentSeries k))
    (hconst : ∀ a : A, CharPModel.constantsHom N A a ∈ B)
    (hπconst : ∀ a : A, π ⟨CharPModel.constantsHom N A a, hconst a⟩
      = algebraMap k (modularFunctionFieldC k N) (red a))
    (hval : ∀ (b : B) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), P.sp w = v →
      ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (a : AlgebraicClosure ℚ) ∧ v.HasValue (π b) (red a)) :
    ∃ (T : modularFunctionFieldBar N)
      (hT : (T : LaurentSeries
        (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
      (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨T,
        hT⟩ ∈ modularFunctionFieldC k N),
      (∃ c : k, v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) c) = 1) ∧
      ∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u' = v →
        ∃ a : A, 0 < u'.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ∧
          0 < v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) (red a)) := by

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨t, htmem, ht1⟩ : ∃ t : modularFunctionFieldC k N, t ∈ v.toValuationSubring ∧ v.ord t = 1 :=
    ⟨ϖ, ϖ.2, v.ord_coe_irreducible hϖ⟩
  obtain ⟨b, b', hb'0, hbb'⟩ := hloc t htmem
  have hval0 : v.HasValue (0 : modularFunctionFieldC k N) (0 : k) := by
    have h := v.hasValue_algebraMap (0 : k)
    rwa [map_zero] at h
  have hπb' : π b' ≠ 0 := fun h0 => hb'0 (by rw [h0]; exact hval0)
  have hπb'L : ((π b' : modularFunctionFieldC k N) : LaurentSeries k) ≠ 0 :=
    fun h0 => hπb' (Subtype.ext h0)
  have hb'ne : b' ≠ 0 := fun h0 => hπb' (by rw [h0, map_zero])
  have hb'Bar : (b' : modularFunctionFieldBar N) ≠ 0 := fun h0 => hb'ne (Subtype.ext h0)
  have hb'L : ((b' : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    fun h0 => hb'Bar (Subtype.ext h0)

  have hinv : (((b' : modularFunctionFieldBar N)⁻¹ : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
    obtain ⟨r, s, hs, hrs⟩ := hB b'
    have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, hB b'⟩ hrs
    have hr : r ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) := by
      rw [CharPReduction.notMem_redKer_iff, ← hspec]
      exact mul_ne_zero (fun h0 => hπb'L ((hπ b').symm.trans h0))
        (CharPReduction.redRes_ne_zero_of_notMem hs)
    refine ⟨s, r, hr, ?_⟩
    rw [IntermediateField.coe_inv, inv_mul_eq_iff_eq_mul₀ hb'L]
    exact hrs.symm

  obtain ⟨T, hTdef⟩ : ∃ T : modularFunctionFieldBar N,
      T = (b : modularFunctionFieldBar N) * (b' : modularFunctionFieldBar N)⁻¹ := ⟨_, rfl⟩
  have hT : (T : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
    rw [hTdef, IntermediateField.coe_mul]
    exact mul_mem (hB b) hinv
  have hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨T, hT⟩ ∈ modularFunctionFieldC k N :=
    CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨T, hT⟩

  have hTL : (⟨(T : LaurentSeries (AlgebraicClosure ℚ)), hT⟩ : CharPReduction.modularLocalized N A.toSubring red)
      * ⟨_, hB b'⟩ = ⟨_, hB b⟩ := by
    apply Subtype.ext
    show (T : LaurentSeries (AlgebraicClosure ℚ)) * _ = _
    rw [hTdef, IntermediateField.coe_mul, IntermediateField.coe_inv, inv_mul_cancel_right₀ hb'L]
  have hTred : CharPReduction.modularRedLocHom N A.toSubring red ⟨T, hT⟩ = (t : LaurentSeries k) := by
    have h1 := congrArg (CharPReduction.modularRedLocHom N A.toSubring red) hTL
    rw [map_mul, hπ b', hπ b] at h1
    have h2 : ((t : modularFunctionFieldC k N) : LaurentSeries k)
        * ((π b' : modularFunctionFieldC k N) : LaurentSeries k)
        = ((π b : modularFunctionFieldC k N) : LaurentSeries k) := by
      rw [← IntermediateField.coe_mul, hbb']
    exact mul_right_cancel₀ hπb'L (h1.trans h2.symm)
  have hTbar : fibreReduction T hT hmem = t := Subtype.ext hTred
  refine ⟨T, hT, hmem, ⟨0, ?_⟩, ?_⟩
  · rw [map_zero, sub_zero, hTbar]
    exact ht1
  intro u' hu'
  obtain ⟨a₁, h₁w, h₁v⟩ := hval b u' hu'
  obtain ⟨a₂, h₂w, h₂v⟩ := hval b' u' hu'

  have hred₂ : red a₂ ≠ 0 := fun h0 => hb'0 (by rw [← h0]; exact h₂v)
  have hunit : IsUnit a₂ := IsLocalRing.notMem_maximalIdeal.mp
    (fun hm => hred₂ (penC_red_eq_zero_of_mem_maximalIdeal hred hm))
  obtain ⟨u, rfl⟩ := hunit
  have ha₂ : ((u : A) : AlgebraicClosure ℚ) ≠ 0 :=
    fun h0 => hred₂ (by rw [show (u : A) = 0 from Subtype.ext h0, map_zero])
  obtain ⟨c, hcdef⟩ : ∃ c : A, c = a₁ * (↑(u⁻¹) : A) := ⟨_, rfl⟩
  have hcF : (c : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) * (((u : A) : AlgebraicClosure ℚ))⁻¹ := by
    have h1 : (((↑(u⁻¹) : A) : AlgebraicClosure ℚ)) * ((u : A) : AlgebraicClosure ℚ) = 1 :=
      congrArg (fun x : A => (x : AlgebraicClosure ℚ)) u.inv_mul
    rw [hcdef, show ((a₁ * (↑(u⁻¹) : A) : A) : AlgebraicClosure ℚ)
      = (a₁ : AlgebraicClosure ℚ) * ((↑(u⁻¹) : A) : AlgebraicClosure ℚ) from rfl,
      eq_inv_of_mul_eq_one_left h1]
  have hredc : red c = red a₁ * (red (u : A))⁻¹ := by
    have h2 : red (↑(u⁻¹) : A) * red (u : A) = 1 := by
      rw [← map_mul, u.inv_mul, map_one]
    rw [hcdef, map_mul, eq_inv_of_mul_eq_one_left h2]
  have hvT : u'.HasValue T (c : AlgebraicClosure ℚ) := by
    rw [hTdef, hcF]
    exact h₁w.mul (h₂w.inv ha₂)

  have hTc : T ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ) := by
    intro hEq
    have hconst_eq : (CharPModel.constantsHom N A c : modularFunctionFieldBar N)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ) := rfl
    have hbB : b = ⟨CharPModel.constantsHom N A c, hconst c⟩ * b' := by
      apply Subtype.ext
      show (b : modularFunctionFieldBar N) = CharPModel.constantsHom N A c * (b' : modularFunctionFieldBar N)
      rw [hconst_eq, ← hEq, hTdef, inv_mul_cancel_right₀ hb'Bar]
    have hπeq : π b = algebraMap k (modularFunctionFieldC k N) (red c) * π b' := by
      rw [hbB, map_mul, hπconst]
    have ht_eq : t = algebraMap k (modularFunctionFieldC k N) (red c) :=
      mul_right_cancel₀ hπb' (hbb'.trans hπeq)
    rw [ht_eq, v.ord_algebraMap_pn] at ht1
    exact zero_ne_one ht1
  have ht_q : t = π b * (π b')⁻¹ := by
    rw [← hbb', mul_inv_cancel_right₀ hπb']
  have hvt : v.HasValue t (red c) := by
    rw [ht_q, hredc]
    exact h₁v.mul (h₂v.inv hred₂)
  have htc : t ≠ algebraMap k (modularFunctionFieldC k N) (red c) := by
    intro h
    rw [h, v.ord_algebraMap_pn] at ht1
    exact zero_ne_one ht1
  refine ⟨c, ?_, ?_⟩
  · exact ((u'.hasValue_iff_eq_or_ord_sub_pos_pn hvT.mem (c : AlgebraicClosure ℚ)).mp hvT).resolve_left hTc
  · rw [hTbar]
    exact ((v.hasValue_iff_eq_or_ord_sub_pos_pn htmem (red c)).mp hvt).resolve_left htc

private theorem hasCoordinates_main [IsAlgClosed k] (fm : FibreModel N A q k red) (hc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N) :
    HasCoordinates P := by
  unfold HasCoordinates
  intro v
  by_cases hv : jGeomGen k N ∈ v.toValuationSubring
  ·
    have hFIN := ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem N A q hqN k red fm v hv
    exact w2_clause_of_model v hred fm.BFin fm.piFin hFIN.2
      (w2_bfin_mem_localized fm (dataAll N (dvd_refl N)) hqN)
      (fun b => w2_piFin_glue fm b (w2_bfin_mem_localized fm (dataAll N (dvd_refl N)) hqN b))
      fm.constFin_mem fm.piFin_const
      (penC_bfin_values fm hred dataAll hsep hP hqN v hv)
  ·
    have hINF := ModularCurve.CharPModel.FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v
      (fun h => hv h.1)
    exact w2_clause_of_model v hred fm.BInf fm.piInf hINF.2
      (w2_binf_mem_localized fm (dataAll N (dvd_refl N)) hqN)
      (fun b => w2_piInf_glue fm hc (dataAll N (dvd_refl N)) hsep b
        (w2_binf_mem_localized fm (dataAll N (dvd_refl N)) hqN b))
      fm.constInf_mem fm.piInf_const
      (w2_binf_values fm hred dataAll hsep hP hqN v hv)

end ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    [IsAlgClosed k] (fm : FibreModel N A q k red) (hc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N) :
    HasCoordinates P := by
  exact ModularCurve.PlaceSpecialization.hasCoordinates_main fm hc hred dataAll hsep hP hqN

end S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace (solution)
