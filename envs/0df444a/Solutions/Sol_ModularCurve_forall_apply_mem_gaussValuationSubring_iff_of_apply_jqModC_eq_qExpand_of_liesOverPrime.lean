-- Prove2me | solution 1 for ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/20589c19-bdc5-50ae-8072-2247de245303

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC P2MW.S_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH GammaH_mono qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange jqModC map_jqModC exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC"
namespace GaussStableFricke
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

open scoped MatrixGroups
open IsLocalRing

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_ofPowerSeries (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_qExpand (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem jqModC_coeff_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : K))
    (x := HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))) (a := 0) (b := -1)
  rw [zero_add] at h
  rw [jqModC, h, one_mul, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

theorem transcendental_of_order_neg {K : Type*} [Field K] (x : LaurentSeries K) (hx : x.order < 0) :
    Transcendental K x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rintro ⟨p, hp0, hpx⟩
  set d := p.natDegree with hd
  have hsm : ∀ (c : K) (y : LaurentSeries K) (n : ℤ),
      (algebraMap K (LaurentSeries K) c * y).coeff n = c * y.coeff n := by
    intro c y n
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  have key : (Polynomial.aeval x p).coeff (d • x.order) = p.leadingCoeff * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single d]
    · rw [hsm, Polynomial.leadingCoeff]
    · intro i hi hid
      have hi' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
      rw [hsm, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow]
      simp only [nsmul_eq_mul]
      have : (i : ℤ) < d := by exact_mod_cast hi'
      nlinarith
    · intro h
      exact absurd (Finset.self_mem_range_succ d) h
  rw [hpx, HahnSeries.coeff_zero] at key
  have h1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h2 : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr) (pow_ne_zero _ hx0)
  exact mul_ne_zero h1 h2 key.symm

theorem order_neg_of_coeff_ne_zero {K : Type*} [Field K] {x : LaurentSeries K} {n : ℤ} (hn : n < 0)
    (h : x.coeff n ≠ 0) : x.order < 0 :=
  lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h) hn

theorem transcendental_jqModC (K : Type*) [Field K] : Transcendental K (jqModC K) :=
  transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := -1) (by norm_num)
    (by rw [jqModC_coeff_neg_one]; exact one_ne_zero))

theorem transcendental_qExpand_jqModC (K : Type*) [Field K] (n : ℕ) [NeZero n] :
    Transcendental K (qExpand K n (jqModC K)) := by
  refine transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := (n : ℤ) * (-1)) ?_ ?_)
  · have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    linarith
  · rw [qExpand_coeff_mul, jqModC_coeff_neg_one]
    exact one_ne_zero

theorem transcendental_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    (z : E) (h : Transcendental K (z : L)) : Transcendental K z :=
  fun hz => h (IntermediateField.isAlgebraic_iff.mp hz)

end Laurent

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨h0, hu⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rw [Subgroup.mem_sup] at hu
  obtain ⟨y, hy, z, hz, hyz⟩ := hu
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, mul_one] at hyz
    exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨h0, hyz ▸ hy⟩)
  · rw [hk.neg_one_zpow, mul_neg_one] at hyz
    right
    have h0' : -γ ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
      simp [h0]
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩
    have : CohCarrier.gamma0Units M ⟨-γ, h0'⟩ = -CohCarrier.gamma0Units M ⟨γ, h0⟩ := by
      ext
      simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map]
    rw [this, ← hyz, neg_neg]
    exact hy

end ModularCurve.GaussStableFricke

open ModularCurve.GaussStableFricke AlgebraicCurve IsLocalRing in
open scoped MatrixGroups in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H : Subgroup (ZMod N)ˣ) (hpN : ¬ p ∣ N)
    (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ = CohCarrier.GammaH N H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ℕ) [NeZero m]
    (j jm : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hj : ((j : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hjm : ((jm : LaurentSeries (AlgebraicClosure ℚ))) =
      ModularCurve.qExpand (AlgebraicClosure ℚ) m (ModularCurve.jqModC (AlgebraicClosure ℚ)))
    (W₀ : ValuationSubring ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hW₀ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))))
    (w : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≃ₐ[AlgebraicClosure ℚ]
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hwj : w j = jm) (hwjm : w jm = j) :
    ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)), w f ∈ W₀ ↔ f ∈ W₀ := by
  classical

  have hΓdef := hΓ
  clear hΓ
  haveI hΓfi : Γ.FiniteIndex := by
    subst hΓdef
    exact Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH N _)
  have hT : ModularGroup.T ∈ Γ := by
    subst hΓdef
    exact ModularCurve.translation_mem_GammaH _ _

  obtain ⟨R, hR1, hR2⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A Γ hT
  have aux : ∀ (z : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (y : LaurentSeries ↥A), (z : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y →
      ∃ hz : z ∈ R.integers,
        ((R.residue ⟨z, hz⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y := by
    intro z y hzy
    have hy : coeffMap A.subtype y ∈ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := hzy ▸ z.2
    obtain ⟨hO, hres⟩ := hR2 y hy
    have e : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = z := Subtype.ext hzy.symm
    refine ⟨e ▸ hO, ?_⟩
    have : (⟨z, e ▸ hO⟩ : ↥R.integers) = ⟨⟨coeffMap A.subtype y, hy⟩, hO⟩ := Subtype.ext e.symm
    rw [this]
    exact hres
  have hjy : ((j : LaurentSeries (AlgebraicClosure ℚ))) = coeffMap A.subtype (jqModC ↥A) := by
    rw [hj, coeffMap_jqModC]
  have hjmy : ((jm : LaurentSeries (AlgebraicClosure ℚ))) = coeffMap A.subtype (qExpand ↥A m (jqModC ↥A)) := by
    rw [hjm, coeffMap_qExpand, coeffMap_jqModC]
  obtain ⟨hjO, hjres⟩ := aux j _ hjy
  obtain ⟨hjmO, hjmres⟩ := aux jm _ hjmy
  rw [coeffMap_jqModC] at hjres
  rw [coeffMap_qExpand, coeffMap_jqModC] at hjmres
  have htrj : Transcendental (ResidueField ↥A) (R.residue ⟨j, hjO⟩) := by
    apply transcendental_of_coe
    rw [hjres]
    exact transcendental_jqModC (ResidueField ↥A)
  have htrjm : Transcendental (ResidueField ↥A) (R.residue ⟨jm, hjmO⟩) := by
    apply transcendental_of_coe
    rw [hjmres]
    exact transcendental_qExpand_jqModC (ResidueField ↥A) m

  have halg : (algebraMap ↥A (AlgebraicClosure ℚ) : ↥A →+* (AlgebraicClosure ℚ)) = A.subtype := rfl
  have hWR : W₀ = R.integers := by
    ext f
    rw [hW₀ f, hR1 f, halg]
    constructor
    · rintro ⟨x, y, hy0, hxy⟩
      refine ⟨HahnSeries.ofPowerSeries ℤ ↥A x, HahnSeries.ofPowerSeries ℤ ↥A y, ?_, ?_⟩
      · rw [coeffMap_ofPowerSeries]
        intro h
        apply hy0
        exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
      · rw [coeffMap_ofPowerSeries, coeffMap_ofPowerSeries]
        exact hxy
    · rintro ⟨X, Y, hY0, hXY⟩
      obtain ⟨⟨yp, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries ↥A)) Y
      obtain ⟨⟨xp, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries ↥A)) X
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
      simp only [LaurentSeries.coe_algebraMap] at hs ht
      rw [← ha] at hs
      rw [← hb] at ht
      have hXne : ∀ n : ℕ, coeffMap (residue ↥A) (HahnSeries.ofPowerSeries ℤ ↥A (PowerSeries.X ^ n)) ≠ 0 := by
        intro n
        rw [coeffMap_ofPowerSeries, map_pow, PowerSeries.map_X, HahnSeries.ofPowerSeries_X_pow]
        exact HahnSeries.single_ne_zero one_ne_zero
      refine ⟨xp * PowerSeries.X ^ a, yp * PowerSeries.X ^ b, ?_, ?_⟩
      · intro h0
        have h1 : coeffMap (residue ↥A) (HahnSeries.ofPowerSeries ℤ ↥A (yp * PowerSeries.X ^ b)) = 0 := by
          rw [coeffMap_ofPowerSeries, h0, map_zero]
        rw [map_mul, ← hs, map_mul, map_mul] at h1
        exact (mul_ne_zero (mul_ne_zero hY0 (hXne a)) (hXne b)) h1
      · rw [← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries]
        simp only [map_mul]
        rw [← hs, ← ht]
        simp only [map_mul]
        rw [← hXY]
        ring
  subst hWR

  let φ : ↥A →+* ↥R.integers :=
    { toFun := fun a => ⟨algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hφres : R.residue.comp φ = (algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)).comp (residue ↥A) := by
    refine RingHom.ext fun a => ?_
    show R.residue ⟨algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (a : (AlgebraicClosure ℚ)), _⟩ = algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (residue ↥A a)
    exact R.residue_algebraMap a
  have hφsub : R.integers.subtype.comp φ = (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))).comp A.subtype :=
    RingHom.ext fun a => rfl
  have hunit : ∀ (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (ht : t ∈ R.integers), Transcendental (ResidueField ↥A) (R.residue ⟨t, ht⟩) →
      ∀ Q : Polynomial ↥A, Q.map (residue ↥A) ≠ 0 →
        ∃ u : (↥R.integers)ˣ, ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = Polynomial.aeval t (Q.map A.subtype) := by
    intro t ht htr Q hQ
    have hzval : ((Polynomial.eval₂ φ ⟨t, ht⟩ Q : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = Polynomial.aeval t (Q.map A.subtype) := by
      show R.integers.subtype (Polynomial.eval₂ φ ⟨t, ht⟩ Q) = _
      rw [Polynomial.hom_eval₂, hφsub, Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    have hzres : R.residue (Polynomial.eval₂ φ ⟨t, ht⟩ Q) ≠ 0 := by
      rw [Polynomial.hom_eval₂, hφres, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
      intro h0
      exact htr ⟨Q.map (residue ↥A), hQ, h0⟩
    obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hzres
    exact ⟨u, by rw [hu]; exact hzval⟩

  have hinv : ∀ u : (↥R.integers)ˣ, (((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))⁻¹ ∈ R.integers := by
    intro u
    have h1 : ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) * (((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = 1 := by
      rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
    rw [inv_eq_of_mul_eq_one_right h1]
    exact ((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers).2
  have hne : ∀ u : (↥R.integers)ˣ, ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) ≠ 0 := by
    intro u h0
    exact u.ne_zero (Subtype.ext h0)
  have half : ∀ (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
      (h : ∀ Q : Polynomial ↥A, Q.map (residue ↥A) ≠ 0 →
        ∃ u : (↥R.integers)ˣ, ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = Polynomial.aeval t (Q.map A.subtype))
      (r₀ s₀ : Polynomial ↥A) (c d : (AlgebraicClosure ℚ)),
      r₀.map (residue ↥A) ≠ 0 → s₀.map (residue ↥A) ≠ 0 → d ≠ 0 →
      (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) c * Polynomial.aeval t (r₀.map A.subtype) /
          (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) d * Polynomial.aeval t (s₀.map A.subtype)) ∈ R.integers ↔ c / d ∈ A) := by
    intro t h r₀ s₀ c d hr hs hd
    obtain ⟨u, hu⟩ := h r₀ hr
    obtain ⟨v, hv⟩ := h s₀ hs
    rw [← hu, ← hv, ← R.algebraMap_mem_iff (c / d), mul_div_mul_comm, ← map_div₀]
    have key : ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) / ((v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) *
        (((v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) * (((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))⁻¹) = 1 := by
      field_simp [hne u, hne v]
    constructor
    · intro hmem
      rw [show algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (c / d) = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (c / d) *
          (((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) / ((v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) *
            (((v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) * (((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))⁻¹) by rw [mul_assoc, key, mul_one]]
      exact mul_mem hmem (mul_mem (v : ↥R.integers).2 (hinv u))
    · intro hmem
      rw [div_eq_mul_inv ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) ((v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))]
      exact mul_mem hmem (mul_mem (u : ↥R.integers).2 (hinv v))
  have htrace : ∀ (t₁ t₂ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
      (h₁ : ∀ Q : Polynomial ↥A, Q.map (residue ↥A) ≠ 0 →
        ∃ u : (↥R.integers)ˣ, ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = Polynomial.aeval t₁ (Q.map A.subtype))
      (h₂ : ∀ Q : Polynomial ↥A, Q.map (residue ↥A) ≠ 0 →
        ∃ u : (↥R.integers)ˣ, ((u : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = Polynomial.aeval t₂ (Q.map A.subtype))
      (r s : Polynomial (AlgebraicClosure ℚ)),
      (Polynomial.aeval t₁ r / Polynomial.aeval t₁ s ∈ R.integers ↔
        Polynomial.aeval t₂ r / Polynomial.aeval t₂ s ∈ R.integers) := by
    intro t₁ t₂ h₁ h₂ r s
    by_cases hr : r = 0
    · simp [hr]
    by_cases hs : s = 0
    · simp [hs]
    obtain ⟨r₀, c, hc, hrc, hr0⟩ :=
      ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero A r hr
    obtain ⟨s₀, d, hd, hsd, hs0⟩ :=
      ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero A s hs
    have hr' : r = Polynomial.C c * r₀.map A.subtype := by
      rw [hrc, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
    have hs' : s = Polynomial.C d * s₀.map A.subtype := by
      rw [hsd, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hd, Polynomial.C_1, one_mul]
    have e : ∀ t : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)), Polynomial.aeval t r / Polynomial.aeval t s =
        algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) c * Polynomial.aeval t (r₀.map A.subtype) /
          (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) d * Polynomial.aeval t (s₀.map A.subtype)) := by
      intro t
      rw [hr', hs', map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C]
    rw [e t₁, e t₂, half t₁ h₁ r₀ s₀ c d hr0 hs0 hd, half t₂ h₂ r₀ s₀ c d hr0 hs0 hd]

  obtain ⟨-, hfd⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) Γ hT j hj
  haveI := hfd
  obtain ⟨-, hle⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Unit => ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) (fun _ => R) (fun a b _ => Subsingleton.elim a b)
    (j : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (fun _ => hjO) (fun _ => htrj)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hle
  set Γ' : Subgroup SL(2, ℤ) :=
    CohCarrier.GammaH N (H ⊔ Subgroup.zpowers (-1)) with hΓ'def
  have hΓ' : Γ ≤ Γ' := by
    rw [hΓdef]
    exact ModularCurve.GammaH_mono le_sup_left
  have hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ := by
    rw [hΓdef]
    exact fun γ hγ => mem_or_neg_mem_gammaH_of_mem_gammaH_sup _ γ hγ
  haveI hΓ'fi : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΓ'
  have hlow : Γ'.index ≤
      Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({R.residue ⟨j, hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) := by
    subst hΓdef
    exact ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField N
      H hpN A hA (R.residue ⟨j, hjO⟩) hjres
  have hup := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) Γ hT Γ' hΓ'
    hneg j hj
  have hdeg : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(j : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) =
      Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({R.residue ⟨j, hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    le_antisymm (hup.trans hlow) hle
  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({R.residue ⟨j, hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hΓ'fi.index_ne_zero) hlow

  have hV := AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨j, hjO⟩ htrj hfin hdeg
    (R.integers.comap (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))).toAlgHom.toRingHom) (by
      intro e he
      change e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {j} at he
      rw [IntermediateField.mem_adjoin_simple_iff] at he
      obtain ⟨r, s, rfl⟩ := he
      rw [ValuationSubring.mem_comap]
      change w (Polynomial.aeval j r / Polynomial.aeval j s) ∈ R.integers ↔ _
      rw [map_div₀, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hwj]
      exact htrace jm j (hunit jm hjmO htrjm) (hunit j hjO htrj) r s)
  intro f
  have h1 : f ∈ R.integers.comap (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))).toAlgHom.toRingHom ↔ f ∈ R.integers := by rw [hV]
  rw [ValuationSubring.mem_comap] at h1
  exact h1

end S_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime (solution)
