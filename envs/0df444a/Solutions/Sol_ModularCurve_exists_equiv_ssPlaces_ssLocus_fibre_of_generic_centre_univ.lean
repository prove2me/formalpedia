-- Prove2me | solution 1 for ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4e0e7688-94da-568d-9377-b601fe3eb0a8

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
import Theorems.Thm_WeierstrassCurve_bijective_reduceHom_restrict_torsion
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_natDegree_fibrePoly
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_WeierstrassCurve_map_veluQuotientOfSums
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_eq_veluQuotient_of_odd
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_TatePoint_fullKernelDiscAt_univ
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
import Theorems.Thm_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_ModularCurve_TatePoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply HahnSeries.ramScale_apply"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.ModularCurve IsLocalRing"

set_option autoImplicit false

universe u

open Polynomial in

noncomputable section

p2m_open "WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet ssLocus mem_ssLocus_iff Gamma0Pair ModuliPoint ModuliPoint.j Point.heq_zero Point.heq_some Point.heq_nsmul ModuliPoint.map ssPlaces jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace ord_sub_evalAt_pos_of_isRational ofPowerSeries_coeff_of_neg dedekindPsi ModularPolynomialData jqModC jqNModC modularFunctionFieldC fibrePoly arithFrobC baseAut_arithFrobC_apply arithFrobC_smul_jq coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single qTwist qTwist_one_apply dedekindPsi_pos natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero pow_q_sq_eq_self_of_mem_ssJSet eq_zero_of_mem_ssJSet_two eq_zero_of_mem_ssJSet_three ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental isSeparable_jqNModC_of_natCast_ne_zero natDegree_fibrePoly place_deg_eq_one_of_isAlgClosed finite_setOf_ord_jGeomGen_sub_pos ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero exists_phiIrreducible ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ"
namespace FullKernelQuotientRoots
p2m_open "ModularCurve"

section SummingSet

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

private theorem mem_oddOrderSummingSet_pred_iff {Q : W.toAffine.Point} {N : ℕ} (hQ : addOrderOf Q = N)
    (hN : 0 < N) (P : F × F) :
    P ∈ W.oddOrderSummingSet Q (N - 1) ↔
      ∃ R ∈ AddSubgroup.zmultiples Q, R ≠ 0 ∧ R.coordsOrZero = P := by
  classical
  have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (hQ ▸ hN)
  rw [mem_oddOrderSummingSet]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    exact ⟨k • Q, AddSubgroup.nsmul_mem_zmultiples Q k,
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega), rfl⟩
  · rintro ⟨R, hR, hR0, rfl⟩
    rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hR
    obtain ⟨k, hk, rfl⟩ := hR
    rw [Finset.mem_range, hQ] at hk
    refine ⟨k, ?_, by omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (zero_nsmul Q) hR0
    · exact hk0

private theorem oddOrderSummingSet_pred_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ} [NeZero N]
    (hQ : addOrderOf Q = N) (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.oddOrderSummingSet Q (N - 1) = W.oddOrderSummingSet Q' (N - 1) := by
  have hQ' : addOrderOf Q' = N := by
    rw [← Nat.card_zmultiples, ← h, Nat.card_zmultiples, hQ]
  ext P
  rw [mem_oddOrderSummingSet_pred_iff hQ (NeZero.pos N),
    mem_oddOrderSummingSet_pred_iff hQ' (NeZero.pos N), h]

private theorem fullKernelQuotient_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ} [NeZero N]
    (hQ : addOrderOf Q = N) (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  rw [fullKernelQuotient, fullKernelQuotient, oddOrderSummingSet_pred_eq_of_zmultiples_eq hQ h]

end SummingSet

section MapPointHom

variable {F F' : Type u} [Field F] [Field F'] (f : F →+* F')

private theorem j_congr {R : Type u} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂)
    {inst₁ : W₁.IsElliptic} {inst₂ : W₂.IsElliptic} :
    @WeierstrassCurve.j R _ W₁ inst₁ = @WeierstrassCurve.j R _ W₂ inst₂ := by
  subst h
  rfl

private theorem fibrePoly_map (Φ : Polynomial (Polynomial ℤ)) (a : F) :
    fibrePoly Φ (f a) = (fibrePoly Φ a).map f := by
  unfold ModularCurve.fibrePoly
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private theorem map_veluGx (W : WeierstrassCurve F) (x y : F) :
    f (W.veluGx x y) = (W.map f).veluGx (f x) (f y) := by
  simp only [WeierstrassCurve.veluGx, map_sub, map_add, map_mul, map_pow, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

private theorem map_veluGy (W : WeierstrassCurve F) (x y : F) :
    f (W.veluGy x y) = (W.map f).veluGy (f x) (f y) := by
  simp only [WeierstrassCurve.veluGy, map_neg, map_add, map_mul, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

variable [DecidableEq F] [DecidableEq F']

private theorem addOrderOf_mapPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) :
    addOrderOf (mapPointHom f Q) = addOrderOf Q :=
  addOrderOf_injective (mapPointHom f) (fun _ _ h => mapPoint_injective f h) Q

private theorem coordsOrZero_mapPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) :
    (mapPointHom f Q).coordsOrZero = Prod.map f f Q.coordsOrZero := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact Prod.ext (map_zero f).symm (map_zero f).symm
  · rfl

private theorem oddOrderSummingSet_mapPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (mapPointHom f Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  unfold WeierstrassCurve.oddOrderSummingSet
  rw [Finset.image_image]
  congr 1
  funext k
  rw [Function.comp_apply, ← map_nsmul (mapPointHom f) k Q, coordsOrZero_mapPointHom]

private theorem map_fullKernelQuotient {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) :
    (W.fullKernelQuotient Q N).map f = (W.map f).fullKernelQuotient (mapPointHom f Q) N := by
  have hinj : ∀ P ∈ W.oddOrderSummingSet Q (N - 1), ∀ P' ∈ W.oddOrderSummingSet Q (N - 1),
      Prod.map f f P = Prod.map f f P' → P = P' :=
    fun P _ P' _ h => (f.injective.prodMap f.injective) h
  rw [fullKernelQuotient, fullKernelQuotient, WeierstrassCurve.map_veluQuotientOfSums,
    oddOrderSummingSet_mapPointHom, Finset.sum_image hinj, Finset.sum_image hinj, map_sum, map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun P _ => ?_
  · show f (W.veluGx P.1 P.2) = (W.map f).veluGx (f P.1) (f P.2)
    exact map_veluGx f W P.1 P.2
  · show f (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2) =
      f P.1 * (W.map f).veluGx (f P.1) (f P.2) - f P.2 * (W.map f).veluGy (f P.1) (f P.2)
    rw [map_sub, map_mul, map_mul, map_veluGx, map_veluGy]

private theorem fullKernelQuotient_mapPointHom_Δ {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) :
    ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ = f (W.fullKernelQuotient Q N).Δ := by
  rw [← map_fullKernelQuotient, WeierstrassCurve.map_Δ]

private theorem fullKernelQuotient_mapPointHom_Δ_ne_zero_iff {W : WeierstrassCurve F} (Q : W.toAffine.Point)
    (N : ℕ) :
    ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0 ↔ (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rw [fullKernelQuotient_mapPointHom_Δ, map_ne_zero f]

private theorem fullKernelQuotient_mapPointHom_j {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0) :
    @WeierstrassCurve.j F' _ ((W.map f).fullKernelQuotient (mapPointHom f Q) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ =
      f (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  exact (j_congr (map_fullKernelQuotient f Q N).symm).trans ((W.fullKernelQuotient Q N).map_j f)

end MapPointHom

section Disc

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

private theorem fullKernelQuotient_Δ_ne_zero_of_odd {N : ℕ} (hN : Odd N) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rw [W.fullKernelQuotient_eq_veluQuotient_of_odd Q hN hQ]
  refine W.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq ((N - 1) / 2) Q ?_
  rw [hQ]
  obtain ⟨m, rfl⟩ := hN
  omega

private theorem fullKernelQuotient_Δ_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) {N : ℕ} [NeZero N]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  classical
  let f : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := fun h =>
    h2 (f.injective (by rw [map_ofNat, map_zero]; exact h))
  have key := ModularCurve.TatePoint.fullKernelDiscAt_univ N h2' (W.map f) (mapPointHom f Q)
    (by rw [addOrderOf_mapPointHom, hQ])
  exact (fullKernelQuotient_mapPointHom_Δ_ne_zero_iff f Q N).mp key

private theorem fullKernelQuotient_Δ_ne_zero {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rcases Nat.even_or_odd N with hev | hodd
  · refine fullKernelQuotient_Δ_ne_zero_of_two_ne_zero W (fun h2 => hN ?_) Q hQ
    obtain ⟨m, rfl⟩ := hev
    rw [Nat.cast_add, ← two_mul, h2, zero_mul]
  · exact fullKernelQuotient_Δ_ne_zero_of_odd W hodd Q hQ

private theorem isElliptic_fullKernelQuotient {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)⟩

end Disc

section Root

variable {F M : Type u} [Field F] [DecidableEq F] [Field M] [DecidableEq M] [IsAlgClosed M]
  (f : F →+* M)

private theorem isRoot_fibrePoly_j_fullKernelQuotient
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Qfam : ι → (W.map f).toAffine.Point) (hQfam : ∀ i, addOrderOf (Qfam i) = N)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Qfam i))
    (i₀ : ι) (hi₀ : AddSubgroup.zmultiples (Qfam i₀) = AddSubgroup.zmultiples (mapPointHom f Q)) :
    (fibrePoly data.Φ W.j).IsRoot
      (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)⟩) := by
  have hNM : (N : M) ≠ 0 := fun h => hN (f.injective (by rw [map_natCast, map_zero]; exact h))
  have hΔfam : ∀ i, ((W.map f).fullKernelQuotient (Qfam i) N).Δ ≠ 0 := fun i =>
    fullKernelQuotient_Δ_ne_zero (W.map f) hNM (Qfam i) (hQfam i)

  have hprod :=
    ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
      h0 hNM data (W.map f) hι Qfam hQfam hinj hΔfam

  have hrootM : (fibrePoly data.Φ (W.map f).j).IsRoot
      (@WeierstrassCurve.j M _ ((W.map f).fullKernelQuotient (Qfam i₀) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔfam i₀)⟩) := by
    rw [hprod, Polynomial.isRoot_prod]
    exact ⟨i₀, Finset.mem_univ i₀, by
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]⟩

  have hΔ' : ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0 :=
    (fullKernelQuotient_mapPointHom_Δ_ne_zero_iff f Q N).mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)
  have hjM : @WeierstrassCurve.j M _ ((W.map f).fullKernelQuotient (Qfam i₀) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔfam i₀)⟩ =
      f (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)⟩) :=
    (j_congr (fullKernelQuotient_eq_of_zmultiples_eq (hQfam i₀) hi₀)).trans
      (fullKernelQuotient_mapPointHom_j f Q N (fullKernelQuotient_Δ_ne_zero W hN Q hQ) hΔ')
  rw [hjM, WeierstrassCurve.map_j, fibrePoly_map] at hrootM
  exact hrootM.of_map f.injective

omit [IsAlgClosed M] in

private theorem zmultiples_mapPointHom_injective {W : WeierstrassCurve F} {ι : Type*} (Q : ι → W.toAffine.Point)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i)) :
    Function.Injective fun i => AddSubgroup.zmultiples (mapPointHom f (Q i)) := by
  intro i j h
  apply hinj
  have h' : (AddSubgroup.zmultiples (Q i)).map (mapPointHom f) =
      (AddSubgroup.zmultiples (Q j)).map (mapPointHom f) := by
    simpa only [AddMonoidHom.map_zmultiples] using h
  exact AddSubgroup.map_injective (fun _ _ h => mapPoint_injective f h) h'

private theorem isRoot_fibrePoly_j_fullKernelQuotient_of_family
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) (i : ι) :
    (fibrePoly data.Φ W.j).IsRoot
      (@WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) := by
  classical
  exact isRoot_fibrePoly_j_fullKernelQuotient (algebraMap F (AlgebraicClosure F)) h0 hN data W (Q i)
    (hQ i) hι (fun k => mapPointHom (algebraMap F (AlgebraicClosure F)) (Q k))
    (fun k => by rw [addOrderOf_mapPointHom, hQ]) (zmultiples_mapPointHom_injective _ Q hQinj) i rfl

end Root

section BaseChange

variable {F L : Type u} [Field F] [DecidableEq F] [Field L] [DecidableEq L] [Algebra F L]

private theorem mapPointHom_algebraMap_eq_pointMap {W : WeierstrassCurve F} (P : W.toAffine.Point) :
    mapPointHom (algebraMap F L) P =
      Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point) := by
  cases P <;> rfl

private theorem baseChange_fullKernelQuotient {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ) :
    (W.fullKernelQuotient P N)⁄L =
      (W⁄L).fullKernelQuotient (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N := by
  rw [← mapPointHom_algebraMap_eq_pointMap]
  exact map_fullKernelQuotient (algebraMap F L) P N

private theorem baseChange_fullKernelQuotient_j {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient P N).Δ ≠ 0)
    (hΔ' : ((W⁄L).fullKernelQuotient
      (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N).Δ ≠ 0) :
    @WeierstrassCurve.j L _ ((W⁄L).fullKernelQuotient
        (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ =
      algebraMap F L (@WeierstrassCurve.j F _ (W.fullKernelQuotient P N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  haveI : (W.fullKernelQuotient P N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  exact (j_congr (baseChange_fullKernelQuotient P N).symm).trans
    ((W.fullKernelQuotient P N).map_j (algebraMap F L))

private theorem baseChange_fullKernelQuotient_Δ_ne_zero_iff {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ) :
    ((W⁄L).fullKernelQuotient
        (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N).Δ ≠ 0 ↔
      (W.fullKernelQuotient P N).Δ ≠ 0 := by
  rw [← mapPointHom_algebraMap_eq_pointMap]
  exact fullKernelQuotient_mapPointHom_Δ_ne_zero_iff (algebraMap F L) P N

end BaseChange

section Card

variable {F : Type u} [Field F] [DecidableEq F]

private theorem fibrePoly_j_eq_prod_fullKernelQuotient_j_of_family
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical
  let f : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hNM : (N : AlgebraicClosure F) ≠ 0 := fun h =>
    hN (f.injective (by rw [map_natCast, map_zero]; exact h))
  have hΔ' : ∀ i, ((W.map f).fullKernelQuotient (mapPointHom f (Q i)) N).Δ ≠ 0 := fun i =>
    (fullKernelQuotient_mapPointHom_Δ_ne_zero_iff f (Q i) N).mpr (hΔ i)
  have hprod :=
    ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
      h0 hNM data (W.map f) hι (fun i => mapPointHom f (Q i))
      (fun i => by rw [addOrderOf_mapPointHom, hQ]) (zmultiples_mapPointHom_injective f Q hQinj) hΔ'
  apply Polynomial.map_injective f f.injective
  rw [← fibrePoly_map, ← WeierstrassCurve.map_j, hprod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    fullKernelQuotient_mapPointHom_j f (Q i) N (hΔ i) (hΔ' i)]

private theorem card_roots_toFinset_fibrePoly_j
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0)
    (hjinj : Function.Injective fun i =>
      @WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) :
    (fibrePoly data.Φ W.j).roots.toFinset.card = dedekindPsi N := by
  rw [fibrePoly_j_eq_prod_fullKernelQuotient_j_of_family h0 hN data W hι Q hQ hQinj hΔ]
  have hprod : (∏ i, (X - C (@WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N)
      ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))) =
      ((Finset.univ.val.map fun i => @WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩).map fun a => X - C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  show (Finset.univ.image fun i => @WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N)
    ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩).card = _
  rw [Finset.card_image_of_injective _ hjinj, Finset.card_univ, hι]

private theorem card_roots_toFinset_phiAt
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic] (x₀ : F) (hx : W.j = x₀)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0)
    (hjinj : Function.Injective fun i =>
      @WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x₀)).roots.toFinset.card =
      dedekindPsi N := by
  subst hx
  exact card_roots_toFinset_fibrePoly_j h0 hN data W hι Q hQ hQinj hΔ hjinj

end Card

end ModularCurve.FullKernelQuotientRoots

end

noncomputable section

p2m_open "Polynomial WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine AddSubgroup"

namespace FibrePolySeparable

private theorem separable_fibrePoly_of_transcendental {K₀ F : Type u} [Field K₀] [Field F] [Algebra K₀ F]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hN : (N : F) ≠ 0) (jv : F) (hj : Transcendental K₀ jv) :
    (ModularCurve.fibrePoly data.Φ jv).Separable := by
  have hNK₀ : (N : K₀) ≠ 0 := by
    intro h
    apply hN
    rw [← map_natCast (algebraMap K₀ F) N, h, map_zero]
  have hsep :=
    ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K₀ N data hNK₀
  have hinj : Function.Injective (Polynomial.aeval jv : Polynomial K₀ →ₐ[K₀] F) :=
    transcendental_iff_injective.mp hj
  let φ : RatFunc K₀ →+* F :=
    IsFractionRing.lift (g := (Polynomial.aeval jv : Polynomial K₀ →ₐ[K₀] F).toRingHom) hinj
  have hcoh : (φ.comp (algebraMap (Polynomial K₀) (RatFunc K₀))).comp
      (Polynomial.mapRingHom (Int.castRingHom K₀)) =
      Polynomial.eval₂RingHom (Int.castRingHom F) jv := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [IsFractionRing.lift_algebraMap]
    simp
  have hfib : ModularCurve.fibrePoly data.Φ jv =
      ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K₀))).map
        (algebraMap (Polynomial K₀) (RatFunc K₀))).map φ := by
    rw [ModularCurve.fibrePoly, Polynomial.map_map, Polynomial.map_map, hcoh]
  rw [hfib]
  exact hsep.map

private theorem injective_of_separable_prod {K : Type u} [Field K] {ι : Type*} [Fintype ι]
    (c : ι → K) (p : Polynomial K) (hsep : p.Separable)
    (hp : p = ∏ i, (X - C (c i))) : Function.Injective c := by
  classical
  intro a b hab
  by_contra hne
  have hbmem : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ b⟩
  have hdvd : (X - C (c a)) * (X - C (c a)) ∣ p := by
    refine ⟨∏ i ∈ (Finset.univ.erase a).erase b, (X - C (c i)), ?_⟩
    rw [hp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) _ hbmem, hab]
    ring
  exact Polynomial.not_isUnit_X_sub_C (c a) (hsep.squarefree _ hdvd)

private theorem fibrePoly_map {k l : Type u} [Field k] [Field l] (f : k →+* l)
    (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    (ModularCurve.fibrePoly Φ a).map f = ModularCurve.fibrePoly Φ (f a) := by
  rw [ModularCurve.fibrePoly, ModularCurve.fibrePoly, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp

private theorem separable_fibrePoly_algebraMap_of_transcendental {K₀ F L : Type u} [Field K₀] [Field F]
    [Field L] [Algebra K₀ F] [Algebra F L] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hN : (N : F) ≠ 0) (jv : F)
    (hj : Transcendental K₀ jv) :
    (ModularCurve.fibrePoly data.Φ (algebraMap F L jv)).Separable := by
  rw [← fibrePoly_map (algebraMap F L) data.Φ jv]
  exact (separable_fibrePoly_of_transcendental N data hN jv hj).map

private theorem injective_of_separable_of_map_prod {F L : Type u} [Field F] [Field L] (emb : F →+* L)
    {ι : Type*} [Fintype ι] (y : ι → F) (z : ι → L) (p : Polynomial F)
    (hsep : p.Separable)
    (hprod : p.map emb = ∏ i, (X - C (z i)))
    (hcompat : ∀ i, emb (y i) = z i) :
    Function.Injective y := by
  have hinj : Function.Injective z :=
    injective_of_separable_prod z (p.map emb) (hsep.map) hprod
  intro a b hab
  exact hinj (by rw [← hcompat a, ← hcompat b, hab])

private theorem card_roots_toFinset_eq_of_injective_family {F : Type u} [Field F] [DecidableEq F]
    (p : Polynomial F) (hp : p ≠ 0) {ι : Type*} [Fintype ι] (y : ι → F)
    (hinj : Function.Injective y) (hroot : ∀ i, p.IsRoot (y i)) {m : ℕ}
    (hm : Fintype.card ι = m) (hdeg : p.natDegree = m) :
    p.roots.toFinset.card = m := by
  refine le_antisymm ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' p).trans_eq hdeg)) ?_
  have himg : Finset.univ.image y ⊆ p.roots.toFinset := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp, hroot i⟩)
  calc m = Fintype.card ι := hm.symm
    _ = (Finset.univ.image y).card := (Finset.card_image_of_injective Finset.univ hinj).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card himg

end FibrePolySeparable

end

noncomputable section

open Polynomial

namespace FibrePolyRootCount

private theorem bijective_root_family_of_prod {F : Type u} [Field F] {ι : Type*} [Fintype ι]
    (y : ι → F) (p : Polynomial F) (hp : p = ∏ i, (X - C (y i)))
    (hinj : Function.Injective y) :
    ∃ hroot : ∀ i, p.IsRoot (y i),
      Function.Bijective (fun i => (⟨y i, hroot i⟩ : {z : F // p.IsRoot z})) := by
  have heval : ∀ z : F, p.IsRoot z ↔ ∃ i, y i = z := by
    intro z
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C, sub_eq_zero]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  refine ⟨fun i => (heval _).mpr ⟨i, rfl⟩, ?_, ?_⟩
  · intro i i' h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    obtain ⟨i, rfl⟩ := (heval z).mp hz
    exact ⟨i, rfl⟩

private theorem natCard_moduliPoint_j_eq_eq_natCard_roots {L : Type u} [Field L] [DecidableEq L]
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N) (j₀ : L)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ModularCurve.dedekindPsi N)
    (y : ι → L) (hp : ModularCurve.fibrePoly data.Φ j₀ = ∏ i, (X - C (y i)))
    (hinj : Function.Injective y)
    (hmoduli : Nat.card {x : ModularCurve.ModuliPoint N L // ModularCurve.ModuliPoint.j x = j₀}
      = ModularCurve.dedekindPsi N) :
    Nat.card {x : ModularCurve.ModuliPoint N L // ModularCurve.ModuliPoint.j x = j₀}
      = Nat.card {z : L // (ModularCurve.fibrePoly data.Φ j₀).IsRoot z} := by
  obtain ⟨hroot, hbij⟩ := bijective_root_family_of_prod y _ hp hinj
  rw [hmoduli, ← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, hι]

end FibrePolyRootCount

end

noncomputable section

p2m_open "AlgebraicCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine PowerSeries IsLocalRing Polynomial"

namespace LaurentIntegerRing

section Transport

variable {R S : Type*} [CommRing R] [CommRing S]

private lemma mem_maximalIdeal_map {e : R ≃+* S} [IsLocalRing R] [IsLocalRing S] {r : R}
    (hr : r ∈ maximalIdeal R) : e r ∈ maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  intro hu
  apply hr
  have h := hu.map e.symm.toRingHom
  simpa using h

private theorem henselianLocalRing_of_ringEquiv [HenselianLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : HenselianLocalRing S := by
  constructor
  intro f hf a₀ h₁ h₂
  have hcomp : (f.map (e.symm : S →+* R)).map (e : R →+* S) = f := by
    rw [Polynomial.map_map, show ((e : R →+* S).comp (e.symm : S →+* R)) = RingHom.id S from
      RingHom.ext fun s => e.apply_symm_apply s, Polynomial.map_id]
  have h₁' : (f.map (e.symm : S →+* R)).eval ((e.symm : S →+* R) a₀) ∈ maximalIdeal R := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact mem_maximalIdeal_map (e := e.symm) h₁
  have h₂' : IsUnit ((derivative (f.map (e.symm : S →+* R))).eval
      ((e.symm : S →+* R) a₀)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact h₂.map e.symm.toRingHom
  obtain ⟨b, hroot, hb⟩ := HenselianLocalRing.is_henselian
    (f.map (e.symm : S →+* R)) (hf.map _) ((e.symm : S →+* R) a₀) h₁' h₂'
  refine ⟨(e : R →+* S) b, ?_, ?_⟩
  · rw [← hcomp, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      hroot.eq_zero, map_zero]
  · have h := mem_maximalIdeal_map (e := e) hb
    simpa [map_sub, RingEquiv.coe_toRingHom] using h

private theorem henselianLocalRing_of_henselianRing' {T : Type*} [CommRing T] [IsLocalRing T]
    (h : HenselianRing T (maximalIdeal T)) : HenselianLocalRing T := by
  constructor
  intro f hf a₀ h₁ h₂
  exact h.is_henselian f hf a₀ h₁ ((Ideal.Quotient.mk _).isUnit_map h₂)

end Transport

private scoped instance instHenselianLocalRingPowerSeries (k : Type*) [Field k] :
    HenselianLocalRing (PowerSeries k) := by
  refine henselianLocalRing_of_henselianRing' ?_
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

section Laurent

variable (K : Type*) [Field K]

private noncomputable def laurentIntegers : ValuationSubring (LaurentSeries K) :=
  (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).valuationSubring

private theorem mem_laurentIntegers_iff {f : LaurentSeries K} :
    f ∈ laurentIntegers K ↔ ∃ p : PowerSeries K, (p : LaurentSeries K) = f := by
  rw [show (f ∈ laurentIntegers K) ↔
      Valued.v f ≤ (1 : WithZero (Multiplicative ℤ)) from Iff.rfl,
    LaurentSeries.val_le_one_iff_eq_coe]

private noncomputable def powerSeriesEquivLaurentIntegers :
    PowerSeries K ≃+* (laurentIntegers K) := by
  refine RingEquiv.ofBijective
    (((HahnSeries.ofPowerSeries ℤ K : PowerSeries K →+* LaurentSeries K)).codRestrict
      (laurentIntegers K).toSubring
      (fun p => (mem_laurentIntegers_iff K).mpr ⟨p, rfl⟩)) ⟨?_, ?_⟩
  · intro p q h
    exact HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h)
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp⟩ := (mem_laurentIntegers_iff K).mp hf
    exact ⟨p, Subtype.ext hp⟩

private scoped instance : HenselianLocalRing (laurentIntegers K) :=
  henselianLocalRing_of_ringEquiv (powerSeriesEquivLaurentIntegers K)

end Laurent

section Residue

variable (K : Type*) [Field K]

private noncomputable def powerSeriesResidueEquiv :
    ResidueField (PowerSeries K) ≃+* K :=
  (Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (fun c => ⟨PowerSeries.C c, PowerSeries.constantCoeff_C c⟩))

private noncomputable def laurentIntegersResidueEquiv :
    ResidueField (laurentIntegers K) ≃+* K :=
  (ResidueField.mapEquiv (powerSeriesEquivLaurentIntegers K).symm).trans
    (powerSeriesResidueEquiv K)

private scoped instance [IsAlgClosed K] :
    IsAlgClosed (ResidueField (laurentIntegers K)) :=
  IsAlgClosed.of_ringEquiv _ _ (laurentIntegersResidueEquiv K).symm

end Residue

end LaurentIntegerRing
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing"

namespace GenericFibreCurve

private def famChar3 (K : Type u) [CommRing K] : WeierstrassCurve (PowerSeries K) :=
  ⟨0, PowerSeries.X, 0, 1, 0⟩

private def genFibre {K : Type u} [CommRing K] (W : WeierstrassCurve (PowerSeries K)) :
    WeierstrassCurve (LaurentSeries K) :=
  W.map (algebraMap (PowerSeries K) (LaurentSeries K))

private scoped instance genFibre.instIsElliptic {K : Type u} [Field K]
    (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] : (genFibre W).IsElliptic :=
  inferInstanceAs (W.map (algebraMap (PowerSeries K) (LaurentSeries K))).IsElliptic

p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre"
private theorem j_genFibre {K : Type u} [Field K] (W : WeierstrassCurve (PowerSeries K))
    [W.IsElliptic] :
    (genFibre W).j = algebraMap (PowerSeries K) (LaurentSeries K) W.j :=
  W.map_j (algebraMap (PowerSeries K) (LaurentSeries K))

private theorem algebraMap_laurentSeries_factor {K : Type u} [Field K] (c : K) :
    algebraMap K (LaurentSeries K) c
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.C (R := K) c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, LaurentSeries.coe_algebraMap,
    HahnSeries.ofPowerSeries_C]
  rfl

section LaurentSeriesOrder

variable {K : Type u} [Field K]

private theorem algebraMap_laurentSeries_ne_zero {p : PowerSeries K} (hp : p ≠ 0) :
    algebraMap (PowerSeries K) (LaurentSeries K) p ≠ 0 := by
  rw [LaurentSeries.coe_algebraMap]
  exact fun h => hp (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

private theorem order_algebraMap_laurentSeries_eq (n : ℕ) {p : PowerSeries K}
    (h0 : ∀ k, k < n → PowerSeries.coeff k p = 0)
    (hn : PowerSeries.coeff n p ≠ 0) :
    (algebraMap (PowerSeries K) (LaurentSeries K) p).order = n := by
  rw [LaurentSeries.coe_algebraMap]
  have hcn : (HahnSeries.ofPowerSeries ℤ K p).coeff (n : ℤ) = PowerSeries.coeff n p := by
    have hc : (HahnSeries.ofPowerSeries ℤ K p).coeff (n : ℤ)
        = if (n : ℤ) < 0 then 0 else PowerSeries.coeff (n : ℤ).natAbs p :=
      PowerSeries.coeff_coe (f := p) (n : ℤ)
    rw [hc, if_neg (not_lt.mpr (Int.natCast_nonneg n)), Int.natAbs_natCast]
  have hne : HahnSeries.ofPowerSeries ℤ K p ≠ 0 := by
    intro h
    apply hn
    rw [← hcn, h]
    simp
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [hcn]; exact hn)
  · rw [HahnSeries.le_order_iff_forall hne]
    intro j hj
    have hc : (HahnSeries.ofPowerSeries ℤ K p).coeff j
        = if j < 0 then 0 else PowerSeries.coeff j.natAbs p :=
      PowerSeries.coeff_coe (f := p) j
    rw [hc]
    split_ifs with hj0
    · rfl
    · refine h0 j.natAbs ?_
      have h1 : (j.natAbs : ℤ) < (n : ℤ) := by
        rw [Int.natAbs_of_nonneg (not_lt.mp hj0)]
        exact hj
      exact_mod_cast h1

private theorem order_algebraMap_laurentSeries_eq_zero {p : PowerSeries K}
    (hp : PowerSeries.constantCoeff (R := K) p ≠ 0) :
    (algebraMap (PowerSeries K) (LaurentSeries K) p).order = 0 := by
  have h := order_algebraMap_laurentSeries_eq 0 (p := p)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hp)
  exact_mod_cast h

end LaurentSeriesOrder
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre"

end GenericFibreCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet ssLocus mem_ssLocus_iff Gamma0Pair ModuliPoint ModuliPoint.j Point.heq_zero Point.heq_some Point.heq_nsmul ModuliPoint.map ssPlaces jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace ord_sub_evalAt_pos_of_isRational ofPowerSeries_coeff_of_neg dedekindPsi ModularPolynomialData jqModC jqNModC modularFunctionFieldC fibrePoly arithFrobC baseAut_arithFrobC_apply arithFrobC_smul_jq coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single qTwist qTwist_one_apply dedekindPsi_pos natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero pow_q_sq_eq_self_of_mem_ssJSet eq_zero_of_mem_ssJSet_two eq_zero_of_mem_ssJSet_three ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental isSeparable_jqNModC_of_natCast_ne_zero natDegree_fibrePoly place_deg_eq_one_of_isAlgClosed finite_setOf_ord_jGeomGen_sub_pos ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero exists_phiIrreducible ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ"
namespace GenericCentreFibre
p2m_open "ModularCurve"

section PlaceAction

open scoped Pointwise

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

private theorem isRational_smul (g : SemilinearAut K F) (v : Place K F) (hv : v.IsRational) :
    (g • v).IsRational := by
  intro y
  obtain ⟨x, rfl⟩ := (SemilinearAut.smulResidueRingEquiv g v).surjective y
  obtain ⟨a, rfl⟩ := hv x
  exact ⟨SemilinearAut.baseAut g a, (SemilinearAut.smulResidueRingEquiv_algebraMap g v a).symm⟩

private theorem smul_mem_toValuationSubring_smul (g : SemilinearAut K F) (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : g • f ∈ (g • v).toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
  exact hf

private theorem evalAt_smul (g : SemilinearAut K F) (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  have hv' : (g • v).IsRational := isRational_smul g v hv
  have hgf : g • f ∈ (g • v).toValuationSubring := smul_mem_toValuationSubring_smul g v hf
  apply (algebraMap K (g • v).ResidueField).injective
  rw [(g • v).algebraMap_evalAt hv' hgf, ← SemilinearAut.smulResidueRingEquiv_algebraMap,
    v.algebraMap_evalAt hv hf]
  show _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 1

end PlaceAction
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

private def part {α β : Type u} (f : α → β) : α ≃ Σ b : β, {a : α // f a = b} where
  toFun a := ⟨f a, a, rfl⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv := by rintro ⟨b, a, rfl⟩; rfl

section ModuliOfCyclicSubgroup

variable {K : Type u} [Field K] [DecidableEq K]

p2m_open "WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine"

private def pairOf (W : WeierstrassCurve K) [W.IsElliptic] (g : W.toAffine.Point) {N : ℕ}
    (hg : addOrderOf g = N) : ModularCurve.Gamma0Pair N K :=
  ⟨W, ‹_›, g, hg⟩

private def moduliOf (W : WeierstrassCurve K) [W.IsElliptic] (g : W.toAffine.Point) {N : ℕ}
    (hg : addOrderOf g = N) : ModularCurve.ModuliPoint N K :=
  Quot.mk _ (pairOf W g hg)

private noncomputable def toModuli (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ)
    (C : {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g}) :
    {x : ModularCurve.ModuliPoint N K // ModularCurve.ModuliPoint.j x = W.j} :=
  ⟨moduliOf W C.2.choose C.2.choose_spec.1, rfl⟩

omit [DecidableEq K] in

private theorem heq_vcInvFun_one (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) W.toAffine P) P := by
  have h1 : ((1 : VariableChange K) • W).toAffine = W.toAffine := by rw [one_smul]
  cases P with
  | zero => exact Point.heq_zero h1
  | some x y h =>
    exact Point.heq_some h1 (by simp [vcXInv, VariableChange.one_def])
      (by simp [vcYInv, VariableChange.one_def])

private theorem exists_coprime_nsmul_eq_of_zmultiples_eq {N : ℕ} [NeZero N]
    {W : WeierstrassCurve K} {g g' : W.toAffine.Point}
    (hg : addOrderOf g = N) (hg' : addOrderOf g' = N)
    (h : AddSubgroup.zmultiples g = AddSubgroup.zmultiples g') :
    ∃ k : ℕ, k.Coprime N ∧ g' = k • g := by
  have hfin : IsOfFinAddOrder g := addOrderOf_pos_iff.mp (hg ▸ NeZero.pos N)
  have hmem : g' ∈ AddSubgroup.zmultiples g := h ▸ AddSubgroup.mem_zmultiples g'
  rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hmem
  obtain ⟨k, -, rfl⟩ := hmem
  refine ⟨k, ?_, rfl⟩
  have h2 : addOrderOf (k • g) = addOrderOf g / Nat.gcd (addOrderOf g) k :=
    IsOfFinAddOrder.addOrderOf_nsmul g k hfin
  rw [hg', hg] at h2
  have h3 := Nat.div_mul_cancel (Nat.gcd_dvd_left N k)
  rw [← h2] at h3
  have h4 : Nat.gcd N k = 1 :=
    Nat.eq_of_mul_eq_mul_left (NeZero.pos N) (h3.trans (mul_one N).symm)
  exact Nat.Coprime.symm h4

private theorem moduliOf_eq_of_zmultiples_eq {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [W.IsElliptic] {g g' : W.toAffine.Point} (hg : addOrderOf g = N) (hg' : addOrderOf g' = N)
    (h : AddSubgroup.zmultiples g = AddSubgroup.zmultiples g') :
    moduliOf W g hg = moduliOf W g' hg' := by
  obtain ⟨k, hk, rfl⟩ := exists_coprime_nsmul_eq_of_zmultiples_eq hg hg' h
  have h1 : ((1 : VariableChange K) • W).toAffine = W.toAffine := by rw [one_smul]
  exact Quot.sound ⟨1, one_smul _ W, k, hk, (Point.heq_nsmul h1 k (heq_vcInvFun_one W g)).symm⟩

private theorem toModuli_eq {N : ℕ} [NeZero N] (W : WeierstrassCurve K) [W.IsElliptic]
    (C : {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (g : W.toAffine.Point) (hg : addOrderOf g = N) (hC : C.1 = AddSubgroup.zmultiples g) :
    (toModuli W N C).1 = moduliOf W g hg :=
  moduliOf_eq_of_zmultiples_eq W _ hg (C.2.choose_spec.2.symm.trans hC)

private theorem addOrderOf_vcInvFun (γ : WeierstrassCurve.VariableChange K)
    (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    addOrderOf (Point.vcInvFun γ W.toAffine P) = addOrderOf P :=
  addOrderOf_injective
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))
    (Function.LeftInverse.injective Point.vcFun_rightInverse) P

private theorem toModuli_surjective [IsSepClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [NeZero N] : Function.Surjective (toModuli W N) := by
  rintro ⟨x, hx⟩
  obtain ⟨P, rfl⟩ := Quot.exists_rep x
  obtain ⟨W', hE', g', hg'⟩ := P
  haveI := hE'
  change W'.j = W.j at hx
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W' W hx
  subst hγ
  have hg : addOrderOf (Point.vcInvFun γ W'.toAffine g') = N :=
    (addOrderOf_vcInvFun γ W' g').trans hg'
  refine ⟨⟨AddSubgroup.zmultiples (Point.vcInvFun γ W'.toAffine g'), _, hg, rfl⟩,
    Subtype.ext ?_⟩
  rw [toModuli_eq (γ • W') _ (Point.vcInvFun γ W'.toAffine g') hg rfl]
  exact (Quot.sound ⟨γ, rfl, 1, Nat.coprime_one_left N, heq_of_eq (one_nsmul _).symm⟩).symm

private theorem toModuli_bijective_of_natCard_le [IsSepClosed K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ) [NeZero N]
    [Finite {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g}]
    (hle : Nat.card {C : AddSubgroup W.toAffine.Point //
        ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} ≤
      Nat.card {x : ModularCurve.ModuliPoint N K // ModularCurve.ModuliPoint.j x = W.j}) :
    Function.Bijective (toModuli W N) :=
  (toModuli_surjective W N).bijective_of_nat_card_le hle

private theorem toModuli_bijective_of_natCard_eq_dedekindPsi [IsSepClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    (h₁ : Nat.card {C : AddSubgroup W.toAffine.Point //
        ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g}
      = ModularCurve.dedekindPsi N)
    (h₂ : Nat.card {x : ModularCurve.ModuliPoint N K // ModularCurve.ModuliPoint.j x = W.j}
      = ModularCurve.dedekindPsi N) :
    Function.Bijective (toModuli W N) := by
  haveI : Finite {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} :=
    Nat.finite_of_card_ne_zero (h₁ ▸ (ModularCurve.dedekindPsi_pos N (NeZero.ne N)).ne')
  exact toModuli_bijective_of_natCard_le W N (h₁.trans h₂.symm).le

end ModuliOfCyclicSubgroup
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

section CyclicSubgroupCount

open AddSubgroup

variable {A : Type u} [AddCommGroup A]

private theorem isAddCyclic_zmultiples (g : A) : IsAddCyclic (zmultiples g) := by
  refine ⟨⟨g, mem_zmultiples g⟩, fun x => ?_⟩
  obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp x.2
  exact mem_zmultiples_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem exists_generator_of_isAddCyclic_card (H : AddSubgroup A) (N : ℕ)
    (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    ∃ g : A, addOrderOf g = N ∧ H = zmultiples g := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h2 : addOrderOf g = Nat.card H := addOrderOf_eq_card_of_forall_mem_zmultiples hg
  refine ⟨(g : A), ?_, ?_⟩
  · exact (addOrderOf_injective H.subtype (AddSubgroup.subtype_injective H) g).trans
      (h2.trans hcard)
  · ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
      exact mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hx
      rw [← hk]
      exact zsmul_mem g.2 k

private def cycSubEquiv (N : ℕ) :
    {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} ≃
    {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} where
  toFun C := ⟨C.1, by
    obtain ⟨g, hg, hC⟩ := C.2
    rw [hC]
    exact ⟨isAddCyclic_zmultiples g, by rw [Nat.card_zmultiples, hg]⟩⟩
  invFun H := ⟨H.1, by
    obtain ⟨g, h1, h2⟩ := exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2
    exact ⟨g, h1, h2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem natCard_cycSub_zmultiples_eq (N : ℕ) [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    Nat.card {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g}
      = ModularCurve.dedekindPsi N := by
  rw [Nat.card_congr (cycSubEquiv N)]
  exact AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy N e

private theorem natCard_cycSub_zmultiples_eq_of_card (N : ℕ) [NeZero N]
    (hcard : ∀ d : ℕ, d ∣ N → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nat.card {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g}
      = ModularCurve.dedekindPsi N := by
  obtain ⟨e⟩ :=
    AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq (NeZero.ne N) hcard
  exact natCard_cycSub_zmultiples_eq N e

private theorem exists_family (N : ℕ) [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    ∃ (ι : Type u) (_ : Fintype ι) (Q : ι → A),
      Fintype.card ι = ModularCurve.dedekindPsi N ∧
      (∀ i, addOrderOf (Q i) = N) ∧
      Function.Injective (fun i => zmultiples (Q i)) ∧
      ∀ C : AddSubgroup A, (∃ g, addOrderOf g = N ∧ C = zmultiples g) →
        ∃ i, zmultiples (Q i) = C := by
  classical
  have hcount := natCard_cycSub_zmultiples_eq (A := A) N e
  have hfin : Finite {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} :=
    (Nat.card_ne_zero.mp (by
      rw [hcount]
      exact (ModularCurve.dedekindPsi_pos N (NeZero.ne N)).ne')).2
  haveI := hfin
  haveI : Fintype {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} :=
    Fintype.ofFinite _
  choose g hg hC using
    fun C : {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} => C.2
  refine ⟨_, inferInstance, g, ?_, hg, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hcount]
  · intro C C' h
    apply Subtype.ext
    rw [hC C, hC C']
    exact h
  · intro C hCmem
    exact ⟨⟨C, hCmem⟩, (hC ⟨C, hCmem⟩).symm⟩

end CyclicSubgroupCount
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

section

variable (q N : ℕ) [NeZero N] (K : Type u) [Field K] [DecidableEq K]
  [Fact q.Prime] [CharP K q] [IsAlgClosed K]

private abbrev GenVal : Type u := {a : K // a ∈ ModularCurve.ssJSet q K ∧ a ≠ 0 ∧ a ≠ 1728}

private abbrev PlacesU : Type u :=
  {w : Place K (ModularCurve.modularFunctionFieldC K N) //
    w ∈ ModularCurve.ssPlaces q N K
      ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
      ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728}

private abbrev ModuliU : Type u :=
  {x : ModularCurve.ModuliPoint N K //
    x ∈ ModularCurve.ssLocus q N K
      ∧ ModularCurve.ModuliPoint.j x ≠ 0
      ∧ ModularCurve.ModuliPoint.j x ≠ 1728}

private noncomputable def centreP (w : PlacesU q N K) : GenVal q K :=
  ⟨(w : Place K (ModularCurve.modularFunctionFieldC K N)).evalAt (ModularCurve.jGeomGen K N),
    w.2.1.2.2, w.2.2.1, w.2.2.2⟩

private noncomputable def centreM (x : ModuliU q N K) : GenVal q K :=
  ⟨ModularCurve.ModuliPoint.j (x : ModularCurve.ModuliPoint N K),
    x.2.1, x.2.2.1, x.2.2.2⟩

omit [DecidableEq K] in

private theorem evalAt_arithFrobC_smul_jGeomGen
    (w : Place K (ModularCurve.modularFunctionFieldC K N)) (hw : w.IsRational)
    (hj : ModularCurve.jGeomGen K N ∈ w.toValuationSubring) :
    (ModularCurve.arithFrobC q K N • w).evalAt (ModularCurve.jGeomGen K N)
      = w.evalAt (ModularCurve.jGeomGen K N) ^ q := by
  have h := evalAt_smul (ModularCurve.arithFrobC q K N) w hw hj
  have hfix : ModularCurve.arithFrobC q K N • ModularCurve.jGeomGen K N
      = ModularCurve.jGeomGen K N :=
    ModularCurve.arithFrobC_smul_jq (q := q) (K := K) (N := N)
  rw [hfix] at h
  rw [h, ModularCurve.baseAut_arithFrobC_apply]

private noncomputable def reshuffle (a : GenVal q K) (W : WeierstrassCurve K) [W.IsElliptic]
    (hjW : W.j = (a : K)) :
    {x : ModularCurve.ModuliPoint N K // ModularCurve.ModuliPoint.j x = W.j} ≃
      {y : ModuliU q N K // centreM q N K y = a} where
  toFun x :=
    ⟨⟨x.1, ModularCurve.mem_ssLocus_iff.mpr (by rw [x.2, hjW]; exact a.2.1),
      by rw [x.2, hjW]; exact a.2.2.1, by rw [x.2, hjW]; exact a.2.2.2⟩,
      Subtype.ext (x.2.trans hjW)⟩
  invFun y := ⟨y.1.1, (congrArg Subtype.val y.2).trans hjW.symm⟩
  left_inv x := rfl
  right_inv y := rfl

private noncomputable def xZero (a : K) : LaurentSeries K :=
  algebraMap K (LaurentSeries K) a + HahnSeries.single (1 : ℤ) 1

private theorem xZero_sub_algebraMap (a : K) :
    xZero K a - algebraMap K (LaurentSeries K) a = HahnSeries.single (1 : ℤ) 1 := by
  rw [xZero]; ring

private theorem order_xZero_sub (a : K) :
    (xZero K a - algebraMap K (LaurentSeries K) a).order = 1 := by
  rw [xZero_sub_algebraMap, HahnSeries.order_single one_ne_zero]

private theorem coeff_one_xZero (a : K) : (xZero K a).coeff (1 : ℤ) = 1 := by
  simp only [xZero, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_add,
    HahnSeries.coeff_single_same,
    HahnSeries.coeff_single_of_ne (one_ne_zero : (1 : ℤ) ≠ 0), zero_add]

private theorem xZero_ne_algebraMap (a b : K) :
    xZero K a ≠ algebraMap K (LaurentSeries K) b := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (1 : ℤ)) h
  simp only [coeff_one_xZero, ModularCurve.algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_of_ne (one_ne_zero : (1 : ℤ) ≠ 0)] at h1
  exact one_ne_zero h1

private theorem xZero_ne_zero (a : K) : xZero K a ≠ 0 := by
  have := xZero_ne_algebraMap K a 0
  rwa [map_zero] at this

private theorem xZero_ne_1728 (a : K) : xZero K a ≠ 1728 := by
  have := xZero_ne_algebraMap K a 1728
  rwa [map_ofNat] at this

private theorem transcendental_xZero (a : K) : Transcendental K (xZero K a) := by
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K _ hdeg
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (1 : ℤ)) hc
  simp only [ModularCurve.algebraMap_laurentSeries_eq_single, coeff_one_xZero,
    HahnSeries.coeff_single_of_ne (one_ne_zero : (1 : ℤ) ≠ 0)] at h1
  exact zero_ne_one h1

private theorem map_ofJNe0Or1728 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (j : R) :
    (WeierstrassCurve.ofJNe0Or1728 j).map f = WeierstrassCurve.ofJNe0Or1728 (f j) := by
  ext <;> simp [WeierstrassCurve.ofJNe0Or1728, map_ofNat]

private noncomputable def WModel (a : K) : WeierstrassCurve (PowerSeries K) :=
  WeierstrassCurve.ofJNe0Or1728 (PowerSeries.C a + PowerSeries.X)

private theorem genFibre_WModel (a : K) :
    GenericFibreCurve.genFibre (WModel K a) = WeierstrassCurve.ofJNe0Or1728 (xZero K a) := by
  rw [GenericFibreCurve.genFibre, WModel, map_ofJNe0Or1728]
  congr 1
  rw [map_add, ← GenericFibreCurve.algebraMap_laurentSeries_factor, xZero]
  congr 1
  rw [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X]

private noncomputable def WInt (a : K) : WeierstrassCurve (LaurentIntegerRing.laurentIntegers K) :=
  (WModel K a).map (LaurentIntegerRing.powerSeriesEquivLaurentIntegers K)

private theorem WInt_map_subtype (a : K) :
    (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype
      = WeierstrassCurve.ofJNe0Or1728 (xZero K a) := by
  rw [WInt, WeierstrassCurve.map_map, ← genFibre_WModel K a, GenericFibreCurve.genFibre]
  congr 1

private theorem residueEquiv_residue_psEquiv (p : PowerSeries K) :
    LaurentIntegerRing.laurentIntegersResidueEquiv K
        (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K)
          (LaurentIntegerRing.powerSeriesEquivLaurentIntegers K p))
      = PowerSeries.constantCoeff p := by
  rw [LaurentIntegerRing.laurentIntegersResidueEquiv, RingEquiv.trans_apply,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  have hsym : ((LaurentIntegerRing.powerSeriesEquivLaurentIntegers K).symm :
      ↥(LaurentIntegerRing.laurentIntegers K) →+* PowerSeries K)
        ((LaurentIntegerRing.powerSeriesEquivLaurentIntegers K) p) = p :=
    (LaurentIntegerRing.powerSeriesEquivLaurentIntegers K).symm_apply_apply p
  rw [hsym]
  rfl

private theorem WInt_special_fibre (a : K) :
    ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).map
        (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)
      = WeierstrassCurve.ofJNe0Or1728 a := by
  rw [WInt, WeierstrassCurve.map_map, WeierstrassCurve.map_map, WModel, map_ofJNe0Or1728]
  congr 1
  show LaurentIntegerRing.laurentIntegersResidueEquiv K
      (IsLocalRing.residue _ (LaurentIntegerRing.powerSeriesEquivLaurentIntegers K
        (PowerSeries.C a + PowerSeries.X))) = a
  rw [residueEquiv_residue_psEquiv]
  simp

section TLayer

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

private theorem nsmul_mem_torsion {φ : A →+ B} {N : ℕ} {x : A} (hx : N • x = 0) :
    N • φ x = 0 := by rw [← map_nsmul, hx, map_zero]

private theorem addOrderOf_eq_of_injOn_torsion {φ : A →+ B} {N : ℕ} [NeZero N]
    (hinj : Function.Injective
      (fun x : {x : A // N • x = 0} => (⟨φ x, nsmul_mem_torsion x.2⟩ : {y : B // N • y = 0})))
    {g : A} (hg : N • g = 0) : addOrderOf (φ g) = addOrderOf g := by
  have key : ∀ d : ℕ, d • φ g = 0 ↔ d • g = 0 := by
    intro d
    constructor
    · intro h
      have h1 : N • (d • g) = 0 := by rw [smul_comm, hg, smul_zero]
      have h2 : (⟨d • g, h1⟩ : {x : A // N • x = 0}) = ⟨0, by simp⟩ :=
        hinj (Subtype.ext (by simpa [map_nsmul] using h))
      simpa using congrArg Subtype.val h2
    · intro h
      rw [← map_nsmul, h, map_zero]
  refine Nat.dvd_antisymm ?_ ?_
  · exact addOrderOf_dvd_of_nsmul_eq_zero ((key _).mpr (addOrderOf_nsmul_eq_zero g))
  · exact addOrderOf_dvd_of_nsmul_eq_zero ((key _).mp (addOrderOf_nsmul_eq_zero (φ g)))

private theorem nsmul_eq_zero_of_mem_cycSub {N : ℕ} {C : AddSubgroup A}
    (hC : ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g) {x : A} (hx : x ∈ C) :
    N • x = 0 := by
  obtain ⟨g, hg, rfl⟩ := hC
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  have hgN : N • g = 0 := hg ▸ addOrderOf_nsmul_eq_zero g
  rw [smul_comm, hgN, smul_zero]

private noncomputable def cycSubCongr (φ : A →+ B) (N : ℕ) [NeZero N]
    (hbij : Function.Bijective
      (fun x : {x : A // N • x = 0} => (⟨φ x, nsmul_mem_torsion x.2⟩ : {y : B // N • y = 0}))) :
    {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} ≃
      {C : AddSubgroup B // ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} := by
  refine Equiv.ofBijective (fun C => ⟨C.1.map φ, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨g, hg, hC⟩ := C.2
    refine ⟨φ g, ?_, by rw [hC, AddMonoidHom.map_zmultiples]⟩
    rw [addOrderOf_eq_of_injOn_torsion hbij.injective (hg ▸ addOrderOf_nsmul_eq_zero g), hg]
  · intro C C' h
    have hmap : C.1.map φ = C'.1.map φ := congrArg Subtype.val h
    refine Subtype.ext (AddSubgroup.ext fun x => ?_)
    constructor
    · intro hx
      have : φ x ∈ C'.1.map φ := hmap ▸ AddSubgroup.mem_map_of_mem φ hx
      obtain ⟨x', hx', hφ⟩ := this
      have hxx' : x' = x := by
        have h1 := hbij.injective (a₁ := ⟨x', nsmul_eq_zero_of_mem_cycSub C'.2 hx'⟩)
          (a₂ := ⟨x, nsmul_eq_zero_of_mem_cycSub C.2 hx⟩) (Subtype.ext hφ)
        simpa using congrArg Subtype.val h1
      exact hxx' ▸ hx'
    · intro hx
      have : φ x ∈ C.1.map φ := hmap ▸ AddSubgroup.mem_map_of_mem φ hx
      obtain ⟨x', hx', hφ⟩ := this
      have hxx' : x' = x := by
        have h1 := hbij.injective (a₁ := ⟨x', nsmul_eq_zero_of_mem_cycSub C.2 hx'⟩)
          (a₂ := ⟨x, nsmul_eq_zero_of_mem_cycSub C'.2 hx⟩) (Subtype.ext hφ)
        simpa using congrArg Subtype.val h1
      exact hxx' ▸ hx'
  · rintro ⟨C', g', hg', hC'⟩
    obtain ⟨⟨g, hgtor⟩, hφg⟩ := hbij.surjective ⟨g', hg' ▸ addOrderOf_nsmul_eq_zero g'⟩
    have hφg' : φ g = g' := congrArg Subtype.val hφg
    have hord : addOrderOf g = N := by
      rw [← addOrderOf_eq_of_injOn_torsion hbij.injective hgtor, hφg', hg']
    refine ⟨⟨AddSubgroup.zmultiples g, g, hord, rfl⟩, Subtype.ext ?_⟩
    show (AddSubgroup.zmultiples g).map φ = C'
    rw [AddMonoidHom.map_zmultiples, hφg', hC']

end TLayer
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

private theorem WInt_residue_Δ_ne_zero (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).Δ ≠ 0 := by
  intro h
  have h2 := congrArg WeierstrassCurve.Δ (WInt_special_fibre K a)
  rw [WeierstrassCurve.map_Δ, h, map_zero, WeierstrassCurve.ofJNe0Or1728_Δ] at h2
  exact (mul_ne_zero (pow_ne_zero 2 ha0) (pow_ne_zero 9 (sub_ne_zero.mpr ha1728))) h2.symm

private theorem isElliptic_WInt_residue (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (WInt_residue_Δ_ne_zero K a ha0 ha1728)⟩

private theorem natCast_residue_ne_zero (hqN : ¬ q ∣ N) :
    (N : IsLocalRing.ResidueField (LaurentIntegerRing.laurentIntegers K)) ≠ 0 := by
  intro h
  have h2 := congrArg (LaurentIntegerRing.laurentIntegersResidueEquiv K) h
  rw [map_natCast, map_zero] at h2
  exact hqN ((CharP.cast_eq_zero_iff K q N).mp h2)

private theorem bijective_torsion_restrict {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (hbij : Function.Bijective φ) (N : ℕ) :
    Function.Bijective (fun x : {x : A // N • x = 0} =>
      (⟨φ x, nsmul_mem_torsion x.2⟩ : {y : B // N • y = 0})) := by
  constructor
  · intro a b h
    exact Subtype.ext (hbij.injective (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hbij.surjective y
    refine ⟨⟨x, hbij.injective ?_⟩, rfl⟩
    rw [map_nsmul, hy, map_zero]

private theorem surjective_mapPoint_of_ringEquiv {F k : Type u} [Field F] [Field k]
    (e : F ≃+* k) (W₀ : WeierstrassCurve F) :
    Function.Surjective (WeierstrassCurve.mapPoint (e : F →+* k) (W₀ := W₀)) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have hW : (W₀.map (e : F →+* k)).map (e.symm : k →+* F) = W₀ := by
      rw [WeierstrassCurve.map_map]
      have hcomp : ((e.symm : k →+* F).comp (e : F →+* k)) = RingHom.id F :=
        RingHom.ext fun z => e.symm_apply_apply z
      rw [hcomp, WeierstrassCurve.map_id]
    have h' : W₀.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      have h2 := ((W₀.map (e : F →+* k)).toAffine.map_nonsingular
        (e.symm : k →+* F).injective x y).mpr h
      have hWa : (W₀.map (e : F →+* k)).toAffine.map (e.symm : k →+* F) = W₀.toAffine :=
        congrArg WeierstrassCurve.toAffine hW
      rwa [hWa] at h2
    refine ⟨.some (e.symm x) (e.symm y) h', ?_⟩
    rw [WeierstrassCurve.mapPoint_some]
    exact WeierstrassCurve.Affine.Point.some_congr'
      (e.apply_symm_apply x) (e.apply_symm_apply y) _ _

private noncomputable def WfamD (a : K) : WeierstrassCurve K :=
  ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).map
    (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)

private theorem WfamD_Δ_ne_zero (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    (WfamD K a).Δ ≠ 0 := by
  rw [WfamD, WeierstrassCurve.map_Δ]
  intro h
  exact WInt_residue_Δ_ne_zero K a ha0 ha1728
    ((map_eq_zero_iff _ (LaurentIntegerRing.laurentIntegersResidueEquiv K).injective).mp h)

private theorem isElliptic_WfamD (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    (WfamD K a).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (WfamD_Δ_ne_zero K a ha0 ha1728)⟩

private theorem j_WfamD (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    {h1 : (WfamD K a).IsElliptic} : @WeierstrassCurve.j K _ (WfamD K a) h1 = a := by
  haveI : Fact (IsUnit a) := ⟨Ne.isUnit ha0⟩
  haveI : Fact (IsUnit (a - 1728)) := ⟨Ne.isUnit (sub_ne_zero.mpr ha1728)⟩
  exact (ModularCurve.FullKernelQuotientRoots.j_congr (WInt_special_fibre K a)).trans
    (WeierstrassCurve.ofJNe0Or1728_j a)

private noncomputable def cycSubChain (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    [h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h2 : ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h3 : (WfamD K a).IsElliptic] :
    {C : AddSubgroup ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
        ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} ≃
      {C : AddSubgroup (WfamD K a).toAffine.Point //
        ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} := by
  have hbij2 : Function.Bijective (WeierstrassCurve.mapPointHom
      (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)
      (W₀ := (WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K)))) :=
    ⟨fun x y h => WeierstrassCurve.mapPoint_injective _ h,
     fun y => surjective_mapPoint_of_ringEquiv
       (LaurentIntegerRing.laurentIntegersResidueEquiv K) _ y⟩
  unfold WfamD
  exact (cycSubCongr (WeierstrassCurve.reduceHom (WInt_residue_Δ_ne_zero K a ha0 ha1728)) N
      (WeierstrassCurve.bijective_reduceHom_restrict_torsion
        (WInt_residue_Δ_ne_zero K a ha0 ha1728) (natCast_residue_ne_zero q N K hqN))).trans
    (cycSubCongr (WeierstrassCurve.mapPointHom
        (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)
        (W₀ := (WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K)))) N
      (bijective_torsion_restrict _ hbij2 N))

private theorem natCast_laurent_ne_zero (hqN : ¬ q ∣ N) : (N : LaurentSeries K) ≠ 0 := by
  intro h
  have h2 : algebraMap K (LaurentSeries K) (N : K) = 0 := by
    rw [map_natCast]; exact h
  have h3 : (N : K) = 0 :=
    (map_eq_zero_iff _ (algebraMap K (LaurentSeries K)).injective).mp h2
  exact hqN ((CharP.cast_eq_zero_iff K q N).mp h3)

private theorem isElliptic_WInt_subtype (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [WInt_map_subtype K a]
  rw [WeierstrassCurve.ofJNe0Or1728_Δ]
  exact mul_ne_zero (pow_ne_zero 2 (xZero_ne_zero K a))
    (pow_ne_zero 9 (sub_ne_zero.mpr (xZero_ne_1728 K a)))

private theorem j_WInt_subtype (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    {h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic} :
    @WeierstrassCurve.j _ _ ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) h1
      = xZero K a := by
  haveI : Fact (IsUnit (xZero K a)) := ⟨Ne.isUnit (xZero_ne_zero K a)⟩
  haveI : Fact (IsUnit (xZero K a - 1728)) :=
    ⟨Ne.isUnit (sub_ne_zero.mpr (xZero_ne_1728 K a))⟩
  exact (ModularCurve.FullKernelQuotientRoots.j_congr (WInt_map_subtype K a)).trans
    (WeierstrassCurve.ofJNe0Or1728_j (xZero K a))

private theorem card_torsionBy_WInt_subtype (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    [h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h2 : ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h3 : (WfamD K a).IsElliptic] (d : ℕ) (hd : d ∣ N) :
    Nat.card (Submodule.torsionBy ℤ
        ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point d)
      = d ^ 2 := by

  have hdK : (d : K) ≠ 0 := fun h =>
    hqN (dvd_trans ((CharP.cast_eq_zero_iff K q d).mp h) hd)
  have hdres : (d : IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K)) ≠ 0 := by
    intro h
    have h2 := congrArg (LaurentIntegerRing.laurentIntegersResidueEquiv K) h
    rw [map_natCast, map_zero] at h2
    exact hdK h2
  have bij1 := WeierstrassCurve.bijective_reduceHom_restrict_torsion
    (WInt_residue_Δ_ne_zero K a ha0 ha1728) (N := d) hdres
  have hbij2 : Function.Bijective (WeierstrassCurve.mapPointHom
      (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)
      (W₀ := (WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K)))) :=
    ⟨fun x y h => WeierstrassCurve.mapPoint_injective _ h,
     fun y => surjective_mapPoint_of_ringEquiv
       (LaurentIntegerRing.laurentIntegersResidueEquiv K) _ y⟩
  have bij2 := bijective_torsion_restrict _ hbij2 d

  have hcardK : Nat.card (Submodule.torsionBy ℤ (WfamD K a).toAffine.Point d) = d ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) (WfamD K a) hdK

  have e1 : Submodule.torsionBy ℤ
      ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point d ≃
      {x : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
        d • x = 0} :=
    Equiv.subtypeEquivRight fun x => by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  have e4 : Submodule.torsionBy ℤ (WfamD K a).toAffine.Point d ≃
      {x : (WfamD K a).toAffine.Point // d • x = 0} :=
    Equiv.subtypeEquivRight fun x => by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  calc Nat.card (Submodule.torsionBy ℤ
        ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point d)
      = Nat.card {x : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
          d • x = 0} := Nat.card_congr e1
    _ = Nat.card {x : ((WInt K a).map
          (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).toAffine.Point //
          d • x = 0} := Nat.card_congr (Equiv.ofBijective _ bij1)
    _ = Nat.card {x : (WfamD K a).toAffine.Point // d • x = 0} :=
        Nat.card_congr (Equiv.ofBijective _ bij2)
    _ = Nat.card (Submodule.torsionBy ℤ (WfamD K a).toAffine.Point d) :=
        (Nat.card_congr e4).symm
    _ = d ^ 2 := hcardK

private theorem card_roots_fibrePoly_xZero [DecidableEq (LaurentSeries K)] (a : K)
    (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (hqN : ¬ q ∣ N) (data : ModularCurve.ModularPolynomialData N) :
    (ModularCurve.fibrePoly data.Φ (xZero K a)).roots.toFinset.card
      = ModularCurve.dedekindPsi N := by
  classical
  haveI hWe := isElliptic_WInt_subtype K a ha0 ha1728
  haveI := isElliptic_WInt_residue K a ha0 ha1728
  haveI := isElliptic_WfamD K a ha0 ha1728
  have hjW' : @WeierstrassCurve.j _ _ ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype)
      hWe = xZero K a := j_WInt_subtype K a ha0 ha1728
  have hNL : (N : LaurentSeries K) ≠ 0 := natCast_laurent_ne_zero q N K hqN
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (NeZero.ne N) (fun d hd => card_torsionBy_WInt_subtype q N K a ha0 ha1728 hqN d hd)
  obtain ⟨ι, hι, Q, hcι, hQ, hQinj, -⟩ := exists_family
    (A := ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point) N e
  have hΔv : ∀ i, (((WInt K a).map
      (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient (Q i) N).Δ ≠ 0 := fun i =>
    ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_Δ_ne_zero _ hNL (Q i) (hQ i)
  have hp := ModularCurve.FullKernelQuotientRoots.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_family
    (h0 := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero)
    hNL data _ hcι Q hQ hQinj hΔv
  rw [hjW'] at hp
  have hsep := FibrePolySeparable.separable_fibrePoly_of_transcendental N data hNL (xZero K a)
    (transcendental_xZero K a)
  have hcinj := FibrePolySeparable.injective_of_separable_prod _ _ hsep hp
  refine FibrePolySeparable.card_roots_toFinset_eq_of_injective_family _
    ((data.monic.map _).ne_zero) _ hcinj (fun i => ?_) hcι ?_
  · show (ModularCurve.fibrePoly data.Φ (xZero K a)).IsRoot _
    rw [hp, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · exact (ModularCurve.natDegree_fibrePoly data.monic _).trans data.natDegree_eq

private theorem xZero_eq_algebraMap_ps (a : K) :
    xZero K a = algebraMap (PowerSeries K) (LaurentSeries K)
      (PowerSeries.C a + PowerSeries.X) := by
  rw [xZero, map_add, ← GenericFibreCurve.algebraMap_laurentSeries_factor]
  congr 1
  rw [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X]

private theorem order_xZero (a : K) (ha0 : a ≠ 0) : (xZero K a).order = 0 := by
  rw [xZero_eq_algebraMap_ps]
  exact GenericFibreCurve.order_algebraMap_laurentSeries_eq_zero (by simpa using ha0)

private theorem xZero_mem_laurentIntegers (a : K) :
    xZero K a ∈ LaurentIntegerRing.laurentIntegers K := by
  rw [LaurentIntegerRing.mem_laurentIntegers_iff]
  exact ⟨PowerSeries.C a + PowerSeries.X, by
    rw [xZero_eq_algebraMap_ps, LaurentSeries.coe_algebraMap]⟩

private theorem root_order_nonneg (a : K) {data : ModularCurve.ModularPolynomialData N}
    {z : LaurentSeries K}
    (hz : (ModularCurve.fibrePoly data.Φ (xZero K a)).IsRoot z) : 0 ≤ z.order := by

  set A := LaurentIntegerRing.laurentIntegers K with hA
  set x₀A : A := ⟨xZero K a, xZero_mem_laurentIntegers K a⟩ with hx₀A
  have hPmap : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) x₀A)).map
      (algebraMap A (LaurentSeries K)) = ModularCurve.fibrePoly data.Φ (xZero K a) := by
    rw [Polynomial.map_map]
    show data.Φ.map (((algebraMap ↥A (LaurentSeries K)).comp
      (Polynomial.eval₂RingHom (Int.castRingHom ↥A) x₀A))) = _
    congr 1
    refine RingHom.ext fun P => ?_
    show algebraMap ↥A (LaurentSeries K) (Polynomial.eval₂ (Int.castRingHom ↥A) x₀A P) = _
    rw [Polynomial.hom_eval₂]
    have h1 : (algebraMap ↥A (LaurentSeries K)).comp (Int.castRingHom ↥A)
        = Int.castRingHom (LaurentSeries K) := Subsingleton.elim _ _
    rw [h1]
    rfl
  have hint : IsIntegral A z := by
    refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) x₀A),
      data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hPmap]
    exact hz
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨p, hp⟩ := (LaurentIntegerRing.mem_laurentIntegers_iff K).mp y.2
  have hz' : (p : LaurentSeries K) = z := by
    rw [hp]
    exact hy
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · by_contra hneg
    push Not at hneg
    have hp0 : (HahnSeries.ofPowerSeries ℤ K p : LaurentSeries K) ≠ 0 := by
      rw [hz']; exact hz0
    have hordp : (HahnSeries.ofPowerSeries ℤ K p).order = z.order := by rw [hz']
    have hco : (HahnSeries.ofPowerSeries ℤ K p).coeff
        (HahnSeries.ofPowerSeries ℤ K p).order ≠ 0 :=
      fun h => hp0 (HahnSeries.coeff_order_eq_zero.mp h)
    rw [hordp] at hco
    have hcc : (HahnSeries.ofPowerSeries ℤ K p).coeff z.order
        = if z.order < 0 then 0 else PowerSeries.coeff z.order.natAbs p :=
      PowerSeries.coeff_coe (f := p) z.order
    rw [hcc, if_pos hneg] at hco
    exact hco rfl

private theorem coeffMap_frobenius_xZero (a : K) :
    ModularCurve.coeffMap (frobenius K q) (xZero K a) = xZero K (a ^ q) := by
  rw [xZero, xZero]
  simp only [map_add, ModularCurve.algebraMap_laurentSeries_eq_single,
    ModularCurve.coeffMap_single, map_one, frobenius_def]

private theorem P1_fibre_roots_equiv (data : ModularCurve.ModularPolynomialData N)
    (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)] (a : GenVal q K) :
    ∃ F : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} ≃ {w : PlacesU q N K // centreP q N K w = a},
      ∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = xZero K (a : K) ∧
        ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ ((F y : PlacesU q N K) :
            AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)).toValuationSubring
          ↔ 0 ≤ (ι x).order := by
  classical
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)

  set a₀ : K := (a : K) with ha₀
  have ha0 : a₀ ≠ 0 := a.2.2.1
  have ha1728 : a₀ ≠ 1728 := a.2.2.2
  have hass : a₀ ∈ ModularCurve.ssJSet q K := a.2.1

  have hsep : IsSeparable (IntermediateField.adjoin K
      ({ModularCurve.jqModC K} : Set (LaurentSeries K))) (ModularCurve.jqNModC K N) :=
    ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero K N hN
  have hTfin := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos K N hsep a₀
  set T : Finset (Place K ↥(ModularCurve.modularFunctionFieldC K N)) := hTfin.toFinset with hTdef
  have hT : ∀ w, w ∈ T ↔ 0 < w.ord (ModularCurve.jGeomGen K N
      - algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a₀) := by
    intro w
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  have hΓ : ∀ u ∈ (⊥ : Subgroup Kˣ), ModularCurve.qTwist u (xZero K a₀) = xZero K a₀ := by
    intro u hu
    rw [Subgroup.mem_bot] at hu
    subst hu
    exact ModularCurve.qTwist_one_apply _
  have hcard_bot : Nat.card (↥(⊥ : Subgroup Kˣ)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext (by
      rw [Subgroup.mem_bot.mp x.2, Subgroup.mem_bot.mp y.2])⟩, ⟨1, Subgroup.one_mem _⟩⟩
  have htame : ((Nat.card (↥(⊥ : Subgroup Kˣ)) : ℕ) : K) ≠ 0 := by
    rw [hcard_bot, Nat.cast_one]; exact one_ne_zero
  have hm : (xZero K a₀ - algebraMap K (LaurentSeries K) a₀).order
      = (Nat.card (↥(⊥ : Subgroup Kˣ)) : ℤ) := by
    rw [order_xZero_sub, hcard_bot, Nat.cast_one]
  have hcard : ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (xZero K a₀))).roots.toFinset).card = ModularCurve.dedekindPsi N :=
    card_roots_fibrePoly_xZero q N K a₀ ha0 ha1728 hqN data
  obtain ⟨f, hf0, hf1, hf2, hf3⟩ :=
    ModularCurve.exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ q N K hqN data a₀
      (xZero K a₀) ⊥ hΓ htame hm hcard T hT

  have hfinj : Function.Injective f := by
    intro y y' h
    obtain ⟨u, hu, huq⟩ := (hf2 y y').mp h
    rw [Subgroup.mem_bot] at hu
    subst hu
    rw [ModularCurve.qTwist_one_apply] at huq
    exact Subtype.ext huq

  have hf_mem_T : ∀ y, f y ∈ T := by
    intro y
    rw [hT]
    have horb := hf3 y
    have horb1 : Set.ncard {y' : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K a₀))).IsRoot z} |
          ∃ u ∈ (⊥ : Subgroup Kˣ), ModularCurve.qTwist u y.1 = y'.1} = 1 := by
      rw [Set.ncard_eq_one]
      refine ⟨y, ?_⟩
      ext y'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, hu, huq⟩
        rw [Subgroup.mem_bot] at hu
        subst hu
        rw [ModularCurve.qTwist_one_apply] at huq
        exact (Subtype.ext huq).symm
      · rintro rfl
        exact ⟨1, Subgroup.one_mem _, ModularCurve.qTwist_one_apply _⟩
    rw [horb1, Nat.cast_one] at horb
    omega

  have hj_mem : ∀ y, ModularCurve.jGeomGen K N ∈ (f y).toValuationSubring := by
    intro y
    have hord := (hT (f y)).mp (hf_mem_T y)
    have hmem : ModularCurve.jGeomGen K N -
          algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a₀
        ∈ (f y).toValuationSubring :=
      (f y).mem_of_ord_nonneg (ModularCurve.jGeomGen_sub_algebraMap_ne_zero K N a₀) hord.le
    have := add_mem hmem ((f y).algebraMap_mem' a₀)
    rwa [sub_add_cancel] at this

  have hjN_mem : ∀ y, ModularCurve.jNGeomGen K N ∈ (f y).toValuationSubring := by
    intro y
    obtain ⟨ι, hιj, hιjN, hιval⟩ := hf0 y
    rw [hιval, hιjN]
    exact root_order_nonneg N K a₀ y.2
  have haff : ∀ y, ModularCurve.IsAffineGeomPlace K N (f y) :=
    fun y => ⟨hj_mem y, hjN_mem y⟩

  have hrat : ∀ y, (f y).IsRational := fun y =>
    (Place.isRational_iff_deg_eq_one (f y)).mpr
      (ModularCurve.place_deg_eq_one_of_isAlgClosed K N (f y))

  have heval : ∀ y, (f y).evalAt (ModularCurve.jGeomGen K N) = a₀ := by
    intro y
    have hord := (hT (f y)).mp (hf_mem_T y)
    have := (f y).evalAt_congr (hj_mem y) ((f y).algebraMap_mem' a₀) (Or.inr hord)
    rw [this, (f y).evalAt_algebraMap]

  have hPU : ∀ y, (f y) ∈ ModularCurve.ssPlaces q N K ∧
      (f y).evalAt (ModularCurve.jGeomGen K N) ≠ 0 ∧
      (f y).evalAt (ModularCurve.jGeomGen K N) ≠ 1728 := fun y =>
    ⟨⟨hrat y, haff y, by rw [heval y]; exact hass⟩,
      by rw [heval y]; exact ha0, by rw [heval y]; exact ha1728⟩
  have hctr : ∀ y, centreP q N K ⟨f y, hPU y⟩ = a := fun y =>
    Subtype.ext (heval y)

  let g : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K a₀))).IsRoot z} → {w : PlacesU q N K // centreP q N K w = a} :=
    fun y => ⟨⟨f y, hPU y⟩, hctr y⟩
  have hginj : Function.Injective g := fun y y' h =>
    hfinj (congrArg (fun x => ((x : PlacesU q N K) :
      Place K ↥(ModularCurve.modularFunctionFieldC K N))) (congrArg Subtype.val h))
  have hgsurj : Function.Surjective g := by
    rintro ⟨⟨w, hwP⟩, hwctr⟩
    have heva : w.evalAt (ModularCurve.jGeomGen K N) = a₀ := congrArg Subtype.val hwctr
    have hwrat : w.IsRational := hwP.1.1
    have hwaff : ModularCurve.IsAffineGeomPlace K N w := hwP.1.2.1
    have hwT : w ∈ T := by
      rw [hT]
      have := ModularCurve.ord_sub_evalAt_pos_of_isRational hwrat hwaff.1
        (ModularCurve.jGeomGen_sub_algebraMap_ne_zero K N _)
      rwa [heva] at this
    obtain ⟨y, hy⟩ := hf1 w hwT
    exact ⟨y, Subtype.ext (Subtype.ext hy)⟩
  refine ⟨Equiv.ofBijective g ⟨hginj, hgsurj⟩, ?_⟩
  intro y

  exact hf0 y

private theorem P2_roots_cycSub_equiv (data : ModularCurve.ModularPolynomialData N)
    (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)] (a : GenVal q K)
    [h1 : ((WInt K (a : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic] :
    ∃ E : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} ≃
        {C : AddSubgroup ((WInt K (a : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
          ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g},
      ∀ (g : ((WInt K (a : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point)
        (hg : addOrderOf g = N)
        (hΔ : (((WInt K (a : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N).Δ ≠ 0),
        ((E.symm ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K (a : K)))).IsRoot z}) : LaurentSeries K)
          = @WeierstrassCurve.j _ _ (((WInt K (a : K)).map
              (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩ := by
  classical
  have hNL : (N : LaurentSeries K) ≠ 0 := natCast_laurent_ne_zero q N K hqN
  haveI h2 := isElliptic_WInt_residue K (a : K) a.2.2.1 a.2.2.2
  haveI h3 := isElliptic_WfamD K (a : K) a.2.2.1 a.2.2.2
  haveI : DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K)) :=
    Classical.decEq _
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (NeZero.ne N)
    (fun d hd => card_torsionBy_WInt_subtype q N K (a : K) a.2.2.1 a.2.2.2 hqN d hd)
  obtain ⟨ι, hιF, Q, hcι, hQ, hQinj, hQsurj⟩ := exists_family
    (A := ((WInt K (a : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point) N e
  have hΔv : ∀ i, (((WInt K (a : K)).map
      (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient (Q i) N).Δ ≠ 0 := fun i =>
    ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_Δ_ne_zero _ hNL (Q i) (hQ i)
  have hp := ModularCurve.FullKernelQuotientRoots.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_family
    (h0 := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero)
    hNL data _ hcι Q hQ hQinj hΔv
  rw [j_WInt_subtype K (a : K) a.2.2.1 a.2.2.2] at hp
  have hsep := FibrePolySeparable.separable_fibrePoly_of_transcendental N data hNL
    (xZero K (a : K)) (transcendental_xZero K (a : K))
  have hcinj := FibrePolySeparable.injective_of_separable_prod _ _ hsep hp

  let jQuotRaw : {C : AddSubgroup ((WInt K (a : K)).map
      (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
      ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} → LaurentSeries K := fun C =>
    @WeierstrassCurve.j _ _ (((WInt K (a : K)).map
      (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient C.2.choose N)
      ⟨isUnit_iff_ne_zero.mpr (ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_Δ_ne_zero _ hNL
        C.2.choose C.2.choose_spec.1)⟩
  have hvalRaw : ∀ C (i : ι), AddSubgroup.zmultiples (Q i) = C.1 →
      jQuotRaw C = @WeierstrassCurve.j _ _ (((WInt K (a : K)).map
        (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔv i)⟩ := fun C i hi =>
    ModularCurve.FullKernelQuotientRoots.j_congr
      (ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_eq_of_zmultiples_eq C.2.choose_spec.1
        (C.2.choose_spec.2.symm.trans hi.symm))
  have hroot : ∀ C, (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (xZero K (a : K)))).IsRoot (jQuotRaw C) := by
    intro C
    obtain ⟨i, hi⟩ := hQsurj C.1 C.2
    show (ModularCurve.fibrePoly data.Φ (xZero K (a : K))).IsRoot (jQuotRaw C)
    rw [Polynomial.IsRoot, hp, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [hvalRaw C i hi]
    exact sub_self _
  let f : {C : AddSubgroup ((WInt K (a : K)).map
      (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
      ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g} →
      {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} := fun C => ⟨jQuotRaw C, hroot C⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro C C' hCC'
      obtain ⟨i, hi⟩ := hQsurj C.1 C.2
      obtain ⟨i', hi'⟩ := hQsurj C'.1 C'.2
      have hv : jQuotRaw C = jQuotRaw C' := congrArg Subtype.val hCC'
      rw [hvalRaw C i hi, hvalRaw C' i' hi'] at hv
      have hii' : i = i' := hcinj hv
      refine Subtype.ext ?_
      rw [← hi, ← hi', hii']
    · intro y
      have hy : Polynomial.eval y.1 (∏ i, (Polynomial.X - Polynomial.C
          (@WeierstrassCurve.j _ _ (((WInt K (a : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient (Q i) N)
            ⟨isUnit_iff_ne_zero.mpr (hΔv i)⟩))) = 0 := by
        rw [← hp]
        exact y.2
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hy
      obtain ⟨i, -, hi⟩ := hy
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hi
      refine ⟨⟨AddSubgroup.zmultiples (Q i), Q i, hQ i, rfl⟩, Subtype.ext ?_⟩
      show jQuotRaw _ = y.1
      rw [hvalRaw _ i rfl, ← hi]
  refine ⟨(Equiv.ofBijective f hfbij).symm, ?_⟩
  intro g hg hΔ
  show (f ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : LaurentSeries K) = _
  show jQuotRaw ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ = _
  exact ModularCurve.FullKernelQuotientRoots.j_congr
    (ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_eq_of_zmultiples_eq
      (⟨g, hg, rfl⟩ : ∃ g' , addOrderOf g' = N ∧ AddSubgroup.zmultiples g
        = AddSubgroup.zmultiples g').choose_spec.1
      ((⟨g, hg, rfl⟩ : ∃ g', addOrderOf g' = N ∧ AddSubgroup.zmultiples g
        = AddSubgroup.zmultiples g').choose_spec.2.symm))

section FrobeniusEquivariance

omit [DecidableEq K] [IsAlgClosed K] in

private theorem P3_coeffMap_ofPowerSeries (f : K →+* K) (p : PowerSeries K) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ K p)
      = HahnSeries.ofPowerSeries ℤ K (p.map f) := by
  ext k
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk,
      ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem P3_coeffMap_frobenius_mem_iff (x : LaurentSeries K) :
    ModularCurve.coeffMap (frobenius K q) x ∈ LaurentIntegerRing.laurentIntegers K
      ↔ x ∈ LaurentIntegerRing.laurentIntegers K := by
  rw [LaurentIntegerRing.mem_laurentIntegers_iff, LaurentIntegerRing.mem_laurentIntegers_iff]
  constructor
  · rintro ⟨p, hp⟩
    have hinj : Function.Injective (ModularCurve.coeffMap (frobenius K q)) := by
      intro x₁ x₂ h
      ext k
      have hk := congrArg (fun z : LaurentSeries K => z.coeff k) h
      simp only [ModularCurve.coeffMap_coeff] at hk
      exact frobenius_inj K q hk
    refine ⟨p.map ((frobeniusEquiv K q).symm : K →+* K), hinj ?_⟩
    rw [P3_coeffMap_ofPowerSeries, ← hp]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact (frobeniusEquiv K q).apply_symm_apply _
  · rintro ⟨p, rfl⟩
    exact ⟨p.map (frobenius K q), (P3_coeffMap_ofPowerSeries K _ p).symm⟩

private theorem P3_resEquiv_residue_coeffMap (x : LaurentSeries K)
    (hx : x ∈ LaurentIntegerRing.laurentIntegers K)
    (hx' : ModularCurve.coeffMap (frobenius K q) x ∈ LaurentIntegerRing.laurentIntegers K) :
    LaurentIntegerRing.laurentIntegersResidueEquiv K
        (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K) ⟨_, hx'⟩)
      = frobenius K q (LaurentIntegerRing.laurentIntegersResidueEquiv K
          (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K) ⟨x, hx⟩)) := by
  obtain ⟨p, rfl⟩ := (LaurentIntegerRing.mem_laurentIntegers_iff K).mp hx
  have h1 : (⟨(p : LaurentSeries K), hx⟩ : LaurentIntegerRing.laurentIntegers K)
      = LaurentIntegerRing.powerSeriesEquivLaurentIntegers K p := rfl
  have h2 : (⟨ModularCurve.coeffMap (frobenius K q) (p : LaurentSeries K), hx'⟩ :
        LaurentIntegerRing.laurentIntegers K)
      = LaurentIntegerRing.powerSeriesEquivLaurentIntegers K (p.map (frobenius K q)) :=
    Subtype.ext (P3_coeffMap_ofPowerSeries K _ p)
  rw [h1, h2, residueEquiv_residue_psEquiv, residueEquiv_residue_psEquiv,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]

private theorem P3_Wg_map_coeffMap (a a' : K) (hpow : a' = a ^ q) :
    ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
        (ModularCurve.coeffMap (frobenius K q))
      = (WInt K a').map (LaurentIntegerRing.laurentIntegers K).subtype := by
  rw [WInt_map_subtype, WInt_map_subtype, map_ofJNe0Or1728, coeffMap_frobenius_xZero, hpow]

private theorem P3_WfamD_map_frobenius (a a' : K) (hpow : a' = a ^ q) :
    (WfamD K a).map (frobenius K q) = WfamD K a' := by
  have ha : WfamD K a = WeierstrassCurve.ofJNe0Or1728 a := WInt_special_fibre K a
  have ha' : WfamD K a' = WeierstrassCurve.ofJNe0Or1728 a' := WInt_special_fibre K a'
  rw [ha, ha', map_ofJNe0Or1728, hpow, frobenius_def]

omit [DecidableEq K] [IsAlgClosed K] in

private theorem P3_reduceHom_apply [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    {W : WeierstrassCurve (LaurentIntegerRing.laurentIntegers K)}
    (hΔ : (W.map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).Δ ≠ 0)
    (P : (W.map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point) :
    WeierstrassCurve.reduceHom hΔ P = WeierstrassCurve.reducePoint hΔ P := rfl

private theorem P3_mem_iff_of_heq {F₀ : Type u} [Field F₀] [DecidableEq F₀]
    {V V' : WeierstrassCurve F₀} (e : V = V')
    {S : AddSubgroup V.toAffine.Point} {S' : AddSubgroup V'.toAffine.Point} (hS : HEq S' S)
    {x y : F₀} (h : V.toAffine.Nonsingular x y) (h' : V'.toAffine.Nonsingular x y) :
    WeierstrassCurve.Affine.Point.some x y h' ∈ S'
      ↔ WeierstrassCurve.Affine.Point.some x y h ∈ S := by
  subst e
  have hSS : S' = S := eq_of_heq hS
  subst hSS
  exact Iff.rfl

private theorem P3_heq_of_forall_mem_iff {F₀ : Type u} [Field F₀] [DecidableEq F₀]
    {V V' : WeierstrassCurve F₀}
    (e : V = V') {S : AddSubgroup V.toAffine.Point} {S' : AddSubgroup V'.toAffine.Point}
    (hmem : ∀ (x y : F₀) (h : V.toAffine.Nonsingular x y) (h' : V'.toAffine.Nonsingular x y),
      WeierstrassCurve.Affine.Point.some x y h' ∈ S'
        ↔ WeierstrassCurve.Affine.Point.some x y h ∈ S) :
    HEq S' S := by
  subst e
  refine heq_of_eq (AddSubgroup.ext fun P => ?_)
  cases P with
  | zero => exact ⟨fun _ => S.zero_mem, fun _ => S'.zero_mem⟩
  | some x y h => exact hmem x y h h

omit [IsAlgClosed K] in

private theorem P3_map_moduliOf (σ : K →+* K) (W : WeierstrassCurve K)
    [W.IsElliptic] (g : W.toAffine.Point) {n : ℕ} (hg : addOrderOf g = n) :
    ModularCurve.ModuliPoint.map σ (moduliOf W g hg) =
      moduliOf (W.map σ) (WeierstrassCurve.mapPoint σ (W₀ := W) g)
        ((WeierstrassCurve.addOrderOf_mapPoint σ (W₀ := W) g).trans hg) :=
  rfl

private theorem P3_toModuli_natural_of_map_eq (σ : K →+* K) (W : WeierstrassCurve K)
    [W.IsElliptic] (W' : WeierstrassCurve K) [W'.IsElliptic] (h : W.map σ = W')
    (C : {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (C' : {C' : AddSubgroup W'.toAffine.Point //
      ∃ g' : W'.toAffine.Point, addOrderOf g' = N ∧ C' = AddSubgroup.zmultiples g'})
    (hC : HEq C'.1 (C.1.map (WeierstrassCurve.mapPointHom σ (W₀ := W)))) :
    (toModuli W' N C').1 = ModularCurve.ModuliPoint.map σ (toModuli W N C).1 := by
  subst h
  obtain ⟨g, hg, hCg⟩ := C.2
  have hC' : C'.1 = AddSubgroup.zmultiples (WeierstrassCurve.mapPoint σ (W₀ := W) g) := by
    rw [eq_of_heq hC, hCg, AddMonoidHom.map_zmultiples, WeierstrassCurve.mapPointHom_apply]
  rw [toModuli_eq W C g hg hCg, P3_map_moduliOf,
    toModuli_eq (W.map σ) C' (WeierstrassCurve.mapPoint σ (W₀ := W) g)
      ((WeierstrassCurve.addOrderOf_mapPoint σ (W₀ := W) g).trans hg) hC']

omit [DecidableEq K] [IsAlgClosed K] in

private theorem P3_fibrePoly_map_coeffMap (Φ : Polynomial (Polynomial ℤ)) (x : LaurentSeries K) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x)).map
        (ModularCurve.coeffMap (frobenius K q))
      = Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (ModularCurve.coeffMap (frobenius K q) x)) := by
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast, map_intCast]
  · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private theorem P3_subgroup_leg (data : ModularCurve.ModularPolynomialData N) (hqN : ¬ q ∣ N)
    [DecidableEq (LaurentSeries K)] (a : K)
    [h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    (V : WeierstrassCurve (LaurentSeries K)) [hV1 : V.IsElliptic]
    (hV : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
        (ModularCurve.coeffMap (frobenius K q)) = V)
    (x₁ : LaurentSeries K) (hx₁ : ModularCurve.coeffMap (frobenius K q) (xZero K a) = x₁)
    (E : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K a))).IsRoot z} ≃
        {C : AddSubgroup ((WInt K a).map
            (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
          ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (hE : ∀ (g : ((WInt K a).map
          (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point)
        (hg : addOrderOf g = N)
        (hΔ : (((WInt K a).map
            (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N).Δ ≠ 0),
        ((E.symm ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K a))).IsRoot z}) : LaurentSeries K)
          = @WeierstrassCurve.j _ _ (((WInt K a).map
              (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩)
    (E' : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          x₁)).IsRoot z} ≃
        {C : AddSubgroup V.toAffine.Point // ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (hE' : ∀ (g : V.toAffine.Point) (hg : addOrderOf g = N)
        (hΔ : (V.fullKernelQuotient g N).Δ ≠ 0),
        ((E'.symm ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              x₁)).IsRoot z}) : LaurentSeries K)
          = @WeierstrassCurve.j _ _ (V.fullKernelQuotient g N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩)
    (y : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K a))).IsRoot z})
    (y' : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          x₁)).IsRoot z})
    (hyy' : (y' : LaurentSeries K) = ModularCurve.coeffMap (frobenius K q) (y : LaurentSeries K)) :
    HEq (E' y').1 ((E y).1.map (WeierstrassCurve.mapPointHom
      (ModularCurve.coeffMap (frobenius K q))
      (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype))) := by
  subst hV
  subst hx₁
  refine heq_of_eq ?_
  obtain ⟨g, hg, hCg⟩ := (E y).2
  have hN : (N : LaurentSeries K) ≠ 0 := natCast_laurent_ne_zero q N K hqN
  have hΔ : (((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient
      g N).Δ ≠ 0 :=
    ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_Δ_ne_zero _ hN g hg

  have hEy : E y = ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ := Subtype.ext hCg
  have hyj : (y : LaurentSeries K) = @WeierstrassCurve.j _ _
      (((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N)
      ⟨isUnit_iff_ne_zero.mpr hΔ⟩ := by
    rw [← hE g hg hΔ, ← hEy, Equiv.symm_apply_apply]

  have hg' : addOrderOf (WeierstrassCurve.mapPoint (ModularCurve.coeffMap (frobenius K q))
      (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) g) = N :=
    (WeierstrassCurve.addOrderOf_mapPoint _ g).trans hg
  have hΔ' : ((((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
      (ModularCurve.coeffMap (frobenius K q))).fullKernelQuotient
      (WeierstrassCurve.mapPoint (ModularCurve.coeffMap (frobenius K q))
        (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) g) N).Δ ≠ 0 :=
    ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_Δ_ne_zero _ hN _ hg'

  have hy'j : (y' : LaurentSeries K) = @WeierstrassCurve.j _ _
      ((((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
        (ModularCurve.coeffMap (frobenius K q))).fullKernelQuotient
        (WeierstrassCurve.mapPoint (ModularCurve.coeffMap (frobenius K q))
          (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) g) N)
      ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ := by
    rw [hyy', hyj]
    exact (ModularCurve.FullKernelQuotientRoots.fullKernelQuotient_mapPointHom_j
      (ModularCurve.coeffMap (frobenius K q)) g N hΔ hΔ').symm
  have hE'y' : E' y' = ⟨AddSubgroup.zmultiples (WeierstrassCurve.mapPoint
      (ModularCurve.coeffMap (frobenius K q))
      (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) g), _, hg', rfl⟩ := by
    rw [← Equiv.apply_symm_apply E' ⟨_, _, hg', rfl⟩]
    congr 1
    exact Subtype.ext (hy'j.trans (hE' _ hg' hΔ').symm)
  have hval' : (E' y').1 = AddSubgroup.zmultiples (WeierstrassCurve.mapPoint
      (ModularCurve.coeffMap (frobenius K q))
      (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype) g) := by
    rw [hE'y']
  rw [hval', hCg, AddMonoidHom.map_zmultiples, WeierstrassCurve.mapPointHom_apply]

private theorem P3_cycSubChain_val (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    (a : K) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    [h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h2 : ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h3 : (WfamD K a).IsElliptic]
    (C : {C : AddSubgroup ((WInt K a).map
        (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
      ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g}) :
    (cycSubChain q N K a ha0 ha1728 hqN C).1 =
      (C.1.map (WeierstrassCurve.reduceHom (WInt_residue_Δ_ne_zero K a ha0 ha1728))).map
        (WeierstrassCurve.mapPointHom
          (LaurentIntegerRing.laurentIntegersResidueEquiv K : _ →+* K)
          (W₀ := (WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K)))) := by
  unfold cycSubChain
  rfl

private theorem P3_chain_leg (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    (a a' : K) (hpow : a' = a ^ q) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (ha0' : a' ≠ 0) (ha1728' : a' ≠ 1728)
    [h1 : ((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h1' : ((WInt K a').map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h2 : ((WInt K a).map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h2' : ((WInt K a').map (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h3 : (WfamD K a).IsElliptic] [h3' : (WfamD K a').IsElliptic]
    (C : {C : AddSubgroup ((WInt K a).map
        (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
      ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (C' : {C : AddSubgroup ((WInt K a').map
        (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
      ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (hC : HEq C'.1 (C.1.map (WeierstrassCurve.mapPointHom
      (ModularCurve.coeffMap (frobenius K q))
      (W₀ := (WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype)))) :
    HEq (cycSubChain q N K a' ha0' ha1728' hqN C').1
      ((cycSubChain q N K a ha0 ha1728 hqN C).1.map
        (WeierstrassCurve.mapPointHom (frobenius K q) (W₀ := WfamD K a))) := by
  have e₁ := P3_Wg_map_coeffMap q K a a' hpow
  have e₂ := P3_WfamD_map_frobenius q K a a' hpow
  rw [P3_cycSubChain_val, P3_cycSubChain_val]
  refine P3_heq_of_forall_mem_iff e₂ fun x y h h' => ?_
  constructor
  ·
    intro hmem
    obtain ⟨P₁, hP₁, hP₁eq⟩ := AddSubgroup.mem_map.mp hmem
    obtain ⟨P₂, hP₂, rfl⟩ := AddSubgroup.mem_map.mp hP₁
    rcases P₂ with _ | ⟨X₂, Y₂, hXY₂⟩
    · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero] at hP₁eq
      exact absurd hP₁eq.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
    ·
      have hXY₂' : (((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
          (ModularCurve.coeffMap (frobenius K q))).toAffine.Nonsingular X₂ Y₂ := by
        rw [e₁]; exact hXY₂
      obtain ⟨P, hP, hPeq⟩ := AddSubgroup.mem_map.mp
        ((P3_mem_iff_of_heq e₁ hC hXY₂' hXY₂).mp hP₂)
      rcases P with _ | ⟨X, Y, hXY⟩
      · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero] at hPeq
        exact absurd hPeq.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
      rw [WeierstrassCurve.mapPointHom_apply, WeierstrassCurve.mapPoint_some,
        WeierstrassCurve.Affine.Point.some.injEq] at hPeq
      obtain ⟨rfl, rfl⟩ := hPeq
      by_cases hXA : X ∈ LaurentIntegerRing.laurentIntegers K
      · have hX₂A : ModularCurve.coeffMap (frobenius K q) X ∈ LaurentIntegerRing.laurentIntegers K :=
          (P3_coeffMap_frobenius_mem_iff q K X).mpr hXA
        have hYA : Y ∈ LaurentIntegerRing.laurentIntegers K :=
          WeierstrassCurve.Affine.Y_mem_of_X_mem _ hXY.1 hXA
        have hY₂A : ModularCurve.coeffMap (frobenius K q) Y ∈ LaurentIntegerRing.laurentIntegers K :=
          WeierstrassCurve.Affine.Y_mem_of_X_mem _ hXY₂.1 hX₂A

        rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_mem _ _ hX₂A] at hP₁eq

        obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hP₁eq
        refine AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.mem_map.mpr
          ⟨_, AddSubgroup.mem_map.mpr ⟨_, hP, rfl⟩, rfl⟩, ?_⟩
        rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_mem _ _ hXA]
        change WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some x y h
        refine WeierstrassCurve.Affine.Point.some_congr' ?_ ?_ _ _
        · rw [← hx]
          exact (P3_resEquiv_residue_coeffMap q K X hXA hX₂A).symm
        · rw [← hy]
          exact (P3_resEquiv_residue_coeffMap q K Y hYA hY₂A).symm
      · have hX₂A : ModularCurve.coeffMap (frobenius K q) X ∉ LaurentIntegerRing.laurentIntegers K :=
          fun h2 => hXA ((P3_coeffMap_frobenius_mem_iff q K X).mp h2)
        rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_notMem _ _ hX₂A] at hP₁eq
        simp only [map_zero] at hP₁eq
        exact absurd hP₁eq.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  ·
    intro hmem
    obtain ⟨P₁, hP₁, hP₁eq⟩ := AddSubgroup.mem_map.mp hmem
    obtain ⟨P₀, hP₀, rfl⟩ := AddSubgroup.mem_map.mp hP₁
    obtain ⟨P, hP, rfl⟩ := AddSubgroup.mem_map.mp hP₀
    rcases P with _ | ⟨X, Y, hXY⟩
    · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero, map_zero] at hP₁eq
      exact absurd hP₁eq.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
    by_cases hXA : X ∈ LaurentIntegerRing.laurentIntegers K
    · have hYA : Y ∈ LaurentIntegerRing.laurentIntegers K :=
        WeierstrassCurve.Affine.Y_mem_of_X_mem _ hXY.1 hXA
      have hX₂A : ModularCurve.coeffMap (frobenius K q) X ∈ LaurentIntegerRing.laurentIntegers K :=
        (P3_coeffMap_frobenius_mem_iff q K X).mpr hXA

      rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_mem _ _ hXA] at hP₁eq
      obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hP₁eq

      have hXY₂' : (((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).map
          (ModularCurve.coeffMap (frobenius K q))).toAffine.Nonsingular
          (ModularCurve.coeffMap (frobenius K q) X) (ModularCurve.coeffMap (frobenius K q) Y) :=
        (((WInt K a).map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.map_nonsingular
          (ModularCurve.coeffMap (frobenius K q)).injective X Y).mpr hXY
      have hXY₂ : ((WInt K a').map (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Nonsingular
          (ModularCurve.coeffMap (frobenius K q) X) (ModularCurve.coeffMap (frobenius K q) Y) := by
        rw [← e₁]; exact hXY₂'
      have hP₂ : WeierstrassCurve.Affine.Point.some _ _ hXY₂ ∈ C'.1 :=
        (P3_mem_iff_of_heq e₁ hC hXY₂' hXY₂).mpr
          (AddSubgroup.mem_map.mpr ⟨_, hP, rfl⟩)
      have hY₂A : ModularCurve.coeffMap (frobenius K q) Y ∈ LaurentIntegerRing.laurentIntegers K :=
        WeierstrassCurve.Affine.Y_mem_of_X_mem _ hXY₂.1 hX₂A
      refine AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.mem_map.mpr ⟨_, hP₂, rfl⟩, ?_⟩
      rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_mem _ _ hX₂A]
      change WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some x y h'
      refine WeierstrassCurve.Affine.Point.some_congr' ?_ ?_ _ _
      · rw [← hx]
        exact P3_resEquiv_residue_coeffMap q K X hXA hX₂A
      · rw [← hy]
        exact P3_resEquiv_residue_coeffMap q K Y hYA hY₂A
    · rw [P3_reduceHom_apply, WeierstrassCurve.reducePoint_some_of_notMem _ _ hXA] at hP₁eq
      simp only [map_zero] at hP₁eq
      exact absurd hP₁eq.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)

private theorem P3_place_leg (data : ModularCurve.ModularPolynomialData N)
    [DecidableEq (LaurentSeries K)]
    (a a' : GenVal q K) (hpow : ((a' : GenVal q K) : K) = ((a : GenVal q K) : K) ^ q)
    (F : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} ≃ {w : PlacesU q N K // centreP q N K w = a})
    (hF : ∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = xZero K (a : K) ∧
        ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ ((F y : PlacesU q N K) :
            AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)).toValuationSubring
          ↔ 0 ≤ (ι x).order)
    (F' : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a' : K)))).IsRoot z} ≃ {w : PlacesU q N K // centreP q N K w = a'})
    (hF' : ∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = xZero K (a' : K) ∧
        ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ ((F' y : PlacesU q N K) :
            AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)).toValuationSubring
          ↔ 0 ≤ (ι x).order)
    (u : PlacesU q N K) (hu : centreP q N K u = a)
    (hw' : ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
           ∈ ModularCurve.ssPlaces q N K
          ∧ (ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))).evalAt
                (ModularCurve.jGeomGen K N) ≠ 0
          ∧ (ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))).evalAt
                (ModularCurve.jGeomGen K N) ≠ 1728)
    (hc' : centreP q N K ⟨_, hw'⟩ = a') :
    ((F'.symm ⟨⟨_, hw'⟩, hc'⟩ : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a' : K)))).IsRoot z}) : LaurentSeries K)
      = ModularCurve.coeffMap (frobenius K q)
          ((F.symm ⟨u, hu⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K (a : K)))).IsRoot z}) : LaurentSeries K) := by
  have hx₀ : ModularCurve.coeffMap (frobenius K q) (xZero K (a : K)) = xZero K (a' : K) := by
    rw [coeffMap_frobenius_xZero, hpow]

  have hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (xZero K (a' : K)))).IsRoot
      (ModularCurve.coeffMap (frobenius K q) ((F.symm ⟨u, hu⟩ : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z}) : LaurentSeries K)) := by
    rw [← hx₀, ← P3_fibrePoly_map_coeffMap]
    exact (F.symm ⟨u, hu⟩).2.map
  obtain ⟨ι, hιj, hιjN, hιw⟩ := hF (F.symm ⟨u, hu⟩)
  obtain ⟨ι', hι'j, hι'jN, hι'w⟩ := hF' ⟨_, hroot⟩
  rw [Equiv.apply_symm_apply] at hιw

  have key := ModularCurve.arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ q N K ι ι'
    (by
      show ι' (ModularCurve.jGeomGen K N)
          = ModularCurve.coeffMap (frobenius K q) (ι (ModularCurve.jGeomGen K N))
      rw [hι'j, hιj, hx₀])
    (by
      show ι' (ModularCurve.jNGeomGen K N)
          = ModularCurve.coeffMap (frobenius K q) (ι (ModularCurve.jNGeomGen K N))
      rw [hι'jN, hιjN])
    (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
    ((F' ⟨_, hroot⟩ : PlacesU q N K) :
      AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)) hιw hι'w
  have hF'y : F' ⟨_, hroot⟩ = ⟨⟨_, hw'⟩, hc'⟩ := Subtype.ext (Subtype.ext key.symm)
  rw [← hF'y, Equiv.symm_apply_apply]

end FrobeniusEquivariance
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

private theorem P3_frobenius_square (data : ModularCurve.ModularPolynomialData N)
    (hqN : ¬ q ∣ N) [DecidableEq (LaurentSeries K)]
    [DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K))]
    (a a' : GenVal q K) (hpow : ((a' : GenVal q K) : K) = ((a : GenVal q K) : K) ^ q)
    [h1 : ((WInt K (a : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h1' : ((WInt K (a' : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic]
    [h2 : ((WInt K (a : K)).map
      (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h2' : ((WInt K (a' : K)).map
      (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic]
    [h3 : (WfamD K (a : K)).IsElliptic] [h3' : (WfamD K (a' : K)).IsElliptic]
    (F : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} ≃ {w : PlacesU q N K // centreP q N K w = a})
    (hF : ∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = xZero K (a : K) ∧
        ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ ((F y : PlacesU q N K) :
            AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)).toValuationSubring
          ↔ 0 ≤ (ι x).order)
    (F' : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a' : K)))).IsRoot z} ≃ {w : PlacesU q N K // centreP q N K w = a'})
    (hF' : ∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = xZero K (a' : K) ∧
        ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ ((F' y : PlacesU q N K) :
            AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)).toValuationSubring
          ↔ 0 ≤ (ι x).order)
    (E : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a : K)))).IsRoot z} ≃
        {C : AddSubgroup ((WInt K (a : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
          ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (hE : ∀ (g : ((WInt K (a : K)).map
          (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point)
        (hg : addOrderOf g = N)
        (hΔ : (((WInt K (a : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N).Δ ≠ 0),
        ((E.symm ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K (a : K)))).IsRoot z}) : LaurentSeries K)
          = @WeierstrassCurve.j _ _ (((WInt K (a : K)).map
              (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩)
    (E' : {z : LaurentSeries K //
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (xZero K (a' : K)))).IsRoot z} ≃
        {C : AddSubgroup ((WInt K (a' : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point //
          ∃ g, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})
    (hE' : ∀ (g : ((WInt K (a' : K)).map
          (LaurentIntegerRing.laurentIntegers K).subtype).toAffine.Point)
        (hg : addOrderOf g = N)
        (hΔ : (((WInt K (a' : K)).map
            (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N).Δ ≠ 0),
        ((E'.symm ⟨AddSubgroup.zmultiples g, g, hg, rfl⟩ : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
              (xZero K (a' : K)))).IsRoot z}) : LaurentSeries K)
          = @WeierstrassCurve.j _ _ (((WInt K (a' : K)).map
              (LaurentIntegerRing.laurentIntegers K).subtype).fullKernelQuotient g N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩)
    (u : PlacesU q N K) (hu : centreP q N K u = a)
    (hw' : ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
           ∈ ModularCurve.ssPlaces q N K
          ∧ (ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))).evalAt
                (ModularCurve.jGeomGen K N) ≠ 0
          ∧ (ModularCurve.arithFrobC q K N
             • (u : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))).evalAt
                (ModularCurve.jGeomGen K N) ≠ 1728)
    (hc' : centreP q N K ⟨_, hw'⟩ = a') :
    ((toModuli (WfamD K (a' : K)) N
        ((F'.symm.trans (E'.trans (cycSubChain q N K (a' : K) a'.2.2.1 a'.2.2.2 hqN)))
          ⟨⟨_, hw'⟩, hc'⟩) :
        {x : ModularCurve.ModuliPoint N K //
          ModularCurve.ModuliPoint.j x = (WfamD K (a' : K)).j}) :
        ModularCurve.ModuliPoint N K)
      = ModularCurve.ModuliPoint.map (frobenius K q)
          ((toModuli (WfamD K (a : K)) N
              ((F.symm.trans (E.trans (cycSubChain q N K (a : K) a.2.2.1 a.2.2.2 hqN)))
                ⟨u, hu⟩) :
            {x : ModularCurve.ModuliPoint N K //
              ModularCurve.ModuliPoint.j x = (WfamD K (a : K)).j}) :
            ModularCurve.ModuliPoint N K) := by

  have hyy' := P3_place_leg q N K data a a' hpow F hF F' hF' u hu hw' hc'

  have e₁ := P3_Wg_map_coeffMap q K (a : K) (a' : K) hpow
  have e₂ := P3_WfamD_map_frobenius q K (a : K) (a' : K) hpow
  have hx₁ : ModularCurve.coeffMap (frobenius K q) (xZero K (a : K)) = xZero K (a' : K) := by
    rw [coeffMap_frobenius_xZero, hpow]

  have hsub := P3_subgroup_leg q N K data hqN (a : K)
    ((WInt K (a' : K)).map (LaurentIntegerRing.laurentIntegers K).subtype) e₁ (xZero K (a' : K)) hx₁
    E hE E' hE' (F.symm ⟨u, hu⟩) (F'.symm ⟨⟨_, hw'⟩, hc'⟩) hyy'

  have hchain := P3_chain_leg q N K hqN (a : K) (a' : K) hpow a.2.2.1 a.2.2.2 a'.2.2.1 a'.2.2.2
    (E (F.symm ⟨u, hu⟩)) (E' (F'.symm ⟨⟨_, hw'⟩, hc'⟩)) hsub

  exact P3_toModuli_natural_of_map_eq N K (frobenius K q) (WfamD K (a : K)) (WfamD K (a' : K))
    e₂ _ _ hchain

private theorem exists_place_side_equivs (hqN : ¬ q ∣ N) :
    ∃ (Wfam : GenVal q K → {W : WeierstrassCurve K // W.IsElliptic})
      (hfj : ∀ a : GenVal q K, @WeierstrassCurve.j K _ (Wfam a).1 (Wfam a).2 = (a : K))
      (P : (a : GenVal q K) → ({w : PlacesU q N K // centreP q N K w = a} ≃
        {C : AddSubgroup (Wfam a).1.toAffine.Point //
          ∃ g : (Wfam a).1.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g})),
      ∀ (a a' : GenVal q K) (_ : (a' : K) = (a : K) ^ q)
        (u : PlacesU q N K) (hu : centreP q N K u = a)
        (hw' : ModularCurve.arithFrobC q K N
                 • (u : Place K (ModularCurve.modularFunctionFieldC K N))
               ∈ ModularCurve.ssPlaces q N K
              ∧ (ModularCurve.arithFrobC q K N
                 • (u : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 0
              ∧ (ModularCurve.arithFrobC q K N
                 • (u : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 1728)
        (hc' : centreP q N K ⟨_, hw'⟩ = a'),
        haveI := (Wfam a).2
        haveI := (Wfam a').2
        ((toModuli (Wfam a').1 N (P a' ⟨⟨_, hw'⟩, hc'⟩) :
            {x : ModularCurve.ModuliPoint N K //
              ModularCurve.ModuliPoint.j x = @WeierstrassCurve.j K _ (Wfam a').1 (Wfam a').2}) :
            ModularCurve.ModuliPoint N K)
          = ModularCurve.ModuliPoint.map (frobenius K q)
              ((toModuli (Wfam a).1 N (P a ⟨u, hu⟩) :
                {x : ModularCurve.ModuliPoint N K //
                  ModularCurve.ModuliPoint.j x = @WeierstrassCurve.j K _ (Wfam a).1 (Wfam a).2}) :
                ModularCurve.ModuliPoint N K) := by
  classical
  haveI : DecidableEq (LaurentSeries K) := Classical.decEq _
  haveI : DecidableEq (IsLocalRing.ResidueField ↥(LaurentIntegerRing.laurentIntegers K)) :=
    Classical.decEq _
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible N
  have inst1 : ∀ a : GenVal q K,
      ((WInt K (a : K)).map (LaurentIntegerRing.laurentIntegers K).subtype).IsElliptic :=
    fun a => isElliptic_WInt_subtype K _ a.2.2.1 a.2.2.2
  have inst2 : ∀ a : GenVal q K,
      ((WInt K (a : K)).map
        (IsLocalRing.residue (LaurentIntegerRing.laurentIntegers K))).IsElliptic :=
    fun a => isElliptic_WInt_residue K _ a.2.2.1 a.2.2.2
  have inst3 : ∀ a : GenVal q K, (WfamD K (a : K)).IsElliptic :=
    fun a => isElliptic_WfamD K _ a.2.2.1 a.2.2.2
  choose F hF using fun a : GenVal q K => P1_fibre_roots_equiv q N K data hqN a
  choose E hE using fun a : GenVal q K =>
    P2_roots_cycSub_equiv q N K data hqN a (h1 := inst1 a)
  refine ⟨fun a => ⟨WfamD K (a : K), inst3 a⟩,
    fun a => j_WfamD K _ a.2.2.1 a.2.2.2,
    fun a =>
      haveI := inst1 a
      haveI := inst2 a
      haveI := inst3 a
      (F a).symm.trans ((E a).trans (cycSubChain q N K (a : K) a.2.2.1 a.2.2.2 hqN)), ?_⟩
  intro a a' hpow u hu hw' hc'
  exact P3_frobenius_square q N K data hqN a a' hpow
    (h1 := inst1 a) (h1' := inst1 a') (h2 := inst2 a) (h2' := inst2 a')
    (h3 := inst3 a) (h3' := inst3 a')
    (F a) (hF a) (F a') (hF a') (E a) (hE a) (E a') (hE a') u hu hw' hc'

private theorem toModuli_bijective (hqN : ¬ q ∣ N) (W : WeierstrassCurve K) [W.IsElliptic]
    (hss : W.j ∈ ModularCurve.ssJSet q K) (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728) :
    Function.Bijective (toModuli W N) := by
  have hq : q.Prime := Fact.out
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hj0 (ModularCurve.eq_zero_of_mem_ssJSet_two W.j hss
      (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet 2 hss))
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hj0 (ModularCurve.eq_zero_of_mem_ssJSet_three W.j hss
      (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet 3 hss))
  have h2 : (2 : K) ≠ 0 := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff K q 2).mp h))
  have h3 : (3 : K) ≠ 0 := fun h =>
    hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
      ((CharP.cast_eq_zero_iff K q 3).mp h))
  have h₁ : Nat.card {C : AddSubgroup W.toAffine.Point //
      ∃ g : W.toAffine.Point, addOrderOf g = N ∧ C = AddSubgroup.zmultiples g}
      = ModularCurve.dedekindPsi N := by
    refine natCard_cycSub_zmultiples_eq_of_card N ?_
    intro d hd
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      exact fun h => hN (by rw [Nat.cast_mul, h, zero_mul])
    exact WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) W (n := d) hdK
  have h₂ : Nat.card {x : ModularCurve.ModuliPoint N K //
      ModularCurve.ModuliPoint.j x = W.j} = ModularCurve.dedekindPsi N :=
    ModularCurve.natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero N K hN h2 h3
      W.j hj0 hj1728
  exact toModuli_bijective_of_natCard_eq_dedekindPsi W N h₁ h₂

end
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

private theorem fibre_of_generic_centre_skeleton
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type u) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K] :
    ∃ e : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728} ≃
          {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728},
      (∀ w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728},
        ModularCurve.ModuliPoint.j ((e w : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = (w : Place K (ModularCurve.modularFunctionFieldC K N)).evalAt
              (ModularCurve.jGeomGen K N)) ∧
      (∀ (w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728})
        (hw' : ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))
               ∈ ModularCurve.ssPlaces q N K
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 0
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 1728),
        ((e ⟨_, hw'⟩ : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = ModularCurve.ModuliPoint.map (frobenius K q)
              ((e w : {x : ModularCurve.ModuliPoint N K //
                  x ∈ ModularCurve.ssLocus q N K
                    ∧ ModularCurve.ModuliPoint.j x ≠ 0
                    ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)) := by
  classical
  obtain ⟨Wfam, hfj, P, hsq⟩ := exists_place_side_equivs q N K hqN
  let E : (a : GenVal q K) → ({w : PlacesU q N K // centreP q N K w = a} ≃
      {x : ModuliU q N K // centreM q N K x = a}) := fun a =>
    haveI := (Wfam a).2
    (P a).trans ((Equiv.ofBijective (toModuli (Wfam a).1 N)
      (toModuli_bijective q N K hqN (Wfam a).1
        (by rw [hfj a]; exact a.2.1)
        (by rw [hfj a]; exact a.2.2.1)
        (by rw [hfj a]; exact a.2.2.2))).trans
      (reshuffle q N K a (Wfam a).1 (hfj a)))
  refine ⟨(part (centreP q N K)).trans
    ((Equiv.sigmaCongrRight E).trans (part (centreM q N K)).symm), ?_, ?_⟩
  · intro w
    exact congrArg Subtype.val (E (centreP q N K w) ⟨w, rfl⟩).2
  · intro w hw'
    have hrat : (w : Place K (ModularCurve.modularFunctionFieldC K N)).IsRational := w.2.1.1
    have hj : ModularCurve.jGeomGen K N
        ∈ (w : Place K (ModularCurve.modularFunctionFieldC K N)).toValuationSubring :=
      w.2.1.2.1.1
    have ha' : ((centreP q N K ⟨_, hw'⟩ : GenVal q K) : K)
        = ((centreP q N K w : GenVal q K) : K) ^ q :=
      evalAt_arithFrobC_smul_jGeomGen q N K
        (w : Place K (ModularCurve.modularFunctionFieldC K N)) hrat hj
    exact hsq (centreP q N K w) (centreP q N K ⟨_, hw'⟩) ha' w rfl hw' rfl

end ModularCurve.GenericCentreFibre
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"
p2m_reactivate "P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.LaurentIntegerRing P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve.genFibre P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ.GenericFibreCurve"

theorem solution
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K] :
    ∃ e : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728} ≃
          {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728},
      (∀ w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728},
        ModularCurve.ModuliPoint.j ((e w : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = (w : Place K (ModularCurve.modularFunctionFieldC K N)).evalAt
              (ModularCurve.jGeomGen K N)) ∧
      (∀ (w : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 0
              ∧ w.evalAt (ModularCurve.jGeomGen K N) ≠ 1728})
        (hw' : ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))
               ∈ ModularCurve.ssPlaces q N K
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 0
              ∧ (ModularCurve.arithFrobC q K N
                 • (w : Place K (ModularCurve.modularFunctionFieldC K N))).evalAt
                    (ModularCurve.jGeomGen K N) ≠ 1728),
        ((e ⟨_, hw'⟩ : {x : ModularCurve.ModuliPoint N K //
            x ∈ ModularCurve.ssLocus q N K
              ∧ ModularCurve.ModuliPoint.j x ≠ 0
              ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)
          = ModularCurve.ModuliPoint.map (frobenius K q)
              ((e w : {x : ModularCurve.ModuliPoint N K //
                  x ∈ ModularCurve.ssLocus q N K
                    ∧ ModularCurve.ModuliPoint.j x ≠ 0
                    ∧ ModularCurve.ModuliPoint.j x ≠ 1728}) : ModularCurve.ModuliPoint N K)) :=
  ModularCurve.GenericCentreFibre.fibre_of_generic_centre_skeleton q N hqN K

end S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ
end P2MW
export P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ (solution)
