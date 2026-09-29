-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a3169af5-b819-5038-a059-72e21f0bfea1

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq.ModularCurve"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul jq coeff_jq_neg_one evalAtJ evalAtJ_X ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral deg_eq_one_modularFunctionFieldC KroneckerCongruence isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen IsCentreOf ssJSet towerInclBar deg_eq_one_modularFunctionFieldBar nonempty_modularPolynomialData"
namespace TowerReduction
p2m_open "ModularCurve"

private theorem isRational_of_isCurveOver {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N]
    [IsCurveOver k ↥(modularFunctionFieldC k N)] (w : Place k ↥(modularFunctionFieldC k N)) : w.IsRational := by
  have h : w.deg = 1 := deg_eq_one_modularFunctionFieldC k N w
  haveI : Module.Finite k w.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0) (h : Module.finrank k w.ResidueField = 1)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

private theorem mem_of_monic_of_eval_eq_zero {F : Type*} [Field F] (B : ValuationSubring F) {p : Polynomial F}
    (hp : p.Monic) (hcoeff : ∀ i, p.coeff i ∈ B) {z : F} (hz : p.eval z = 0) : z ∈ B := by
  have hlift : p ∈ Polynomial.lifts (algebraMap B F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨p.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨Q, hQmap, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hp
  have hint : IsIntegral B z := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [show Polynomial.eval₂ (algebraMap B F) z Q = (Q.map _).eval z from (Polynomial.eval_map _ z).symm,
      hQmap, hz]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

private theorem isRational_bar {N : ℕ} [NeZero N]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : W.IsRational := by
  have h : W.deg = 1 := deg_eq_one_modularFunctionFieldBar N W
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0) (h : Module.finrank (AlgebraicClosure ℚ) W.ResidueField = 1)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ)).2

private theorem ord_sub_evalAt_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    (hrat : w.IsRational) {f : F} (hf : f ∈ w.toValuationSubring)
    (hne : f - algebraMap K F (w.evalAt f) ≠ 0) :
    0 < w.ord (f - algebraMap K F (w.evalAt f)) := by
  have hmem : f - algebraMap K F (w.evalAt f) ∈ w.toValuationSubring := sub_mem hf (w.algebraMap_mem' _)
  rcases eq_or_ne (w.ord (f - algebraMap K F (w.evalAt f))) 0 with h0 | h0
  · exfalso
    refine w.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K w.ResidueField (w.evalAt (f - algebraMap K F (w.evalAt f))) = 0 := by
      rw [w.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (w.evalAt f), hmem⟩ : w.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K w.toValuationSubring (w.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (w.evalAt f) = f - (algebraMap K w.toValuationSubring (w.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← w.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K w.ResidueField).injective).mp hres
  · have hnonneg := w.ord_nonneg_of_mem hmem
    omega

private theorem exists_ord_sub_algebraMap_pos (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (x : A)
    (hx : 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))) :
    ∃ y : A, 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (y : AlgebraicClosure ℚ)) := by
  classical
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  have hrat : W.IsRational := isRational_bar W

  have hj0 : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) ∈ W.toValuationSubring := by
    by_cases h0 : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ) = 0
    · rw [sub_eq_zero.mp h0]
      exact W.algebraMap_mem' _
    · have hmem := W.mem_of_ord_nonneg h0 hx.le
      have hadd := add_mem hmem (W.algebraMap_mem' (x : AlgebraicClosure ℚ))
      rwa [sub_add_cancel] at hadd

  let evO : Polynomial ℤ →+* W.toValuationSubring :=
    Polynomial.eval₂RingHom (Int.castRingHom W.toValuationSubring) ⟨_, hj0⟩
  let evF : Polynomial ℤ →+* ↥(modularFunctionFieldBar N) := W.toValuationSubring.subtype.comp evO

  have hcomp : (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))).comp evF
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, evalAtJ_X]
    show algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))
        (W.toValuationSubring.subtype (Polynomial.eval₂ (Int.castRingHom W.toValuationSubring) ⟨_, hj0⟩
          Polynomial.X)) = coeffEmb (AlgebraicClosure ℚ) jq
    rw [Polynomial.eval₂_X]
    rfl

  have hΦF : dataN.Φ.eval₂ evF (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) = 0 := by
    apply (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [map_zero, Polynomial.hom_eval₂, hcomp]
    have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) dataN.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂] at h
    exact h

  have hjN0 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) ∈ W.toValuationSubring := by
    refine mem_of_monic_of_eval_eq_zero W.toValuationSubring (p := dataN.Φ.map evF) (dataN.monic.map evF)
      (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      exact (evO (dataN.Φ.coeff i)).2
    · rw [Polynomial.eval_map]
      exact hΦF

  have hevj : W.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) = (x : AlgebraicClosure ℚ) := by
    rw [W.evalAt_congr hj0 (W.algebraMap_mem' (x : AlgebraicClosure ℚ)) (Or.inr hx)]
    exact W.evalAt_algebraMap (x : AlgebraicClosure ℚ)

  let e : AlgebraicClosure ℚ ≃+* W.ResidueField :=
    RingEquiv.ofBijective (algebraMap (AlgebraicClosure ℚ) W.ResidueField)
      ⟨W.algebraMap_residueField_injective, hrat⟩
  let ψ : W.toValuationSubring →+* AlgebraicClosure ℚ :=
    e.symm.toRingHom.comp (IsLocalRing.residue W.toValuationSubring)
  have hψ : ∀ (f : ↥(modularFunctionFieldBar N)) (hf : f ∈ W.toValuationSubring), ψ ⟨f, hf⟩ = W.evalAt f := by
    intro f hf
    apply W.algebraMap_residueField_injective
    rw [W.algebraMap_evalAt hrat hf]
    show e (e.symm (IsLocalRing.residue W.toValuationSubring ⟨f, hf⟩)) = _
    exact e.apply_symm_apply _

  have hΦO : dataN.Φ.eval₂ evO ⟨_, hjN0⟩ = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ dataN.Φ evO W.toValuationSubring.subtype ⟨_, hjN0⟩
    show W.toValuationSubring.subtype (dataN.Φ.eval₂ evO ⟨_, hjN0⟩)
        = ((0 : W.toValuationSubring) : ↥(modularFunctionFieldBar N))
    rw [h, ZeroMemClass.coe_zero]
    exact hΦF
  have hψev : ψ.comp evO
      = Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    show ψ (Polynomial.eval₂ (Int.castRingHom W.toValuationSubring) ⟨_, hj0⟩ Polynomial.X)
        = (x : AlgebraicClosure ℚ)
    rw [Polynomial.eval₂_X, hψ, hevj]
  have hroot : dataN.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ))
      (W.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N))) = 0 := by
    have h := congrArg ψ hΦO
    rw [map_zero, Polynomial.hom_eval₂, hψev, hψ] at h
    exact h

  set y0 : AlgebraicClosure ℚ := W.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) with hy0

  have hyA : y0 ∈ A := by
    refine mem_of_monic_of_eval_eq_zero A
      (p := dataN.Φ.map
        (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ)))
      (dataN.monic.map _) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map, Polynomial.coe_eval₂RingHom]
      have h := Polynomial.hom_eval₂ (dataN.Φ.coeff i) (Int.castRingHom A) A.subtype x
      rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A))
        (Int.castRingHom (AlgebraicClosure ℚ))] at h
      show Polynomial.eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (A.subtype x) (dataN.Φ.coeff i) ∈ A
      rw [← h]
      exact SetLike.coe_mem _
    · rw [Polynomial.eval_map]
      exact hroot

  have hne : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) y0 ≠ 0 := by
    intro h
    have h' := congrArg
      (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-(N : ℤ)))
      (sub_eq_zero.mp h)
    have hl : (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-(N : ℤ)))
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ :
          ↥(modularFunctionFieldBar N)) = 1 := by
      show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)).coeff (-(N : ℤ)) = 1
      rw [coeffEmb_coeff, show (-(N : ℤ)) = (N : ℤ) * (-1) from (mul_neg_one (N : ℤ)).symm, qExpand_coeff_mul,
        coeff_jq_neg_one, map_one]
    have hr : (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-(N : ℤ)))
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) y0) = 0 := by
      show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) y0).coeff (-(N : ℤ)) = 0
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne]
      exact neg_ne_zero.mpr (by exact_mod_cast NeZero.ne N)
    exact one_ne_zero (hl.symm.trans (h'.trans hr))
  exact ⟨⟨y0, hyA⟩, ord_sub_evalAt_pos W hrat hjN0 hne⟩

end ModularCurve.TowerReduction

theorem solution
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    [IsCurveOver k ↥(modularFunctionFieldC k N)] {red : ↥A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hι : (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)).toRingHom.IsIntegral)
    (a : k) (hss : a ∈ ssJSet q k)
    (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hVj : ∃ x : A, red x = a ∧
      0 < V'.ord (jFun 1 q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (x : AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : V.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) hι = V') :
    P.reduceFst V ∈ ssPlaces q N k ∧ (P.reduceFst V).evalAt (jGeomGen k N) = a := by
  obtain ⟨x, hxa, hxpos⟩ := hVj

  have hτj :
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) (jFun 1 q)
        = jFun N q := rfl
  have he : 0 < Place.ramificationIndexAlong
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) V := by
    letI := algebraAlong
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q))
    haveI := isScalarTower_along
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q))
    haveI := isIntegral_along
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) hι
    exact V.ramificationIndex_pos (F := ↥(modularFunctionFieldBar (1 * q)))
  have hup : 0 < V.ord (jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ)) := by
    have key := Place.ord_restrictAlong
      (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) hι V
      (jFun 1 q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))
    rw [hV, map_sub, hτj, AlgHom.commutes] at key
    rw [key]
    exact mul_pos (by exact_mod_cast he) hxpos

  have hαj : (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) = jFun N q := rfl
  have hdown : 0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ)) := by
    have key := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
          ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))
    rw [map_sub, hαj, AlgHom.commutes] at key
    have hnn : (0 : ℤ) ≤ (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) V : ℤ) :=
      Int.natCast_nonneg _
    rw [key] at hup
    nlinarith [hup, hnn]

  obtain ⟨y, hy⟩ := ModularCurve.TowerReduction.exists_ord_sub_algebraMap_pos N A _ x hdown
  have hc : IsCentreOf k N (red x, red y) (P.reduceFst V) :=
    And.intro (P.d0_j _ x hdown) (P.d0_jN _ y hy)

  have hrat : (P.reduceFst V).IsRational := ModularCurve.TowerReduction.isRational_of_isCurveOver _
  have hev : (P.reduceFst V).evalAt (jGeomGen k N) = red x := hc.evalAt_jGeomGen
  refine ⟨(mem_ssPlaces_iff q N k).mpr ((isSupersingularPlace_iff q N k _).mpr ?_), hev.trans hxa⟩
  exact ⟨hrat, hc.isAffineGeomPlace, by rw [hev, hxa]; exact hss⟩

#print axioms solution

end S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq (solution)
