-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/44e6b329-ca6e-5405-87e9-da2a64f3c7e5

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Classical

namespace SpecJReduction

variable {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem sheet
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 := by
  exact ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one hqN P b hb

variable {P : PlaceSpecialization A q N data hKr k red hα hβ}

private noncomputable def jFull : modularFunctionFieldFull (N * q) :=
  ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩

private noncomputable def jQFull : modularFunctionFieldFull (N * q) :=
  ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩

private theorem coe_jFun : ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem jFun_mem_integers₁ (R : ProlongationTuple P) : jFun N q ∈ R.R₁.integers := by
  rw [R.mem_integersFst_iff, coe_jFun]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _ (CharPReduction.jqModC_mem_modularRing _ _)

private theorem red_mk_eq_intCast (red : A →+* k) {x : AlgebraicClosure ℚ} (h : x ∈ A) {c : ℤ}
    (hx : x = (c : AlgebraicClosure ℚ)) : red ⟨x, h⟩ = (c : k) := by
  subst hx
  have hc : (⟨(c : AlgebraicClosure ℚ), h⟩ : A) = (c : A) := Subtype.ext (by simp)
  rw [hc, map_intCast]

private theorem residue₁_jFun (R : ProlongationTuple P) (h₁ : jFun N q ∈ R.R₁.integers) :
    R.residue₁ ⟨jFun N q, h₁⟩ = ⟨jqModC k, jqModC_mem k N⟩ := by
  have hmem : ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := (R.mem_integersFst_iff _).mp h₁
  obtain ⟨h, hres⟩ := R.residue₁_eq_modularRedLocHom (jFun N q) hmem
  apply Subtype.ext
  rw [residue₁_apply]
  refine Eq.trans (hres.trans ?_) rfl
  erw [CharPReduction.redLocHom_apply]
  have hr : (⟨((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hmem⟩ :
        CharPReduction.modularLocalized (N * q) A.toSubring red)
      = ⟨((⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring⟩ :
            CharPReduction.modularRing (N * q) A.toSubring) : LaurentSeries (AlgebraicClosure ℚ)),
          CharPReduction.subring_le_localizedAtKer A.toSubring red
            (CharPReduction.modularRing (N * q) A.toSubring)
            (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)
            (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)⟩ :=
    Subtype.ext (coe_jFun (N := N) (q := q))
  rw [hr]
  refine (CharPReduction.redLoc_coe _).trans ?_
  rw [CharPReduction.redRes_apply]
  ext n
  rw [CharPReduction.coeffRed_coeff]
  show red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, _⟩ = (jqModC k).coeff n
  rw [coeff_jqModC_eq_intCast (R := k)]
  exact red_mk_eq_intCast red _ (coeff_jqModC_eq_intCast (R := AlgebraicClosure ℚ) n)

private theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jFun N q) = jQFun N q := by
  have hex := ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out) hqN
  have hAL := ModularCurve.isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have h1 := (hAL 1 inferInstance (one_dvd N)).1
  show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
      ⟨coeffEmb (AlgebraicClosure ℚ) (jFull (N := N) (q := q)).1, coeffEmb_mem_laurentBaseChange _ (jFull (N := N) (q := q)).2⟩
    = ⟨coeffEmb (AlgebraicClosure ℚ) (jQFull (N := N) (q := q)).1, coeffEmb_mem_laurentBaseChange _ (jQFull (N := N) (q := q)).2⟩
  rw [geomAut_coeffEmb]
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (atkinLehnerInvolutionFull N q (jFull (N := N) (q := q))).1 = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
  have h1' : atkinLehnerInvolutionFull N q (jFull (N := N) (q := q)) = jQFull (N := N) (q := q) := by
    have e1 : (jFull (N := N) (q := q))
        = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :=
      Subtype.ext (qExpand_one_apply (R := ℚ) jq).symm
    rw [e1, h1]
    exact Subtype.ext (qExpand_congr (R := ℚ) (one_mul q) jq)
  rw [h1']
  rfl

private noncomputable def innerHom (R : ProlongationTuple P) : Polynomial ℤ →+* R.R₁.integers :=
  Polynomial.eval₂RingHom (Int.castRingHom R.R₁.integers)
    (⟨jFun N q, jFun_mem_integers₁ R⟩ : R.R₁.integers)

private theorem eval₂_map_innerHom (R : ProlongationTuple P) :
    Polynomial.eval₂ (algebraMap R.R₁.integers (modularFunctionFieldBar (N * q))) (jQFun N q)
      (data.Φ.map (innerHom R)) = 0 := by
  rw [Polynomial.eval₂_map]
  apply Subtype.ext
  show (modularFunctionFieldBar (N * q)).val.toRingHom (Polynomial.eval₂ _ _ _)
      = (modularFunctionFieldBar (N * q)).val.toRingHom 0
  rw [map_zero, Polynomial.hom_eval₂]
  have hcomp : ((modularFunctionFieldBar (N * q)).val.toRingHom.comp
        ((algebraMap R.R₁.integers (modularFunctionFieldBar (N * q))).comp (innerHom R)))
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · simp [innerHom, evalAtJ, jFun]
  rw [hcomp]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [Polynomial.hom_eval₂, map_zero] at h0
  exact h0

private theorem mem_of_isIntegral_valuationSubring {K : Type*} [Field K] (V : ValuationSubring K)
    (x : K) (hx : IsIntegral V x) : x ∈ V := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  rw [← hy]
  exact y.2

private theorem jQFun_mem_integers₁ (R : ProlongationTuple P) : jQFun N q ∈ R.R₁.integers :=
  @mem_of_isIntegral_valuationSubring (modularFunctionFieldBar (N * q)) _ R.R₁.integers (jQFun N q)
    ⟨data.Φ.map (innerHom R), data.monic.map _, eval₂_map_innerHom R⟩

private theorem jFun_mem_integers₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P) :
    jFun N q ∈ R.R₂.integers := by
  rw [R.mem_integersSnd_iff, atkinLehnerBar_jFun hqN]
  exact (R.mem_integersFst_iff _).mp (jQFun_mem_integers₁ R)

private theorem residue_jFun_ne_zero (R : ProlongationTuple P) (h₁ : jFun N q ∈ R.R₁.integers) :
    R.R₁.residue ⟨jFun N q, h₁⟩ ≠ 0 := by
  intro h0
  have hC := residue₁_jFun R h₁
  rw [residue₁_apply, h0, map_zero] at hC
  have hser := congrArg (fun x : modularFunctionFieldC k N => (x : LaurentSeries k)) hC
  simp only [ZeroMemClass.coe_zero] at hser
  exact jqModC_ne_zero_of_nontrivial (R := k) hser.symm

private theorem residue_jQFun_ne_zero (R : ProlongationTuple P) (hE : jQFun N q ∈ R.R₁.integers) :
    R.R₁.residue ⟨jQFun N q, hE⟩ ≠ 0 := by
  set y : LaurentSeries A := qExpand A q (jqModC A) with hy_def
  have helt : coeffMap A.subtype y = (jQFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    show coeffMap A.subtype (qExpand A q (jqModC A)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [coeffMap_qExpand, coeffMap_jqModC, coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := helt ▸ (jQFun N q).2
  obtain ⟨h, hser⟩ := R.residue₁_coeffMap y hy
  have hel : (⟨jQFun N q, hE⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hy⟩, h⟩ :=
    Subtype.ext (Subtype.ext helt.symm)
  rw [hel]
  intro h0
  rw [h0] at hser
  simp only [ZeroMemClass.coe_zero] at hser

  have hk := congrArg (coeffMap R.redBar) hser
  rw [map_zero, coeffMap_coeffMap] at hk
  have hred : R.redBar.comp (IsLocalRing.residue A) = red := RingHom.ext R.redBar_residue
  rw [hred, hy_def, coeffMap_qExpand, coeffMap_jqModC, qExpand_jqModC_eq_pow k data hKr] at hk
  exact pow_ne_zero q (jqModC_ne_zero_of_nontrivial (R := k)) hk.symm

private theorem residue₂_jFun_ne_zero (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (h₂ : jFun N q ∈ R.R₂.integers) : R.R₂.residue ⟨jFun N q, h₂⟩ ≠ 0 := by
  rw [R.residue₂_eq]
  have hel : (⟨ProlongationTuple.atkinLehnerBar N q (jFun N q),
      (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₂)⟩ : R.R₁.integers)
      = ⟨jQFun N q, jQFun_mem_integers₁ R⟩ := Subtype.ext (atkinLehnerBar_jFun hqN)
  rw [hel]
  exact residue_jQFun_ne_zero R _

private theorem jFun_twoSided (hqN : ¬ q ∣ N) (R : ProlongationTuple P) :
    ∃ (h₁ : jFun N q ∈ R.R₁.integers) (h₂ : jFun N q ∈ R.R₂.integers),
      R.R₁.residue ⟨jFun N q, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨jFun N q, h₂⟩ ≠ 0 ∧
        R.residue₁ ⟨jFun N q, h₁⟩ = ⟨jqModC k, jqModC_mem k N⟩ :=
  ⟨jFun_mem_integers₁ R, jFun_mem_integers₂ hqN R, residue_jFun_ne_zero R _,
    residue₂_jFun_ne_zero hqN R _, residue₁_jFun R _⟩

private theorem ord_jFun_eq_mul (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    W.ord (jFun N q)
      = (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)
        * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ := by
  have hjα : jFun N q = heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩) :=
    Subtype.ext (by simp [jFun])
  rw [hjα, Place.ord_restrictAlong _ hα]

private theorem mapDomain_restrictAlong_apply
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) E b
      = ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, E W := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro W hW
    rw [Finset.mem_filter] at hW
    rw [Place.mem_fiberAlong]
    exact hW.2
  · intro W hWf hW
    rw [Finset.mem_filter, not_and] at hW
    by_contra hne
    exact hW (Finsupp.mem_support_iff.mpr hne) ((Place.mem_fiberAlong).mp hWf)

private theorem push_filter_isInftySide_eq
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (DJ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hDJ : ∀ W, DJ W = W.ord (jFun N q))
    (Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDj : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩) :
    Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        (DJ.filter (IsInftySide P))
      = Dj.filter (fun b => Dj b < 0) := by
  ext b
  rw [mapDomain_restrictAlong_apply, Finsupp.filter_apply]
  have hterm : ∀ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
      (DJ.filter (IsInftySide P)) W
        = if IsInftySide P W then
            (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) * Dj b else 0 := by
    intro W hW
    rw [Finsupp.filter_apply, hDJ, ord_jFun_eq_mul (hα := hα), (Place.mem_fiberAlong).mp hW, hDj]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  split_ifs with hneg
  · rw [← Finset.sum_mul, sheet hqN P b (by rw [← hDj]; exact hneg), one_mul]
  · apply Finset.sum_eq_zero
    intro W hW
    rw [Finset.mem_filter] at hW
    have hWb := (Place.mem_fiberAlong).mp hW.1
    have hcusp : W.ord (jFun N q) ≤ 0 := by simpa using hW.2.1 (0 : A)
    rw [ord_jFun_eq_mul (hα := hα), hWb, ← hDj] at hcusp
    exact le_antisymm hcusp (mul_nonneg (Int.natCast_nonneg _) (not_lt.mp hneg))

end SpecJReduction

open SpecJReduction in
theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (Dj : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDj : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Dj b = b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    Finsupp.mapDomain P.sp (Dj.filter (fun b => Dj b < 0)) v
      = v.ord ⟨jqModC k, jqModC_mem k N⟩ := by
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨h₁, h₂, hr₁, hr₂, hres⟩ := jFun_twoSided hqN R
  have hj0 : jFun N q ≠ 0 := by
    intro h0
    apply hr₁
    have : (⟨jFun N q, h₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨DJ, hDJ, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (jFun N q) hj0
  obtain ⟨⟨c, hc, hcv⟩, -⟩ :=
    ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
      hqN P v hv
  have law := hmodel.2.2.1 (jFun N q) h₁ h₂ hr₁ hr₂ DJ hDJ c hc
  rw [hcv, hres] at law
  rw [← law, ← push_filter_isInftySide_eq hqN P DJ hDJ Dj hDj]
  have hcomp : Finsupp.mapDomain P.reduceFst (DJ.filter (IsInftySide P))
      = Finsupp.mapDomain
          (P.sp ∘ fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
          (DJ.filter (IsInftySide P)) := rfl
  rw [hcomp, Finsupp.mapDomain_comp]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_sp_filter_neg_divisor_j_eq_ord_jqModC_of_isModel (solution)
