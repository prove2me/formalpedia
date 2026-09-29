-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9346cbb7-4517-5241-a58c-93b7c75eabd0

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_of_surjective
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace CuspSideDescent

section hasValue
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

private theorem hvAdd {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem hvNeg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

private theorem hvSub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hvAdd h (hvNeg h')

private theorem hasValue_zero_of_ord_pos {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  by_contra hne
  have hu : IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := (residue_ne_zero_iff_isUnit _).mp hne
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  simp only at this
  omega

private theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have h0 := v.ord_nonneg_of_mem h.mem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have := (residue_ne_zero_iff_isUnit _).mpr hu
    exact this (by rw [h.residue_eq, map_zero])

end hasValue

section along
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

private theorem hasValue_map_of_hasValue_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') {g : F} {a : K} (h : (w.restrictAlong φ hφ).HasValue g a) :
    w.HasValue (φ g) a := by
  by_cases hga : g = algebraMap K F a
  · subst hga
    rw [AlgHom.commutes]
    exact w.hasValue_algebraMap a
  · have hsub : (w.restrictAlong φ hφ).HasValue (g - algebraMap K F a) 0 := by
      have := hvSub h ((w.restrictAlong φ hφ).hasValue_algebraMap a)
      rwa [sub_self] at this
    have hne : g - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hga
    have hpos := ord_pos_of_hasValue_zero hsub hne
    have hne' : φ (g - algebraMap K F a) ≠ 0 := (map_ne_zero φ).mpr hne
    have hpos' : 0 < w.ord (φ (g - algebraMap K F a)) := by
      rw [Place.ord_restrictAlong φ hφ w]
      exact mul_pos (by exact_mod_cast ramificationIndexAlong_pos φ hφ w) hpos
    have h0 := hasValue_zero_of_ord_pos hne' hpos'
    have := hvAdd h0 (w.hasValue_algebraMap a)
    rwa [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at this

end along

section tower

private theorem dvd_NQ (N q : ℕ) : 1 * q ∣ N * q := ⟨N, by ring⟩

end tower

section main

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem main (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsCuspidal P W) :
    ProlongationTuple.IsInftySide P W ∨ ProlongationTuple.IsZeroSide P W := by
  classical

  have hι : (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)).toRingHom.IsIntegral :=
    ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) (dvd_NQ N q)
  have he : 0 < Place.ramificationIndexAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) W :=
    ramificationIndexAlong_pos (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) hι W

  have hjF : towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q) (PlaceSpecialization.jFun (q := q))
      = ProlongationTuple.jFun N q := by
    apply Subtype.ext
    rw [coe_towerInclBar]
    rfl
  have hjQ : towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q) (PlaceSpecialization.jqFun (q := q))
      = ProlongationTuple.jQFun N q := by
    apply Subtype.ext
    rw [coe_towerInclBar]
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [qExpand_congr (one_mul q)]
  have htI : (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) (PlaceSpecialization.tInfty (q := q)) = ProlongationTuple.tInfty N q := by
    simp only [PlaceSpecialization.tInfty, ProlongationTuple.tInfty, map_div₀, map_pow, hjF, hjQ, one_mul]
  have htZ : (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) (PlaceSpecialization.tZero (q := q)) = ProlongationTuple.tZero N q := by
    simp only [PlaceSpecialization.tZero, ProlongationTuple.tZero, map_div₀, map_pow, hjF, hjQ, one_mul]

  set W₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) := W.restrictAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) hι with hW₁_def
  have hord : ∀ f : ↥(modularFunctionFieldBar (1 * q)),
      W.ord ((towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) f) = Place.ramificationIndexAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) W * W₁.ord f :=
    fun f => Place.ord_restrictAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) hι W f

  have hker : ∀ m : A, m ∈ IsLocalRing.maximalIdeal ↥A → red m = 0 := fun m hm =>
    ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red hm
  let red' : IsLocalRing.ResidueField ↥A →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hker
  have hred' : ∀ a : A, red' (IsLocalRing.residue ↥A a) = red a := fun a =>
    Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hker
  haveI : CharP (IsLocalRing.ResidueField ↥A) q := (RingHom.charP_iff_charP red' q).mpr inferInstance

  obtain ⟨P₁⟩ := ModularCurve.placeSpecialization_exists_level_one_of_surjective q data hKr A
    (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) IsLocalRing.residue_surjective
    (ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q)
    (ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q)
  have hW₁ : PlaceSpecialization.IsCuspidal P₁ W₁ := by
    intro a
    have h := hW a
    have e := hord (PlaceSpecialization.jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
    rw [map_sub, hjF, AlgHom.commutes] at e
    unfold ProlongationTuple.IsCuspidal at h
    rw [e] at h
    exact nonpos_of_mul_nonpos_right h (by exact_mod_cast he)

  have h1 := ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal P₁ W₁ hW₁
  unfold PlaceSpecialization.IsInftySide PlaceSpecialization.IsZeroSide at h1
  rcases h1 with ⟨-, τ, hτ, hv⟩ | ⟨hc', τ, hτ, hv⟩
  · left
    show ProlongationTuple.IsCuspidal P W ∧ ∃ τ : A, red τ = 1 ∧
      W.HasValue (ProlongationTuple.tInfty N q) (τ : AlgebraicClosure ℚ)
    refine ⟨hW, τ, ?_, ?_⟩
    · rw [← hred' τ, hτ, map_one]
    · have := hasValue_map_of_hasValue_restrictAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) hι W hv
      rwa [htI] at this
  · right
    show ProlongationTuple.IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧
      W.HasValue (ProlongationTuple.tZero N q) (τ : AlgebraicClosure ℚ)
    refine ⟨?_, τ, ?_, ?_⟩
    · intro a
      have h := hc' a
      have e := hord (PlaceSpecialization.jqFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
      rw [map_sub, hjQ, AlgHom.commutes] at e
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast (Nat.zero_le _)) h
    · rw [← hred' τ, hτ, map_one]
    · have := hasValue_map_of_hasValue_restrictAlong (towerInclBar (AlgebraicClosure ℚ) (dvd_NQ N q)) hι W hv
      rwa [htZ] at this

end main

end CuspSideDescent

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsCuspidal P W) :
    ProlongationTuple.IsInftySide P W ∨ ProlongationTuple.IsZeroSide P W := by
  have _hqN := hqN
  exact CuspSideDescent.main P W hW

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal (solution)
