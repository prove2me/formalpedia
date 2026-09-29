-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/da129188-b55b-5db5-ab97-d1af3be2d8c1

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul
import Theorems.Thm_AlgebraicCurve_exists_place_over_of_simple_root_along
import Theorems.Thm_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace FibreDegree

private theorem finrankAlong_heckeAlphaBar (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  obtain ⟨τ, hτα, hτβ⟩ :=
    exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar (AlgebraicClosure ℚ) N q σ hσ
  have hβ : finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
    rw [finrankAlong_heckeBetaBar, if_neg hqN]
  have h1 := finrankAlong_comp (heckeAlphaBar (AlgebraicClosure ℚ) N q) τ.toAlgHom
  have h2 := finrankAlong_comp (heckeBetaBar (AlgebraicClosure ℚ) N q) τ.toAlgHom
  rw [hτα] at h1
  rw [hτβ] at h2

  have htt : (q + 1) * 1 = (q + 1) * (finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom *
      finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom) := by
    rw [mul_one, ← mul_assoc, ← hβ, ← h2, ← h1]
  have ht1 : finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom = 1 :=
    Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) htt).symm
  rw [h2, hβ, ht1, mul_one]

private theorem sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N) (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = q + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hfin := finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q
  have hsep := separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  have hsum := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong
    (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hfin hsep b
  rw [finrankAlong_heckeAlphaBar N q hqN] at hsum
  have hsum' : (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = ((q + 1 : ℕ) : ℤ) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [inertiaDegAlong_eq_one_laurentBaseChange (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W,
      Nat.cast_one, mul_one]
  rw [hsum', Nat.cast_add, Nat.cast_one]

end FibreDegree

namespace CuspFibre

private theorem exists_algEquiv_apply_eq_pow_of_pow_eq_one (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ q := by
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN
  have hζq : IsPrimitiveRoot (ζ₀ ^ q) N := hζ₀.pow_of_coprime q hcop
  have hconj : IsConjRoot ℚ (ζ₀ ^ q) ζ₀ := by
    rw [isConjRoot_def, ← Polynomial.cyclotomic_eq_minpoly_rat hζq (NeZero.pos N),
      ← Polynomial.cyclotomic_eq_minpoly_rat hζ₀ (NeZero.pos N)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ, fun μ hμ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

private theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem restrictAlong_smul_eq {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral)
    (hβ : β.toRingHom.IsIntegral) (g : F' ≃ₐ[K] F') (h : ∀ x, g (β x) = α x)
    (W : Place K F') : (g • W).restrictAlong α hα = W.restrictAlong β hβ := by
  apply Place.ext
  ext x
  rw [mem_restrictAlong_iff, mem_restrictAlong_iff, Place.smul_toValuationSubring, ← h x]
  exact ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := β x)

private theorem jFun_ne_zero (N q : ℕ) [NeZero N] [NeZero q] : jFun N q ≠ 0 := fun h => by
  have h0 : ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero
  rw [h, ZeroMemClass.coe_zero] at h0
  exact h0 rfl

private theorem jQFun_ne_zero (N q : ℕ) [NeZero N] [NeZero q] : jQFun N q ≠ 0 := fun h => by
  have h0 : ((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr ((map_ne_zero (qExpand ℚ q)).mpr jq_ne_zero)
  rw [h, ZeroMemClass.coe_zero] at h0
  exact h0 rfl

private theorem exists_not_inftySide_of_pole
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
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, ¬ IsInftySide P W ∧
      (q : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_pow_of_pow_eq_one N q hqN
  obtain ⟨W₁, W₂, -, hW₂b, -, he₂, -, hW₂a⟩ :=
    exists_pair_fiberAlong_heckeBetaBar_of_ord_neg N q hqN hα hβ σ hσ b hb

  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull (N := N) (ℓ := q)
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨-, hβα⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hAL
  have hβα' : ∀ x, atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q x)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q x :=
    fun x => AlgHom.congr_fun hβα x
  refine ⟨atkinLehnerBar N q • W₂, ?_, ?_, ?_⟩
  ·
    rw [Place.mem_fiberAlong, restrictAlong_smul_eq _ _ hα hβ _ hβα', hW₂b]
  ·
    rw [isInftySide_atkinLehnerBar_smul_iff P hqN W₂]
    rintro ⟨-, τ, hτ, hval⟩
    have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [ZeroMemClass.coe_eq_zero] at h0
      rw [h0, map_zero] at hτ
      exact zero_ne_one hτ
    have hord0 : W₂.ord (tZero N q) = 0 := hval.ord_eq_zero hτ0
    have hj0 := jFun_ne_zero N q
    have hjQ0 := jQFun_ne_zero N q

    have htZ : W₂.ord (tZero N q) = W₂.ord (jFun N q) - q * W₂.ord (jQFun N q) := by
      change W₂.ord (jFun N q / jQFun N q ^ q) = _
      rw [div_eq_mul_inv, W₂.ord_mul hj0 (inv_ne_zero (pow_ne_zero _ hjQ0)), Place.ord_inv,
        ← zpow_natCast, Place.ord_zpow]
      ring

    have hJQ : heckeBetaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = jQFun N q :=
      Subtype.ext (coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm
    have hJ : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = jFun N q :=
      Subtype.ext (coe_heckeAlphaBar _ _ _)

    have hsJ : arithmeticGalois (modularFunctionFieldFull N) σ •
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ jq)
    have hbJ : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        = (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
          ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      have h := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull N) σ)
        (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      rw [hsJ, hW₂a] at h
      exact h
    have hordQ : W₂.ord (jQFun N q) = q * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      rw [← hJQ, Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W₂, hW₂b, he₂]
    have hordJ : W₂.ord (jFun N q)
        = (W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      rw [← hJ, Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W₂, ← hbJ]

    have hle : (W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) ≤ q + 1 := by
      rw [← FibreDegree.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN
        (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)]
      exact Finset.single_le_sum (f := fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
        (fun W _ => Nat.cast_nonneg _) (Place.mem_fiberAlong.mpr rfl)
    have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
    rw [htZ, hordJ, hordQ] at hord0
    have he' : ((W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) - q * q)
        * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = 0 := by
      rw [sub_mul, mul_assoc]
      exact hord0
    rcases mul_eq_zero.mp he' with h | h
    · have h2q : 2 * (q : ℤ) ≤ q * q := mul_le_mul_of_nonneg_right hq2 (by linarith)
      linarith
    · exact hb.ne h
  ·
    rw [Place.ramificationIndexAlong_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (heckeBetaBar (AlgebraicClosure ℚ) N q) (atkinLehnerBar N q) AlgEquiv.refl
      (fun x => (hβα' x).symm) W₂, he₂]

end CuspFibre

section DeepPlaceAnalysis

open IsLocalRing ModularCurve.PlaceSpecialization

noncomputable section

namespace HeckeFibreValues

local notation "ℚ̄" => AlgebraicClosure ℚ

section Values

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem hasValue_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (g : F) (a : K) : (w.restrictAlong φ hφ).HasValue g a ↔ w.HasValue (φ g) a := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  change (w.restrict F).HasValue g a ↔ w.HasValue (algebraMap F F' g) a
  constructor
  · rintro ⟨hg, hres⟩
    refine ⟨hg, ?_⟩
    have h := congrArg (Place.restrictResidueMap F w) hres
    rw [Place.restrictResidueMap_residue, ← Place.algebraMap_residueField_eq,
      ← IsScalarTower.algebraMap_apply] at h
    exact h
  · rintro ⟨hg', hres⟩
    have hg : g ∈ (w.restrict F).toValuationSubring := hg'
    refine ⟨hg, (Place.restrictResidueMap F w).injective ?_⟩
    rw [Place.restrictResidueMap_residue, ← Place.algebraMap_residueField_eq,
      ← IsScalarTower.algebraMap_apply]
    exact hres

private theorem residue_eq_of_hasValue (v : Place K F) (r : v.toValuationSubring) {a : K}
    (h : v.HasValue (r : F) a) : residue v.toValuationSubring r = algebraMap K v.ResidueField a := by
  obtain ⟨h', e⟩ := h
  exact e

private theorem ord_pos_of_hasValue_zero (v : Place K F) {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) :
    0 < v.ord g := by
  obtain ⟨hmem, hres⟩ := h
  rw [map_zero] at hres
  have hr : (⟨g, hmem⟩ : v.toValuationSubring) ≠ 0 := fun e => hg (congrArg Subtype.val e)
  have h1 := (Place.mem_maximalIdeal_iff_ord_pos' (v := v) hr).mp
    ((IsLocalRing.residue_eq_zero_iff _).mp hres)
  simpa using h1

end Values

section Equation

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

private def jN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

private theorem heckeAlphaBar_jN (N q : ℕ) [NeZero N] [Fact q.Prime] :
    heckeAlphaBar ℚ̄ N q (jN N) = jFun N q := by
  apply Subtype.ext
  simp [jN, jFun, coe_heckeAlphaBar]

private theorem heckeBetaBar_jN (N q : ℕ) [NeZero N] [Fact q.Prime] :
    heckeBetaBar ℚ̄ N q (jN N) = jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  change qExpand ℚ̄ q (coeffEmb ℚ̄ jq) = coeffEmb ℚ̄ (qExpand ℚ q jq)
  exact (coeffMap_qExpand (algebraMap ℚ ℚ̄) q jq).symm

private theorem coeffEmb_jq_eq_jqModC : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  have hmap : jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = jNum.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : k = (-1 : ℤ) <;> simp [hk]
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : 0 ≤ k
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        ← hmap, PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega),
        map_zero]

private theorem transcendental_jN (N : ℕ) [NeZero N] : Transcendental ℚ̄ (jN N) := by
  have h := transcendental_jqModC (AlgebraicClosure ℚ)
  rw [← coeffEmb_jq_eq_jqModC] at h
  intro halg
  apply h
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := congrArg (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at h2
  simpa [jN] using h2

private theorem evalModularPair_jQFun_jFun (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) :
    evalModularPair (jQFun N q) (jFun N q) data.Φ = 0 := by
  letI := algebraAlong (heckeBetaBar ℚ̄ N q)
  have hmin : minpoly (modularFunctionFieldBar N) (jFun N q)
      = data.Φ.map (Polynomial.aeval (R := ℤ) (jN N)).toRingHom := by
    rw [← heckeAlphaBar_jN N q]
    exact ModularCurve.minpoly_heckeAlphaBar_along_heckeBetaBar N q hqN data
      (ModularPolynomialData.evalSymm_of_prime q data)
  have h0 := minpoly.aeval (modularFunctionFieldBar N) (jFun N q)
  rw [hmin, Polynomial.aeval_def, Polynomial.eval₂_map] at h0
  have hcomp : (algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))).comp
        (Polynomial.aeval (R := ℤ) (jN N)).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom _) (jQFun N q) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show (heckeBetaBar ℚ̄ N q) (Polynomial.aeval (jN N) (Polynomial.X : Polynomial ℤ)) = _
    rw [Polynomial.aeval_X, heckeBetaBar_jN, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hcomp] at h0
  exact h0

private theorem evalModularPair_values (hqN : ¬ q ∣ N) (data : ModularPolynomialData q)
    (W : Place ℚ̄ (modularFunctionFieldBar (N * q))) {J y : ℚ̄}
    (hJ : W.HasValue (jQFun N q) J) (hy : W.HasValue (jFun N q) y) :
    evalModularPair J y data.Φ = 0 := by
  obtain ⟨hJm, hJr⟩ := hJ
  obtain ⟨hym, hyr⟩ := hy
  have hO : evalModularPair (⟨jQFun N q, hJm⟩ : W.toValuationSubring) ⟨jFun N q, hym⟩ data.Φ = 0 := by
    apply Subtype.ext
    exact (map_evalModularPair W.toValuationSubring.subtype _ _ data.Φ).trans
      (evalModularPair_jQFun_jFun hqN data)
  apply (algebraMap ℚ̄ W.ResidueField).injective
  rw [map_zero, map_evalModularPair, ← hJr, ← hyr,
    ← map_evalModularPair (IsLocalRing.residue W.toValuationSubring), hO, map_zero]

private theorem hasValue_sub_self {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) {g : F} {a : K}
    (h : W.HasValue g a) : W.HasValue (g - algebraMap K F a) 0 := by
  obtain ⟨hm, hr⟩ := h
  refine ⟨sub_mem hm (W.algebraMap_mem' a), ?_⟩
  have e : (⟨g - algebraMap K F a, sub_mem hm (W.algebraMap_mem' a)⟩ : W.toValuationSubring)
      = ⟨g, hm⟩ - ⟨algebraMap K F a, W.algebraMap_mem' a⟩ := rfl
  rw [e, map_sub, hr, (Place.hasValue_algebraMap (v := W) a).residue_eq, ← map_sub, sub_self]

private theorem jFun_sub_ne_zero (y : ℚ̄) : jFun N q - algebraMap ℚ̄ (modularFunctionFieldBar (N * q)) y ≠ 0 := by
  intro h
  have h1 : heckeAlphaBar ℚ̄ N q (jN N - algebraMap ℚ̄ (modularFunctionFieldBar N) y) = 0 := by
    rw [map_sub, heckeAlphaBar_jN, AlgHom.commutes]; exact h
  have h2 : jN N = algebraMap ℚ̄ (modularFunctionFieldBar N) y :=
    sub_eq_zero.mp ((map_eq_zero_iff _ (heckeAlphaBar ℚ̄ N q).toRingHom.injective).mp h1)
  exact transcendental_jN N (h2 ▸ isAlgebraic_algebraMap y)

private theorem evalModularPair_comm {R : Type*} [CommRing R] {Φ : Polynomial (Polynomial ℤ)} (hΦ : swapBivar Φ = Φ)
    (x c : R) : evalModularPair x c Φ = evalModularPair c x Φ := by
  conv_lhs => rw [← hΦ]
  change (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) c)
      (Polynomial.eval₂ swapInner (Polynomial.C Polynomial.X) Φ) = _
  rw [Polynomial.hom_eval₂]
  unfold evalModularPair
  congr 1
  · refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [swapInner]
  · simp

end Equation

section Coefficients

private theorem natDegree_Φ {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) :
    data.Φ.natDegree = q + 1 := by
  rw [data.natDegree_eq, dedekindPsi_prime hq.out]

private theorem coeff_top {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) :
    data.Φ.coeff (q + 1) = 1 := by
  have h := data.monic.coeff_natDegree
  rwa [natDegree_Φ data] at h

private theorem swapInner_coeff (c : Polynomial ℤ) (i : ℕ) :
    (swapInner c).coeff i = Polynomial.C (c.coeff i) := by
  induction c using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, Polynomial.coeff_add, hp, hr]
  | monomial m a =>
    simp only [swapInner, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_monomial,
      Polynomial.coeff_monomial, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all

private theorem swapBivar_coeff_coeff (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff i).coeff j = (Φ.coeff j).coeff i := by
  induction Φ using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, Polynomial.coeff_add, hp, hr]
  | monomial n c =>
    simp only [swapBivar, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.coeff_monomial]
    rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, swapInner_coeff, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp_all

private theorem natDegree_coeff_le_of_pos {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) {i : ℕ}
    (hi : 0 < i) : (data.Φ.coeff i).natDegree ≤ q := by
  have hsymm : swapBivar data.Φ = data.Φ := swapBivar_eq_of_evalSymm (data.evalSymm_of_prime q)
  have htop : (data.Φ.coeff i).coeff (q + 1) = 0 := by
    have h := swapBivar_coeff_coeff data.Φ (q + 1) i
    rw [hsymm, coeff_top data, Polynomial.coeff_one, if_neg (by omega)] at h
    exact h.symm
  have hle : (data.Φ.coeff i).natDegree ≤ q + 1 := data.natDegree_coeff_le q i
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rcases Nat.lt_or_ge (q + 1) n with h | h
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle h)
  · have : n = q + 1 := by omega
    rw [this]
    exact htop

private noncomputable def principal (q : ℕ) : Polynomial (Polynomial ℤ) :=
  (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)

private theorem principal_eq (q : ℕ) :
    principal q = Polynomial.C (Polynomial.X ^ (q + 1)) - Polynomial.C (Polynomial.X ^ q) * Polynomial.X ^ q -
      Polynomial.C Polynomial.X * Polynomial.X + Polynomial.X ^ (q + 1) := by
  unfold principal
  simp only [Polynomial.C_pow]
  ring

private theorem principal_coeff (q : ℕ) (i : ℕ) :
    (principal q).coeff i =
      (if i = 0 then Polynomial.X ^ (q + 1) else 0) - (if i = q then Polynomial.X ^ q else 0) -
        (if i = 1 then Polynomial.X else 0) + (if i = q + 1 then 1 else 0) := by
  rw [principal_eq, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_X_pow]

private theorem reduceModBivar_principal (q : ℕ) :
    reduceModBivar q (principal q) =
      (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
  unfold principal
  simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]

private theorem dvd_coeff_sub_principal {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (i k : ℕ) :
    (q : ℤ) ∣ ((data.Φ - principal q).coeff i).coeff k := by
  have h : reduceModBivar q (data.Φ - principal q) = 0 := by
    rw [map_sub, reduceModBivar_principal, sub_eq_zero]
    exact hKr
  have h1 := congrArg (fun P => Polynomial.coeff (Polynomial.coeff P i) k) h
  simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero,
    eq_intCast] at h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h1

private theorem valuation_eval₂_le_of_dvd (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (p : Polynomial ℤ)
    {d : ℕ} (hp : ∀ k, (q : ℤ) ∣ p.coeff k) (hd : p.natDegree ≤ d) {J : AlgebraicClosure ℚ}
    (hJ : 1 ≤ A.valuation J) :
    A.valuation (p.eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
      A.valuation (q : AlgebraicClosure ℚ) * A.valuation J ^ d := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  refine Valuation.map_sum_le _ fun k hk => ?_
  obtain ⟨m, hm⟩ := hp k
  have hm1 : A.valuation (m : AlgebraicClosure ℚ) ≤ 1 := A.valuation_le_one ⟨(m : AlgebraicClosure ℚ), by simp⟩
  have hk' : k ≤ d := by simpa [Nat.lt_succ_iff] using hk
  simp only [hm, map_mul, map_pow, eq_intCast, Int.cast_natCast]
  refine le_trans (mul_le_mul' (mul_le_mul' le_rfl hm1) (pow_le_pow_right₀ hJ hk')) ?_
  rw [mul_one]

private theorem coeff_eval_eq {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) (i : ℕ)
    (J : AlgebraicClosure ℚ) :
    (data.Φ.coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J =
      ((principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J +
        ((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J := by
  rw [← Polynomial.eval₂_add, Polynomial.coeff_sub, add_sub_cancel]

private theorem natDegree_remainder_le {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) (i : ℕ) :
    ((data.Φ - principal q).coeff i).natDegree ≤ q + 1 ∧
      (0 < i → ((data.Φ - principal q).coeff i).natDegree ≤ q) := by
  have hprin : ((principal q).coeff i).natDegree ≤ q + 1 ∧ (0 < i → ((principal q).coeff i).natDegree ≤ q) := by
    rw [principal_coeff]
    constructor
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_) <;> (try split_ifs) <;> simp
    · intro hi
      rw [if_neg hi.ne']
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_) <;> (try split_ifs) <;> simp
      exact hq.out.one_lt.le
  rw [Polynomial.coeff_sub]
  constructor
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (data.natDegree_coeff_le q i) hprin.1)
  · intro hi
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (natDegree_coeff_le_of_pos data hi) (hprin.2 hi))

private theorem coeff_sizes {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hJ : A.valuation J = γ)
    (hγ : 1 < γ) :
    A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
    A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
    (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
    data.Φ.coeff (q + 1) = 1 := by
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hJ1 : 1 ≤ A.valuation J := by rw [hJ]; exact hγ.le
  have hsmall : ∀ d : ℕ, A.valuation (q : AlgebraicClosure ℚ) * γ ^ d < γ ^ d := fun d => by
    have hpos : (0 : A.ValueGroup) < γ ^ d := zero_lt_iff.2 (pow_ne_zero _ hγ0)
    simpa only [one_mul] using mul_lt_mul_of_pos_right hqA hpos
  have hrem : ∀ i, A.valuation (((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
      A.valuation (q : AlgebraicClosure ℚ) * γ ^ (q + 1) := fun i => by
    rw [← hJ]
    exact valuation_eval₂_le_of_dvd A q _ (dvd_coeff_sub_principal data hKr i) (natDegree_remainder_le data i).1 hJ1
  have hrem' : ∀ i, 0 < i →
      A.valuation (((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
        A.valuation (q : AlgebraicClosure ℚ) * γ ^ q := fun i hi => by
    rw [← hJ]
    exact valuation_eval₂_le_of_dvd A q _ (dvd_coeff_sub_principal data hKr i) ((natDegree_remainder_le data i).2 hi)
      hJ1
  have hq0 : (0 : ℕ) ≠ q := hq.out.ne_zero.symm
  have hq1 : (1 : ℕ) ≠ q := hq.out.one_lt.ne
  refine ⟨?_, ?_, ?_, coeff_top data⟩
  ·
    have hp : ((principal q).coeff 0).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J = J ^ (q + 1) := by
      rw [principal_coeff]
      simp [hq0]
    rw [coeff_eval_eq, hp, Valuation.map_add_eq_of_lt_left _ ?_, Valuation.map_pow, hJ]
    rw [Valuation.map_pow, hJ]
    exact lt_of_le_of_lt (hrem 0) (hsmall _)
  ·
    have hp : ((principal q).coeff q).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J = -(J ^ q) := by
      rw [principal_coeff]
      simp [hq0.symm, hq1.symm]
    rw [coeff_eval_eq, hp, Valuation.map_add_eq_of_lt_left _ ?_, Valuation.map_neg, Valuation.map_pow, hJ]
    rw [Valuation.map_neg, Valuation.map_pow, hJ]
    exact lt_of_le_of_lt (hrem' q hq.out.pos) (hsmall _)
  ·
    intro i hi1 hiq
    have hiq' : i ≠ q := by omega
    have hiq1 : i ≠ q + 1 := by omega
    have hi0 : i ≠ 0 := by omega
    have hγq : γ < γ ^ q := by
      simpa only [pow_one] using pow_lt_pow_right₀ hγ hq.out.one_lt
    have hp : A.valuation (((principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) < γ ^ q := by
      rw [principal_coeff, if_neg hi0, if_neg hiq', if_neg hiq1]
      by_cases hi : i = 1
      · rw [if_pos hi]
        simp only [zero_sub, sub_zero, add_zero, Polynomial.eval₂_neg, Polynomial.eval₂_X, Valuation.map_neg, hJ]
        exact hγq
      · rw [if_neg hi]
        simp only [sub_zero, add_zero, Polynomial.eval₂_zero, Valuation.map_zero]
        exact zero_lt_iff.2 (pow_ne_zero _ hγ0)
    rw [coeff_eval_eq]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hp (lt_of_le_of_lt (hrem' i (by omega)) (hsmall _)))

end Coefficients

end HeckeFibreValues

namespace NewtonSizes

open Polynomial

section generic

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

private theorem not_dominant {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → K}
    (hsum : ∑ i ∈ s, f i = 0) {j : ι} (hj : j ∈ s) (hne : v (f j) ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → v (f i) < v (f j)) : False := by
  have h := v.map_sum_eq_of_lt hj (fun i hi => by
    have hi' := Finset.mem_sdiff.1 hi
    exact hlt i hi'.1 (by simpa using hi'.2))
  rw [hsum, v.map_zero] at h
  exact hne h.symm

private theorem no_dominant_term {P : K[X]} {n : ℕ} (hdeg : P.natDegree < n) {y : K} (hy : P.IsRoot y)
    {j : ℕ} (hj : j < n) (hne : v (P.coeff j * y ^ j) ≠ 0)
    (hlt : ∀ i, i < n → i ≠ j → v (P.coeff i * y ^ i) < v (P.coeff j * y ^ j)) : False := by
  have hsum : ∑ i ∈ Finset.range n, P.coeff i * y ^ i = 0 := by
    rw [← eval_eq_sum_range' hdeg y]
    exact hy.eq_zero
  exact not_dominant v hsum (Finset.mem_range.2 hj) hne (fun i hi hij => hlt i (Finset.mem_range.1 hi) hij)

private theorem pos_of_ne_zero {a : Γ₀} (ha : a ≠ 0) : 0 < a := lt_of_le_of_ne zero_le' ha.symm

private theorem root_size_eq_or_pow_eq {q : ℕ} (hq : 1 < q) {γ : Γ₀} (hγ : 1 < γ) {P : K[X]}
    (hdeg : P.natDegree ≤ q + 1) (htop : P.coeff (q + 1) = 1) (hcq : v (P.coeff q) = γ ^ q)
    (hc0 : v (P.coeff 0) = γ ^ (q + 1)) (hmid : ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i) < γ ^ q)
    {y : K} (hy : P.IsRoot y) : v y = γ ^ q ∨ v y ^ q = γ := by
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hγq : 1 < γ ^ q := one_lt_pow₀ hγ (by omega)

  have hy0 : v y ≠ 0 := by
    intro h0
    rw [v.zero_iff] at h0
    subst h0
    have h := hy.eq_zero
    rw [← coeff_zero_eq_eval_zero] at h
    rw [h, v.map_zero] at hc0
    exact (pow_ne_zero _ hγ0) hc0.symm
  have hδq : v y ^ q ≠ 0 := pow_ne_zero _ hy0
  have hterm : ∀ i, v (P.coeff i * y ^ i) = v (P.coeff i) * v y ^ i := fun i => by
    rw [v.map_mul, v.map_pow]
  have htopterm : v (P.coeff (q + 1) * y ^ (q + 1)) = v y ^ q * v y := by
    rw [hterm, htop, v.map_one, one_mul, pow_succ]
  have hqterm : v (P.coeff q * y ^ q) = γ ^ q * v y ^ q := by rw [hterm, hcq]
  have h0term : v (P.coeff 0 * y ^ 0) = γ ^ q * γ := by rw [hterm, hc0, pow_zero, mul_one, pow_succ]

  have hmidterm : ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i * y ^ i) < γ ^ q * v y ^ i := fun i h1 h2 => by
    rw [hterm]
    exact mul_lt_mul_of_pos_right (hmid i h1 h2) (pos_of_ne_zero (pow_ne_zero _ hy0))

  have hmid_big : 1 ≤ v y → ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i * y ^ i) < γ ^ q * v y ^ q :=
    fun hδ1 i h1 h2 => (hmidterm i h1 h2).trans_le
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hδ1 (by omega)) zero_le')
  have hlt_deg : P.natDegree < q + 2 := by omega
  rcases lt_trichotomy (γ ^ q) (v y) with hA | hC | hB
  ·
    exfalso
    have hδ1 : 1 ≤ v y := (hγq.trans hA).le
    have hq_lt_top : v (P.coeff q * y ^ q) < v (P.coeff (q + 1) * y ^ (q + 1)) := by
      rw [hqterm, htopterm, mul_comm (γ ^ q)]
      exact mul_lt_mul_of_pos_left hA (pos_of_ne_zero hδq)
    refine no_dominant_term v hlt_deg hy (j := q + 1) (by omega) ?_ ?_
    · rw [htopterm]
      exact mul_ne_zero hδq hy0
    · intro i hi hij
      rcases Nat.lt_or_ge i 1 with hi0 | hi1
      ·
        have hi0' : i = 0 := by omega
        rw [hi0']
        refine lt_trans ?_ hq_lt_top
        rw [h0term, hqterm]
        refine mul_lt_mul_of_pos_left ?_ (pos_of_ne_zero (pow_ne_zero _ hγ0))
        calc γ < γ ^ q := by
                calc γ = γ ^ 1 := (pow_one γ).symm
                  _ < γ ^ q := pow_lt_pow_right₀ hγ hq
          _ < v y := hA
          _ ≤ v y ^ q := by
                calc v y = v y ^ 1 := (pow_one _).symm
                  _ ≤ v y ^ q := pow_le_pow_right₀ hδ1 (by omega)
      · rcases Nat.lt_or_ge i q with hiq | hiq
        ·
          refine lt_trans ?_ hq_lt_top
          rw [hqterm]
          exact hmid_big hδ1 i hi1 (by omega)
        ·
          have hiq' : i = q := by omega
          rw [hiq']
          exact hq_lt_top
  · exact Or.inl hC.symm
  ·
    rcases lt_trichotomy (v y ^ q) γ with hB2 | hB3 | hB1
    ·
      exfalso
      refine no_dominant_term v hlt_deg hy (j := 0) (by omega) ?_ ?_
      · rw [h0term]
        exact mul_ne_zero (pow_ne_zero _ hγ0) hγ0
      · have hq_lt_0 : v (P.coeff q * y ^ q) < v (P.coeff 0 * y ^ 0) := by
          rw [hqterm, h0term]
          exact mul_lt_mul_of_pos_left hB2 (pos_of_ne_zero (pow_ne_zero _ hγ0))
        intro i hi hij
        rcases Nat.lt_or_ge i q with hiq | hiq
        ·
          have hi1 : 1 ≤ i := by omega
          rcases le_or_gt 1 (v y) with hδ1 | hδ1
          · refine lt_trans ?_ hq_lt_0
            rw [hqterm]
            exact hmid_big hδ1 i hi1 (by omega)
          ·
            rw [h0term]
            calc v (P.coeff i * y ^ i) = v (P.coeff i) * v y ^ i := hterm i
              _ ≤ v (P.coeff i) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le' hδ1.le) zero_le'
              _ = v (P.coeff i) := mul_one _
              _ < γ ^ q := hmid i hi1 (by omega)
              _ = γ ^ q * 1 := (mul_one _).symm
              _ < γ ^ q * γ := mul_lt_mul_of_pos_left hγ (pos_of_ne_zero (pow_ne_zero _ hγ0))
        · rcases Nat.lt_or_ge i (q + 1) with hiq1 | hiq1
          · have hiq' : i = q := by omega
            rw [hiq']
            exact hq_lt_0
          ·
            have hi' : i = q + 1 := by omega
            rw [hi', htopterm, h0term]
            calc v y ^ q * v y = v y * v y ^ q := mul_comm _ _
              _ < γ ^ q * v y ^ q := mul_lt_mul_of_pos_right hB (pos_of_ne_zero hδq)
              _ < γ ^ q * γ := mul_lt_mul_of_pos_left hB2 (pos_of_ne_zero (pow_ne_zero _ hγ0))
    · exact Or.inr hB3
    ·
      exfalso
      have hδ1 : 1 ≤ v y := by
        by_contra h
        exact (not_le.2 (hγ.trans hB1)) (pow_le_one₀ zero_le' (not_le.1 h).le)
      refine no_dominant_term v hlt_deg hy (j := q) (by omega) ?_ ?_
      · rw [hqterm]
        exact mul_ne_zero (pow_ne_zero _ hγ0) hδq
      · intro i hi hij
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have hi0' : i = 0 := by omega
          rw [hi0', h0term, hqterm]
          exact mul_lt_mul_of_pos_left hB1 (pos_of_ne_zero (pow_ne_zero _ hγ0))
        · rcases Nat.lt_or_ge i q with hiq | hiq
          · rw [hqterm]
            exact hmid_big hδ1 i hi1 (by omega)
          · have hi' : i = q + 1 := by omega
            rw [hi', htopterm, hqterm, mul_comm (v y ^ q) (v y)]
            exact mul_lt_mul_of_pos_right hB (pos_of_ne_zero hδq)

end generic

section unique

variable {K : Type*} [Field K] [IsAlgClosed K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

private theorem prod_roots_size {P : K[X]} (hmonic : P.Monic) : (P.roots.map v).prod = v (P.coeff 0) := by
  have hP := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic IsAlgClosed.card_roots_eq_natDegree
  conv_rhs => rw [← hP]
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [v.map_neg]

private theorem card_roots_filter_size_eq {q : ℕ} (hq : 1 < q) {γ : Γ₀} (hγ : 1 < γ) {P : K[X]} (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hc0 : v (P.coeff 0) = γ ^ (q + 1))
    (hdich : ∀ y, P.IsRoot y → v y = γ ^ q ∨ v y ^ q = γ) :
    Multiset.card (P.roots.filter fun y => v y = γ ^ q) = 1 := by
  have hsplit : P.roots.filter (fun y => v y = γ ^ q) + P.roots.filter (fun y => ¬ v y = γ ^ q) = P.roots :=
    Multiset.filter_add_not _ _
  have hcard : Multiset.card (P.roots.filter fun y => v y = γ ^ q) +
      Multiset.card (P.roots.filter fun y => ¬ v y = γ ^ q) = q + 1 := by
    rw [← Multiset.card_add, hsplit, IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hbig : ((P.roots.filter fun y => v y = γ ^ q).map v).prod =
      (γ ^ q) ^ Multiset.card (P.roots.filter fun y => v y = γ ^ q) := by
    have h : ∀ x ∈ (P.roots.filter fun y => v y = γ ^ q).map v, x = γ ^ q := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      exact (Multiset.mem_filter.1 hy).2
    rw [Multiset.eq_replicate_card.2 h, Multiset.prod_replicate, Multiset.card_map]
  have hsmall : ((P.roots.filter fun y => ¬ v y = γ ^ q).map v).prod ^ q =
      γ ^ Multiset.card (P.roots.filter fun y => ¬ v y = γ ^ q) := by
    rw [← Multiset.prod_map_pow]
    have h : ∀ x ∈ (P.roots.filter fun y => ¬ v y = γ ^ q).map (fun y => v y ^ q), x = γ := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hy' := Multiset.mem_filter.1 hy
      exact (hdich y ((mem_roots hmonic.ne_zero).1 hy'.1)).resolve_left hy'.2
    rw [Multiset.eq_replicate_card.2 h, Multiset.prod_replicate, Multiset.card_map]
  have htotal : ((P.roots.filter fun y => v y = γ ^ q).map v).prod *
      ((P.roots.filter fun y => ¬ v y = γ ^ q).map v).prod = γ ^ (q + 1) := by
    rw [← Multiset.prod_add, ← Multiset.map_add, hsplit, prod_roots_size v hmonic, hc0]
  have hpow := congrArg (fun x : Γ₀ => x ^ q) htotal
  simp only [mul_pow, hsmall, hbig, ← pow_mul] at hpow
  rw [← pow_add] at hpow
  have hexp := pow_right_injective₀ (zero_lt_one.trans hγ) hγ.ne' hpow
  have hb1 : Multiset.card (P.roots.filter fun y => v y = γ ^ q) ≤ 1 := by
    by_contra hb
    have hb' : 2 ≤ Multiset.card (P.roots.filter fun y => v y = γ ^ q) := not_le.1 hb
    have h3 : q * 2 * q ≤ q * Multiset.card (P.roots.filter fun y => v y = γ ^ q) * q :=
      Nat.mul_le_mul_right q (Nat.mul_le_mul_left q hb')
    nlinarith [h3, Nat.mul_le_mul_left q hq, hexp, hcard]
  have hb2 : 1 ≤ Multiset.card (P.roots.filter fun y => v y = γ ^ q) := by
    by_contra hb
    have hb0 : Multiset.card (P.roots.filter fun y => v y = γ ^ q) = 0 := by omega
    rw [hb0] at hexp hcard
    nlinarith [hexp, hcard, Nat.mul_le_mul_left q hq]
  omega

private theorem eq_of_isRoot_of_size_eq {q : ℕ} (hq : 1 < q) {γ : Γ₀} (hγ : 1 < γ) {P : K[X]} (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hc0 : v (P.coeff 0) = γ ^ (q + 1))
    (hdich : ∀ y, P.IsRoot y → v y = γ ^ q ∨ v y ^ q = γ) {y₁ y₂ : K}
    (h₁ : P.IsRoot y₁) (hv₁ : v y₁ = γ ^ q) (h₂ : P.IsRoot y₂) (hv₂ : v y₂ = γ ^ q) : y₁ = y₂ := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 (card_roots_filter_size_eq v hq hγ hmonic hdeg hc0 hdich)
  have hmem : ∀ y, P.IsRoot y → v y = γ ^ q → y = a := fun y hy hvy => by
    have h : y ∈ P.roots.filter fun z => v z = γ ^ q :=
      Multiset.mem_filter.2 ⟨(mem_roots hmonic.ne_zero).2 hy, hvy⟩
    rw [ha] at h
    exact Multiset.mem_singleton.1 h
  rw [hmem y₁ h₁ hv₁, hmem y₂ h₂ hv₂]

private theorem rootMultiplicity_eq_one_of_size_eq [DecidableEq K] {q : ℕ} (hq : 1 < q) {γ : Γ₀} (hγ : 1 < γ) {P : K[X]} (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hc0 : v (P.coeff 0) = γ ^ (q + 1))
    (hdich : ∀ y, P.IsRoot y → v y = γ ^ q ∨ v y ^ q = γ) {y : K} (hy : P.IsRoot y) (hvy : v y = γ ^ q) :
    P.rootMultiplicity y = 1 := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 (card_roots_filter_size_eq v hq hγ hmonic hdeg hc0 hdich)
  have hmem : y ∈ P.roots.filter fun z => v z = γ ^ q :=
    Multiset.mem_filter.2 ⟨(mem_roots hmonic.ne_zero).2 hy, hvy⟩
  rw [← count_roots, ← Multiset.count_filter_of_pos (p := fun z => v z = γ ^ q) hvy, ha]
  rw [ha] at hmem
  rw [Multiset.mem_singleton.1 hmem, Multiset.count_singleton_self]

end unique

end NewtonSizes

namespace NormOfGenerator

open Polynomial IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

private theorem norm_sub_algebraMap (x : E) (b : F) (hx : (minpoly F x).natDegree = Module.finrank F E) :
    Algebra.norm F (x - algebraMap F E b) = (-1) ^ Module.finrank F E * (minpoly F x).eval b := by
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hming : minpoly F (x - algebraMap F E b) = (minpoly F x).comp (X + C b) := minpoly.sub_algebraMap x b
  have hintg : IsIntegral F (x - algebraMap F E b) := hint.sub isIntegral_algebraMap
  have hdegg : (minpoly F (x - algebraMap F E b)).natDegree = Module.finrank F E := by
    rw [hming, natDegree_comp, natDegree_X_add_C, mul_one, hx]
  have h1 : Module.finrank F F⟮x - algebraMap F E b⟯ = Module.finrank F E :=
    (IntermediateField.adjoin.finrank hintg).trans hdegg
  have h2 : Module.finrank F⟮x - algebraMap F E b⟯ E = 1 := by
    have ht := Module.finrank_mul_finrank (F := F) (K := F⟮x - algebraMap F E b⟯) (A := E)
    rw [h1] at ht
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos (ht.trans (mul_one _).symm)
  rw [Algebra.norm_eq_norm_adjoin F (x - algebraMap F E b), h2, pow_one]
  have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hintg)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim,
    hdegg, hming, coeff_zero_eq_eval_zero, eval_comp] at hpb
  rw [hpb]
  simp

private theorem norm_sub_algebraMap_of_natDegree_eq (x : E) (b : F) {n : ℕ} (hdeg : (minpoly F x).natDegree = n)
    (hfr : Module.finrank F E = n) :
    Algebra.norm F (x - algebraMap F E b) = (-1) ^ n * (minpoly F x).eval b := by
  rw [← hfr]
  exact norm_sub_algebraMap x b (hdeg.trans hfr.symm)

end NormOfGenerator

namespace HeckeFibreValues

local notation "ℚ̄" => AlgebraicClosure ℚ

section modular_glue
open Polynomial

private noncomputable def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (J : AlgebraicClosure ℚ) :
    Polynomial (AlgebraicClosure ℚ) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) J)

private theorem fibrePoly_coeff (Φ : Polynomial (Polynomial ℤ)) (J : AlgebraicClosure ℚ) (i : ℕ) :
    (fibrePoly Φ J).coeff i = (Φ.coeff i).eval₂ (Int.castRingHom _) J := by
  simp [fibrePoly, coeff_map]

private theorem eval_fibrePoly (Φ : Polynomial (Polynomial ℤ)) (J y : AlgebraicClosure ℚ) :
    (fibrePoly Φ J).eval y = evalModularPair J y Φ := by
  unfold evalModularPair
  simp [fibrePoly, eval_map]

private theorem isRoot_fibrePoly {Φ : Polynomial (Polynomial ℤ)} {J y : AlgebraicClosure ℚ}
    (heq : evalModularPair J y Φ = 0) : (fibrePoly Φ J).IsRoot y := by
  rw [IsRoot, eval_fibrePoly]
  exact heq

private theorem fibrePoly_root_size {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hγ : 1 < γ)
    (hψ : data.Φ.natDegree = q + 1)
    (hc : A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
      A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
      (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
      data.Φ.coeff (q + 1) = 1) :
    ∀ y, (fibrePoly data.Φ J).IsRoot y → A.valuation y = γ ^ q ∨ A.valuation y ^ q = γ := by
  obtain ⟨hc0, hcq, hmid, htop⟩ := hc
  intro y hy
  refine NewtonSizes.root_size_eq_or_pow_eq A.valuation hq.out.one_lt hγ (P := fibrePoly data.Φ J)
    (natDegree_map_le.trans hψ.le) ?_ ?_ ?_ ?_ hy
  · rw [fibrePoly_coeff, htop, eval₂_one]
  · rw [fibrePoly_coeff, hcq]
  · rw [fibrePoly_coeff, hc0]
  · intro i h1 h2
    rw [fibrePoly_coeff]
    exact hmid i h1 h2

private theorem deepRoot_unique {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hγ : 1 < γ)
    (hψ : data.Φ.natDegree = q + 1)
    (hc : A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
      A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
      (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
      data.Φ.coeff (q + 1) = 1)
    {y y' : AlgebraicClosure ℚ} (hy : evalModularPair J y data.Φ = 0) (hy' : evalModularPair J y' data.Φ = 0)
    (hvy : A.valuation y = γ ^ q) (hvy' : A.valuation y' = γ ^ q) : y = y' := by
  have hmonic : (fibrePoly data.Φ J).Monic := data.monic.map _
  have hdeg : (fibrePoly data.Φ J).natDegree = q + 1 := (data.monic.natDegree_map _).trans hψ
  have hc0 : A.valuation ((fibrePoly data.Φ J).coeff 0) = γ ^ (q + 1) := by
    rw [fibrePoly_coeff]
    exact hc.1
  exact NewtonSizes.eq_of_isRoot_of_size_eq A.valuation hq.out.one_lt hγ hmonic hdeg hc0
    (fibrePoly_root_size A data hγ hψ hc) (isRoot_fibrePoly hy) hvy (isRoot_fibrePoly hy') hvy'

private theorem deepRoot_simple {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hγ : 1 < γ)
    (hψ : data.Φ.natDegree = q + 1)
    (hc : A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
      A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
      (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
      data.Φ.coeff (q + 1) = 1)
    {y : AlgebraicClosure ℚ} (hy : evalModularPair J y data.Φ = 0) (hvy : A.valuation y = γ ^ q) :
    evalModularPair J y (Polynomial.derivative data.Φ) ≠ 0 := by
  classical
  intro hder
  have hmonic : (fibrePoly data.Φ J).Monic := data.monic.map _
  have hdeg : (fibrePoly data.Φ J).natDegree = q + 1 := (data.monic.natDegree_map _).trans hψ
  have hc0 : A.valuation ((fibrePoly data.Φ J).coeff 0) = γ ^ (q + 1) := by
    rw [fibrePoly_coeff]
    exact hc.1
  have hmult : (fibrePoly data.Φ J).rootMultiplicity y = 1 :=
    NewtonSizes.rootMultiplicity_eq_one_of_size_eq A.valuation hq.out.one_lt hγ hmonic hdeg hc0
      (fibrePoly_root_size A data hγ hψ hc) (isRoot_fibrePoly hy) hvy
  have hder' : (Polynomial.derivative (fibrePoly data.Φ J)).IsRoot y := by
    have h : fibrePoly (Polynomial.derivative data.Φ) J = Polynomial.derivative (fibrePoly data.Φ J) :=
      (Polynomial.derivative_map data.Φ _).symm
    rw [← h]
    exact isRoot_fibrePoly hder
  have hne : fibrePoly data.Φ J ≠ 0 := hmonic.ne_zero
  have h2 : 1 < (fibrePoly data.Φ J).rootMultiplicity y :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).2 ⟨isRoot_fibrePoly hy, hder'⟩
  omega

end modular_glue

section UniquePlace

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

private def innerAt {R : Type*} [CommRing R] (c : R) (Φ : Polynomial (Polynomial ℤ)) : Polynomial R :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) c)

private theorem eval_innerAt {R : Type*} [CommRing R] (c t : R) (Φ : Polynomial (Polynomial ℤ)) :
    (innerAt c Φ).eval t = evalModularPair c t Φ := by
  simp [innerAt, evalModularPair, Polynomial.eval_map]

private theorem map_innerAt {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R)
    (Φ : Polynomial (Polynomial ℤ)) : (innerAt c Φ).map f = innerAt (f c) Φ := by
  simp only [innerAt, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp

private theorem derivative_innerAt {R : Type*} [CommRing R] (c : R) (Φ : Polynomial (Polynomial ℤ)) :
    Polynomial.derivative (innerAt c Φ) = innerAt c (Polynomial.derivative Φ) := by
  simp [innerAt, Polynomial.derivative_map]

private theorem innerAt_monic {R : Type*} [CommRing R] [Nontrivial R] (c : R) (data : ModularPolynomialData q) :
    (innerAt c data.Φ).Monic :=
  data.monic.map _

private theorem jN_hasValue_restrictAlong (hβ : HeckeBetaBarIntegral ℚ̄ N q)
    (W : Place ℚ̄ (modularFunctionFieldBar (N * q))) {J : ℚ̄} (hJ : W.HasValue (jQFun N q) J) :
    (W.restrictAlong (heckeBetaBar ℚ̄ N q) hβ).HasValue (jN N) J := by
  rw [hasValue_restrictAlong_iff, heckeBetaBar_jN]
  exact hJ

private theorem ord_norm_jFun_sub (hqN : ¬ q ∣ N) (data : ModularPolynomialData q)
    (v : Place ℚ̄ (modularFunctionFieldBar N)) (b : modularFunctionFieldBar N) :
    letI := algebraAlong (heckeBetaBar ℚ̄ N q)
    v.ord (Algebra.norm (modularFunctionFieldBar N) (jFun N q - heckeBetaBar ℚ̄ N q b))
      = v.ord ((innerAt (jN N) data.Φ).eval b) := by
  letI hAlg : Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := algebraAlong (heckeBetaBar ℚ̄ N q)
  letI : Module (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := hAlg.toModule
  haveI := isScalarTower_along (heckeBetaBar ℚ̄ N q)
  haveI : Module.Finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
    ModularCurve.finiteAlong_heckeBetaBar_of_prime ℚ̄ N q
  have hmin : minpoly (modularFunctionFieldBar N) (jFun N q) = innerAt (jN N) data.Φ := by
    rw [← heckeAlphaBar_jN N q]
    refine (ModularCurve.minpoly_heckeAlphaBar_along_heckeBetaBar N q hqN data
      (ModularPolynomialData.evalSymm_of_prime q data)).trans ?_
    unfold innerAt
    congr 1
  have hdeg : (minpoly (modularFunctionFieldBar N) (jFun N q)).natDegree = q + 1 := by
    rw [hmin, innerAt, data.monic.natDegree_map, data.natDegree_eq, ModularCurve.dedekindPsi_prime Fact.out]
  have hfr : Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) = q + 1 := by
    have h := ModularCurve.finrankAlong_heckeBetaBar ℚ̄ N q
    rw [if_neg hqN] at h
    exact h
  change v.ord (Algebra.norm (modularFunctionFieldBar N)
    (jFun N q - algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) b)) = _
  rw [NormOfGenerator.norm_sub_algebraMap_of_natDegree_eq (jFun N q) b hdeg hfr, hmin]
  rcases neg_one_pow_eq_or (R := modularFunctionFieldBar N) (q + 1) with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Place.ord_neg]

end UniquePlace

end HeckeFibreValues

end

end DeepPlaceAnalysis

namespace InftySideMass

private theorem not_isInftySide_of_ord_sub_pos
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
    {a : A}
    (ha : 0 < b.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)))
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b) :
    ¬ IsInftySide P W := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have _ := hqN
  intro hinf
  have hJ : heckeAlphaBar (AlgebraicClosure ℚ) N q
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ = jFun N q :=
    Subtype.ext (coe_heckeAlphaBar _ _ _)
  have hmap : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [map_sub, hJ, AlgHom.commutes]
  have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
  rw [hmap, Place.mem_fiberAlong.mp hW] at hord
  have h1 := Place.one_le_ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W
  have he : (0 : ℤ) < (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by omega
  have hpos : 0 < W.ord (jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
    rw [hord]
    exact mul_pos he ha
  exact absurd (hinf.1 a) (not_le.mpr hpos)

open Classical in

private theorem le_sum_of_ord_sub_pos
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
    (a : A)
    (ha : 0 < b.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  have hall : (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W)
      = Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b :=
    Finset.filter_eq_self.mpr fun W hW => not_isInftySide_of_ord_sub_pos hqN P b ha hW
  rw [hall, FibreDegree.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN b]
  omega

open Classical in

private theorem le_sum_of_sum_filter_isInftySide_le_one
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
    (hinf : (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) ≤ 1) :
    (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  have htot := FibreDegree.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN b
  have hsplit : (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      + (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (fun W => ¬ IsInftySide P W),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      = ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    convert Finset.sum_filter_add_sum_filter_not (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b) (IsInftySide P)
      (fun W => (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
  have _ := P
  rw [htot] at hsplit
  omega

open Classical in

private theorem sum_filter_isInftySide_le_sum_filter_isZeroSide
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      ≤ ∑ W ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ b).filter (IsZeroSide P),
          (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull (N := N) (ℓ := q)
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨-, hβα⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hAL
  have hβα' : ∀ x, atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q x) = heckeAlphaBar (AlgebraicClosure ℚ) N q x :=
    fun x => AlgHom.congr_fun hβα x

  have hinv : ∀ x, (atkinLehnerBar N q)⁻¹ (heckeAlphaBar (AlgebraicClosure ℚ) N q x) = heckeBetaBar (AlgebraicClosure ℚ) N q x := by
    intro x
    rw [← hβα' x, AlgEquiv.aut_inv]
    exact AlgEquiv.symm_apply_apply _ _

  have he : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (atkinLehnerBar N q • W).ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
        = W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) :=
    fun W => Place.ramificationIndexAlong_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q) (heckeBetaBar (AlgebraicClosure ℚ) N q) (atkinLehnerBar N q)
      AlgEquiv.refl (fun x => (hβα' x).symm) W

  have hmem : ∀ W' ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
      (atkinLehnerBar N q)⁻¹ • W' ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ b).filter (IsZeroSide P) := by
    intro W' hW'
    rw [Finset.mem_filter] at hW' ⊢
    refine ⟨?_, ?_⟩
    · rw [Place.mem_fiberAlong] at hW' ⊢
      rw [CuspFibre.restrictAlong_smul_eq (heckeBetaBar (AlgebraicClosure ℚ) N q) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hβ hα (atkinLehnerBar N q)⁻¹ hinv W']
      exact hW'.1
    · rw [← isInftySide_atkinLehnerBar_smul_iff P hqN, smul_inv_smul]
      exact hW'.2
  calc (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      = ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
          (((atkinLehnerBar N q)⁻¹ • W).ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [← he ((atkinLehnerBar N q)⁻¹ • W), smul_inv_smul]
    _ = ∑ W ∈ ((Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P)).image
          (fun W => (atkinLehnerBar N q)⁻¹ • W), (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
        rw [Finset.sum_image]
        intro W₁ _ W₂ _ h
        exact MulAction.injective ((atkinLehnerBar N q)⁻¹) h
    _ ≤ ∑ W ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ b).filter (IsZeroSide P), (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun W _ _ => by positivity
        intro W hW
        rw [Finset.mem_image] at hW
        obtain ⟨W', hW', rfl⟩ := hW
        exact hmem W' hW'

private theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {g : F} {a : K} (h : w.HasValue g a) (n : ℕ) : w.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using w.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem valuation_eq_one_of_red_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (τ : A) (hred : red τ = 1) :
    A.valuation (τ : AlgebraicClosure ℚ) = 1 := by
  have hker : τ - 1 ∈ RingHom.ker red := by
    rw [RingHom.mem_ker, map_sub, map_one, hred, sub_self]
  have hmax : τ - 1 ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) hker
  have hunit : IsUnit τ := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    rw [← IsLocalRing.mem_maximalIdeal, ← neg_sub, Ideal.neg_mem_iff]
    exact hmax
  exact (A.valuation_eq_one_iff τ).mp hunit

private theorem valuation_natCast_lt_one {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.valuation (q : AlgebraicClosure ℚ) < 1 := by
  have hker : ((q : ℕ) : A) ∈ RingHom.ker red := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hmax : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) hker
  have h := (A.valuation_lt_one_iff ((q : ℕ) : A)).mp hmax
  simpa using h

private theorem exists_hasValue_jFun_of_isZeroSide
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = v)
    {J : AlgebraicClosure ℚ} (hJ : v.HasValue (HeckeFibreValues.jN N) J) (hzero : IsZeroSide P W) :
    W.HasValue (jQFun N q) J ∧
      ∃ y : AlgebraicClosure ℚ, W.HasValue (jFun N q) y ∧ A.valuation y = A.valuation J ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have _ := hqN
  have hJW : W.HasValue (jQFun N q) J := by
    have h : (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).HasValue (HeckeFibreValues.jN N) J := by
      rw [hW]
      exact hJ
    rw [HeckeFibreValues.hasValue_restrictAlong_iff, HeckeFibreValues.heckeBetaBar_jN] at h
    exact h
  obtain ⟨-, τ, hτ, hval⟩ := hzero
  refine ⟨hJW, (τ : AlgebraicClosure ℚ) * J ^ q, ?_, ?_⟩
  · have hjQ : jQFun N q ≠ 0 := CuspFibre.jQFun_ne_zero N q
    have hj : jFun N q = tZero N q * jQFun N q ^ q := by
      rw [tZero, div_mul_cancel₀ _ (pow_ne_zero q hjQ)]
    rw [hj]
    exact hval.mul (hasValue_pow W hJW q)
  · rw [map_mul, map_pow, valuation_eq_one_of_red_eq_one red τ hτ, one_mul]

open Classical HeckeFibreValues in

private theorem exists_place_over_of_root {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    (data : ModularPolynomialData q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {J y : AlgebraicClosure ℚ}
    (hJv : v.HasValue (jN N) J) (hEy : evalModularPair J y data.Φ = 0)
    (hsimp : evalModularPair J y (Polynomial.derivative data.Φ) ≠ 0) :
    ∃ w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      w₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) = 1 ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = v →
          0 < W.ord (jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) y) → W = w₀ := by
  classical
  have hjNmem : jN N ∈ v.toValuationSubring := hJv.mem
  set c : v.toValuationSubring := ⟨jN N, hjNmem⟩ with hcdef
  set Q : Polynomial v.toValuationSubring := innerAt c data.Φ with hQdef
  set b : v.toValuationSubring := ⟨algebraMap (AlgebraicClosure ℚ) _ y, v.algebraMap_mem' y⟩ with hbdef
  have hQmonic : Q.Monic := innerAt_monic c data
  have hQmap : Q.map (algebraMap v.toValuationSubring (modularFunctionFieldBar N)) = innerAt (jN N) data.Φ := by
    rw [hQdef, map_innerAt]; rfl

  have hx : (Q.map (algebraMap v.toValuationSubring (modularFunctionFieldBar N))).eval₂ (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom (jFun N q) = 0 := by
    rw [hQmap, innerAt, Polynomial.eval₂_map]
    have hcomp : (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (Polynomial.eval₂RingHom (Int.castRingHom _) (jN N))
        = Polynomial.eval₂RingHom (Int.castRingHom _) (jQFun N q) := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp [heckeBetaBar_jN]
    rw [hcomp]
    exact evalModularPair_jQFun_jFun hqN data

  have hc_res : IsLocalRing.residue v.toValuationSubring c = algebraMap (AlgebraicClosure ℚ) v.ResidueField J :=
    residue_eq_of_hasValue v c hJv
  have hb_res : IsLocalRing.residue v.toValuationSubring b = algebraMap (AlgebraicClosure ℚ) v.ResidueField y :=
    residue_eq_of_hasValue v b (Place.hasValue_algebraMap v y)
  have hQb : ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N)
      = evalModularPair (jN N) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) y) data.Φ := by
    rw [hQdef, eval_innerAt]
    exact map_evalModularPair v.toValuationSubring.subtype c b data.Φ
  have hQb_val : v.HasValue ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N) 0 := by
    refine ⟨(Q.eval b).2, ?_⟩
    change IsLocalRing.residue v.toValuationSubring (Q.eval b) = _
    rw [hQdef, eval_innerAt, map_evalModularPair, hc_res, hb_res, ← map_evalModularPair, hEy]
  have hswap : swapBivar data.Φ = data.Φ :=
    ModularCurve.swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_prime q data)
  have hQb_ne : ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N) ≠ 0 := by
    rw [hQb, evalModularPair_comm hswap, ← eval_innerAt, ← map_innerAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      Polynomial.eval_map, ← Polynomial.aeval_def]
    intro h0
    exact (innerAt_monic y data).ne_zero (transcendental_iff.mp (transcendental_jN N) _ h0)
  have hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N) :=
    ord_pos_of_hasValue_zero v hQb_val hQb_ne

  have hsimple : IsUnit ((Polynomial.derivative Q).eval b) := by
    by_contra hu
    have hm : (Polynomial.derivative Q).eval b ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hm
    rw [hQdef, derivative_innerAt, eval_innerAt, map_evalModularPair, hc_res, hb_res, ← map_evalModularPair] at h0
    exact hsimp ((algebraMap (AlgebraicClosure ℚ) v.ResidueField).injective (h0.trans (map_zero _).symm))
  have hQbF : ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N)
      = (innerAt (jN N) data.Φ).eval (b : modularFunctionFieldBar N) := by
    rw [← hQmap, Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply (algebraMap v.toValuationSubring (modularFunctionFieldBar N)) b).symm
  have hnorm : letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q);
      v.ord (Algebra.norm (modularFunctionFieldBar N) (jFun N q - heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N)))
        = v.ord ((Q.eval b : v.toValuationSubring) : modularFunctionFieldBar N) := by
    rw [hQbF]
    exact ord_norm_jFun_sub hqN data v b

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨w₀, -, -, he₀, -, huniq⟩ :=
    AlgebraicCurve.exists_place_over_of_simple_root_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
      (ModularCurve.finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q) v hQmonic hx b hroot hsimple hnorm
  have hβb : heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N)
      = algebraMap (AlgebraicClosure ℚ) _ y := (heckeBetaBar (AlgebraicClosure ℚ) N q).commutes y
  refine ⟨w₀, he₀, fun W hWv hvan => huniq W hWv ?_⟩
  rw [hβb]
  exact hvan

open HeckeFibreValues in

private theorem exists_hasValue_jN_of_disc {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hdisc : ∀ a : A, v.ord (jN N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0)
    (h0 : v.ord (jN N) = 0) :
    ∃ J : AlgebraicClosure ℚ, v.HasValue (jN N) J ∧ 1 < A.valuation J := by
  have hjN0 : jN N ≠ 0 := by
    intro h
    exact transcendental_jN N (h ▸ isAlgebraic_zero)
  obtain ⟨hmem, -⟩ := v.exists_isUnit_of_ord_eq_zero hjN0 h0
  obtain ⟨J, hJv⟩ : ∃ J : AlgebraicClosure ℚ, v.HasValue (jN N) J := by
    have hrat := isRational_place_modularFunctionFieldBar N v
    exact (v.exists_hasValue_of_surjective hrat hmem).imp fun _ h => h.1
  refine ⟨J, hJv, ?_⟩
  by_contra hle
  push Not at hle
  have hJA : J ∈ A := A.mem_of_valuation_le_one J hle
  have hsub : jN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) J ≠ 0 := by
    intro h
    exact transcendental_jN N (by rw [sub_eq_zero.mp h]; exact isAlgebraic_algebraMap J)
  have hpos : 0 < v.ord (jN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) J) :=
    ord_pos_of_hasValue_zero v (hasValue_sub_self v hJv) hsub
  exact absurd hpos (not_lt.mpr (hdisc ⟨J, hJA⟩))

open Classical HeckeFibreValues in

private theorem le_sum_of_forall_ord_sub_nonpos_of_ord_eq_zero
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hdisc : ∀ a : A, v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0)
    (h0 : v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) = 0) :
    (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα v).filter
        (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  classical
  apply le_sum_of_sum_filter_isInftySide_le_one hqN P v
  refine (sum_filter_isInftySide_le_sum_filter_isZeroSide hqN P v).trans ?_
  obtain ⟨J, hJv, hγ⟩ := exists_hasValue_jN_of_disc A v hdisc h0
  have hqA : A.valuation (q : AlgebraicClosure ℚ) < 1 := valuation_natCast_lt_one A red

  by_cases hne : ((Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ v).filter (IsZeroSide P)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact zero_le_one
  obtain ⟨W, hWmem⟩ := hne
  rw [Finset.mem_filter, Place.mem_fiberAlong] at hWmem
  obtain ⟨hJW, y, hyW, hyγ⟩ := exists_hasValue_jFun_of_isZeroSide hqN P v hWmem.1 hJv hWmem.2

  have hEy : evalModularPair J y data.Φ = 0 := evalModularPair_values hqN data W hJW hyW
  have hc4 := coeff_sizes A hqA data hKr rfl hγ
  have hsimp : evalModularPair J y (Polynomial.derivative data.Φ) ≠ 0 :=
    deepRoot_simple A data hγ (natDegree_Φ data) hc4 hEy hyγ
  obtain ⟨w₀, he₀, huniq⟩ := exists_place_over_of_root hqN data hβ v hJv hEy hsimp

  have hall : ∀ W' ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ v).filter (IsZeroSide P), W' = w₀ := by
    intro W' hW'
    rw [Finset.mem_filter, Place.mem_fiberAlong] at hW'
    obtain ⟨hJW', y', hy'W', hy'γ⟩ := exists_hasValue_jFun_of_isZeroSide hqN P v hW'.1 hJv hW'.2
    have hEy' : evalModularPair J y' data.Φ = 0 := evalModularPair_values hqN data W' hJW' hy'W'
    have hyy' : y = y' := deepRoot_unique A data hγ (natDegree_Φ data) hc4 hEy hEy' hyγ hy'γ
    refine huniq W' hW'.1 ?_
    rw [hyy']
    exact ord_pos_of_hasValue_zero W' (hasValue_sub_self W' hy'W') (jFun_sub_ne_zero y')

  calc (∑ W' ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ v).filter (IsZeroSide P),
          (W'.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ))
      ≤ ∑ W' ∈ ({w₀} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))),
          (W'.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun W' hW' => Finset.mem_singleton.mpr (hall W' hW'))
          fun _ _ _ => by positivity
    _ = (w₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) := Finset.sum_singleton _ _
    _ = 1 := by rw [he₀, Nat.cast_one]

end InftySideMass

open Classical in

theorem solution
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
    :
    (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  by_cases hb : b.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) < 0
  ·
    obtain ⟨W₁, hW₁, hnot₁, hq₁⟩ := CuspFibre.exists_not_inftySide_of_pole hqN P b hb
    have hnn : ∀ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W),
        (0 : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
      fun W _ => Nat.cast_nonneg _
    exact hq₁.trans (Finset.single_le_sum hnn (Finset.mem_filter.mpr ⟨hW₁, hnot₁⟩))
  · by_cases hint : ∃ a : A, 0 < b.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    ·
      obtain ⟨a, ha⟩ := hint
      exact InftySideMass.le_sum_of_ord_sub_pos hqN P b a ha
    ·
      have hdisc : ∀ a : A, b.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 :=
        fun a => not_lt.mp fun h => hint ⟨a, h⟩
      have h0 : b.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) = 0 := by
        refine le_antisymm ?_ (not_lt.mp hb)
        simpa using hdisc 0
      exact InftySideMass.le_sum_of_forall_ord_sub_nonpos_of_ord_eq_zero hqN P b hdisc h0

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong (solution)
