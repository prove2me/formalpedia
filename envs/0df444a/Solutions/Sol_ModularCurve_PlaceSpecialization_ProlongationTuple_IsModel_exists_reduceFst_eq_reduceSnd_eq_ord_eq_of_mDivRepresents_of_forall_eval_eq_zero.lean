-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d23117b4-612d-52a2-92b7-3ad84d3dc8fa

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_IncidenceSystem
import Definitions.Def_MDivRepresents
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_PowerSeries_coeff_eq_coeff_of_forall_coeff_eval_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_aeval
import Theorems.Thm_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X
import Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace Roots

theorem ord_eq_of_forall_le_of_degree_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (hdeg1 : ∀ w : Place K F, w.deg = 1)
    {f : F} (hf : f ≠ 0) (E : Divisor K F) (hE : E.degree = 0) (hle : ∀ v, E v ≤ v.ord f) :
    ∀ v, v.ord f = E v := by
  classical
  obtain ⟨D, hD, hD0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf

  have hnn : ∀ v, 0 ≤ (D - E) v := fun v => by
    rw [Finsupp.sub_apply, hD v]; linarith [hle v]
  have hdeg0 : (D - E).degree = 0 := by rw [map_sub, hD0, hE, sub_zero]
  have hzero : ∀ v, (D - E) v = 0 := by
    intro v
    have hsum : (D - E).degree = (D - E).sum fun w n => n := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply]
      exact Finsupp.sum_congr fun w _ => by simp [hdeg1 w]
    rw [hdeg0, Finsupp.sum] at hsum
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hnn w)).mp hsum.symm
    by_cases hv : v ∈ (D - E).support
    · exact h v hv
    · exact Finsupp.notMem_support_iff.mp hv
  intro v
  have := hzero v
  rw [Finsupp.sub_apply, hD v] at this
  linarith

theorem one_add_sum_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    {n : ℕ} (hs : Fin n → ↥(modularFunctionFieldBar (N * q))) (hh₁ : ∀ l, hs l ∈ R.R₁.integers)
    (a : Fin n → A) (ha : ∀ l, a l ∈ IsLocalRing.maximalIdeal A) :
    (1 + ∑ l, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a l : AlgebraicClosure ℚ) * hs l) ≠ 0 := by
  classical
  have hconst : ∀ l, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a l : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    fun l => (R.R₁.algebraMap_mem_iff (a l : AlgebraicClosure ℚ)).mpr (a l).2
  set x : R.R₁.integers := 1 + ∑ l, (⟨_, hconst l⟩ : R.R₁.integers) * ⟨hs l, hh₁ l⟩ with hxdef
  have hcoe : (x : ↥(modularFunctionFieldBar (N * q))) = 1 + ∑ l, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a l : AlgebraicClosure ℚ) * hs l := by
    rw [hxdef]
    push_cast
    rfl
  have hres : R.R₁.residue x = 1 := by
    rw [hxdef, map_add, map_one, map_sum]
    have h0 : ∀ l, R.R₁.residue ((⟨_, hconst l⟩ : R.R₁.integers) * ⟨hs l, hh₁ l⟩) = 0 := by
      intro l
      rw [map_mul, R.R₁.residue_algebraMap (a l), (IsLocalRing.residue_eq_zero_iff _).mpr (ha l),
        map_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun l _ => h0 l), add_zero]
  intro h0
  rw [← hcoe] at h0
  have hx0 : x = 0 := Subtype.ext h0
  rw [hx0, map_zero] at hres
  exact zero_ne_one hres

theorem red_eq_zero_of_mem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    red a = 0 := by
  rw [← R.redBar_residue a, (IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero]

theorem red_eq_of_sub_mem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) {a b : A} (h : a - b ∈ IsLocalRing.maximalIdeal A) :
    red a = red b := by
  have := red_eq_zero_of_mem R h
  rwa [map_sub, sub_eq_zero] at this

theorem disc_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    {B : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hB : P.IsStrictFst B) (haff : IsAffineGeomPlace k N (P.reduceFst B))
    {z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))} {u₀ : A} (htri : IsFstTriple (q := q) (P.reduceFst B) (red u₀) z y₁ y₂)
    (a : A) (ha : a - u₀ ∈ IsLocalRing.maximalIdeal A) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Q ∧ P.reduceFst Q = P.reduceFst B ∧
      Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1 ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Q' → P.reduceFst Q' = P.reduceFst B → Q' ≠ Q →
        Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by
  have hred : red a = red u₀ := red_eq_of_sub_mem R ha
  have hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst B))
      ≠ P.reduceFst B := hB.2
  rcases htri with ⟨hz, -, -, hc⟩ | ⟨hz, -, -, hc⟩
  · subst hz
    obtain ⟨Q, ⟨h1, h2, h3⟩, h4⟩ :=
      hR.exists_isStrictFst_reduceFst_eq_ord_jFun_sub_eq_one P hqN R _ hv haff (red u₀) hc a hred
    exact ⟨Q, h1, h2, h3, h4⟩
  · subst hz
    obtain ⟨Q, ⟨h1, h2, h3⟩, h4⟩ :=
      hR.exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one P hqN R _ hv haff (red u₀) hc a hred
    exact ⟨Q, h1, h2, h3, h4⟩

theorem disc_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    {B : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hB : P.IsStrictSnd B) (haff : IsAffineGeomPlace k N (P.reduceSnd B))
    {z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))} {u₀ : A} (htri : IsSndTriple (q := q) (P.reduceSnd B) (red u₀) z y₁ y₂)
    (a : A) (ha : a - u₀ ∈ IsLocalRing.maximalIdeal A) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Q ∧ P.reduceSnd Q = P.reduceSnd B ∧
      Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1 ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Q' → P.reduceSnd Q' = P.reduceSnd B → Q' ≠ Q →
        Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by
  have hred : red a = red u₀ := red_eq_of_sub_mem R ha
  have hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd B))
      ≠ P.reduceSnd B := hB.2
  rcases htri with ⟨hz, -, -, hc⟩ | ⟨hz, -, -, hc⟩
  · subst hz
    obtain ⟨Q, ⟨h1, h2, h3⟩, h4⟩ :=
      hR.exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one P hqN R _ hv haff (red u₀) hc a hred
    exact ⟨Q, h1, h2, h3, h4⟩
  · subst hz
    obtain ⟨Q, ⟨h1, h2, h3⟩, h4⟩ :=
      hR.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one P hqN R _ hv haff (red u₀) hc a hred
    exact ⟨Q, h1, h2, h3, h4⟩

theorem eval_inc_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i : Fin g) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.inc i r) = 0 := by
  induction r using Fin.lastCases with
  | last => exact hroot (IncidenceSystem.Var.u i)
  | cast r =>
    have h := hroot (IncidenceSystem.Var.c (finProdFinEquiv (i, r)))
    simpa [IncidenceSystem.Data.system] using h

theorem eval_branch_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i : Fin g) (j : Fin 2) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.branch i j r) = 0 :=
  hroot (IncidenceSystem.Var.w i j r)

theorem eval_inv_eq_zero_of_root {g m' : ℕ} {A' : Type*} [CommRing A'] (Dt : IncidenceSystem.Data g 2 m' A')
    (Pt : IncidenceSystem.Var g 2 m' → A') (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (kk : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : MvPolynomial.eval Pt (Dt.inv kk i r) = 0 :=
  hroot (IncidenceSystem.Var.σ kk i r)

theorem evalBar_eq_aeval {N' q' : ℕ} {A' : ValuationSubring (AlgebraicClosure ℚ)}
    (c : Option (Fin 2) → ↥(modularFunctionFieldBar (N' * q'))) (H : MvPolynomial (Option (Fin 2)) A') :
    PlaceSpecialization.evalBar N' q' c H = MvPolynomial.aeval c (MvPolynomial.map (algebraMap A' (AlgebraicClosure ℚ)) H) := by
  rw [PlaceSpecialization.evalBar, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

theorem hasValue_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b : K} (h : 0 < Q.ord (y - algebraMap K F b)) : Q.HasValue y b := by
  have hmem : y - algebraMap K F b ∈ Q.toValuationSubring := by
    by_cases h0 : y - algebraMap K F b = 0
    · rw [h0]; exact zero_mem _
    · exact Q.mem_of_ord_nonneg h0 h.le
  have hy : y ∈ Q.toValuationSubring := by
    have := add_mem hmem (Q.algebraMap_mem' b)
    rwa [sub_add_cancel] at this
  refine ⟨hy, ?_⟩
  have hmax := Q.mk_mem_maximalIdeal_of_ord_pos hmem h
  have hx : (⟨y - algebraMap K F b, hmem⟩ : Q.toValuationSubring)
      = ⟨y, hy⟩ - algebraMap K Q.toValuationSubring b := by
    refine Subtype.ext ?_
    show y - algebraMap K F b = y - (algebraMap K Q.toValuationSubring b : F)
    rw [Place.coe_algebraMap]
  rw [hx] at hmax
  have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Q.residue_algebraMap]

theorem eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    {y : F} {b b' : K} (h : 0 < Q.ord (y - algebraMap K F b)) (h' : 0 < Q.ord (y - algebraMap K F b')) : b = b' :=
  (hasValue_of_ord_sub_pos Q h).unique (hasValue_of_ord_sub_pos Q h')

section Iso
open MvPolynomial

theorem aeval_eq_eval_optionEquivLeft {R : Type*} [CommRing R] {σ τ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    (e : Option τ ≃ σ) (g : σ → S) (H : MvPolynomial σ R) :
    aeval g H =
      ((optionEquivLeft R τ (rename e.symm H)).map
        (aeval (fun t => g (e (some t))) : MvPolynomial τ R →ₐ[R] S).toRingHom).eval (g (e none)) := by

  let ev : Polynomial (MvPolynomial τ R) →ₐ[R] S :=
    Polynomial.aevalTower (aeval (fun t => g (e (some t)))) (g (e none))
  let Φ : MvPolynomial σ R →ₐ[R] S :=
    ev.comp (((optionEquivLeft R τ).toAlgHom).comp (rename e.symm))
  have hΦ : ∀ H', Φ H' = ((optionEquivLeft R τ (rename e.symm H')).map
      (aeval (fun t => g (e (some t))) : MvPolynomial τ R →ₐ[R] S).toRingHom).eval (g (e none)) := by
    intro H'
    simp only [Φ, ev, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [Polynomial.eval_map]
    rfl
  rw [← hΦ]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext (f := aeval g) (g := Φ) fun s => ?_)) H

  rw [aeval_X, hΦ]
  rcases hs : e.symm s with _ | t
  · have : s = e none := by rw [← hs, Equiv.apply_symm_apply]
    rw [rename_X, hs, optionEquivLeft_X_none, Polynomial.map_X, Polynomial.eval_X, this]
  · have : s = e (some t) := by rw [← hs, Equiv.apply_symm_apply]
    rw [rename_X, hs, optionEquivLeft_X_some, Polynomial.map_C, Polynomial.eval_C]
    simp [this]

end Iso

theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] {w : Place K F} {g g' : F} {a a' : K}
    (h : w.HasValue g a) (h' : w.HasValue g' a') : w.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : w.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) {ι : Type*}
    (fs : ι → F) (vals : ι → K) (h : ∀ o, w.HasValue (fs o) (vals o)) (H : MvPolynomial ι K) :
    w.HasValue (MvPolynomial.aeval fs H) (MvPolynomial.aeval vals H) := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    exact Place.hasValue_algebraMap w c
  | add p q hp hq => rw [map_add, map_add]; exact hasValue_add hp hq
  | mul_X p o hp => rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]; exact hp.mul (h o)

theorem evalAt_eq_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {g : F} {a : K} (h : w.HasValue g a) : w.evalAt g = a := by
  rw [w.evalAt_of_mem h.mem, h.residue_eq, Place.residueInv_algebraMap]

theorem eval_sub_eval_mem {A : Type*} [CommRing A] (I : Ideal A) {ι : Type*} (v v' : ι → A)
    (h : ∀ o, v o - v' o ∈ I) (H : MvPolynomial ι A) :
    MvPolynomial.eval v H - MvPolynomial.eval v' H ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hv : (Ideal.Quotient.mk I) ∘ v = (Ideal.Quotient.mk I) ∘ v' :=
    funext fun o => (Ideal.Quotient.eq).mpr (h o)
  show Ideal.Quotient.mk I (MvPolynomial.eval₂ (RingHom.id A) v H) = Ideal.Quotient.mk I (MvPolynomial.eval₂ (RingHom.id A) v' H)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hv]

theorem aeval_map_algebraMap {A L : Type*} [CommRing A] [CommRing L] [Algebra A L] {ι : Type*} (vA : ι → A)
    (H : MvPolynomial ι A) :
    MvPolynomial.aeval (fun o => algebraMap A L (vA o)) (MvPolynomial.map (algebraMap A L) H)
      = algebraMap A L (MvPolynomial.eval vA H) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  show MvPolynomial.eval₂ ((algebraMap L L).comp (algebraMap A L)) (fun o => algebraMap A L (vA o)) H
    = algebraMap A L (MvPolynomial.eval₂ (RingHom.id A) vA H)
  rw [MvPolynomial.eval₂_comp_left]
  congr 1

section Branch
open MvPolynomial

theorem derivative_optionEquivLeft {R : Type*} [CommRing R] {σ : Type*} (p : MvPolynomial (Option σ) R) :
    Polynomial.derivative (optionEquivLeft R σ p) = optionEquivLeft R σ (pderiv none p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => rw [optionEquivLeft_C, Polynomial.derivative_C, pderiv_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p o hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
    cases o with
    | none => rw [optionEquivLeft_X_none, Polynomial.derivative_X, pderiv_X]; simp; ring
    | some t => rw [optionEquivLeft_X_some, Polynomial.derivative_C, pderiv_X]; simp; ring

theorem aeval_congr_of_not_mem_vars {R : Type*} [CommRing R] {σ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    (H : MvPolynomial σ R) (s : σ) (hH : s ∉ H.vars) (g g' : σ → S) (hg : ∀ o, o ≠ s → g o = g' o) :
    aeval g H = aeval g' H := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← coe_eval₂Hom, ← coe_eval₂Hom]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun o ho _ => hg o ?_) rfl
  rintro rfl; exact hH ho

def sw : Option (Fin 2) ≃ Option (Fin 2) := Equiv.swap none (some 0)

theorem sw_none : sw none = some 0 := by simp [sw]
theorem sw_some0 : sw (some 0) = none := by simp [sw]
theorem sw_some1 : sw (some 1) = some 1 := by
  simp [sw, Equiv.swap_apply_of_ne_of_ne]

theorem jet_eq_taylorCoeff_of_branch {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (H : MvPolynomial (Option (Fin 2)) K) (hvars : (some 1 : Option (Fin 2)) ∉ H.vars)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hrel : aeval fs H = 0)
    (hunit : Q.evalAt (aeval fs (pderiv (some 0) H)) ≠ 0)
    (w : Fin 2 → Fin m → K)
    (hw0 : ∀ hm : 0 < m, w 0 ⟨0, hm⟩ = Q.evalAt (fs (some 0)))
    (hbranch : ∀ r : Fin m, (aeval (fun o : Option (Fin 2) =>
        Option.elim o (Polynomial.C a + Polynomial.X) (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff r = 0) :
    ∀ r : Fin m, w 0 r = Place.taylorCoeff Q t r (fs (some 0)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro r; exact r.elim0

  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  set φ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K := aeval (fun s => Ser (sw (some s))) with hφ
  set f : Polynomial (PowerSeries K) := (optionEquivLeft K (Fin 2) (rename sw.symm H)).map φ.toRingHom with hf
  have hiso : ∀ (H' : MvPolynomial (Option (Fin 2)) K) (Y : PowerSeries K),
      ((optionEquivLeft K (Fin 2) (rename sw.symm H')).map φ.toRingHom).eval Y
        = aeval (Function.update Ser (some 0) Y) H' := by
    intro H' Y
    rw [aeval_eq_eval_optionEquivLeft sw (Function.update Ser (some 0) Y) H', sw_none, Function.update_self]
    have hg : (fun s : Fin 2 => Function.update Ser (some 0) Y (sw (some s))) = fun s => Ser (sw (some s)) := by
      funext s
      apply Function.update_of_ne
      fin_cases s <;> simp [sw, Equiv.swap_apply_def]
    rw [hg]

  have hroot : f.eval (Ser (some 0)) = 0 := by
    rw [hf, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs H, hrel]
    ext n
    rw [PowerSeries.coeff_mk, map_zero, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp

  set Y : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 0 ⟨n, h⟩ else 0 with hYdef
  set Y₂ : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 1 ⟨n, h⟩ else 0 with hY₂def
  have hYcoeff : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (![Y, Y₂] j) = w j i := by
    intro j i
    fin_cases j <;> simp [hYdef, hY₂def, PowerSeries.coeff_mk, i.2]
  have hcand : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0 := by
    intro r hr
    rw [hf, hiso]
    have hcongr : aeval (Function.update Ser (some 0) Y) H
        = aeval (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) ![Y, Y₂]) H := by
      refine aeval_congr_of_not_mem_vars H (some 1) hvars _ _ fun o ho => ?_
      rcases o with _ | j
      · rw [Function.update_of_ne (by simp), hSer]; simp only [Option.elim]; exact hz
      · fin_cases j
        · simp
        · exact absurd rfl ho
    rw [hcongr, ← MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq H a w ![Y, Y₂] hYcoeff ⟨r, hr⟩]
    exact hbranch ⟨r, hr⟩

  have h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff (Ser (some 0)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos hm, Place.taylorCoeff_zero]
    exact hw0 hm

  have hder : f.derivative = (optionEquivLeft K (Fin 2) (rename sw.symm (pderiv (some 0) H))).map φ.toRingHom := by
    rw [hf, Polynomial.derivative_map, derivative_optionEquivLeft]
    congr 2
    have hsw : (none : Option (Fin 2)) = sw.symm (some 0) := by
      rw [Equiv.eq_symm_apply, sw_none]
    rw [hsw, pderiv_rename sw.symm.injective]
  have hunit' : IsUnit (PowerSeries.constantCoeff (f.derivative.eval (Ser (some 0)))) := by
    rw [hder, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Place.taylorCoeff_zero]
    exact isUnit_iff_ne_zero.mpr hunit

  have hmain := PowerSeries.coeff_eq_coeff_of_forall_coeff_eval_eq_zero f (Ser (some 0)) Y hroot hunit' h0 m hcand
  intro r
  have e := hmain r r.2
  rw [hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos r.2] at e
  exact e

theorem coeff_aeval_congr {K : Type*} [CommRing K] {σ : Type*} (H : MvPolynomial σ K) (m : ℕ)
    (g g' : σ → PowerSeries K) (h : ∀ s, ∀ r, r < m → PowerSeries.coeff r (g s) = PowerSeries.coeff r (g' s)) :
    ∀ r, r < m → PowerSeries.coeff r (MvPolynomial.aeval g H) = PowerSeries.coeff r (MvPolynomial.aeval g' H) := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X ^ m}
  have hq : ∀ s, Ideal.Quotient.mk I (g s) = Ideal.Quotient.mk I (g' s) := by
    intro s
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro r hr
    rw [map_sub, h s r hr, sub_self]
  have hcomp : (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval g)
      = (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval g') := by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    congr 1
    funext s
    exact hq s
  have hdiff : MvPolynomial.aeval g H - MvPolynomial.aeval g' H ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact congrArg (fun φ : MvPolynomial σ K →ₐ[K] (PowerSeries K ⧸ I) => φ H) hcomp
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hdiff
  intro r hr
  have e := hdiff r hr
  rwa [map_sub, sub_eq_zero] at e

def sw1 : Option (Fin 2) ≃ Option (Fin 2) := Equiv.swap none (some 1)

theorem sw1_none : sw1 none = some 1 := by simp [sw1]

theorem jet_eq_taylorCoeff_of_branch_snd {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (H : MvPolynomial (Option (Fin 2)) K)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hrel : aeval fs H = 0)
    (hunit : Q.evalAt (aeval fs (pderiv (some 1) H)) ≠ 0)
    (w : Fin 2 → Fin m → K)
    (hw₀ : ∀ r : Fin m, w 0 r = Place.taylorCoeff Q t r (fs (some 0)))
    (hw0 : ∀ hm : 0 < m, w 1 ⟨0, hm⟩ = Q.evalAt (fs (some 1)))
    (hbranch : ∀ r : Fin m, (aeval (fun o : Option (Fin 2) =>
        Option.elim o (Polynomial.C a + Polynomial.X) (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff r = 0) :
    ∀ r : Fin m, w 1 r = Place.taylorCoeff Q t r (fs (some 1)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro r; exact r.elim0
  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  set φ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K := aeval (fun s => Ser (sw1 (some s))) with hφ
  set f : Polynomial (PowerSeries K) := (optionEquivLeft K (Fin 2) (rename sw1.symm H)).map φ.toRingHom with hf
  have hiso : ∀ (H' : MvPolynomial (Option (Fin 2)) K) (Y : PowerSeries K),
      ((optionEquivLeft K (Fin 2) (rename sw1.symm H')).map φ.toRingHom).eval Y
        = aeval (Function.update Ser (some 1) Y) H' := by
    intro H' Y
    rw [aeval_eq_eval_optionEquivLeft sw1 (Function.update Ser (some 1) Y) H', sw1_none, Function.update_self]
    have hg : (fun s : Fin 2 => Function.update Ser (some 1) Y (sw1 (some s))) = fun s => Ser (sw1 (some s)) := by
      funext s
      apply Function.update_of_ne
      fin_cases s <;> simp [sw1, Equiv.swap_apply_def]
    rw [hg]
  have hroot : f.eval (Ser (some 1)) = 0 := by
    rw [hf, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs H, hrel]
    ext n
    rw [PowerSeries.coeff_mk, map_zero, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp
  set Y₁ : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 0 ⟨n, h⟩ else 0 with hY₁def
  set Y : PowerSeries K := PowerSeries.mk fun n => if h : n < m then w 1 ⟨n, h⟩ else 0 with hYdef
  have hYcoeff : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (![Y₁, Y] j) = w j i := by
    intro j i
    fin_cases j <;> simp [hYdef, hY₁def, PowerSeries.coeff_mk, i.2]
  have hcand : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0 := by
    intro r hr
    rw [hf, hiso]
    have hcongr := coeff_aeval_congr H m (Function.update Ser (some 1) Y)
      (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) ![Y₁, Y]) (fun o r' hr' => ?_) r hr
    · rw [hcongr, ← MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq H a w ![Y₁, Y] hYcoeff ⟨r, hr⟩]
      exact hbranch ⟨r, hr⟩
    · rcases o with _ | j
      · rw [Function.update_of_ne (by simp), hSer]; simp only [Option.elim]; rw [hz]
      · fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, ne_eq, Option.some.injEq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, Option.elim, Matrix.cons_val_zero]
          rw [hSer, PowerSeries.coeff_mk, hY₁def, PowerSeries.coeff_mk, dif_pos hr']
          exact (hw₀ ⟨r', hr'⟩).symm
        · simp
  have h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff (Ser (some 1)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos hm, Place.taylorCoeff_zero]
    exact hw0 hm
  have hder : f.derivative = (optionEquivLeft K (Fin 2) (rename sw1.symm (pderiv (some 1) H))).map φ.toRingHom := by
    rw [hf, Polynomial.derivative_map, derivative_optionEquivLeft]
    congr 2
    have hsw : (none : Option (Fin 2)) = sw1.symm (some 1) := by
      rw [Equiv.eq_symm_apply, sw1_none]
    rw [hsw, pderiv_rename sw1.symm.injective]
  have hunit' : IsUnit (PowerSeries.constantCoeff (f.derivative.eval (Ser (some 1)))) := by
    rw [hder, hiso, Function.update_eq_self, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Place.taylorCoeff_zero]
    exact isUnit_iff_ne_zero.mpr hunit
  have hmain := PowerSeries.coeff_eq_coeff_of_forall_coeff_eval_eq_zero f (Ser (some 1)) Y hroot hunit' h0 m hcand
  intro r
  have e := hmain r r.2
  rw [hYdef, hSer, PowerSeries.coeff_mk, PowerSeries.coeff_mk, dif_pos r.2] at e
  exact e

theorem sigma_eq_taylorCoeff_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1)
    {m : ℕ} (S : MvPolynomial (Option (Fin 2)) K)
    (fs : Option (Fin 2) → F) (hfs : ∀ o, fs o ∈ Q.toValuationSubring)
    (a : K) (hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C a + PowerSeries.X)
    (hs0 : Q.evalAt (aeval fs S) ≠ 0)
    (w : Fin 2 → Fin m → K) (hw : ∀ j (r : Fin m), w j r = Place.taylorCoeff Q t r (fs (some j)))
    (σ : Fin m → K)
    (hinv : ∀ r : Fin m, ((∑ i : Fin m, Polynomial.monomial (i : ℕ) (σ i)) *
        aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C a + Polynomial.X)
          (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) S - 1).coeff r = 0) :
    ∀ r : Fin m, σ r = Place.taylorCoeff Q t r (aeval fs S)⁻¹ := by
  classical
  set Ser : Option (Fin 2) → PowerSeries K := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer

  have hScoeff : ∀ i : Fin m, (aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C a + Polynomial.X)
      (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) S).coeff i = Place.taylorCoeff Q t i (aeval fs S) := by
    intro i
    rw [MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq S a w (fun j => Ser (some j))
      (fun j i' => by rw [hSer, PowerSeries.coeff_mk, hw]) i]
    have hfun : (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C a + PowerSeries.X) fun j => Ser (some j)) = Ser := by
      funext o; rcases o with _ | j
      · simp only [Option.elim]; rw [← hz]
      · rfl
    rw [hfun, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs S, PowerSeries.coeff_mk]

  have hσcoeff : ∀ n, (∑ i : Fin m, Polynomial.monomial (i : ℕ) (σ i)).coeff n = if h : n < m then σ ⟨n, h⟩ else 0 := by
    intro n
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨n, h⟩ : Fin m)]
      · simp
      · intro j _ hj; rw [if_neg]; intro e; exact hj (Fin.ext e)
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · exact Finset.sum_eq_zero fun j _ => if_neg (fun e => h (by rw [← e]; exact j.2))

  set σ' : ℕ → K := fun n => if h : n < m then σ ⟨n, h⟩ else 0 with hσ'
  have hsys : ∀ r, r < m → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ' x.1 * Place.taylorCoeff Q t x.2 (aeval fs S)
      = if r = 0 then 1 else 0 := by
    intro r hr
    have h := hinv ⟨r, hr⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_one, sub_eq_zero] at h
    simp only [Fin.val_mk] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hx) hr
    rw [hσcoeff, hσ', hScoeff ⟨x.2, hx2⟩]
  have hsmem : ∀ S' : MvPolynomial (Option (Fin 2)) K, aeval fs S' ∈ Q.toValuationSubring := by
    intro S'
    induction S' using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact Q.algebraMap_mem' c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p o hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hfs o)
  have hres := Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq Q hQ ht (hsmem S) hs0 m σ' hsys
  intro r
  have e := hres r r.2
  simp only [hσ'] at e
  rw [dif_pos r.2] at e
  simpa using e

theorem smul_mem' {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (c : K) {f : F}
    (hf : f ∈ w.toValuationSubring) : c • f ∈ w.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (w.algebraMap_mem' c) hf

theorem taylorCoeff_sum_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) (hw : w.IsRational) {t : F} (ht : w.ord t = 1)
    {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ w.toValuationSubring) (r : ℕ) :
    Place.taylorCoeff w t r (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Place.taylorCoeff w t r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp
  | insert i s hi ih =>
    have hfi : f i ∈ w.toValuationSubring := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ w.toValuationSubring := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsmem : (∑ j ∈ s, c j • f j) ∈ w.toValuationSubring :=
      sum_mem fun j hj => smul_mem' w (c j) (hfs j hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Place.taylorCoeff_add w hw ht (smul_mem' w (c i) hfi) hsmem,
      Place.taylorCoeff_smul w hw ht hfi, ih hfs]

theorem taylorCoeff_sum_smul_div_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hQ : Q.IsRational) {t : F} (ht : Q.ord t = 1) {m : ℕ}
    {ι : Type*} [Fintype ι] (c : ι → K) (p s : ι → F)
    (hp : ∀ kk, p kk ∈ Q.toValuationSubring) (hsinv : ∀ kk, (s kk)⁻¹ ∈ Q.toValuationSubring)
    (Pp Sg : ι → Polynomial K)
    (hPp : ∀ kk (i : Fin m), (Pp kk).coeff i = Place.taylorCoeff Q t i (p kk))
    (hSg : ∀ kk (i : Fin m), (Sg kk).coeff i = Place.taylorCoeff Q t i (s kk)⁻¹)
    (r : Fin m) :
    ∑ kk, c kk * (Pp kk * Sg kk).coeff r = Place.taylorCoeff Q t r (∑ kk, c kk • (p kk * (s kk)⁻¹)) := by
  classical
  rw [taylorCoeff_sum_smul Q hQ ht _ c _ (fun kk _ => mul_mem (hp kk) (hsinv kk)) r]
  refine Finset.sum_congr rfl fun kk _ => ?_
  congr 1
  rw [Polynomial.coeff_mul, Place.taylorCoeff_mul Q hQ ht (hp kk) (hsinv kk) r]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.fst_le hx) r.2
  have hx2 : x.2 < m := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hx) r.2
  rw [hPp kk ⟨x.1, hx1⟩, hSg kk ⟨x.2, hx2⟩]

end Branch

theorem eq_of_eval_eq_zero_of_sub_mem {A : Type*} [CommRing A] [IsLocalRing A] (f : Polynomial A) {x y : A}
    (hx : f.eval x = 0) (hy : f.eval y = 0) (hxy : y - x ∈ IsLocalRing.maximalIdeal A)
    (hder : IsUnit (f.derivative.eval x)) : y = x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f x (y - x)
  rw [show x + (y - x) = y by ring, hy, hx, zero_add] at hk

  have hu : IsUnit (f.derivative.eval x + k * (y - x)) := by
    have hmem : k * (y - x) ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hxy
    by_contra hnu
    have hmem2 : f.derivative.eval x + k * (y - x) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : f.derivative.eval x ∈ IsLocalRing.maximalIdeal A := by
      have := sub_mem hmem2 hmem
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hder
  have h0 : (y - x) * (f.derivative.eval x + k * (y - x)) = 0 := by
    have : (y - x) * (f.derivative.eval x + k * (y - x))
        = f.derivative.eval x * (y - x) + k * (y - x) ^ 2 := by ring
    rw [this, ← hk]
  have : y - x = 0 := (hu.mul_left_eq_zero).mp h0
  exact sub_eq_zero.mp this

section PointCore
open MvPolynomial

theorem coeff_sum_monomial_fin {R : Type*} [Semiring R] {n : ℕ} (c : Fin n → R) (i : Fin n) :
    (∑ r : Fin n, Polynomial.monomial (r : ℕ) (c r)).coeff i = c i := by
  classical
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg]; intro e; exact hj (Fin.ext e)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem map_spoly {g m' : ℕ} {A' L' : Type*} [CommRing A'] [CommRing L'] (φ : A' →+* L')
    (Pt : IncidenceSystem.Var g 2 m' → A') (kk : Option (Fin (g * m'))) (i : Fin g) :
    (IncidenceSystem.spoly Pt kk i).map φ
      = ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (φ (Pt (IncidenceSystem.Var.σ kk i r))) := by
  rw [IncidenceSystem.spoly, ← Polynomial.coe_mapRingHom, map_sum]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial]

theorem eval_zero_substAt {g m' : ℕ} {A' : Type*} [CommRing A'] (Pt : IncidenceSystem.Var g 2 m' → A') (i : Fin g)
    (H : MvPolynomial (Option (Fin 2)) A') :
    (IncidenceSystem.substAt Pt i H).eval 0 = MvPolynomial.eval (IncidenceSystem.Data.ptCoord Pt i) H := by
  classical
  unfold IncidenceSystem.substAt
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom (0 : A')).comp (algebraMap A' (Polynomial A')) = RingHom.id A' := by
    ext a; simp
  rw [hC]
  show MvPolynomial.eval₂ (RingHom.id A') _ H = MvPolynomial.eval₂ (RingHom.id A') (IncidenceSystem.Data.ptCoord Pt i) H
  congr 1
  funext o
  rw [Function.comp_apply, Polynomial.coe_evalRingHom]
  rcases o with _ | j
  · simp [IncidenceSystem.coordAt, IncidenceSystem.Data.ptCoord]
  · simp only [IncidenceSystem.coordAt, IncidenceSystem.Data.ptCoord, Option.elim, IncidenceSystem.wpoly,
      Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
    · simp
    · intro r _ hr
      have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
      simp [zero_pow this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem map_substAt {g m' : ℕ} {A' L' : Type*} [CommRing A'] [CommRing L'] (φ : A' →+* L')
    (Pt : IncidenceSystem.Var g 2 m' → A') (i : Fin g) (H : MvPolynomial (Option (Fin 2)) A') :
    (IncidenceSystem.substAt Pt i H).map φ
      = MvPolynomial.eval₂ (Polynomial.C : L' →+* Polynomial L') (fun o : Option (Fin 2) => Option.elim o
          (Polynomial.C (φ (Pt (IncidenceSystem.Var.u i))) + Polynomial.X)
          (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (φ (Pt (IncidenceSystem.Var.w i j r)))))
        (MvPolynomial.map φ H) := by
  classical
  unfold IncidenceSystem.substAt
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.mapRingHom φ).comp (algebraMap A' (Polynomial A')) = (Polynomial.C : L' →+* Polynomial L').comp φ := by
    ext a; simp
  rw [hC]
  congr 1
  funext o
  rw [Function.comp_apply, Polynomial.coe_mapRingHom]
  rcases o with _ | j
  · simp [IncidenceSystem.coordAt]
  · simp only [IncidenceSystem.coordAt, Option.elim, IncidenceSystem.wpoly]
    rw [← Polynomial.coe_mapRingHom, map_sum]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial]

set_option maxHeartbeats 6400000 in
theorem point_core {L F : Type*} [Field L] [Field F] [Algebra L F] {A : ValuationSubring L}
    {k : Type*} [Field k] (red : A →+* k) (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    {g m' : ℕ} (Dt : IncidenceSystem.Data g 2 m' A) (i : Fin g)
    (z y₁ y₂ : F) (τ : A) (hsec : Option (Fin (g * m')) → F)
    (hvars : (some 1 : Option (Fin 2)) ∉ (Dt.G i 0).vars)
    (hb : ∀ j, aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂])
      (MvPolynomial.map (algebraMap A L) (Dt.G i j)) = 0)
    (hd : ∀ kk, aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂]) (MvPolynomial.map (algebraMap A L) (Dt.p kk i))
      = hsec kk * (z - algebraMap L F (Dt.u₀ i : L)) ^ m' * (z - algebraMap L F (τ : L))
        * aeval (fun o : Option (Fin 2) => Option.elim o z ![y₁, y₂]) (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))
    (he : ∀ kk, red (Dt.sVal Dt.centre kk i) ≠ 0) (hf : ∀ j, red (Dt.dG Dt.centre i j) ≠ 0)
    (Pt : IncidenceSystem.Var g 2 m' → A) (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (Q : Place L F) (hQ : Q.IsRational)
    (hordz : Q.ord (z - algebraMap L F (Pt (IncidenceSystem.Var.u i) : L)) = 1)
    (hvalQ : ∀ j : Fin 2, ∃ b : A, 0 < Q.ord (![y₁, y₂] j - algebraMap L F (b : L)) ∧ red b = red (Dt.w₀ i j 0))
    (hg0 : (∑ kk, (Option.elim kk (1 : L) fun k' => (Pt (IncidenceSystem.Var.c k') : L)) • hsec kk)
      * (z - algebraMap L F (Dt.u₀ i : L)) ^ m' * (z - algebraMap L F (τ : L)) ≠ 0) :
    ((m' + 1 : ℕ) : ℤ) ≤ Q.ord ((∑ kk, (Option.elim kk (1 : L) fun k' => (Pt (IncidenceSystem.Var.c k') : L)) • hsec kk)
      * (z - algebraMap L F (Dt.u₀ i : L)) ^ m' * (z - algebraMap L F (τ : L))) := by
  classical

  set a : A := Pt (IncidenceSystem.Var.u i) with ha
  set t : F := z - algebraMap L F (a : L) with htdef
  set fs : Option (Fin 2) → F := fun o => Option.elim o z ![y₁, y₂] with hfsdef
  have hφinj : Function.Injective (algebraMap A L) := Subtype.val_injective
  have hne_of_red : ∀ x : A, red x ≠ 0 → algebraMap A L x ≠ 0 := by
    intro x hx h0
    apply hx
    have : x = 0 := hφinj (by rw [h0, map_zero])
    rw [this, map_zero]
  have hsubmem : ∀ {x y : A}, red x = red y → x - y ∈ IsLocalRing.maximalIdeal A := by
    intro x y h
    rw [← hker, map_sub, h, sub_self]
  have hred_eq_of_sub : ∀ {x y : A}, x - y ∈ IsLocalRing.maximalIdeal A → red x = red y := by
    intro x y h
    have := (hker _).mpr h
    rwa [map_sub, sub_eq_zero] at this

  have ht : Q.ord t = 1 := hordz
  obtain ⟨b₀, hb₀, hrb₀⟩ := hvalQ 0
  obtain ⟨b₁, hb₁, hrb₁⟩ := hvalQ 1
  set vA : Option (Fin 2) → A := fun o => Option.elim o a ![b₀, b₁] with hvAdef
  have hval : ∀ o, Q.HasValue (fs o) (algebraMap A L (vA o)) := by
    intro o
    rcases o with _ | j
    · exact hasValue_of_ord_sub_pos Q (show 0 < Q.ord t by rw [ht]; exact one_pos)
    · fin_cases j
      · exact hasValue_of_ord_sub_pos Q hb₀
      · exact hasValue_of_ord_sub_pos Q hb₁
  have hfs : ∀ o, fs o ∈ Q.toValuationSubring := fun o => (hval o).mem

  have hcong : ∀ o, vA o - IncidenceSystem.Data.ptCoord Dt.centre i o ∈ IsLocalRing.maximalIdeal A := by
    intro o
    rcases o with _ | j
    · exact hPt (IncidenceSystem.Var.u i)
    · fin_cases j
      · exact hsubmem hrb₀
      · exact hsubmem hrb₁

  have hvalpoly : ∀ H : MvPolynomial (Option (Fin 2)) A,
      Q.HasValue (aeval fs (MvPolynomial.map (algebraMap A L) H)) (algebraMap A L (MvPolynomial.eval vA H)) := by
    intro H
    have h := hasValue_aeval Q fs (fun o => algebraMap A L (vA o)) hval (MvPolynomial.map (algebraMap A L) H)
    rwa [aeval_map_algebraMap] at h
  have hred_eval : ∀ H : MvPolynomial (Option (Fin 2)) A,
      red (MvPolynomial.eval vA H) = red (MvPolynomial.eval (IncidenceSystem.Data.ptCoord Dt.centre i) H) :=
    fun H => hred_eq_of_sub (eval_sub_eval_mem _ _ _ hcong H)

  have hs_ne : ∀ kk, Q.evalAt (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i))) ≠ 0 := by
    intro kk
    rw [evalAt_eq_of_hasValue Q (hvalpoly _)]
    apply hne_of_red
    rw [hred_eval]
    exact he kk
  have hs_val_ne : ∀ kk, algebraMap A L (MvPolynomial.eval vA (Dt.s kk i)) ≠ 0 := by
    intro kk; have := hs_ne kk; rwa [evalAt_eq_of_hasValue Q (hvalpoly _)] at this
  have hsF_ne : ∀ kk, aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)) ≠ 0 :=
    fun kk => (hvalpoly _).ne_zero (hs_val_ne kk)
  have hsinv : ∀ kk, (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ ∈ Q.toValuationSubring :=
    fun kk => ((hvalpoly _).inv (hs_val_ne kk)).mem
  have hdG_ne : ∀ j, Q.evalAt (aeval fs (pderiv (some j) (MvPolynomial.map (algebraMap A L) (Dt.G i j)))) ≠ 0 := by
    intro j
    rw [MvPolynomial.pderiv_map, evalAt_eq_of_hasValue Q (hvalpoly _)]
    apply hne_of_red
    rw [hred_eval]
    exact hf j

  have hza : Q.evalAt z = (a : L) := evalAt_eq_of_hasValue Q (hval none)
  have hz : (PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs none)) = PowerSeries.C (algebraMap A L a) + PowerSeries.X := by
    have h := Place.mk_taylorCoeff_eq_C_add_X Q hQ (hfs none) (by
      show Q.ord (z - algebraMap L F (Q.evalAt z)) = 1
      rw [hza]; exact ht)
    rw [show fs none = z from rfl] at h ⊢
    rw [hza] at h
    exact h

  have hbranch0 : ∀ j, MvPolynomial.eval (IncidenceSystem.Data.ptCoord Pt i) (Dt.G i j) = 0 := by
    intro j
    rw [← eval_zero_substAt, ← Polynomial.coeff_zero_eq_eval_zero]
    exact_mod_cast (by
      have h := eval_branch_eq_zero_of_root Dt Pt hroot i j 0
      rwa [IncidenceSystem.eval_branch] at h)
  have hrootA : ∀ j, MvPolynomial.eval vA (Dt.G i j) = 0 := by
    intro j
    apply hφinj
    rw [map_zero]
    exact ((hvalpoly (Dt.G i j)).unique (by rw [hb j]; simpa using Place.hasValue_algebraMap Q (0 : L))).symm ▸ rfl

  have haev : ∀ (gg : Option (Fin 2) → A) (H' : MvPolynomial (Option (Fin 2)) A),
      aeval gg H' = MvPolynomial.eval gg H' := fun gg H' => RingHom.congr_fun (MvPolynomial.coe_aeval_eq_eval gg) H'
  have hisoA : ∀ (e : Option (Fin 2) ≃ Option (Fin 2)) (H' : MvPolynomial (Option (Fin 2)) A) (Y : A),
      ((optionEquivLeft A (Fin 2) (rename e.symm H')).map
        (aeval (fun s => vA (e (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom).eval Y
        = MvPolynomial.eval (Function.update vA (e none) Y) H' := by
    intro e H' Y
    rw [← haev, aeval_eq_eval_optionEquivLeft e (Function.update vA (e none) Y) H', Function.update_self]
    have hg : (fun s : Fin 2 => Function.update vA (e none) Y (e (some s))) = fun s => vA (e (some s)) := by
      funext s
      apply Function.update_of_ne
      intro h
      exact Option.some_ne_none s (e.injective h)
    rw [hg]
  have hptc : IncidenceSystem.Data.ptCoord Pt i
      = fun o => Option.elim o a ![Pt (IncidenceSystem.Var.w i 0 0), Pt (IncidenceSystem.Var.w i 1 0)] := by
    funext o
    rcases o with _ | j
    · rfl
    · fin_cases j <;> rfl
  have hunitA : ∀ j, IsUnit (MvPolynomial.eval vA (pderiv (some j) (Dt.G i j))) := by
    intro j
    by_contra hnu
    have hmem : MvPolynomial.eval vA (pderiv (some j) (Dt.G i j)) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    apply hf j
    show red (MvPolynomial.eval (IncidenceSystem.Data.ptCoord Dt.centre i) (pderiv (some j) (Dt.G i j))) = 0
    rw [← hred_eval, hker]
    exact hmem

  have hw00 : Pt (IncidenceSystem.Var.w i 0 0) = b₀ := by
    set F₀ : Polynomial A := (optionEquivLeft A (Fin 2) (rename sw.symm (Dt.G i 0))).map
      (aeval (fun s => vA (sw (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom with hF₀
    have hevF : ∀ Y, F₀.eval Y = MvPolynomial.eval (Function.update vA (some 0) Y) (Dt.G i 0) := by
      intro Y; rw [hF₀, hisoA sw, sw_none]
    have hx : F₀.eval (Pt (IncidenceSystem.Var.w i 0 0)) = 0 := by
      rw [hevF, ← hbranch0 0, hptc, ← haev, ← haev]
      refine aeval_congr_of_not_mem_vars _ (some 1) hvars _ _ fun o ho => ?_
      rcases o with _ | j
      · rw [Function.update_of_ne (by simp)]; rfl
      · fin_cases j
        · simp
        · exact absurd rfl ho
    have hy : F₀.eval b₀ = 0 := by
      rw [hevF]
      have : Function.update vA (some 0) b₀ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]; exact hrootA 0
    have hder : F₀.derivative.eval b₀ = MvPolynomial.eval vA (pderiv (some 0) (Dt.G i 0)) := by
      rw [hF₀, Polynomial.derivative_map, derivative_optionEquivLeft,
        show (none : Option (Fin 2)) = sw.symm (some 0) by rw [Equiv.eq_symm_apply, sw_none],
        pderiv_rename sw.symm.injective, hisoA sw, sw_none]
      have : Function.update vA (some 0) b₀ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]
    have hcg : Pt (IncidenceSystem.Var.w i 0 0) - b₀ ∈ IsLocalRing.maximalIdeal A := by
      have h1 := hPt (IncidenceSystem.Var.w i 0 0)
      have h2 : b₀ - Dt.w₀ i 0 0 ∈ IsLocalRing.maximalIdeal A := hsubmem hrb₀
      have := sub_mem h1 h2
      simp only [IncidenceSystem.Data.centre] at this
      convert this using 1; ring
    exact eq_of_eval_eq_zero_of_sub_mem F₀ hy hx hcg (hder ▸ hunitA 0)

  have hw10 : Pt (IncidenceSystem.Var.w i 1 0) = b₁ := by
    set F₁ : Polynomial A := (optionEquivLeft A (Fin 2) (rename sw1.symm (Dt.G i 1))).map
      (aeval (fun s => vA (sw1 (some s))) : MvPolynomial (Fin 2) A →ₐ[A] A).toRingHom with hF₁
    have hevF : ∀ Y, F₁.eval Y = MvPolynomial.eval (Function.update vA (some 1) Y) (Dt.G i 1) := by
      intro Y; rw [hF₁, hisoA sw1, sw1_none]
    have hx : F₁.eval (Pt (IncidenceSystem.Var.w i 1 0)) = 0 := by
      rw [hevF, ← hbranch0 1, hptc, hw00]
      have hfun : Function.update vA (some 1) (Pt (IncidenceSystem.Var.w i 1 0))
          = fun o => Option.elim o a ![b₀, Pt (IncidenceSystem.Var.w i 1 0)] := by
        funext o
        rcases o with _ | j
        · rw [Function.update_of_ne (by simp)]; rfl
        · fin_cases j
          · rw [Function.update_of_ne (by simp)]; rfl
          · simp
      rw [hfun]
    have hy : F₁.eval b₁ = 0 := by
      rw [hevF]
      have : Function.update vA (some 1) b₁ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]; exact hrootA 1
    have hder : F₁.derivative.eval b₁ = MvPolynomial.eval vA (pderiv (some 1) (Dt.G i 1)) := by
      rw [hF₁, Polynomial.derivative_map, derivative_optionEquivLeft,
        show (none : Option (Fin 2)) = sw1.symm (some 1) by rw [Equiv.eq_symm_apply, sw1_none],
        pderiv_rename sw1.symm.injective, hisoA sw1, sw1_none]
      have : Function.update vA (some 1) b₁ = vA := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this]
    have hcg : Pt (IncidenceSystem.Var.w i 1 0) - b₁ ∈ IsLocalRing.maximalIdeal A := by
      have h1 := hPt (IncidenceSystem.Var.w i 1 0)
      have h2 : b₁ - Dt.w₀ i 1 0 ∈ IsLocalRing.maximalIdeal A := hsubmem hrb₁
      have := sub_mem h1 h2
      simp only [IncidenceSystem.Data.centre] at this
      convert this using 1; ring
    exact eq_of_eval_eq_zero_of_sub_mem F₁ hy hx hcg (hder ▸ hunitA 1)

  set w : Fin 2 → Fin (m' + 1) → L := fun j r => algebraMap A L (Pt (IncidenceSystem.Var.w i j r)) with hwdef
  have hsubst : ∀ H : MvPolynomial (Option (Fin 2)) A, (IncidenceSystem.substAt Pt i H).map (algebraMap A L)
      = aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C (algebraMap A L a) + Polynomial.X)
          (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (w j r))) (MvPolynomial.map (algebraMap A L) H) := by
    intro H
    rw [map_substAt, MvPolynomial.aeval_def, Polynomial.algebraMap_eq]
  have hbranch : ∀ j (r : Fin (m' + 1)), (aeval (fun o : Option (Fin 2) => Option.elim o
      (Polynomial.C (algebraMap A L a) + Polynomial.X) (fun j => ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (w j r)))
        (MvPolynomial.map (algebraMap A L) (Dt.G i j))).coeff r = 0 := by
    intro j r
    rw [← hsubst, Polynomial.coeff_map]
    have h := eval_branch_eq_zero_of_root Dt Pt hroot i j r
    rw [IncidenceSystem.eval_branch] at h
    rw [h, map_zero]
  have hvars' : (some 1 : Option (Fin 2)) ∉ (MvPolynomial.map (algebraMap A L) (Dt.G i 0)).vars :=
    fun h => hvars (MvPolynomial.vars_map _ _ h)
  have hw₀ : ∀ r : Fin (m' + 1), w 0 r = Place.taylorCoeff Q t r (fs (some 0)) :=
    jet_eq_taylorCoeff_of_branch Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.G i 0)) hvars' fs hfs
      (algebraMap A L a) hz (hb 0) (hdG_ne 0) w
      (fun _ => by simp only [hwdef, Fin.zero_eta]; rw [hw00, evalAt_eq_of_hasValue Q (hval (some 0))]; rfl) (hbranch 0)
  have hw₁ : ∀ r : Fin (m' + 1), w 1 r = Place.taylorCoeff Q t r (fs (some 1)) :=
    jet_eq_taylorCoeff_of_branch_snd Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.G i 1)) fs hfs
      (algebraMap A L a) hz (hb 1) (hdG_ne 1) w hw₀
      (fun _ => by simp only [hwdef, Fin.zero_eta]; rw [hw10, evalAt_eq_of_hasValue Q (hval (some 1))]; rfl) (hbranch 1)
  have hw : ∀ j (r : Fin (m' + 1)), w j r = Place.taylorCoeff Q t r (fs (some j)) := by
    intro j r; fin_cases j; exacts [hw₀ r, hw₁ r]

  set Ser : Option (Fin 2) → PowerSeries L := fun o => PowerSeries.mk fun n => Place.taylorCoeff Q t n (fs o) with hSer
  have hcoeffH : ∀ (H : MvPolynomial (Option (Fin 2)) A) (r : Fin (m' + 1)),
      ((IncidenceSystem.substAt Pt i H).map (algebraMap A L)).coeff r
        = Place.taylorCoeff Q t r (aeval fs (MvPolynomial.map (algebraMap A L) H)) := by
    intro H r
    rw [hsubst, MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq _ _ w (fun j => Ser (some j))
      (fun j i' => by rw [hSer, PowerSeries.coeff_mk, hw]) r]
    have hfun : (fun o : Option (Fin 2) => Option.elim o (PowerSeries.C (algebraMap A L a) + PowerSeries.X)
        fun j => Ser (some j)) = Ser := by
      funext o; rcases o with _ | j
      · simp only [Option.elim]; rw [← hz]
      · rfl
    rw [hfun, hSer, ← Place.mk_taylorCoeff_aeval Q hQ ht fs hfs _, PowerSeries.coeff_mk]

  have hσ : ∀ kk (r : Fin (m' + 1)), algebraMap A L (Pt (IncidenceSystem.Var.σ kk i r))
      = Place.taylorCoeff Q t r (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ := by
    intro kk
    refine sigma_eq_taylorCoeff_inv Q hQ ht (MvPolynomial.map (algebraMap A L) (Dt.s kk i)) fs hfs
      (algebraMap A L a) hz (hs_ne kk) w hw _ fun r => ?_
    have h := eval_inv_eq_zero_of_root Dt Pt hroot kk i r
    rw [IncidenceSystem.eval_inv] at h
    have h' := congrArg (algebraMap A L) h
    rw [map_zero, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, hsubst] at h'
    rw [← h', map_spoly]

  set cc : Option (Fin (g * m')) → L := fun kk => Option.elim kk (1 : L) fun k' => (Pt (IncidenceSystem.Var.c k') : L)
    with hcc
  set pF : Option (Fin (g * m')) → F := fun kk => aeval fs (MvPolynomial.map (algebraMap A L) (Dt.p kk i)) with hpF
  set sF : Option (Fin (g * m')) → F := fun kk => aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)) with hsF
  have hpmem : ∀ kk, pF kk ∈ Q.toValuationSubring := fun kk => (hvalpoly _).mem
  have htc : ∀ r : Fin (m' + 1), Place.taylorCoeff Q t r (∑ kk, cc kk • (pF kk * (sF kk)⁻¹)) = 0 := by
    intro r
    rw [← taylorCoeff_sum_smul_div_eq Q hQ ht cc pF sF hpmem hsinv
      (fun kk => (IncidenceSystem.substAt Pt i (Dt.p kk i)).map (algebraMap A L))
      (fun kk => (IncidenceSystem.spoly Pt kk i).map (algebraMap A L))
      (fun kk i' => hcoeffH _ i') (fun kk i' => by
        show (Polynomial.map (algebraMap A L) (IncidenceSystem.spoly Pt kk i)).coeff i' = _
        rw [map_spoly, coeff_sum_monomial_fin, hσ]) r]
    have h := eval_inc_eq_zero_of_root Dt Pt hroot i r
    rw [IncidenceSystem.eval_inc] at h
    have h' := congrArg (algebraMap A L) h
    rw [map_zero, map_add, map_sum] at h'
    rw [← h', Fintype.sum_option]
    congr 1
    · rw [hcc]; simp only [Option.elim, one_mul]
      rw [← Polynomial.coeff_map, Polynomial.map_mul]
    · refine Finset.sum_congr rfl fun k' _ => ?_
      rw [hcc]; simp only [Option.elim, map_mul]
      rw [← Polynomial.coeff_map, Polynomial.map_mul]
      rfl

  have hsum : (∑ kk, cc kk • (pF kk * (sF kk)⁻¹))
      = (∑ kk, cc kk • hsec kk) * (z - algebraMap L F (Dt.u₀ i : L)) ^ m' * (z - algebraMap L F (τ : L)) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kk _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
    congr 1
    show aeval fs (MvPolynomial.map (algebraMap A L) (Dt.p kk i)) * (aeval fs (MvPolynomial.map (algebraMap A L) (Dt.s kk i)))⁻¹ = _
    rw [hd kk, mul_inv_cancel_right₀ (hsF_ne kk)]
  have hGmem : (∑ kk, cc kk • (pF kk * (sF kk)⁻¹)) ∈ Q.toValuationSubring :=
    sum_mem fun kk _ => smul_mem' Q _ (mul_mem (hpmem kk) (hsinv kk))
  have hG0 : (∑ kk, cc kk • (pF kk * (sF kk)⁻¹)) ≠ 0 := by rw [hsum]; exact hg0
  rw [← hsum]
  exact (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord Q hQ ht hGmem hG0 (m' + 1)).mp fun q hq => htc ⟨q, hq⟩

end PointCore

section Global
open MvPolynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem red_ker_iff {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (a : A) :
    red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h
    rw [← IsLocalRing.residue_eq_zero_iff]
    apply R.redBar.injective
    rw [R.redBar_residue, h, map_zero]
  · exact red_eq_zero_of_mem R

theorem isAffineGeomPlace_frob {v : Place k ↥(modularFunctionFieldC k N)} (hv : IsAffineGeomPlace k N v) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := by
  have hrat : v.IsRational :=
    (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  exact ((exists_isCentreOf_of_isRational hrat hv).frobOnPlacesGeomLevel data hKr).isAffineGeomPlace

theorem exists_value_red_eq {Qpp B : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} {v : Place k ↥(modularFunctionFieldC k N)} {y : ↥(modularFunctionFieldBar (N * q))} {ygen : ↥(modularFunctionFieldC k N)} {w₀ : A}
    (h1 : ∃ b : A, 0 < Qpp.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)) ∧
      0 < v.ord (ygen - algebraMap k ↥(modularFunctionFieldC k N) (red b)))
    (h2 : ∃ b : A, 0 < B.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)) ∧
      0 < v.ord (ygen - algebraMap k ↥(modularFunctionFieldC k N) (red b)))
    (hc : 0 < B.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w₀ : AlgebraicClosure ℚ))) :
    ∃ b : A, 0 < Qpp.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)) ∧ red b = red w₀ := by
  obtain ⟨b, hb, hbv⟩ := h1
  obtain ⟨b', hb', hb'v⟩ := h2
  refine ⟨b, hb, ?_⟩
  have e1 : (b' : AlgebraicClosure ℚ) = (w₀ : AlgebraicClosure ℚ) := eq_of_ord_sub_pos B hb' hc
  have e2 : red b = red b' := eq_of_ord_sub_pos v hbv hb'v
  rw [e2, Subtype.ext e1]

theorem ord_pow_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (w : Place K' F') {x : F'} (hx : x ≠ 0) (n : ℕ) :
    w.ord (x ^ n) = n * w.ord x := by
  induction n with
  | zero => rw [pow_zero, Place.ord_one]; simp
  | succ n ih => rw [pow_succ, Place.ord_mul w (pow_ne_zero n hx) hx, ih]; push_cast; ring

set_option maxHeartbeats 6400000 in

theorem point_fst (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {T₁ : Finset (Place k ↥(modularFunctionFieldC k N))} (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v) (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v)
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A)
    (Pt : IncidenceSystem.Var (d₁ + d₂) 2 m' → A)
    (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i₁ : Fin d₁) (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (τ : A)
    (htri : IsFstTriple (q := q) (P.reduceFst (Q₁ i₁)) (red (Dt.u₀ (finSumFinEquiv (Sum.inl i₁)))) z y₁ y₂)
    (hb : ∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.G (finSumFinEquiv (Sum.inl i₁)) j) = 0)
    (hvars : (some 1 : Option (Fin 2)) ∉ (Dt.G (finSumFinEquiv (Sum.inl i₁)) 0).vars)
    (hc1 : 0 < (Q₁ i₁).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ (finSumFinEquiv (Sum.inl i₁)) : AlgebraicClosure ℚ)))
    (hc2 : ∀ j : Fin 2, 0 < (Q₁ i₁).ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.w₀ (finSumFinEquiv (Sum.inl i₁)) j 0 : AlgebraicClosure ℚ)))
    (hc3 : 0 < (Q₁' i₁).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)))
    (hd : ∀ kk, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.p kk (finSumFinEquiv (Sum.inl i₁)))
      = Option.elim kk 1 (fun kk => h kk.succ) * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ (finSumFinEquiv (Sum.inl i₁)) : AlgebraicClosure ℚ)) ^ m'
        * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) * evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.s kk (finSumFinEquiv (Sum.inl i₁))))
    (he : ∀ kk, red (Dt.sVal Dt.centre kk (finSumFinEquiv (Sum.inl i₁))) ≠ 0)
    (hf : ∀ j, red (Dt.dG Dt.centre (finSumFinEquiv (Sum.inl i₁)) j) ≠ 0) :
    ∃ Qpp : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Qpp ∧ P.reduceFst Qpp = P.reduceFst (Q₁ i₁) ∧
      (((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₁' i₁) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₁ i₁) (1 : ℤ)) Qpp) := by
  classical
  set i : Fin (d₁ + d₂) := finSumFinEquiv (Sum.inl i₁) with hidef
  set v := P.reduceFst (Q₁ i₁) with hvdef
  have haff : IsAffineGeomPlace k N v := hT₁aff v ((hT₁ v).mpr ⟨i₁, rfl⟩)
  have haff' : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := isAffineGeomPlace_frob haff

  obtain ⟨Qpp, hQs, hQr, hQz, hQoth⟩ :=
    disc_fst P hqN R hR (hQ₁ i₁) haff htri (Pt (IncidenceSystem.Var.u i)) (hPt (IncidenceSystem.Var.u i))
  obtain ⟨Qc, hQcs, hQcr, hQcz, hQcoth⟩ :=
    disc_fst P hqN R hR (hQ₁ i₁) haff htri (Dt.u₀ i) (by rw [sub_self]; exact zero_mem _)

  have hBc : Q₁ i₁ = Qc := by
    by_contra hne
    have := hQcoth (Q₁ i₁) (hQ₁ i₁) rfl hne
    rw [this] at hc1
    exact lt_irrefl _ hc1

  have hQrat : Qpp.IsRational :=
    (Place.isRational_iff_deg_eq_one Qpp).mpr (deg_eq_one_modularFunctionFieldBar (N * q) Qpp)

  have hrB' : P.reduceFst (Q₁' i₁) = v := hred₁ i₁
  have hsndQ : P.reduceSnd Qpp = frobOnPlacesGeomLevel k N data hKr v := by rw [← hQs.1, hQr]
  have hsndB : P.reduceSnd (Q₁ i₁) = frobOnPlacesGeomLevel k N data hKr v := by rw [← (hQ₁ i₁).1]

  have key : ∀ (hτ : τ - Dt.u₀ i ∈ IsLocalRing.maximalIdeal A)
      (hvalQ : ∀ j : Fin 2, ∃ b : A, 0 < Qpp.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)) ∧
        red b = red (Dt.w₀ i j 0)),
      ((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₁' i₁) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₁ i₁) (1 : ℤ)) Qpp := by
    intro hτ hvalQ
    obtain ⟨Qt, hQts, hQtr, hQtz, hQtoth⟩ := disc_fst P hqN R hR (hQ₁ i₁) haff htri τ hτ
    have hBt : Q₁' i₁ = Qt := by
      by_contra hne
      have := hQtoth (Q₁' i₁) (hQ₁' i₁) hrB' hne
      rw [this] at hc3
      exact lt_irrefl _ hc3

    have hordu : Qpp.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) = (Finsupp.single (Q₁ i₁) (1 : ℤ)) Qpp := by
      rw [Finsupp.single_apply, hBc]
      by_cases hq : Qc = Qpp
      · rw [if_pos hq, ← hq]; exact hQcz
      · rw [if_neg hq]; exact hQcoth Qpp hQs hQr (Ne.symm hq)
    have hordτ : Qpp.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) = (Finsupp.single (Q₁' i₁) (1 : ℤ)) Qpp := by
      rw [Finsupp.single_apply, hBt]
      by_cases hq : Qt = Qpp
      · rw [if_pos hq, ← hq]; exact hQtz
      · rw [if_neg hq]; exact hQtoth Qpp hQs hQr (Ne.symm hq)

    set f : ↥(modularFunctionFieldBar (N * q)) := 1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ with hfdef
    have hf0 : f ≠ 0 := one_add_sum_ne_zero R (fun k' => h k'.succ) (fun k' => hh₁ _) (fun k' => Pt (IncidenceSystem.Var.c k'))
      (fun k' => by simpa [IncidenceSystem.Data.centre] using hPt (IncidenceSystem.Var.c k'))
    have hzu0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have h1 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((Dt.u₀ i : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)) := by
        rw [map_sub, ← sub_eq_zero.mp h0]
      have h2 := hQz
      rw [h1] at h2
      by_cases hc : (Dt.u₀ i : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ) = 0
      · rw [hc, map_zero, Place.ord_zero] at h2; exact zero_ne_one h2
      · rw [(Qpp.hasValue_algebraMap _).ord_eq_zero hc] at h2; exact zero_ne_one h2
    have hzτ0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have h1 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((τ : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)) := by
        rw [map_sub, ← sub_eq_zero.mp h0]
      have h2 := hQz
      rw [h1] at h2
      by_cases hc : (τ : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ) = 0
      · rw [hc, map_zero, Place.ord_zero] at h2; exact zero_ne_one h2
      · rw [(Qpp.hasValue_algebraMap _).ord_eq_zero hc] at h2; exact zero_ne_one h2

    have hcomb : (∑ kk, (Option.elim kk (1 : AlgebraicClosure ℚ) fun k' => (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ))
        • (Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ)) = f := by
      rw [Fintype.sum_option, hfdef]
      simp only [Option.elim, one_smul]
      congr 1
    have hg0 : (∑ kk, (Option.elim kk (1 : AlgebraicClosure ℚ) fun k' => (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ))
        • (Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ))
        * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) ^ m' * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ≠ 0 := by
      rw [hcomb]; exact mul_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hzu0)) hzτ0
    have hcore := point_core (L := AlgebraicClosure ℚ) red (red_ker_iff R) Dt i z y₁ y₂ τ (fun kk => Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ)
      hvars (fun j => by rw [← evalBar_eq_aeval]; exact hb j)
      (fun kk => by rw [← evalBar_eq_aeval, ← evalBar_eq_aeval]; exact hd kk) he hf Pt hPt hroot Qpp hQrat hQz hvalQ hg0
    rw [hcomb, Place.ord_mul Qpp (mul_ne_zero hf0 (pow_ne_zero _ hzu0)) hzτ0,
      Place.ord_mul Qpp hf0 (pow_ne_zero _ hzu0), ord_pow_eq Qpp hzu0, hordu, hordτ] at hcore
    linarith
  refine ⟨Qpp, hQs, hQr, ?_⟩

  rcases htri with ⟨hz, hy1, hy2, -⟩ | ⟨hz, hy1, hy2, -⟩
  · subst hz hy1 hy2

    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) (by rw [hrB']; exact haff)
    obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
    refine key ?_ fun j => ?_
    · rw [← red_ker_iff R, map_sub, sub_eq_zero]
      have e1 : (a' : AlgebraicClosure ℚ) = (τ : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₁' i₁) ha' hc3
      have e2 : (a'' : AlgebraicClosure ℚ) = (Dt.u₀ i : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₁ i₁) ha'' hc1
      rw [hrB'] at ha'v
      have e3 : red a' = red a'' := eq_of_ord_sub_pos v ha'v ha''v
      rw [← Subtype.ext e1, ← Subtype.ext e2, e3]
    · fin_cases j
      · exact exists_value_red_eq
          (P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst Qpp (by rw [hQr]; exact haff))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
              exact ⟨b, hb, by rw [hQr]; exact hbv⟩)
          (hc2 0)
      · exact exists_value_red_eq
          (P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Qpp (by rw [hsndQ]; exact haff'))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₁ i₁) (by rw [hsndB]; exact haff')
              exact ⟨b, hb, by rw [hsndQ]; rw [hsndB] at hbv; exact hbv⟩)
          (hc2 1)
  · subst hz hy1 hy2

    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁' i₁) (by rw [hrB']; exact haff)
    obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
    refine key ?_ fun j => ?_
    · rw [← red_ker_iff R, map_sub, sub_eq_zero]
      have e1 : (a' : AlgebraicClosure ℚ) = (τ : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₁' i₁) ha' hc3
      have e2 : (a'' : AlgebraicClosure ℚ) = (Dt.u₀ i : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₁ i₁) ha'' hc1
      rw [hrB'] at ha'v
      have e3 : red a' = red a'' := eq_of_ord_sub_pos v ha'v ha''v
      rw [← Subtype.ext e1, ← Subtype.ext e2, e3]
    · fin_cases j
      · exact exists_value_red_eq
          (P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst Qpp (by rw [hQr]; exact haff))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₁ i₁) haff
              exact ⟨b, hb, by rw [hQr]; exact hbv⟩)
          (hc2 0)
      · exact exists_value_red_eq
          (P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Qpp (by rw [hsndQ]; exact haff'))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₁ i₁) (by rw [hsndB]; exact haff')
              exact ⟨b, hb, by rw [hsndQ]; rw [hsndB] at hbv; exact hbv⟩)
          (hc2 1)

set_option maxHeartbeats 6400000 in

theorem point_snd (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {T₂ : Finset (Place k ↥(modularFunctionFieldC k N))} (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j)) (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A)
    (Pt : IncidenceSystem.Var (d₁ + d₂) 2 m' → A)
    (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0)
    (i₂ : Fin d₂) (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (τ : A)
    (htri : IsSndTriple (q := q) (P.reduceSnd (Q₂ i₂)) (red (Dt.u₀ (finSumFinEquiv (Sum.inr i₂)))) z y₁ y₂)
    (hb : ∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.G (finSumFinEquiv (Sum.inr i₂)) j) = 0)
    (hvars : (some 1 : Option (Fin 2)) ∉ (Dt.G (finSumFinEquiv (Sum.inr i₂)) 0).vars)
    (hc1 : 0 < (Q₂ i₂).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ (finSumFinEquiv (Sum.inr i₂)) : AlgebraicClosure ℚ)))
    (hc2 : ∀ j : Fin 2, 0 < (Q₂ i₂).ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.w₀ (finSumFinEquiv (Sum.inr i₂)) j 0 : AlgebraicClosure ℚ)))
    (hc3 : 0 < (Q₂' i₂).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)))
    (hd : ∀ kk, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.p kk (finSumFinEquiv (Sum.inr i₂)))
      = Option.elim kk 1 (fun kk => h kk.succ) * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ (finSumFinEquiv (Sum.inr i₂)) : AlgebraicClosure ℚ)) ^ m'
        * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) * evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (Dt.s kk (finSumFinEquiv (Sum.inr i₂))))
    (he : ∀ kk, red (Dt.sVal Dt.centre kk (finSumFinEquiv (Sum.inr i₂))) ≠ 0)
    (hf : ∀ j, red (Dt.dG Dt.centre (finSumFinEquiv (Sum.inr i₂)) j) ≠ 0) :
    ∃ Qpp : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Qpp ∧ P.reduceSnd Qpp = P.reduceSnd (Q₂ i₂) ∧
      (((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₂' i₂) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₂ i₂) (1 : ℤ)) Qpp) := by
  classical
  set i : Fin (d₁ + d₂) := finSumFinEquiv (Sum.inr i₂) with hidef
  set v := P.reduceSnd (Q₂ i₂) with hvdef
  have haff : IsAffineGeomPlace k N v := hT₂aff v ((hT₂ v).mpr ⟨i₂, rfl⟩)
  have haff' : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := isAffineGeomPlace_frob haff

  obtain ⟨Qpp, hQs, hQr, hQz, hQoth⟩ :=
    disc_snd P hqN R hR (hQ₂ i₂) haff htri (Pt (IncidenceSystem.Var.u i)) (hPt (IncidenceSystem.Var.u i))
  obtain ⟨Qc, hQcs, hQcr, hQcz, hQcoth⟩ :=
    disc_snd P hqN R hR (hQ₂ i₂) haff htri (Dt.u₀ i) (by rw [sub_self]; exact zero_mem _)

  have hBc : Q₂ i₂ = Qc := by
    by_contra hne
    have := hQcoth (Q₂ i₂) (hQ₂ i₂) rfl hne
    rw [this] at hc1
    exact lt_irrefl _ hc1

  have hQrat : Qpp.IsRational :=
    (Place.isRational_iff_deg_eq_one Qpp).mpr (deg_eq_one_modularFunctionFieldBar (N * q) Qpp)

  have hrB' : P.reduceSnd (Q₂' i₂) = v := hred₂ i₂
  have hfstQ : P.reduceFst Qpp = frobOnPlacesGeomLevel k N data hKr v := by rw [hQs.1, hQr]
  have hfstB : P.reduceFst (Q₂ i₂) = frobOnPlacesGeomLevel k N data hKr v := (hQ₂ i₂).1

  have key : ∀ (hτ : τ - Dt.u₀ i ∈ IsLocalRing.maximalIdeal A)
      (hvalQ : ∀ j : Fin 2, ∃ b : A, 0 < Qpp.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)) ∧
        red b = red (Dt.w₀ i j 0)),
      ((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₂' i₂) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₂ i₂) (1 : ℤ)) Qpp := by
    intro hτ hvalQ
    obtain ⟨Qt, hQts, hQtr, hQtz, hQtoth⟩ := disc_snd P hqN R hR (hQ₂ i₂) haff htri τ hτ
    have hBt : Q₂' i₂ = Qt := by
      by_contra hne
      have := hQtoth (Q₂' i₂) (hQ₂' i₂) hrB' hne
      rw [this] at hc3
      exact lt_irrefl _ hc3

    have hordu : Qpp.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) = (Finsupp.single (Q₂ i₂) (1 : ℤ)) Qpp := by
      rw [Finsupp.single_apply, hBc]
      by_cases hq : Qc = Qpp
      · rw [if_pos hq, ← hq]; exact hQcz
      · rw [if_neg hq]; exact hQcoth Qpp hQs hQr (Ne.symm hq)
    have hordτ : Qpp.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) = (Finsupp.single (Q₂' i₂) (1 : ℤ)) Qpp := by
      rw [Finsupp.single_apply, hBt]
      by_cases hq : Qt = Qpp
      · rw [if_pos hq, ← hq]; exact hQtz
      · rw [if_neg hq]; exact hQtoth Qpp hQs hQr (Ne.symm hq)

    set f : ↥(modularFunctionFieldBar (N * q)) := 1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ with hfdef
    have hf0 : f ≠ 0 := one_add_sum_ne_zero R (fun k' => h k'.succ) (fun k' => hh₁ _) (fun k' => Pt (IncidenceSystem.Var.c k'))
      (fun k' => by simpa [IncidenceSystem.Data.centre] using hPt (IncidenceSystem.Var.c k'))
    have hzu0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have h1 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((Dt.u₀ i : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)) := by
        rw [map_sub, ← sub_eq_zero.mp h0]
      have h2 := hQz
      rw [h1] at h2
      by_cases hc : (Dt.u₀ i : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ) = 0
      · rw [hc, map_zero, Place.ord_zero] at h2; exact zero_ne_one h2
      · rw [(Qpp.hasValue_algebraMap _).ord_eq_zero hc] at h2; exact zero_ne_one h2
    have hzτ0 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have h1 : z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((τ : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ)) := by
        rw [map_sub, ← sub_eq_zero.mp h0]
      have h2 := hQz
      rw [h1] at h2
      by_cases hc : (τ : AlgebraicClosure ℚ) - (Pt (IncidenceSystem.Var.u i) : AlgebraicClosure ℚ) = 0
      · rw [hc, map_zero, Place.ord_zero] at h2; exact zero_ne_one h2
      · rw [(Qpp.hasValue_algebraMap _).ord_eq_zero hc] at h2; exact zero_ne_one h2

    have hcomb : (∑ kk, (Option.elim kk (1 : AlgebraicClosure ℚ) fun k' => (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ))
        • (Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ)) = f := by
      rw [Fintype.sum_option, hfdef]
      simp only [Option.elim, one_smul]
      congr 1
    have hg0 : (∑ kk, (Option.elim kk (1 : AlgebraicClosure ℚ) fun k' => (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ))
        • (Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ))
        * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Dt.u₀ i : AlgebraicClosure ℚ)) ^ m' * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ≠ 0 := by
      rw [hcomb]; exact mul_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hzu0)) hzτ0
    have hcore := point_core (L := AlgebraicClosure ℚ) red (red_ker_iff R) Dt i z y₁ y₂ τ (fun kk => Option.elim kk (1 : ↥(modularFunctionFieldBar (N * q))) fun kk => h kk.succ)
      hvars (fun j => by rw [← evalBar_eq_aeval]; exact hb j)
      (fun kk => by rw [← evalBar_eq_aeval, ← evalBar_eq_aeval]; exact hd kk) he hf Pt hPt hroot Qpp hQrat hQz hvalQ hg0
    rw [hcomb, Place.ord_mul Qpp (mul_ne_zero hf0 (pow_ne_zero _ hzu0)) hzτ0,
      Place.ord_mul Qpp hf0 (pow_ne_zero _ hzu0), ord_pow_eq Qpp hzu0, hordu, hordτ] at hcore
    linarith
  refine ⟨Qpp, hQs, hQr, ?_⟩

  rcases htri with ⟨hz, hy1, hy2, -⟩ | ⟨hz, hy1, hy2, -⟩
  · subst hz hy1 hy2

    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) (by rw [hrB']; exact haff)
    obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
    refine key ?_ fun j => ?_
    · rw [← red_ker_iff R, map_sub, sub_eq_zero]
      have e1 : (a' : AlgebraicClosure ℚ) = (τ : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₂' i₂) ha' hc3
      have e2 : (a'' : AlgebraicClosure ℚ) = (Dt.u₀ i : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₂ i₂) ha'' hc1
      rw [hrB'] at ha'v
      have e3 : red a' = red a'' := eq_of_ord_sub_pos v ha'v ha''v
      rw [← Subtype.ext e1, ← Subtype.ext e2, e3]
    · fin_cases j
      · exact exists_value_red_eq
          (P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Qpp (by rw [hQr]; exact haff))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
              exact ⟨b, hb, by rw [hQr]; exact hbv⟩)
          (hc2 0)
      · exact exists_value_red_eq
          (P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst Qpp (by rw [hfstQ]; exact haff'))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₂ i₂) (by rw [hfstB]; exact haff')
              exact ⟨b, hb, by rw [hfstQ]; rw [hfstB] at hbv; exact hbv⟩)
          (hc2 1)
  · subst hz hy1 hy2

    obtain ⟨a', ha', ha'v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂' i₂) (by rw [hrB']; exact haff)
    obtain ⟨a'', ha'', ha''v⟩ := P.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
    refine key ?_ fun j => ?_
    · rw [← red_ker_iff R, map_sub, sub_eq_zero]
      have e1 : (a' : AlgebraicClosure ℚ) = (τ : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₂' i₂) ha' hc3
      have e2 : (a'' : AlgebraicClosure ℚ) = (Dt.u₀ i : AlgebraicClosure ℚ) := eq_of_ord_sub_pos (Q₂ i₂) ha'' hc1
      rw [hrB'] at ha'v
      have e3 : red a' = red a'' := eq_of_ord_sub_pos v ha'v ha''v
      rw [← Subtype.ext e1, ← Subtype.ext e2, e3]
    · fin_cases j
      · exact exists_value_red_eq
          (P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd Qpp (by rw [hQr]; exact haff))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd (Q₂ i₂) haff
              exact ⟨b, hb, by rw [hQr]; exact hbv⟩)
          (hc2 0)
      · exact exists_value_red_eq
          (P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst Qpp (by rw [hfstQ]; exact haff'))
          (by obtain ⟨b, hb, hbv⟩ := P.exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst (Q₂ i₂) (by rw [hfstB]; exact haff')
              exact ⟨b, hb, by rw [hfstQ]; rw [hfstB] at hbv; exact hbv⟩)
          (hc2 1)

end Global

section Main
open MvPolynomial

theorem sum_single_apply_of_injective {α ι : Type*} [Fintype ι] [DecidableEq α] (v : ι → α)
    (hv : Function.Injective v) (n : ℤ) (a : α) :
    (∑ i, Finsupp.single (v i) n) a = if ∃ i, v i = a then n else 0 := by
  classical
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j _ hj
      rw [if_neg]
      intro hji
      exact hj (hv (hji.trans hi.symm))
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · push_neg at h
    exact Finset.sum_eq_zero fun i _ => if_neg (h i)

theorem exists_eq_of_sum_single_apply_ne_zero {α ι : Type*} [Fintype ι] (v : ι → α) (n : ℤ) (a : α)
    (h : (∑ i, Finsupp.single (v i) n) a ≠ 0) : ∃ i, v i = a := by
  classical
  by_contra hne
  push_neg at hne
  apply h
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (hne i)]

theorem not_isStrictFst_of_isStrictSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hS : P.IsStrictSnd W) : ¬ P.IsStrictFst W := by
  intro hF
  apply hF.2
  rw [hF.1]
  exact hS.1.symm

theorem roots_main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh0 : h 0 = 1)
    (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (hhL : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
        + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l))
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A) (hrep : P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt)
    (Pt : IncidenceSystem.Var (d₁ + d₂) 2 m' → A)
    (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0) :
    ∃ (Q₁'' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂'' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁'' i)) ∧ (∀ j, P.IsStrictSnd (Q₂'' j)) ∧
      (∀ i, P.reduceFst (Q₁'' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂'' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V.ord f =
            ((m' + 1 : ℕ) : ℤ) * ((∑ i, Finsupp.single (Q₁'' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂'' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V) := by
  classical
  obtain ⟨hpts, -⟩ := hrep
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)

  have H1 : ∀ i₁ : Fin d₁, ∃ Qpp : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Qpp ∧ P.reduceFst Qpp = P.reduceFst (Q₁ i₁) ∧
      (((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₁' i₁) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₁ i₁) (1 : ℤ)) Qpp) := by
    intro i₁
    obtain ⟨z, y₁, y₂, τ, ha, hb, hvars, hc1, hc2, hc3, hd, -, -, -, he, hf⟩ := hpts (finSumFinEquiv (Sum.inl i₁))
    simp only [Equiv.symm_apply_apply, Sum.elim_inl] at ha hc1 hc2 hc3
    exact point_fst P hqN R hR Q₁ Q₂ Q₁' Q₂' hT₁ hT₁aff hQ₁ hQ₁' hred₁ m' h hh₁ Dt Pt hPt hroot i₁ z y₁ y₂ τ
      ha hb hvars hc1 hc2 hc3 hd he hf
  have H2 : ∀ i₂ : Fin d₂, ∃ Qpp : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Qpp ∧ P.reduceSnd Qpp = P.reduceSnd (Q₂ i₂) ∧
      (((m' + 1 : ℕ) : ℤ) ≤ Qpp.ord (1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ)
        + (Finsupp.single (Q₂' i₂) (1 : ℤ)) Qpp + (m' : ℤ) * (Finsupp.single (Q₂ i₂) (1 : ℤ)) Qpp) := by
    intro i₂
    obtain ⟨z, y₁, y₂, τ, ha, hb, hvars, hc1, hc2, hc3, hd, -, -, -, he, hf⟩ := hpts (finSumFinEquiv (Sum.inr i₂))
    simp only [Equiv.symm_apply_apply, Sum.elim_inr] at ha hc1 hc2 hc3
    exact point_snd P hqN R hR Q₁ Q₂ Q₁' Q₂' hT₂ hT₂aff hQ₂ hQ₂' hred₂ m' h hh₁ Dt Pt hPt hroot i₂ z y₁ y₂ τ
      ha hb hvars hc1 hc2 hc3 hd he hf
  choose Qf hQf using H1
  choose Qs hQs using H2
  refine ⟨Qf, Qs, fun i => (hQf i).1, fun j => (hQs j).1, fun i => (hQf i).2.1, fun j => (hQs j).2.1, ?_⟩
  set f : ↥(modularFunctionFieldBar (N * q)) := 1 + ∑ k', algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (Pt (IncidenceSystem.Var.c k') : AlgebraicClosure ℚ) * h k'.succ with hfdef
  have hf0 : f ≠ 0 := one_add_sum_ne_zero R (fun k' => h k'.succ) (fun k' => hh₁ _) (fun k' => Pt (IncidenceSystem.Var.c k'))
    (fun k' => by simpa [IncidenceSystem.Data.centre] using hPt (IncidenceSystem.Var.c k'))
  refine ⟨f, hf0, ?_⟩

  set E' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE'
  set E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₀
  set E'' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ i, Finsupp.single (Qf i) (1 : ℤ) + ∑ j, Finsupp.single (Qs j) (1 : ℤ) with hE''
  set E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := (((m' + 1 : ℕ) : ℤ)) • E'' - E' - (m' : ℤ) • E₀ with hEdef
  have hEapp : ∀ V, E V = ((m' + 1 : ℕ) : ℤ) * E'' V - E' V - (m' : ℤ) * E₀ V := fun V => by
    rw [hEdef, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  suffices hmain : ∀ V, V.ord f = E V by
    intro V; rw [hmain V, hEapp]

  have hdeg1 : ∀ (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), w.deg = 1 := fun w => deg_eq_one_modularFunctionFieldBar (N * q) w
  have hsumdeg : ∀ {ι : Type} [Fintype ι] (g' : ι → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      Divisor.degree (∑ i, Finsupp.single (g' i) (1 : ℤ)) = Fintype.card ι := by
    intro ι _ g'
    rw [map_sum]
    simp only [Divisor.degree_single, hdeg1, Nat.cast_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hEdeg : E.degree = 0 := by
    rw [hEdef, map_sub, map_sub, map_zsmul, map_zsmul, hE'', hE', hE₀, map_add, map_add, map_add,
      hsumdeg, hsumdeg, hsumdeg, hsumdeg, hsumdeg, hsumdeg, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  refine ord_eq_of_forall_le_of_degree_eq_zero hdeg1 hf0 E hEdeg fun V => ?_

  have hglob : -(E' V + (m' : ℤ) * E₀ V) ≤ V.ord f := by
    set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := E' + (m' : ℤ) • E₀ with hD
    have hDapp : ∀ W, D W = E' W + (m' : ℤ) * E₀ W := fun W => by
      rw [hD, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have hmem : ∀ l, h l ∈ riemannRochSpace D := fun l =>
      mem_riemannRochSpace_iff.mpr fun W => Or.inr (by rw [hDapp]; exact hhL l W)
    have hfmem : f ∈ riemannRochSpace D := by
      rw [hfdef]
      refine add_mem ?_ (sum_mem fun k' _ => ?_)
      · rw [← hh0]; exact hmem 0
      · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hmem _)
    rcases (mem_riemannRochSpace_iff.mp hfmem) V with h0 | hb
    · exact absurd h0 hf0
    · rw [hDapp] at hb; exact hb

  have hnn : ∀ {ι : Type} [Fintype ι] (g' : ι → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), 0 ≤ (∑ i, Finsupp.single (g' i) (1 : ℤ)) W := by
    intro ι _ g' W
    rw [Finsupp.coe_finset_sum, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => by rw [Finsupp.single_apply]; split_ifs <;> omega
  have hge : ∀ {ι : Type} [Fintype ι] (g' : ι → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (i : ι) (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      Finsupp.single (g' i) (1 : ℤ) V' ≤ (∑ i', Finsupp.single (g' i') (1 : ℤ)) V' := by
    intro ι _ g' i V'
    rw [Finsupp.coe_finset_sum, Finset.sum_apply]
    have hnn' : ∀ i' ∈ (Finset.univ : Finset ι), 0 ≤ (Finsupp.single (g' i') (1 : ℤ)) V' := fun i' _ => by
      rw [Finsupp.single_apply]; split_ifs <;> omega
    exact Finset.single_le_sum hnn' (Finset.mem_univ i)

  have hQf_inj : Function.Injective Qf := fun i i' hii => hinj₁ (by
    show P.reduceFst (Q₁ i) = P.reduceFst (Q₁ i')
    rw [← (hQf i).2.1, ← (hQf i').2.1, hii])
  have hQs_inj : Function.Injective Qs := fun j j' hjj => hinj₂ (by
    show P.reduceSnd (Q₂ j) = P.reduceSnd (Q₂ j')
    rw [← (hQs j).2.1, ← (hQs j').2.1, hjj])
  have hexcl : ∀ i j, Qf i ≠ Qs j := fun i j h' =>
    not_isStrictFst_of_isStrictSnd P (hQs j).1 (h' ▸ (hQf i).1)
  rw [hEapp]
  by_cases hV1 : ∃ i, Qf i = V
  · obtain ⟨i, rfl⟩ := hV1
    have hE''V : E'' (Qf i) = 1 := by
      rw [hE'', Finsupp.add_apply, sum_single_apply_of_injective Qf hQf_inj, if_pos ⟨i, rfl⟩]
      have : (∑ j, Finsupp.single (Qs j) (1 : ℤ)) (Qf i) = 0 := by
        by_contra hz
        obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz
        exact hexcl i j hj.symm
      rw [this, add_zero]
    have hb := (hQf i).2.2
    have h1 : Finsupp.single (Q₁' i) (1 : ℤ) (Qf i) ≤ E' (Qf i) := by
      rw [hE', Finsupp.add_apply]; linarith [hge Q₁' i (Qf i), hnn Q₂' (Qf i)]
    have h2 : Finsupp.single (Q₁ i) (1 : ℤ) (Qf i) ≤ E₀ (Qf i) := by
      rw [hE₀, Finsupp.add_apply]; linarith [hge Q₁ i (Qf i), hnn Q₂ (Qf i)]
    rw [hE''V]
    have hm0 : (0 : ℤ) ≤ m' := Nat.cast_nonneg _
    nlinarith
  by_cases hV2 : ∃ j, Qs j = V
  · obtain ⟨j, rfl⟩ := hV2
    have hE''V : E'' (Qs j) = 1 := by
      rw [hE'', Finsupp.add_apply, sum_single_apply_of_injective Qs hQs_inj, if_pos ⟨j, rfl⟩]
      have : (∑ i, Finsupp.single (Qf i) (1 : ℤ)) (Qs j) = 0 := by
        by_contra hz
        obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero _ _ _ hz
        exact hexcl i j hi
      rw [this, zero_add]
    have hb := (hQs j).2.2
    have h1 : Finsupp.single (Q₂' j) (1 : ℤ) (Qs j) ≤ E' (Qs j) := by
      rw [hE', Finsupp.add_apply]; linarith [hge Q₂' j (Qs j), hnn Q₁' (Qs j)]
    have h2 : Finsupp.single (Q₂ j) (1 : ℤ) (Qs j) ≤ E₀ (Qs j) := by
      rw [hE₀, Finsupp.add_apply]; linarith [hge Q₂ j (Qs j), hnn Q₁ (Qs j)]
    rw [hE''V]
    have hm0 : (0 : ℤ) ≤ m' := Nat.cast_nonneg _
    nlinarith

  have hE''V : E'' V = 0 := by
    rw [hE'', Finsupp.add_apply]
    have h1 : (∑ i, Finsupp.single (Qf i) (1 : ℤ)) V = 0 := by
      by_contra hz; exact hV1 (exists_eq_of_sum_single_apply_ne_zero _ _ _ hz)
    have h2 : (∑ j, Finsupp.single (Qs j) (1 : ℤ)) V = 0 := by
      by_contra hz; exact hV2 (exists_eq_of_sum_single_apply_ne_zero _ _ _ hz)
    rw [h1, h2, add_zero]
  rw [hE''V, mul_zero, zero_sub]
  linarith

end Main

end Roots

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh0 : h 0 = 1)
    (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (hhL : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
        + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l))
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A) (hrep : P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt)
    (Pt : IncidenceSystem.Var (d₁ + d₂) 2 m' → A)
    (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0) :
    ∃ (Q₁'' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂'' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁'' i)) ∧ (∀ j, P.IsStrictSnd (Q₂'' j)) ∧
      (∀ i, P.reduceFst (Q₁'' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂'' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V.ord f =
            ((m' + 1 : ℕ) : ℤ) * ((∑ i, Finsupp.single (Q₁'' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂'' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V) :=
  Roots.roots_main hqN hW R hR hRL hNV hO Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hT₁sm hT₂sm hT₁gen hT₂gen hgp₁ hgp₂ hdeg Q₁' Q₂' hQ₁' hQ₂' hred₁ hred₂ Qs hQs hQs' m' h hh0 hh₁ hhL Dt hrep Pt hPt hroot

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero (solution)
