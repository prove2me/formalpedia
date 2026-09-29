-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/475ada07-36cd-5210-af3e-9d03dd932422

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeAlphaBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

noncomputable section

namespace Ws18DecompEquiv

theorem restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

theorem liesOverPrime_of_red {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) : A.LiesOverPrime q := by
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  have hq : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
  rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 : red ((q : ℕ) : ↥A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  obtain ⟨u, hu'⟩ := hu
  have : red (u * u⁻¹ : (↥A)ˣ) = 1 := by rw [mul_inv_cancel, Units.val_one, map_one]
  rw [Units.val_mul, map_mul, hu', h0, zero_mul] at this
  exact zero_ne_one this

theorem exists_pow_mul_of_isFrobeniusAt_pow {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {φ₀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ₀ : A.IsFrobeniusAt φ₀ q) {n : ℕ}
    (hσ : A.IsFrobeniusAt σ (q ^ n)) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ ∧ σ = φ₀ ^ n * τ := by
  have hφD : φ₀ ∈ A.decompositionSubgroup ℚ := hφ₀.mem_decompositionSubgroup
  have hσD : σ ∈ A.decompositionSubgroup ℚ := hσ.mem_decompositionSubgroup

  set Φ : ↥(A.decompositionSubgroup ℚ) := ⟨φ₀, hφD⟩ with hΦ
  set Sg : ↥(A.decompositionSubgroup ℚ) := ⟨σ, hσD⟩ with hSg
  have hΦpow : ∀ (m : ℕ) (x : IsLocalRing.ResidueField ↥A), (Φ ^ m) • x = x ^ (q ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih => intro x; rw [pow_succ, mul_smul, hΦ, hφ₀.smul_residue_eq, ← hΦ, ih, ← pow_mul, ← pow_succ']
  set T : ↥(A.decompositionSubgroup ℚ) := (Φ ^ n)⁻¹ * Sg with hT
  have hTfix : ∀ x : IsLocalRing.ResidueField ↥A, T • x = x := by
    intro x
    rw [hT, mul_smul, hSg, hσ.smul_residue_eq, inv_smul_eq_iff, hΦpow]
  have hTker : T ∈ A.inertiaSubgroup ℚ := by
    show T ∈ MonoidHom.ker _
    rw [MonoidHom.mem_ker]
    ext x
    exact hTfix x
  refine ⟨(T : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ⟨T, hTker, rfl⟩, ?_⟩
  have : Sg = Φ ^ n * T := by rw [hT, mul_inv_cancel_left]
  have h := congrArg (fun z : ↥(A.decompositionSubgroup ℚ) => (z : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) this
  simpa [hSg, hΦ] using h

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem frobOnPlacesGeomLevel_iterate_eq_arithFrobC_pow_smul [IsAlgClosed k]
    (m : ℕ) (w : Place k (modularFunctionFieldC k N)) :
    (frobOnPlacesGeomLevel k N data hKr)^[m] w = (arithFrobC q k N) ^ m • w := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul,
        ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr]

theorem sp_arithmeticGalois_smul_of_isFrobeniusAt_pow [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ) (hσ : A.IsFrobeniusAt σ (q ^ n))
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    P.sp (arithmeticGalois (modularFunctionFieldFull N) σ • U) = (arithFrobC q k N) ^ n • P.sp U := by
  obtain ⟨φ₀, hφ₀⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime (Fact.out : q.Prime) A
    (liesOverPrime_of_red (k := k) red)
  obtain ⟨τ, hτ, rfl⟩ := exists_pow_mul_of_isFrobeniusAt_pow hφ₀ hσ
  rw [map_mul, map_pow, mul_smul]

  have hiter : ∀ (m : ℕ) (U' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      P.sp ((arithmeticGalois (modularFunctionFieldFull N) φ₀) ^ m • U') = (frobOnPlacesGeomLevel k N data hKr)^[m] (P.sp U') := by
    intro m
    induction m with
    | zero => intro U'; simp
    | succ m ih =>
        intro U'
        rw [pow_succ', mul_smul, P.d6_frobenius φ₀ hφ₀, ih, Function.iterate_succ_apply']
  rw [hiter, P.d6_inertia τ hτ, frobOnPlacesGeomLevel_iterate_eq_arithFrobC_pow_smul]

end Ws18DecompEquiv

open Ws18DecompEquiv in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ) (hσ : A.IsFrobeniusAt σ (q ^ n))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceFst V ∧
    P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceSnd V := by
  constructor
  · show P.sp ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V).restrictAlong
        (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = _
    rw [restrictAlong_semilinearAut_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
        (g := arithmeticGalois (modularFunctionFieldFull N) σ)
        (g' := arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
        (fun x => arithmeticGalois_smul_heckeAlphaBar N q σ x) V]
    exact sp_arithmeticGalois_smul_of_isFrobeniusAt_pow P σ n hσ _
  · show P.sp ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V).restrictAlong
        (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = _
    rw [restrictAlong_semilinearAut_smul (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
        (g := arithmeticGalois (modularFunctionFieldFull N) σ)
        (g' := arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
        (fun x => arithmeticGalois_smul_heckeBetaBar N q σ x) V]
    exact sp_arithmeticGalois_smul_of_isFrobeniusAt_pow P σ n hσ _

end

end S_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow (solution)
