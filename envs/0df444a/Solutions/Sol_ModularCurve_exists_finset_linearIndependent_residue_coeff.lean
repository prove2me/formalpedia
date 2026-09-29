-- Prove2me | solution 1 for ModularCurve.exists_finset_linearIndependent_residue_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c054ca2d-3c0d-5a98-bcf8-0f75c3fc4fd0

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_linearIndependent_residue_coeff

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_finset_linearIndependent_residue_coeff.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar"
namespace ResidueIndependenceAux
p2m_open "ModularCurve"

theorem exists_det_ne_zero_of_linearIndependent {K : Type*} [Field K] {ι : Type*} :
    ∀ {r : ℕ} (v : Fin r → ι → K), LinearIndependent K v →
      ∃ J : Fin r → ι, (Matrix.of fun i j => v i (J j)).det ≠ 0
  | 0, v, _ => ⟨Fin.elim0, by simp [Matrix.det_fin_zero]⟩
  | (r + 1), v, hv => by
    classical

    have htail : LinearIndependent K (fun i : Fin r => v i.succ) := hv.comp Fin.succ (Fin.succ_injective _)
    obtain ⟨J', hJ'⟩ := exists_det_ne_zero_of_linearIndependent (fun i : Fin r => v i.succ) htail

    set c : Fin (r + 1) → K := fun i =>
      (-1) ^ (i : ℕ) * (Matrix.of fun a b => v (i.succAbove a) (J' b)).det with hc
    have hc0 : c 0 ≠ 0 := by
      rw [hc]
      simp only [Fin.val_zero, pow_zero, one_mul]
      simpa [Fin.succAbove_zero] using hJ'

    by_contra hall
    push Not at hall
    have hexp : ∀ t : ι, (Matrix.of fun i j => v i ((Fin.cases t J' : Fin (r + 1) → ι) j)).det
        = ∑ i, c i * v i t := by
      intro t
      rw [Matrix.det_succ_column_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc]
      simp only [Matrix.of_apply, Fin.cases_zero, Matrix.submatrix, Fin.cases_succ]
      ring
    have hsum : ∑ i, c i • v i = 0 := by
      funext t
      rw [Finset.sum_apply, Pi.zero_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hexp t]
      exact hall (Fin.cases t J')
    exact hc0 (Fintype.linearIndependent_iff.mp hv c hsum 0)

theorem exists_int_poly_aeval_eq_zero_coeff_zero_ne (μ : AlgebraicClosure ℚ) (hμ : μ ≠ 0) :
    ∃ q : ℤ[X], aeval μ q = 0 ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic μ
  set q₀ : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p with hq₀
  have hq₀0 : q₀ ≠ 0 := fun h => hp0 ((IsFractionRing.integerNormalization_eq_zero_iff (p := p)).mp h)
  have hq₀μ : aeval μ q₀ = 0 := IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) p hp

  suffices key : ∀ (n : ℕ) (q : ℤ[X]), q.natDegree ≤ n → q ≠ 0 → aeval μ q = 0 →
      ∃ q' : ℤ[X], aeval μ q' = 0 ∧ q'.coeff 0 ≠ 0 from key _ q₀ le_rfl hq₀0 hq₀μ
  intro n
  induction n with
  | zero =>
    intro q hdeg hq0 hqμ
    refine ⟨q, hqμ, fun h0 => hq0 ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, h0, map_zero]
  | succ n ih =>
    intro q hdeg hq0 hqμ
    by_cases h0 : q.coeff 0 = 0
    ·
      have hq : X * q.divX = q := by
        have := Polynomial.X_mul_divX_add q
        rwa [h0, map_zero, add_zero] at this
      have hdx0 : q.divX ≠ 0 := by
        intro h; apply hq0; rw [← hq, h, mul_zero]
      have hdeg' : q.divX.natDegree ≤ n := by
        have := Polynomial.natDegree_divX_eq_natDegree_tsub_one (p := q)
        omega
      have hμ' : aeval μ q.divX = 0 := by
        have : aeval μ (X * q.divX) = 0 := by rw [hq]; exact hqμ
        rw [map_mul, aeval_X] at this
        exact (mul_eq_zero.mp this).resolve_left hμ
      exact ih q.divX hdeg' hdx0 hμ'
    · exact ⟨q, hqμ, h0⟩

theorem isUnit_of_aeval_eq_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) (q : ℤ[X]) (hq0 : ¬ ℓ ∣ (q.coeff 0).natAbs)
    (μ : A) (hμ : aeval (μ : AlgebraicClosure ℚ) q = 0) : IsUnit μ := by
  by_contra hmax
  have hmax' : μ ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal μ).mpr (mem_nonunits_iff.mpr hmax)

  have hrel : μ * aeval μ q.divX + (q.coeff 0 : A) = 0 := by
    apply Subtype.ext
    have h1 := congrArg (aeval (μ : AlgebraicClosure ℚ)) (Polynomial.X_mul_divX_add q)
    rw [map_add, map_mul, aeval_X, aeval_C, hμ] at h1

    have h2 : (aeval (μ : AlgebraicClosure ℚ) q.divX) = ((aeval μ q.divX : A) : AlgebraicClosure ℚ) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def,
        show ((Polynomial.eval₂ (algebraMap ℤ A) μ q.divX : A) : AlgebraicClosure ℚ)
          = A.subtype (Polynomial.eval₂ (algebraMap ℤ A) μ q.divX) from rfl,
        Polynomial.hom_eval₂, RingHom.ext_int (A.subtype.comp (algebraMap ℤ A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
      rfl
    rw [h2] at h1
    push_cast
    simpa using h1
  have hc0 : ((q.coeff 0 : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    have : ((q.coeff 0 : ℤ) : A) = -(μ * aeval μ q.divX) := eq_neg_of_add_eq_zero_right hrel
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ hmax')

  have hℓA : ((ℓ : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    have hlt : A.valuation ((ℓ : AlgebraicClosure ℚ)) < 1 := (A.mem_nonunits_iff).mp hA
    have : (((ℓ : ℤ) : A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by push_cast; rfl
    exact (A.valuation_lt_one_iff _).mpr (by rw [this]; exact hlt)

  have hcop : IsCoprime (q.coeff 0) (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hq0
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (1 : A) = (a : A) * ((q.coeff 0 : ℤ) : A) + (b : A) * ((ℓ : ℤ) : A) := by exact_mod_cast hab.symm
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc0) (Ideal.mul_mem_left _ _ hℓA)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

end ModularCurve.ResidueIndependenceAux

open ModularCurve.ResidueIndependenceAux in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : LinearIndependent (AlgebraicClosure ℚ) s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ hint : ∀ (i : Fin r) (k : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) ∈ A,
          LinearIndependent (IsLocalRing.ResidueField A)
            (fun i : Fin r => fun k : ℤ => IsLocalRing.residue A ⟨_, hint i k⟩) := by
  classical

  set f : Fin r → ℤ → AlgebraicClosure ℚ := fun i k => (s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k with hf

  let φ : modularFunctionFieldBar N →ₗ[AlgebraicClosure ℚ] (ℤ → AlgebraicClosure ℚ) :=
    { toFun := fun x k => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff k
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [IntermediateField.coe_smul, Algebra.smul_def]
        have halg : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c = HahnSeries.single 0 c := by
          rw [show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c
              = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (PowerSeries.C c) from rfl,
            HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
        rw [halg, HahnSeries.coeff_single_zero_mul] }
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply HahnSeries.ext
    funext k
    have := congrFun hx k
    simp at this
    exact this
  have hf_li : LinearIndependent (AlgebraicClosure ℚ) f := by
    have := hs.map' φ hφ
    exact this
  obtain ⟨J, hJ⟩ := exists_det_ne_zero_of_linearIndependent f hf_li
  set μ : AlgebraicClosure ℚ := (Matrix.of fun i j => f i (J j)).det with hμ
  obtain ⟨q, hqμ, hq0⟩ := exists_int_poly_aeval_eq_zero_coeff_zero_ne μ hJ
  refine ⟨(q.coeff 0).natAbs.primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro ℓ hℓ hℓS A hA hint
  have hℓdvd : ¬ ℓ ∣ (q.coeff 0).natAbs := fun hd =>
    hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hd, Int.natAbs_ne_zero.mpr hq0⟩)

  set M : Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ⟨f i (J j), hint i (J j)⟩ with hM
  have hMdet : ((M.det : A) : AlgebraicClosure ℚ) = μ := by
    rw [hμ, show ((M.det : A) : AlgebraicClosure ℚ) = A.subtype M.det from rfl, RingHom.map_det]
    rfl
  have hunit : IsUnit M.det := isUnit_of_aeval_eq_zero hℓ hA q hℓdvd M.det (by rw [hMdet]; exact hqμ)
  have hres : (M.map (IsLocalRing.residue A)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h0
    exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)) hunit

  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hres
  exact LinearIndependent.of_comp (LinearMap.funLeft (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A) J) hrows

end S_ModularCurve_exists_finset_linearIndependent_residue_coeff
end P2MW
export P2MW.S_ModularCurve_exists_finset_linearIndependent_residue_coeff (solution)
