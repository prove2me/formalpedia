-- Prove2me | solution 1 for LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fb4705e1-06f0-52af-b7a2-ab3776316ba1

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
set_option autoImplicit false

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section QuadraticRoots

variable {K : Type*} [Field K]

private theorem forall_quadratic_ne_zero_of_not_isSquare {t n₀ : K} (h : ¬ IsSquare (t ^ 2 - 4 * n₀)) (r : K) :
    r * r - t * r + n₀ ≠ 0 := by
  intro hr
  refine h ⟨2 * r - t, ?_⟩
  linear_combination (-4) * hr

private theorem ne_zero_of_not_isSquare {d : K} (h : ¬ IsSquare d) : d ≠ 0 := by
  rintro rfl
  exact h ⟨0, (mul_zero 0).symm⟩

private theorem forall_quadratic_ne_zero_of_scaling {t n₀ t' n' c : K} (ht : t = c * t')
    (hn : n₀ = c * c * n') (hroot : ∀ r : K, r * r - t * r + n₀ ≠ 0) (r : K) :
    r * r - t' * r + n' ≠ 0 := by
  intro h
  refine hroot (c * r) ?_
  rw [ht, hn]
  linear_combination c * c * h

end QuadraticRoots

section ValueGroup

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K] in

private theorem ringHom_map_units_inv (f : R →+* K) (u : Rˣ) : f ((u⁻¹ : Rˣ) : R) = (f (u : R))⁻¹ := by
  have hfu : f (u : R) * f ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact eq_inv_of_mul_eq_one_right hfu

private theorem exists_eq_zpow_mul_algebraMap_unit {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (a : ℤ) (u : Rˣ), x = algebraMap R K ϖ ^ a * algebraMap R K (u : R) := by
  have hinj := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq0
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  have hu' : algebraMap R K (u' : R) ≠ 0 := (map_ne_zero_iff _ hinj).mpr u'.ne_zero
  refine ⟨(m : ℤ) - m', u * u'⁻¹, ?_⟩
  rw [div_eq_iff hqK, zpow_natCast_sub_natCast₀ hϖK, Units.val_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
    ringHom_map_units_inv, div_eq_mul_inv]
  have h1 : (algebraMap R K ϖ ^ m')⁻¹ * algebraMap R K ϖ ^ m' = 1 := inv_mul_cancel₀ (pow_ne_zero _ hϖK)
  have h2 : (algebraMap R K (u' : R))⁻¹ * algebraMap R K (u' : R) = 1 := inv_mul_cancel₀ hu'
  calc algebraMap R K (u : R) * algebraMap R K ϖ ^ m
      = algebraMap R K ϖ ^ m * ((algebraMap R K ϖ ^ m')⁻¹ * algebraMap R K ϖ ^ m')
          * (algebraMap R K (u : R) * ((algebraMap R K (u' : R))⁻¹ * algebraMap R K (u' : R))) := by
        rw [h1, h2, mul_one, mul_one, mul_comm]
    _ = _ := by ring

private theorem exists_trace_det_scaling {ϖ : R} (hϖ : Irreducible ϖ) (t n₀ : K) (hn : n₀ ≠ 0) :
    ∃ (k : ℤ) (t₁ n₁ : R), t = algebraMap R K ϖ ^ k * algebraMap R K t₁ ∧
      n₀ = algebraMap R K ϖ ^ (2 * k) * algebraMap R K n₁ ∧ ¬ (ϖ ∣ t₁ ∧ ϖ ^ 2 ∣ n₁) := by
  have hinj := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hndvd : ∀ u : Rˣ, ¬ ϖ ∣ (u : R) := fun u h => hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)
  have hnsq : ∀ (u : Rˣ) (r : ℕ), r ≤ 1 → ¬ ϖ ^ 2 ∣ ϖ ^ r * (u : R) := by
    intro u r hr h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
    · rw [pow_zero, one_mul] at h
      exact hndvd u (dvd_trans (dvd_pow_self ϖ two_ne_zero) h)
    · rw [pow_one, pow_two] at h
      exact hndvd u ((mul_dvd_mul_iff_left hϖ.ne_zero).mp h)
  obtain ⟨a, u, hu⟩ := exists_eq_zpow_mul_algebraMap_unit hϖ hn
  have hr0 : 0 ≤ a - 2 * (a / 2) := by omega
  have hr1 : (a - 2 * (a / 2)).toNat ≤ 1 := by omega
  have hexp2 : 2 * (a / 2) + (a - 2 * (a / 2)) = a := by omega
  by_cases ht : t = 0
  · refine ⟨a / 2, 0, ϖ ^ (a - 2 * (a / 2)).toNat * u, ?_, ?_, fun h => hnsq u _ hr1 h.2⟩
    · rw [ht, map_zero, mul_zero]
    · rw [hu, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hr0, ← mul_assoc, ← zpow_add₀ hϖK, hexp2]
  · obtain ⟨b, u', hu'⟩ := exists_eq_zpow_mul_algebraMap_unit hϖ ht
    rcases le_or_gt b (a / 2) with hb | hb
    · have hnn : 0 ≤ a - 2 * b := by omega
      have hexp : 2 * b + (a - 2 * b) = a := by omega
      refine ⟨b, u', ϖ ^ (a - 2 * b).toNat * u, hu', ?_, fun h => hndvd u' h.1⟩
      rw [hu, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hnn, ← mul_assoc, ← zpow_add₀ hϖK, hexp]
    · have hnn : 0 ≤ b - a / 2 := by omega
      have hexp : a / 2 + (b - a / 2) = b := by omega
      refine ⟨a / 2, ϖ ^ (b - a / 2).toNat * u', ϖ ^ (a - 2 * (a / 2)).toNat * u, ?_, ?_,
        fun h => hnsq u _ hr1 h.2⟩
      · rw [hu', map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hnn, ← mul_assoc, ← zpow_add₀ hϖK, hexp]
      · rw [hu, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hr0, ← mul_assoc, ← zpow_add₀ hϖK, hexp2]

end ValueGroup

end LT.LatticeTree

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section ResidueTrichotomy

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem isUnit_of_not_uniformizer_dvd {ϖ : R} (hϖ : Irreducible ϖ) {x : R} (hx : ¬ ϖ ∣ x) : IsUnit x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (dvd_zero ϖ)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  cases m with
  | zero => rw [pow_zero, mul_one]; exact u.isUnit
  | succ m => exact absurd (dvd_mul_of_dvd_right (dvd_pow_self ϖ m.succ_ne_zero) _) hx

private theorem quadratic_residue_trichotomy {ϖ : R} (hϖ : Irreducible ϖ)
    (hH : ∀ t n a₀ : R, ϖ ∣ a₀ * a₀ - t * a₀ + n → ¬ ϖ ∣ 2 * a₀ - t → ∃ a : R, a * a - t * a + n = 0)
    (t₁ n₁ : R) (hroot : ∀ r : R, r * r - t₁ * r + n₁ ≠ 0) (hnorm : ¬ (ϖ ∣ t₁ ∧ ϖ ^ 2 ∣ n₁)) :
    (ϖ ∣ t₁ ∧ ∃ w : Rˣ, n₁ = ϖ * w) ∨
      (¬ ϖ ∣ n₁ ∧ ∀ r : R, ¬ ϖ ∣ r * r - t₁ * r + n₁) ∨
      (∃ a : R, ¬ ϖ ∣ a ∧ ϖ ∣ t₁ - 2 * a ∧ ϖ ∣ n₁ - a * a) := by
  by_cases hn : ϖ ∣ n₁
  · have ht : ϖ ∣ t₁ := by
      by_contra ht
      obtain ⟨a, ha⟩ := hH t₁ n₁ 0 (by simpa using hn) (by simpa using ht)
      exact hroot a ha
    refine Or.inl ⟨ht, ?_⟩
    obtain ⟨w, rfl⟩ := hn
    have hw : ¬ ϖ ∣ w := fun h => hnorm ⟨ht, by rw [pow_two]; exact mul_dvd_mul_left ϖ h⟩
    exact ⟨(isUnit_of_not_uniformizer_dvd hϖ hw).unit, by rw [IsUnit.unit_spec]⟩
  · by_cases hres : ∃ r : R, ϖ ∣ r * r - t₁ * r + n₁
    · obtain ⟨r₀, hr₀⟩ := hres
      have h2 : ϖ ∣ 2 * r₀ - t₁ := by
        by_contra h2
        obtain ⟨a, ha⟩ := hH t₁ n₁ r₀ hr₀ h2
        exact hroot a ha
      have h2' : ϖ ∣ t₁ - 2 * r₀ := by
        have e : t₁ - 2 * r₀ = -(2 * r₀ - t₁) := by ring
        rw [e]
        exact dvd_neg.mpr h2
      refine Or.inr (Or.inr ⟨r₀, fun hr => hn ?_, h2', ?_⟩)
      · have e : n₁ = (r₀ * r₀ - t₁ * r₀ + n₁) - r₀ * (r₀ - t₁) := by ring
        rw [e]
        exact dvd_sub hr₀ (dvd_mul_of_dvd_left hr _)
      · have e : n₁ - r₀ * r₀ = (r₀ * r₀ - t₁ * r₀ + n₁) + r₀ * (t₁ - 2 * r₀) := by ring
        rw [e]
        exact dvd_add hr₀ (dvd_mul_of_dvd_right h2' _)
    · exact Or.inr (Or.inl ⟨hn, fun r h => hres ⟨r, h⟩⟩)

end ResidueTrichotomy

end LT.LatticeTree

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section

variable {K : Type*} [Field K]

private theorem exists_conj_eq_of_mul_eq (M A C : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0) (h : M * A = A * C) :
    ∃ x : Matrix.GeneralLinearGroup (Fin 2) K,
      ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * x = C := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  refine ⟨hu.unit, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_inv, IsUnit.unit_spec, mul_assoc, h, ← mul_assoc,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), one_mul]

private theorem exists_conj_eq_companion {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hroot : ∀ r : K, r * r - M.trace * r + M.det ≠ 0) :
    ∃ x : Matrix.GeneralLinearGroup (Fin 2) K,
      ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * x =
        !![0, -M.det; 1, M.trace] := by
  by_cases hc : M 1 0 = 0
  · by_cases hb : M 0 1 = 0
    · exfalso
      apply hroot (M 0 0)
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, hb, hc]
      ring
    · refine exists_conj_eq_of_mul_eq M !![0, M 0 1; 1, M 1 1] !![0, -M.det; 1, M.trace] ?_ ?_
      · rw [Matrix.det_fin_two_of]
        simpa using hb
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
  · refine exists_conj_eq_of_mul_eq M !![1, M 0 0; 0, M 1 0] !![0, -M.det; 1, M.trace] ?_ ?_
    · rw [Matrix.det_fin_two_of]
      simpa using hc
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

end

section

open scoped Matrix in

private theorem forall_mulVec_eq_smul_imp_eq_zero_of_forall_not_dvd
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (Y : Matrix (Fin 2) (Fin 2) R) (h : ∀ r : R, ¬ ϖ ∣ r * r - Y.trace * r + Y.det) :
    ∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
      (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0 := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ.prime
  intro a w hw
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  set κ : R →+* R ⧸ Ideal.span {ϖ} := Ideal.Quotient.mk (Ideal.span {ϖ})
  have h0 : κ (Y 0 0) * w 0 + κ (Y 0 1) * w 1 = κ r * w 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 0
  have h1 : κ (Y 1 0) * w 0 + κ (Y 1 1) * w 1 = κ r * w 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 1
  have hχ : κ r * κ r - (κ (Y 0 0) + κ (Y 1 1)) * κ r + (κ (Y 0 0) * κ (Y 1 1) - κ (Y 0 1) * κ (Y 1 0)) ≠ 0 := by
    intro h0'
    have h2 : κ (r * r - Y.trace * r + Y.det) = 0 := by
      rw [Matrix.trace_fin_two, Matrix.det_fin_two]
      simp only [map_add, map_sub, map_mul]
      linear_combination h0'
    exact h r (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2))
  have hχ0 : (κ r * κ r - (κ (Y 0 0) + κ (Y 1 1)) * κ r
      + (κ (Y 0 0) * κ (Y 1 1) - κ (Y 0 1) * κ (Y 1 0))) * w 0 = 0 := by
    linear_combination (κ (Y 1 1) - κ r) * h0 - κ (Y 0 1) * h1
  have hχ1 : (κ r * κ r - (κ (Y 0 0) + κ (Y 1 1)) * κ r
      + (κ (Y 0 0) * κ (Y 1 1) - κ (Y 0 1) * κ (Y 1 0))) * w 1 = 0 := by
    linear_combination (-κ (Y 1 0)) * h0 + (κ (Y 0 0) - κ r) * h1
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp hχ0).resolve_left hχ
  · exact (mul_eq_zero.mp hχ1).resolve_left hχ

end

end LT.LatticeTree

open scoped Matrix

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section NormalFormRecursion

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private def IsNormalForm (ϖ : R) (P : Matrix (Fin 2) (Fin 2) K) : Prop :=
  (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) R) (d : ℕ) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R),
      (∀ i j, (γ' : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j) ∧
      (∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
        (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
      P = (γ' : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K : R → K)) ∨
  (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) R) (d : ℕ) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ),
      (∀ i j, (γ' : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j) ∧
      Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
      P = (γ' : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K : R → K)) ∨
  (∃ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ),
      Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
      P = Y.map (algebraMap R K : R → K))

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem smul_one_add_smul_apply (a e : R) (g : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + e • g) i j = a * (1 : Matrix (Fin 2) (Fin 2) R) i j + e * g i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem det_smul_one_add_smul (a e : R) (g : Matrix (Fin 2) (Fin 2) R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + e • g).det =
      a * a + e * (a * (g 0 0 + g 1 1)) + e * e * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

private theorem algebraMap_matrix_one_apply (i j : Fin 2) :
    algebraMap R K ((1 : Matrix (Fin 2) (Fin 2) R) i j) = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
  fin_cases i <;> fin_cases j <;> simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

private theorem map_smul_one_add_smul (a e : R) (g : Matrix (Fin 2) (Fin 2) R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + e • g).map (algebraMap R K : R → K) =
      algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K e • g.map (algebraMap R K : R → K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    algebraMap_matrix_one_apply]

private theorem units_conj_smul_one_add_smul (x : Matrix.GeneralLinearGroup (Fin 2) K) (c e : K)
    (P : Matrix (Fin 2) (Fin 2) K) :
    ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (c • (1 : Matrix (Fin 2) (Fin 2) K) + e • P) * (x : Matrix (Fin 2) (Fin 2) K) =
      c • (1 : Matrix (Fin 2) (Fin 2) K) +
        e • (((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * P *
          (x : Matrix (Fin 2) (Fin 2) K)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

omit [IsFractionRing R K] in

private theorem isNormalForm_shift_lift {ϖ : R} (hϖ : Irreducible ϖ) {a : R} (ha : ¬ ϖ ∣ a) {d : ℕ} (hd : 0 < d)
    {P : Matrix (Fin 2) (Fin 2) K} (hP : IsNormalForm ϖ P) :
    IsNormalForm ϖ (algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K ϖ ^ d • P) := by
  have hprime := hϖ.prime
  have hunit : ∀ m : R, ¬ ϖ ∣ a + ϖ ^ d * m := by
    intro m h
    apply ha
    have h' := dvd_sub h (dvd_mul_of_dvd_left (dvd_pow_self ϖ hd.ne') m)
    rwa [add_sub_cancel_right] at h'
  have hdetG : ∀ g : Matrix (Fin 2) (Fin 2) R, ¬ ϖ ∣ (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ d • g).det := by
    intro g h
    rw [det_smul_one_add_smul] at h
    apply ha
    have h' : ϖ ∣ a * a := by
      have e : a * a = (a * a + ϖ ^ d * (a * (g 0 0 + g 1 1)) + ϖ ^ d * ϖ ^ d * (g 0 0 * g 1 1 - g 0 1 * g 1 0))
          - ϖ ^ d * (a * (g 0 0 + g 1 1) + ϖ ^ d * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) := by ring
      rw [e]
      exact dvd_sub h (dvd_mul_of_dvd_left (dvd_pow_self ϖ hd.ne') _)
    exact (hprime.dvd_or_dvd h').elim id id
  have hGL : ∀ g : Matrix (Fin 2) (Fin 2) R, IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ d • g) := fun g =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_not_uniformizer_dvd hϖ (hdetG g))
  unfold IsNormalForm at hP ⊢
  rcases hP with ⟨γ₃, d', mu', Y', hγ₃, hanis', rfl⟩ | ⟨γ₃, d', mu', Y', w', hγ₃, hdetY, htrY, rfl⟩ |
    ⟨Y', w', hdetY, htrY, rfl⟩
  · have hG : a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ d • (γ₃ : Matrix (Fin 2) (Fin 2) R)
        = (a + ϖ ^ d * mu') • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ (d + d') • Y' := by
      ext i j
      rw [smul_one_add_smul_apply, smul_one_add_smul_apply, hγ₃ i j]
      ring
    refine Or.inl ⟨(hGL γ₃).unit, d + d', (isUnit_of_not_uniformizer_dvd hϖ (hunit mu')).unit, Y', fun i j => ?_,
      hanis', ?_⟩
    · rw [(hGL γ₃).unit_spec, (isUnit_of_not_uniformizer_dvd hϖ (hunit mu')).unit_spec, hG,
        smul_one_add_smul_apply]
    · rw [(hGL γ₃).unit_spec, map_smul_one_add_smul, map_pow]
  · have hG : a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ d • (γ₃ : Matrix (Fin 2) (Fin 2) R)
        = (a + ϖ ^ d * mu') • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ (d + d') • Y' := by
      ext i j
      rw [smul_one_add_smul_apply, smul_one_add_smul_apply, hγ₃ i j]
      ring
    refine Or.inr (Or.inl ⟨(hGL γ₃).unit, d + d', (isUnit_of_not_uniformizer_dvd hϖ (hunit mu')).unit, Y', w',
      fun i j => ?_, hdetY, htrY, ?_⟩)
    · rw [(hGL γ₃).unit_spec, (isUnit_of_not_uniformizer_dvd hϖ (hunit mu')).unit_spec, hG,
        smul_one_add_smul_apply]
    · rw [(hGL γ₃).unit_spec, map_smul_one_add_smul, map_pow]
  · refine Or.inr (Or.inl ⟨(hGL Y').unit, d, (isUnit_of_not_uniformizer_dvd hϖ ha).unit, Y', w',
      fun i j => ?_, hdetY, htrY, ?_⟩)
    · rw [(hGL Y').unit_spec, (isUnit_of_not_uniformizer_dvd hϖ ha).unit_spec, smul_one_add_smul_apply]
    · rw [(hGL Y').unit_spec, map_smul_one_add_smul, map_pow]

private theorem exists_shift_scale {ϖ : R} (hϖ : Irreducible ϖ) (t₁ n₁ : R) (M : Matrix (Fin 2) (Fin 2) K)
    (htr : M.trace = algebraMap R K t₁) (hdet : M.det = algebraMap R K n₁)
    (hroot : ∀ r : K, r * r - algebraMap R K t₁ * r + algebraMap R K n₁ ≠ 0)
    (a : R) (hta : ϖ ∣ t₁ - 2 * a) (hna : ϖ ∣ n₁ - a * a) :
    ∃ (d : ℕ) (t₃ n₃ : R) (M₃ : Matrix (Fin 2) (Fin 2) K),
      M = algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K ϖ ^ d • M₃ ∧
      M₃.trace = algebraMap R K t₃ ∧ M₃.det = algebraMap R K n₃ ∧
      (∀ r : K, r * r - algebraMap R K t₃ * r + algebraMap R K n₃ ≠ 0) ∧
      ¬ (ϖ ∣ t₃ ∧ ϖ ^ 2 ∣ n₃) ∧
      t₁ * t₁ - 4 * n₁ = ϖ ^ (2 * d) * (t₃ * t₃ - 4 * n₃) ∧
      (d = 0 → ϖ ∣ t₃ ∧ ϖ ∣ n₃) := by
  have hinj := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero

  have hn₂ : ϖ ∣ n₁ - t₁ * a + a * a := by
    have e : n₁ - t₁ * a + a * a = (n₁ - a * a) - a * (t₁ - 2 * a) := by ring
    rw [e]
    exact dvd_sub hna (dvd_mul_of_dvd_right hta _)
  have e₁ : algebraMap R K (t₁ - 2 * a) = algebraMap R K t₁ - 2 * algebraMap R K a := by
    rw [map_sub, map_mul, map_ofNat]
  have e₂ : algebraMap R K (n₁ - t₁ * a + a * a)
      = algebraMap R K n₁ - algebraMap R K t₁ * algebraMap R K a + algebraMap R K a * algebraMap R K a := by
    rw [map_add, map_sub, map_mul, map_mul]

  have htr' : M 0 0 + M 1 1 = algebraMap R K t₁ := by rw [← Matrix.trace_fin_two]; exact htr
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = algebraMap R K n₁ := by rw [← Matrix.det_fin_two]; exact hdet
  have htr₂ : (M - algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K)).trace = algebraMap R K (t₁ - 2 * a) := by
    rw [e₁, Matrix.trace_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linear_combination htr'
  have hdet₂ : (M - algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K)).det = algebraMap R K (n₁ - t₁ * a + a * a) := by
    rw [e₂, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      mul_zero, sub_zero]
    linear_combination hdet' - algebraMap R K a * htr'

  have hroot₂ : ∀ r : K, r * r - algebraMap R K (t₁ - 2 * a) * r + algebraMap R K (n₁ - t₁ * a + a * a) ≠ 0 := by
    intro r h
    rw [e₁, e₂] at h
    exact hroot (r + algebraMap R K a) (by linear_combination h)
  have hn₂K : algebraMap R K (n₁ - t₁ * a + a * a) ≠ 0 := by
    intro h0
    rw [e₂] at h0
    exact hroot (algebraMap R K a) (by linear_combination h0)

  obtain ⟨k, t₃, n₃, ht₃, hn₃, hnorm₃⟩ :=
    exists_trace_det_scaling hϖ (algebraMap R K (t₁ - 2 * a)) (algebraMap R K (n₁ - t₁ * a + a * a)) hn₂K

  have hk : 0 ≤ k := by
    by_contra hk
    rw [not_le] at hk
    have hkm : algebraMap R K ϖ ^ k = (algebraMap R K ϖ ^ (-k).toNat)⁻¹ := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ -k), zpow_neg, inv_inv]
    have hpow : algebraMap R K ϖ ^ (-k).toNat ≠ 0 := pow_ne_zero _ hϖK
    have ht₃K : algebraMap R K t₃ = algebraMap R K (ϖ ^ (-k).toNat * (t₁ - 2 * a)) := by
      rw [map_mul, map_pow, ht₃, hkm, ← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
    have hn₃K : algebraMap R K n₃ = algebraMap R K (ϖ ^ (-k).toNat * ϖ ^ (-k).toNat * (n₁ - t₁ * a + a * a)) := by
      rw [map_mul, map_mul, map_pow, hn₃, two_mul, zpow_add₀ hϖK, hkm]
      have h : algebraMap R K ϖ ^ (-k).toNat * (algebraMap R K ϖ ^ (-k).toNat)⁻¹ = 1 := mul_inv_cancel₀ hpow
      calc algebraMap R K n₃
          = (algebraMap R K ϖ ^ (-k).toNat * (algebraMap R K ϖ ^ (-k).toNat)⁻¹)
              * (algebraMap R K ϖ ^ (-k).toNat * (algebraMap R K ϖ ^ (-k).toNat)⁻¹) * algebraMap R K n₃ := by
            rw [h, one_mul, one_mul]
        _ = _ := by ring
    refine hnorm₃ ⟨?_, ?_⟩
    · rw [hinj ht₃K]
      exact dvd_mul_of_dvd_left (dvd_pow_self ϖ (by omega : (-k).toNat ≠ 0)) _
    · rw [hinj hn₃K, pow_two, mul_assoc]
      exact mul_dvd_mul (dvd_pow_self ϖ (by omega : (-k).toNat ≠ 0))
        (dvd_mul_of_dvd_left (dvd_pow_self ϖ (by omega : (-k).toNat ≠ 0)) _)
  have hkd : algebraMap R K ϖ ^ k = algebraMap R K ϖ ^ k.toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hk]
  have hpow : algebraMap R K ϖ ^ k.toNat ≠ 0 := pow_ne_zero _ hϖK
  have hsq : algebraMap R K ϖ ^ (2 * k) = algebraMap R K ϖ ^ k.toNat * algebraMap R K ϖ ^ k.toNat := by
    rw [two_mul, zpow_add₀ hϖK, hkd]
  rw [hkd] at ht₃
  rw [hsq] at hn₃

  have ht₂R : t₁ - 2 * a = ϖ ^ k.toNat * t₃ := hinj (by rw [map_mul, map_pow]; exact ht₃)
  have hn₂R : n₁ - t₁ * a + a * a = ϖ ^ k.toNat * ϖ ^ k.toNat * n₃ :=
    hinj (by rw [map_mul, map_mul, map_pow]; exact hn₃)
  refine ⟨k.toNat, t₃, n₃, (algebraMap R K ϖ ^ k.toNat)⁻¹ • (M - algebraMap R K a • (1 : Matrix (Fin 2) (Fin 2) K)),
    ?_, ?_, ?_, forall_quadratic_ne_zero_of_scaling ht₃ hn₃ hroot₂, hnorm₃, ?_, fun hd => ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hpow, one_smul]
    abel
  · rw [Matrix.trace_smul, htr₂, ht₃, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
  · rw [Matrix.det_smul, Fintype.card_fin, hdet₂, hn₃]
    have h : (algebraMap R K ϖ ^ k.toNat)⁻¹ * algebraMap R K ϖ ^ k.toNat = 1 := inv_mul_cancel₀ hpow
    calc (algebraMap R K ϖ ^ k.toNat)⁻¹ ^ 2
          * (algebraMap R K ϖ ^ k.toNat * algebraMap R K ϖ ^ k.toNat * algebraMap R K n₃)
        = ((algebraMap R K ϖ ^ k.toNat)⁻¹ * algebraMap R K ϖ ^ k.toNat)
            * ((algebraMap R K ϖ ^ k.toNat)⁻¹ * algebraMap R K ϖ ^ k.toNat) * algebraMap R K n₃ := by ring
      _ = algebraMap R K n₃ := by rw [h, one_mul, one_mul]
  · have e : t₁ * t₁ - 4 * n₁ = (t₁ - 2 * a) * (t₁ - 2 * a) - 4 * (n₁ - t₁ * a + a * a) := by ring
    rw [e, ht₂R, hn₂R]
    ring
  · rw [hd, pow_zero, one_mul] at ht₂R
    rw [hd, pow_zero, one_mul, one_mul] at hn₂R
    exact ⟨by rw [← ht₂R]; exact hta, by rw [← hn₂R]; exact hn₂⟩

private theorem exists_conj_isNormalForm_of_not_pow_dvd_discr {ϖ : R} (hϖ : Irreducible ϖ)
    (hH : ∀ t n a₀ : R, ϖ ∣ a₀ * a₀ - t * a₀ + n → ¬ ϖ ∣ 2 * a₀ - t → ∃ a : R, a * a - t * a + n = 0) (N : ℕ) :
    ∀ (t₁ n₁ : R) (M : Matrix (Fin 2) (Fin 2) K), M.trace = algebraMap R K t₁ → M.det = algebraMap R K n₁ →
      (∀ r : K, r * r - algebraMap R K t₁ * r + algebraMap R K n₁ ≠ 0) → ¬ (ϖ ∣ t₁ ∧ ϖ ^ 2 ∣ n₁) →
      ¬ ϖ ^ N ∣ t₁ * t₁ - 4 * n₁ →
      ∃ x : Matrix.GeneralLinearGroup (Fin 2) K,
        IsNormalForm ϖ (((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M *
          (x : Matrix (Fin 2) (Fin 2) K)) := by
  induction' N using Nat.strong_induction_on with N ih
  intro t₁ n₁ M htr hdet hroot hnorm hdisc
  have hrootM : ∀ r : K, r * r - M.trace * r + M.det ≠ 0 := by
    rw [htr, hdet]
    exact hroot
  have hrootR : ∀ r : R, r * r - t₁ * r + n₁ ≠ 0 := by
    intro r hr
    refine hroot (algebraMap R K r) ?_
    rw [← map_mul, ← map_mul, ← map_sub, ← map_add, hr, map_zero]
  obtain ⟨x, hx⟩ := exists_conj_eq_companion M hrootM
  rcases quadratic_residue_trichotomy hϖ hH t₁ n₁ hrootR hnorm with ⟨ht, w, hw⟩ | ⟨hn, hres⟩ | ⟨a, ha, hta, hna⟩
  ·
    refine ⟨x, ?_⟩
    unfold IsNormalForm
    refine Or.inr (Or.inr ⟨!![0, -n₁; 1, t₁], w, ?_, ?_, ?_⟩)
    · simp [hw]
    · simpa using ht
    · rw [hx, htr, hdet]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  ·
    have hCdet : (!![0, -n₁; 1, t₁] : Matrix (Fin 2) (Fin 2) R).det = n₁ := by
      rw [Matrix.det_fin_two_of]
      ring
    have hCu : IsUnit (!![0, -n₁; 1, t₁] : Matrix (Fin 2) (Fin 2) R) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hCdet]; exact isUnit_of_not_uniformizer_dvd hϖ hn)
    have hY : ∀ r : R, ¬ ϖ ∣ r * r - (!![-1, -n₁; 1, t₁ - 1] : Matrix (Fin 2) (Fin 2) R).trace * r
        + (!![-1, -n₁; 1, t₁ - 1] : Matrix (Fin 2) (Fin 2) R).det := by
      intro r h
      refine hres (r + 1) ?_
      have e : (r + 1) * (r + 1) - t₁ * (r + 1) + n₁
          = r * r - (!![-1, -n₁; 1, t₁ - 1] : Matrix (Fin 2) (Fin 2) R).trace * r
            + (!![-1, -n₁; 1, t₁ - 1] : Matrix (Fin 2) (Fin 2) R).det := by
        rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
        ring
      rw [e]
      exact h
    refine ⟨x, ?_⟩
    unfold IsNormalForm
    refine Or.inl ⟨hCu.unit, 0, 1, !![-1, -n₁; 1, t₁ - 1], fun i j => ?_,
      forall_mulVec_eq_smul_imp_eq_zero_of_forall_not_dvd hϖ _ hY, ?_⟩
    · rw [hCu.unit_spec]
      fin_cases i <;> fin_cases j <;> simp
    · rw [hCu.unit_spec, hx, htr, hdet]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  ·
    obtain ⟨d, t₃, n₃, M₃, hM, htr₃, hdet₃, hroot₃, hnorm₃, hdisc₃, hd0⟩ :=
      exists_shift_scale hϖ t₁ n₁ M htr hdet hroot a hta hna
    rcases Nat.eq_zero_or_pos d with hd | hd
    ·
      have hroot₃M : ∀ r : K, r * r - M₃.trace * r + M₃.det ≠ 0 := by
        rw [htr₃, hdet₃]
        exact hroot₃
      obtain ⟨x₃, hx₃⟩ := exists_conj_eq_companion M₃ hroot₃M
      obtain ⟨ht₃, w₀, hw₀⟩ := hd0 hd
      have hw₀' : ¬ ϖ ∣ w₀ := fun h => hnorm₃ ⟨ht₃, by rw [hw₀, pow_two]; exact mul_dvd_mul_left ϖ h⟩
      have hG : a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ 0 • (!![0, -n₃; 1, t₃] : Matrix (Fin 2) (Fin 2) R)
          = !![a, -n₃; 1, a + t₃] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hGdet :
          ¬ ϖ ∣ (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ 0 • (!![0, -n₃; 1, t₃] : Matrix (Fin 2) (Fin 2) R)).det := by
        rw [hG, Matrix.det_fin_two_of]
        intro h
        apply ha
        have h' : ϖ ∣ a * a := by
          have e : a * a = (a * (a + t₃) - -n₃ * 1) - (a * t₃ + n₃) := by ring
          rw [e]
          exact dvd_sub h (dvd_add (dvd_mul_of_dvd_right ht₃ a) ⟨w₀, hw₀⟩)
        exact (hϖ.prime.dvd_or_dvd h').elim id id
      have hGu :
          IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ 0 • (!![0, -n₃; 1, t₃] : Matrix (Fin 2) (Fin 2) R)) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_not_uniformizer_dvd hϖ hGdet)
      refine ⟨x₃, ?_⟩
      unfold IsNormalForm
      refine Or.inr (Or.inl ⟨hGu.unit, 0, (isUnit_of_not_uniformizer_dvd hϖ ha).unit, !![0, -n₃; 1, t₃],
        (isUnit_of_not_uniformizer_dvd hϖ hw₀').unit, fun i j => ?_, ?_, ?_, ?_⟩)
      · rw [hGu.unit_spec, (isUnit_of_not_uniformizer_dvd hϖ ha).unit_spec, smul_one_add_smul_apply]
      · rw [(isUnit_of_not_uniformizer_dvd hϖ hw₀').unit_spec]
        simp [hw₀]
      · simpa using ht₃
      · have hC : (!![0, -n₃; 1, t₃] : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K : R → K) =
            !![0, -algebraMap R K n₃; 1, algebraMap R K t₃] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp
        rw [hGu.unit_spec, hM, units_conj_smul_one_add_smul, hx₃, htr₃, hdet₃, hd, map_smul_one_add_smul, map_pow,
          hC]
    ·
      have hN0 : N ≠ 0 := by
        rintro rfl
        exact hdisc (by rw [pow_zero]; exact one_dvd _)
      have hN : N - 2 * d < N := by omega
      have hdisc₃' : ¬ ϖ ^ (N - 2 * d) ∣ t₃ * t₃ - 4 * n₃ := by
        intro h
        apply hdisc
        rw [hdisc₃]
        exact dvd_trans (pow_dvd_pow ϖ (by omega : N ≤ 2 * d + (N - 2 * d)))
          (by rw [pow_add]; exact mul_dvd_mul_left _ h)
      obtain ⟨x₄, hx₄⟩ := ih (N - 2 * d) hN t₃ n₃ M₃ htr₃ hdet₃ hroot₃ hnorm₃ hdisc₃'
      refine ⟨x₄, ?_⟩
      rw [hM, units_conj_smul_one_add_smul]
      exact isNormalForm_shift_lift hϖ ha hd hx₄

end NormalFormRecursion

end LT.LatticeTree

open NumberField IsDedekindDomain Polynomial Filter Topology

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section CompletedIntegersAreHenselian

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem mem_adicCompletionIntegers_iff_norm_le_one (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.FinitePlace.norm_def (v := v)]
  constructor
  · intro hy
    exact_mod_cast
      (WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hy
  · intro hy
    exact (WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp
      (by exact_mod_cast hy)

private theorem norm_coe_le_one (x : v.adicCompletionIntegers K) : ‖(x : v.adicCompletion K)‖ ≤ 1 :=
  (mem_adicCompletionIntegers_iff_norm_le_one v x).mp x.2

private theorem norm_coe_le_pow_of_dvd {ϖ x : v.adicCompletionIntegers K} {m : ℕ} (h : ϖ ^ m ∣ x) :
    ‖(x : v.adicCompletion K)‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ m := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) m) (norm_coe_le_one v c)

private theorem dvd_of_norm_coe_le_pow {ϖ x : v.adicCompletionIntegers K} (hϖ : ϖ ≠ 0) {m : ℕ}
    (h : ‖(x : v.adicCompletion K)‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ m) : ϖ ^ m ∣ x := by
  have hϖF : (ϖ : v.adicCompletion K) ≠ 0 := by exact_mod_cast hϖ
  have hpow : ((ϖ : v.adicCompletion K) ^ m) ≠ 0 := pow_ne_zero m hϖF
  have hc : (x : v.adicCompletion K) / (ϖ : v.adicCompletion K) ^ m ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers_iff_norm_le_one v, norm_div, norm_pow,
      div_le_one (pow_pos (norm_pos_iff.mpr hϖF) m)]
    exact h
  refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
  push_cast
  field_simp

private theorem norm_coe_lt_one_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖(ϖ : v.adicCompletion K)‖ < 1 := by
  refine lt_of_le_of_ne (norm_coe_le_one v ϖ) fun h1 => hϖ.not_isUnit ?_
  have hϖF : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hinv : (ϖ : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers_iff_norm_le_one v, norm_inv, h1, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  push_cast
  exact mul_inv_cancel₀ hϖF

private theorem isPrecomplete_span_singleton {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    IsPrecomplete (Ideal.span {ϖ}) (v.adicCompletionIntegers K) := by
  refine ⟨fun f hf => ?_⟩
  simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hf ⊢
  have hcau : CauchySeq fun k => (f k : v.adicCompletion K) := by
    refine cauchySeq_of_le_geometric ‖(ϖ : v.adicCompletion K)‖ 1 (norm_coe_lt_one_of_irreducible v hϖ) fun k => ?_
    have hk := norm_coe_le_pow_of_dvd v (hf (Nat.le_succ k))
    push_cast at hk
    rw [one_mul, dist_eq_norm]
    exact hk
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have hclosed₁ : IsClosed {y : v.adicCompletion K | ‖y‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  have hLmem : L ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers_iff_norm_le_one v]
    exact hclosed₁.mem_of_tendsto hL (Eventually.of_forall fun k => norm_coe_le_one v (f k))
  refine ⟨⟨L, hLmem⟩, fun k => ?_⟩
  apply dvd_of_norm_coe_le_pow v hϖ.ne_zero
  push_cast
  have hclosed₂ :
      IsClosed {y : v.adicCompletion K | ‖(f k : v.adicCompletion K) - y‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ k} :=
    isClosed_le (continuous_const.sub continuous_id).norm continuous_const
  refine hclosed₂.mem_of_tendsto hL (eventually_atTop.mpr ⟨k, fun j hj => ?_⟩)
  have hj' := norm_coe_le_pow_of_dvd v (hf hj)
  push_cast at hj'
  exact hj'

end CompletedIntegersAreHenselian

private theorem exists_quadratic_root_of_approx
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    ∀ t n a₀ : v.adicCompletionIntegers K, ϖ ∣ a₀ * a₀ - t * a₀ + n → ¬ ϖ ∣ 2 * a₀ - t →
      ∃ a : v.adicCompletionIntegers K, a * a - t * a + n = 0 := by
  intro t n a₀ ht hder
  have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal (v.adicCompletionIntegers K)) := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hϖ.not_isUnit
  haveI : IsHausdorff (Ideal.span {ϖ}) (v.adicCompletionIntegers K) := IsHausdorff.of_isDomain _ hne
  haveI : IsPrecomplete (Ideal.span {ϖ}) (v.adicCompletionIntegers K) := isPrecomplete_span_singleton v hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) (v.adicCompletionIntegers K) := {}
  haveI hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hmonic : (X ^ 2 + (C (-t) * X + C n) : (v.adicCompletionIntegers K)[X]).Monic :=
    monic_X_pow_add (by simpa using (degree_linear_lt (a := -t) (b := n)))
  have hmem : (X ^ 2 + (C (-t) * X + C n) : (v.adicCompletionIntegers K)[X]).eval a₀ ∈ Ideal.span {ϖ} := by
    rw [Ideal.mem_span_singleton]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    convert ht using 1
    ring
  have hder' : (derivative (X ^ 2 + (C (-t) * X + C n) : (v.adicCompletionIntegers K)[X])).eval a₀ = 2 * a₀ - t := by
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul,
      eval_C, eval_X, eval_pow, eval_zero, eval_one]
    ring
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      ((derivative (X ^ 2 + (C (-t) * X + C n) : (v.adicCompletionIntegers K)[X])).eval a₀)) := by
    rw [hder']
    exact isUnit_iff_ne_zero.mpr fun h0 =>
      hder (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
  obtain ⟨a, ha, -⟩ :=
    HenselianRing.is_henselian (R := v.adicCompletionIntegers K) (I := Ideal.span {ϖ}) _ hmonic a₀ hmem hunit
  refine ⟨a, ?_⟩
  simp only [IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X] at ha
  linear_combination ha

end LT.LatticeTree

open scoped Matrix

namespace LT
p2m_export "LT" "mk"
namespace LatticeTree
p2m_open "LT"

section NormalForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem exists_not_pow_dvd {ϖ : R} (hϖ : Irreducible ϖ) {x : R} (hx : x ≠ 0) : ∃ N : ℕ, ¬ ϖ ^ N ∣ x := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  refine ⟨m + 1, fun h => hϖ.not_isUnit (isUnit_of_dvd_unit ?_ u.isUnit)⟩
  rw [pow_succ'] at h
  exact (mul_dvd_mul_iff_right (pow_ne_zero m hϖ.ne_zero)).mp h

private theorem exists_conj_eq_zpow_smul_normalForm {ϖ : R} (hϖ : Irreducible ϖ)
    (hH : ∀ t n a₀ : R, ϖ ∣ a₀ * a₀ - t * a₀ + n → ¬ ϖ ∣ 2 * a₀ - t → ∃ a : R, a * a - t * a + n = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) K))) :
    ∃ (x : Matrix.GeneralLinearGroup (Fin 2) K) (k : ℤ),
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) R) (d : ℕ)
          (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) R) i j =
            (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j +
              ϖ ^ d * Y i j) ∧
        (∀ (a : R ⧸ Ideal.span {ϖ})
            (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
          (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) :
              R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) =
          algebraMap R K ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) R).map
              (algebraMap R K
                : R → K)) ∨
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) R) (d : ℕ)
          (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
          (w : Rˣ),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) R) i j =
            (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j +
              ϖ ^ d * Y i j) ∧
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) =
          algebraMap R K ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) R).map
              (algebraMap R K
                : R → K)) ∨
      (∃ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ),
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) =
          algebraMap R K ϖ ^ k •
            Y.map (algebraMap R K
              : R → K)) := by
  have hinj := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hdet0 : Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).ne_zero
  have hroot := forall_quadratic_ne_zero_of_not_isSquare hγ
  have hdisc := ne_zero_of_not_isSquare hγ

  obtain ⟨k, t₁, n₁, ht, hn, hnorm⟩ :=
    exists_trace_det_scaling hϖ (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K))
      (Matrix.det (γ : Matrix (Fin 2) (Fin 2) K)) hdet0
  have hc : algebraMap R K ϖ ^ k ≠ 0 := zpow_ne_zero k hϖK
  have hsq : algebraMap R K ϖ ^ (2 * k) = algebraMap R K ϖ ^ k * algebraMap R K ϖ ^ k := by
    rw [two_mul, zpow_add₀ hϖK]
  rw [hsq] at hn

  have hγM : (γ : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ ^ k • ((algebraMap R K ϖ ^ k)⁻¹ • (γ : Matrix (Fin 2) (Fin 2) K)) := by
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have htrM : ((algebraMap R K ϖ ^ k)⁻¹ • (γ : Matrix (Fin 2) (Fin 2) K)).trace = algebraMap R K t₁ := by
    rw [Matrix.trace_smul, ht, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hdetM : ((algebraMap R K ϖ ^ k)⁻¹ • (γ : Matrix (Fin 2) (Fin 2) K)).det = algebraMap R K n₁ := by
    rw [Matrix.det_smul, Fintype.card_fin, hn]
    have h : (algebraMap R K ϖ ^ k)⁻¹ * algebraMap R K ϖ ^ k = 1 := inv_mul_cancel₀ hc
    calc (algebraMap R K ϖ ^ k)⁻¹ ^ 2 * (algebraMap R K ϖ ^ k * algebraMap R K ϖ ^ k * algebraMap R K n₁)
        = ((algebraMap R K ϖ ^ k)⁻¹ * algebraMap R K ϖ ^ k) * ((algebraMap R K ϖ ^ k)⁻¹ * algebraMap R K ϖ ^ k)
            * algebraMap R K n₁ := by ring
      _ = algebraMap R K n₁ := by rw [h, one_mul, one_mul]
  have hrootM := forall_quadratic_ne_zero_of_scaling ht hn hroot

  have hdisc₁ : t₁ * t₁ - 4 * n₁ ≠ 0 := by
    intro h0
    apply hdisc
    rw [ht, hn]
    have h1 : algebraMap R K (t₁ * t₁ - 4 * n₁) = 0 := by rw [h0, map_zero]
    rw [map_sub, map_mul, map_mul, map_ofNat] at h1
    linear_combination algebraMap R K ϖ ^ k * algebraMap R K ϖ ^ k * h1
  obtain ⟨N, hN⟩ := exists_not_pow_dvd hϖ hdisc₁
  obtain ⟨x, hx⟩ := exists_conj_isNormalForm_of_not_pow_dvd_discr hϖ hH N t₁ n₁ _ htrM hdetM hrootM hnorm hN
  have hconj : ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ ^ k • (((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * ((algebraMap R K ϖ ^ k)⁻¹ • (γ : Matrix (Fin 2) (Fin 2) K)) * (x : Matrix (Fin 2) (Fin 2) K)) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← hγM]
  refine ⟨x, k, ?_⟩
  unfold IsNormalForm at hx
  rcases hx with ⟨γ', d, mu, Y, h1, h2, h3⟩ | ⟨γ', d, mu, Y, w, h1, h2, h3, h4⟩ | ⟨Y, w, h1, h2, h3⟩
  · exact Or.inl ⟨γ', d, mu, Y, h1, h2, by rw [hconj, h3]⟩
  · exact Or.inr (Or.inl ⟨γ', d, mu, Y, w, h1, h2, h3, by rw [hconj, h4]⟩)
  · exact Or.inr (Or.inr ⟨Y, w, h1, h2, by rw [hconj, h3]⟩)

end NormalForm

end LT.LatticeTree

open scoped Matrix
open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) :
    ∃ (x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) (k : ℤ),
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        (∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})
            (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}),
          (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) :
              v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
          (w : (v.adicCompletionIntegers K)ˣ),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) (w : (v.adicCompletionIntegers K)ˣ),
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            Y.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              : v.adicCompletionIntegers K → v.adicCompletion K)) := by
  exact LT.LatticeTree.exists_conj_eq_zpow_smul_normalForm hϖ
    (LT.LatticeTree.exists_quadratic_root_of_approx K v ϖ hϖ) γ hγ

end S_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
end P2MW
export P2MW.S_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr (solution)
