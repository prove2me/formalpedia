-- Prove2me | solution 1 for Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bf1f1dd6-d262-50a6-a431-a66f7bbae455

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit

set_option autoImplicit false

namespace MonodromyEigenvalueTrick

open Polynomial Module

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem isNilpotent_of_spectrum_subset_zero (B : Module.End K W)
    (hB : spectrum K B ⊆ {0}) : IsNilpotent B := by
  classical
  rw [LinearMap.isNilpotent_iff_charpoly]
  have hsplit : B.charpoly.Splits := IsAlgClosed.splits _
  have hmonic : B.charpoly.Monic := LinearMap.charpoly_monic B
  have hroots0 : ∀ r ∈ B.charpoly.roots, r = 0 := by
    intro r hr
    have hr' : B.charpoly.IsRoot r := (mem_roots hmonic.ne_zero).1 hr
    have : r ∈ spectrum K B := (Module.End.mem_spectrum_iff_isRoot_charpoly B r).2 hr'
    simpa using hB this
  have hcard : B.charpoly.roots.card = finrank K W := by
    rw [← hsplit.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  have hrep : B.charpoly.roots = Multiset.replicate (finrank K W) 0 := by
    rw [Multiset.eq_replicate]
    exact ⟨hcard, hroots0⟩
  rw [hsplit.eq_prod_roots_of_monic hmonic, hrep]
  simp

theorem exists_isNilpotent_pow_sub_one_of_forall_pow_mem (A : Module.End K W) (hA : IsUnit A)
    {q : ℕ} (hq : 2 ≤ q) (hstab : ∀ μ ∈ spectrum K A, μ ^ q ∈ spectrum K A) :
    ∃ e : ℕ, 0 < e ∧ IsNilpotent (A ^ e - 1) := by
  classical
  set σ := spectrum K A with hσ
  have hfin : σ.Finite := Module.End.finite_spectrum A
  have h0 : (0 : K) ∉ σ := spectrum.zero_notMem_iff K |>.2 hA

  have hroot : ∀ μ ∈ σ, ∃ e : ℕ, 0 < e ∧ μ ^ e = 1 := by
    intro μ hμ
    have hmem : ∀ k : ℕ, μ ^ (q ^ k) ∈ σ := by
      intro k
      induction k with
      | zero => simpa using hμ
      | succ k ih =>
          have := hstab _ ih
          rwa [← pow_mul, ← pow_succ] at this
    obtain ⟨i, j, hij, hEq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem hmem hfin
    have hμ0 : μ ≠ 0 := fun h => h0 (h ▸ hμ)
    have hle : q ^ i ≤ q ^ j := Nat.pow_le_pow_right (by omega) hij.le
    have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
    refine ⟨q ^ j - q ^ i, Nat.sub_pos_of_lt hlt, ?_⟩
    have h1 : μ ^ (q ^ i) * μ ^ (q ^ j - q ^ i) = μ ^ (q ^ i) * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hle, mul_one]
      exact hEq.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hμ0) h1

  choose! ex hex using hroot
  set e := ∏ μ ∈ hfin.toFinset, ex μ with he
  have hepos : 0 < e := by
    rw [he]
    apply Finset.prod_pos
    intro μ hμ
    exact (hex μ (hfin.mem_toFinset.1 hμ)).1
  have hkill : ∀ μ ∈ σ, μ ^ e = 1 := by
    intro μ hμ
    obtain ⟨c, hc⟩ : ex μ ∣ e := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hμ)
    rw [hc, pow_mul, (hex μ hμ).2, one_pow]
  refine ⟨e, hepos, ?_⟩

  apply isNilpotent_of_spectrum_subset_zero
  have hp : A ^ e - 1 = aeval A (X ^ e - 1 : K[X]) := by
    simp [map_sub, aeval_X_pow]
  have hdeg : 0 < degree (X ^ e - 1 : K[X]) := by
    rw [← C_1, degree_X_pow_sub_C hepos]
    exact_mod_cast hepos
  rw [hp, spectrum.map_polynomial_aeval_of_degree_pos A _ hdeg]
  rintro _ ⟨μ, hμ, rfl⟩
  simp [eval_sub, eval_pow, eval_X, hkill μ hμ]

end AlgClosed

section Descent

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem isNilpotent_of_isNilpotent_baseChange (K : Type*) [Field K] [Algebra F K]
    (f : Module.End F V) (hf : IsNilpotent (f.baseChange K)) : IsNilpotent f := by
  rw [LinearMap.isNilpotent_iff_charpoly] at hf ⊢
  rw [LinearMap.charpoly_baseChange, Module.finrank_baseChange] at hf
  apply Polynomial.map_injective (algebraMap F K) (algebraMap F K).injective
  rw [hf, Polynomial.map_pow, Polynomial.map_X]

end Descent

end MonodromyEigenvalueTrick

open MonodromyEigenvalueTrick in
theorem solution
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g h : Module.End F V) (hg : IsUnit g) (hh : IsUnit h) {q : ℕ} (hq : 2 ≤ q)
    (hrel : h * g = g ^ q * h) :
    ∃ e : ℕ, 0 < e ∧ IsNilpotent (g ^ e - 1) := by
  classical
  let K := AlgebraicClosure F
  let φ := Module.End.baseChangeHom F K V
  set A : Module.End K (TensorProduct F K V) := φ g with hAdef
  set H : Module.End K (TensorProduct F K V) := φ h with hHdef
  have hA : IsUnit A := hg.map φ
  have hH : IsUnit H := hh.map φ
  have hrelK : H * A = A ^ q * H := by
    rw [hAdef, hHdef, ← map_pow, ← map_mul, ← map_mul, hrel]
  obtain ⟨u, hu⟩ := hH
  have hconj : A ^ q = u * A * u⁻¹ := by
    rw [← hu] at hrelK
    calc A ^ q = A ^ q * ((u : Module.End K (TensorProduct F K V)) * ↑u⁻¹) := by simp
      _ = (A ^ q * u) * ↑u⁻¹ := by rw [mul_assoc]
      _ = (u * A) * ↑u⁻¹ := by rw [hrelK]
  have hstab : ∀ μ ∈ spectrum K A, μ ^ q ∈ spectrum K A := by
    intro μ hμ
    have := spectrum.pow_mem_pow A q hμ
    rwa [hconj, spectrum.units_conjugate] at this
  obtain ⟨e, he, hnil⟩ := exists_isNilpotent_pow_sub_one_of_forall_pow_mem A hA hq hstab
  refine ⟨e, he, ?_⟩
  apply isNilpotent_of_isNilpotent_baseChange K
  have : (g ^ e - 1).baseChange K = A ^ e - 1 := by
    have h1 : (g ^ e - 1).baseChange K = φ (g ^ e - 1) := rfl
    rw [h1, map_sub, map_pow, map_one]
  rw [this]
  exact hnil

end S_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
end P2MW
export P2MW.S_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit (solution)
