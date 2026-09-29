-- Prove2me | solution 1 for HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cfdb125d-c7b0-513f-88ce-8ba7d6385689

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binaryFormRepSL"
p2m_open "HeckeEis"

open MvPolynomial Polynomial
open scoped MatrixGroups

namespace UnipotentFixedAux

variable {R : Type*} [CommRing R] {n : ℕ}

private theorem _root_.HeckeEis.UnipotentFixedAux.monomial_eq (n j : ℕ) :
    (MvPolynomial.monomial (Finsupp.single 0 (n - j) + Finsupp.single 1 j) (1 : R))
      = MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]

p2m_export "HeckeEis.UnipotentFixedAux" "monomial_eq"
variable (n) in

noncomputable def expo (j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 (n - j) + Finsupp.single 1 j

theorem expo_injOn : Set.InjOn (expo n) (Finset.range (n + 1) : Set ℕ) := by
  intro i _ j _ h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  simpa [expo, Finsupp.single_apply] using this

theorem degree_eq_iff (d : Fin 2 →₀ ℕ) : d.degree = n ↔ ∃ j ∈ Finset.range (n + 1), expo n j = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  constructor
  · intro h
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i <;> simp [expo, Finsupp.single_apply] <;> omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    simp [expo, Finsupp.single_apply]
    omega

theorem eq_sum_range {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    P = ∑ j ∈ Finset.range (n + 1), MvPolynomial.monomial (expo n j) (MvPolynomial.coeff (expo n j) P) := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · obtain ⟨j, hj, rfl⟩ := (degree_eq_iff d).mp hd
    rw [Finset.sum_eq_single j (fun i hi hne => if_neg fun h => hne (expo_injOn hi hj h)) (fun h => (h hj).elim),
      if_pos rfl]
  · rw [Finset.sum_eq_zero fun i hi => if_neg fun h => hd ((degree_eq_iff d).mpr ⟨i, hi, h⟩)]
    exact ((MvPolynomial.mem_homogeneousSubmodule n P).mp hP).coeff_eq_zero hd

noncomputable def dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X] := MvPolynomial.aeval ![1, Polynomial.X]

theorem dehom_monomial (j : ℕ) (c : R) :
    dehom (MvPolynomial.monomial (expo n j) c) = Polynomial.C c * Polynomial.X ^ j := by
  rw [expo, MvPolynomial.monomial_eq, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  simp [dehom, Polynomial.C_mul']

theorem dehom_eq_sum {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    dehom P = ∑ j ∈ Finset.range (n + 1), Polynomial.C (MvPolynomial.coeff (expo n j) P) * Polynomial.X ^ j := by
  conv_lhs => rw [eq_sum_range hP, map_sum]
  exact Finset.sum_congr rfl fun j _ => dehom_monomial j _

theorem coeff_dehom {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) (j : ℕ) :
    (dehom P).coeff j = if j ∈ Finset.range (n + 1) then MvPolynomial.coeff (expo n j) P else 0 := by
  rw [dehom_eq_sum hP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single j (fun i _ hne => if_neg hne.symm) (fun h' => (h' h).elim), if_pos rfl]
  · exact Finset.sum_eq_zero fun i hi => if_neg fun h' => h (by rw [h']; exact hi)

theorem natDegree_dehom_le {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : (dehom P).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dehom hP, if_neg]
  rw [Finset.mem_range]; omega

theorem dehom_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) R) :
    dehom (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = (dehom P).comp (Polynomial.X + Polynomial.C (h : R)) := by

  revert P
  refine fun P => ?_
  have key : (dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X]).comp (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      = (Polynomial.aeval (Polynomial.X + Polynomial.C (h : R)) : R[X] →ₐ[R] R[X]).comp dehom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, binarySubst_X, ModularGroup.coe_T_zpow]
    fin_cases i <;> simp [dehom, Fin.sum_univ_two, add_comm]
  have := congrArg (fun φ => φ P) key
  simpa [Polynomial.aeval_X, Polynomial.comp_eq_aeval] using this

theorem eq_C_of_comp_X_add_C_eq [IsDomain R] {q : R[X]} (hq : q.natDegree ≤ n) {h : R} (hh : h ≠ 0)
    (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (hinv : q.comp (Polynomial.X + Polynomial.C h) = q) :
    q = Polynomial.C (q.eval 0) := by
  classical

  have hper : ∀ k : ℕ, q.eval ((k : R) * h) = q.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := congrArg (fun r => Polynomial.eval ((k : R) * h) r) hinv
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
      rw [← ih, ← this]
      congr 1; push_cast; ring

  set q' : R[X] := q - Polynomial.C (q.eval 0) with hq'
  have hdeg : q'.natDegree ≤ n := (Polynomial.natDegree_sub_le _ _).trans (by simpa using hq)
  have hroots : ∀ k ∈ Finset.range (n + 1), q'.eval ((k : R) * h) = 0 := fun k _ => by
    simp [hq', hper k]
  have hinj : Set.InjOn (fun k : ℕ => (k : R) * h) (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have : ((i : R) - (j : R)) * h = 0 := by rw [sub_mul]; exact sub_eq_zero.mpr hij
    rcases mul_eq_zero.mp this with h0 | h0
    ·
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := hn (j - i) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination -h0
      · have := hn (i - j) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination h0
    · exact (hh h0).elim
  have hzero : q' = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q' ((Finset.range (n + 1)).image fun k : ℕ => (k : R) * h)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact hroots k hk
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]; omega
  rw [hq', sub_eq_zero] at hzero
  exact hzero

end UnipotentFixedAux

open UnipotentFixedAux in

theorem SolMain.A2 {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) {h : ℤ}
    (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(BinaryForm R n))
    (hP : binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n := by
  classical
  have hsub : binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) = P := by
    simpa using congrArg Subtype.val hP
  have hq : (dehom (P : MvPolynomial (Fin 2) R)).comp (Polynomial.X + Polynomial.C (h : R)) = dehom (P : MvPolynomial (Fin 2) R) := by
    rw [← dehom_binarySubst_T_zpow, hsub]
  have hconst := eq_C_of_comp_X_add_C_eq (natDegree_dehom_le P.2) hh hn hq
  refine ⟨MvPolynomial.coeff (expo n 0) (P : MvPolynomial (Fin 2) R), ?_⟩

  have hcoeff : ∀ j ∈ Finset.range (n + 1), j ≠ 0 → MvPolynomial.coeff (expo n j) (P : MvPolynomial (Fin 2) R) = 0 := by
    intro j hj hj0
    have := congrArg (fun r : R[X] => r.coeff j) hconst
    simp only [Polynomial.coeff_C, if_neg hj0] at this
    rwa [coeff_dehom P.2, if_pos hj] at this
  conv_lhs => rw [eq_sum_range P.2]
  rw [Finset.sum_eq_single 0 (fun j hj hj0 => by rw [hcoeff j hj hj0, map_zero]) (fun h0 => (h0 (by simp)).elim)]
  rw [expo, Nat.sub_zero, Finsupp.single_zero, add_zero, ← MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.smul_eq_C_mul]

end HeckeEis

open scoped MatrixGroups in
theorem solution {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(HeckeEis.BinaryForm R n))
    (hP : HeckeEis.binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n :=
  HeckeEis.SolMain.A2 n hh hn P hP

#print axioms solution

end S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
end P2MW
export P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self (solution)
