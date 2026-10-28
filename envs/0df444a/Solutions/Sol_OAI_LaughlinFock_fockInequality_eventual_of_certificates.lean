-- Prove2me | solution 1 for OAI.LaughlinFock.fockInequality_eventual_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:53:16.828309+00:00
-- url     : https://prove2.me/submissions/9cbadfa3-a6aa-433b-a56b-c82a81973c69

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_averagedRowsFour_eventual_bound

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Model
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model. -/
noncomputable section

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder




theorem pairCoefficient_eq (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p i j =
      if i.val + j.val = p + 1 then
        ((i.val : ℝ) - (j.val : ℝ)) *
          Real.sqrt (((Q.descFactorial i.val : ℝ) * (Q.descFactorial j.val : ℝ) *
            (p.factorial : ℝ)) /
            ((Q : ℝ) * ((2 * Q - 2).descFactorial p : ℝ) *
              (i.val.factorial : ℝ) * (j.val.factorial : ℝ)))
      else 0 := by
  unfold pairCoefficient tensorPairCoefficient Laughlin.pairCoefficient
  split_ifs <;> simp [Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 2 by norm_num),
    mul_comm (Real.sqrt 2)]



theorem annihilator_card {Q : ℕ} (j : Orbital Q) (A B : Occupation Q)
    (h : annihilator Q j A B ≠ 0) : A.card + 1 = B.card := by
  by_cases hc : j ∈ B ∧ A = B.erase j
  · rcases hc with ⟨hj, rfl⟩
    exact Finset.card_erase_add_one hj
  · exact (h (by simp [annihilator, hc])).elim

theorem annihilator_entry_eq_zero {Q : ℕ} (j : Orbital Q) (A B : Occupation Q)
    (h : A.card + 1 ≠ B.card) : annihilator Q j A B = 0 := by
  by_contra hh
  exact h (annihilator_card j A B hh)

 
theorem pairAnnihilator_entry_eq_zero {Q : ℕ} (p : ℕ) (A B : Occupation Q)
    (h : A.card + 2 ≠ B.card) : pairAnnihilator Q p A B = 0 := by
  classical
  simp only [pairAnnihilator, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul]
    suffices hc : (annihilator Q j * annihilator Q i) A B = 0 by simp [hc]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro C _
    by_cases hAC : A.card + 1 = C.card
    · have hCB : C.card + 1 ≠ B.card := by omega
      rw [annihilator_entry_eq_zero i C B hCB, mul_zero]
    · rw [annihilator_entry_eq_zero j A C hAC, zero_mul]
  · rfl

 
theorem hamiltonian_entry_eq_zero {Q : ℕ} (A B : Occupation Q)
    (h : A.card ≠ B.card) : hamiltonian Q A B = 0 := by
  classical
  simp only [hamiltonian, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro C _
  by_cases hCA : C.card + 2 = A.card
  · have hCB : C.card + 2 ≠ B.card := by omega
    rw [pairAnnihilator_entry_eq_zero p C B hCB, mul_zero]
  · rw [pairAnnihilator_entry_eq_zero p C A hCA, star_zero, zero_mul]



theorem sectorHamiltonian_square (Q n : ℕ) :
    (hamiltonian Q * hamiltonian Q).submatrix
        (Subtype.val : SectorOccupation Q n → Occupation Q) Subtype.val =
      sectorHamiltonian Q n * sectorHamiltonian Q n := by
  classical
  ext A B
  change (∑ C : Occupation Q, hamiltonian Q A.val C * hamiltonian Q C B.val) =
    ∑ C : SectorOccupation Q n, hamiltonian Q A.val C.val * hamiltonian Q C.val B.val
  let f : Occupation Q → ℂ := fun C => hamiltonian Q A.val C * hamiltonian Q C B.val
  change ∑ C, f C = ∑ C : SectorOccupation Q n, f C.val
  calc
    _ = ∑ C ∈ Finset.univ.filter (fun C : Occupation Q => C.card = n), f C := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C _ hC
      have hc : A.val.card ≠ C.card := by
        rw [A.property]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using hC
      simp only [f, hamiltonian_entry_eq_zero A.val C hc, zero_mul]
    _ = _ := Finset.sum_subtype _ (by intro C; simp) f



theorem gram_quadratic_form {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (ψ : κ → ℂ) :
    star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) = star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairNormalization
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
private theorem coeff_euler (P : ℝ[X]) (n : ℕ) :
    (euler P).coeff n = (n : ℝ) * P.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]
private theorem euler_mul (P R : ℝ[X]) :
    euler (P * R) = euler P * R + P * euler R := by
  simp only [euler, derivative_mul]
  ring
private theorem euler_add (P R : ℝ[X]) : euler (P + R) = euler P + euler R := by
  simp [euler, mul_add]
private theorem variance_mul (P R : ℝ[X]) :
    variance (P * R) = P^2 * variance R + R^2 * variance P := by
  simp only [variance, euler_mul, euler_add]
  ring
private theorem variance_X_add_one : variance (X + 1) = X := by
  simp [variance, euler]
  ring
private theorem variance_X_add_one_pow (n : ℕ) :
    variance ((X + 1)^(n+1)) = C ((n+1 : ℕ) : ℝ) * X * ((X+1)^n)^2 := by
  induction n with
  | zero => simp [variance_X_add_one]
  | succ n ih =>
    rw [pow_succ (X + 1) (n + 1), variance_mul, variance_X_add_one, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

private theorem weighted_antidiagonal (P : ℝ[X]) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((ij.1 : ℝ) - (ij.2 : ℝ))^2 * P.coeff ij.1 * P.coeff ij.2) =
      2 * (variance P).coeff n := by
  have hswap : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (ij.2 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap (f := fun ij =>
      (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2)]
    apply Finset.sum_congr rfl
    intro ij _
    dsimp only [Prod.swap]
    ring
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 +
       (ij.2 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 -
       2 * ((ij.1 : ℝ) * P.coeff ij.1 * ((ij.2 : ℝ) * P.coeff ij.2))) := by
      apply Finset.sum_congr rfl
      intro ij _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        variance, coeff_sub, pow_two, coeff_mul, coeff_euler]
      simp only [pow_two] at hswap
      rw [hswap]
      have hh : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (ij.1 : ℝ) * ((ij.1 : ℝ) * P.coeff ij.1) * P.coeff ij.2) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 := by
        apply Finset.sum_congr rfl
        intro ij _
        ring
      simp only [pow_two] at hh
      rw [hh]
      ring

 
theorem pair_binomial_identity (Q p : ℕ) (hQ : 1 ≤ Q) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p+1),
      ((ij.1 : ℝ) - (ij.2 : ℝ))^2 * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      2 * (Q : ℝ) * ((2*Q-2).choose p : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n+1 := ⟨Q-1, by omega⟩
  have h := weighted_antidiagonal ((X+1)^(n+1)) (p+1)
  rw [variance_X_add_one_pow] at h
  simp only [coeff_X_add_one_pow, mul_assoc, coeff_C_mul, coeff_X_mul] at h
  rw [← pow_mul, coeff_X_add_one_pow] at h
  have he : 2*(n+1)-2 = n*2 := by omega
  rw [he]
  simpa only [mul_assoc] using h

 
theorem pairCoefficient_sq (Q p : ℕ) (i j : Orbital Q)
    (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    pairCoefficient Q p i j ^ 2 =
      if i.val + j.val = p+1 then
        ((i.val : ℝ) - (j.val : ℝ))^2 * (Q.choose i.val : ℝ) *
          (Q.choose j.val : ℝ) / ((Q : ℝ) * ((2*Q-2).choose p : ℝ))
      else 0 := by
  rw [pairCoefficient_eq]
  split_ifs
  · rw [mul_pow, Real.sq_sqrt (by positivity)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    have hp' : ((2*Q-2).choose p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
    have hi : (i.val.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    have hj : (j.val.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
    have hf : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    field_simp
  · simp

private theorem orbital_sum_eq_antidiagonal (Q p : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ i j, Q < i ∨ Q < j → f i j = 0) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i.val + j.val = p+1 then f i.val j.val else 0) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p+1), f ij.1 ij.2 := by
  classical
  have hi (i : Orbital Q) : (∑ j : Orbital Q,
      if i.val + j.val = p+1 then f i.val j.val else 0) =
      ∑ j ∈ Finset.range (Q+1), if i.val+j=p+1 then f i.val j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if i.val+j=p+1 then f i.val j else 0) _
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ∑ j ∈ Finset.range (Q+1), if i+j=p+1 then f i j else 0) (Q+1)]
  rw [← Finset.sum_product (Finset.range (Q+1)) (Finset.range (Q+1))
    (fun ij : ℕ × ℕ => if ij.1+ij.2=p+1 then f ij.1 ij.2 else 0),
    ← Finset.sum_filter (fun ij : ℕ × ℕ => ij.1+ij.2=p+1) (fun ij => f ij.1 ij.2)]
  have hs : ((Finset.range (Q+1) ×ˢ Finset.range (Q+1)).filter
      (fun ij : ℕ × ℕ => ij.1 + ij.2 = p+1)) =
      (Finset.HasAntidiagonal.antidiagonal (p+1)).filter
        (fun ij : ℕ × ℕ => ij.1 ≤ Q ∧ ij.2 ≤ Q) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Nat.lt_succ_iff]
    tauto
  rw [hs]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ij hij hn
  have hn' : ¬ (ij.1 ≤ Q ∧ ij.2 ≤ Q) := by
    simpa only [Finset.mem_filter, hij, true_and] using hn
  exact hf _ _ (by omega)

 
theorem pairCoefficient_ordered_norm (Q p : ℕ) (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) :
    (∑ i : Orbital Q, ∑ j : Orbital Q, pairCoefficient Q p i j ^ 2) = 2 := by
  have hsum := orbital_sum_eq_antidiagonal Q p
    (fun i j => ((i : ℝ) - (j : ℝ))^2 * (Q.choose i : ℝ) * (Q.choose j : ℝ))
    (by
      intro i j hij
      rcases hij with hi | hj
      · simp [Nat.choose_eq_zero_of_lt hi]
      · simp [Nat.choose_eq_zero_of_lt hj])
  rw [pair_binomial_identity Q p hQ] at hsum
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  calc
    _ = (∑ i : Orbital Q, ∑ j : Orbital Q,
        if i.val+j.val = p+1 then
          ((i.val : ℝ) - (j.val : ℝ))^2 * (Q.choose i.val : ℝ) * (Q.choose j.val : ℝ)
        else 0) / ((Q : ℝ) * ((2*Q-2).choose p : ℝ)) := by
      simp only [Finset.sum_div, ite_div, zero_div, pairCoefficient_sq Q p _ _ hQ hp]
    _ = _ := by rw [hsum]; field_simp

private theorem sum_eq_twice_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsymm : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  have hterm : ∀ i j, f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr hij.le]
    · subst j; simp [hdiag]
    · simp [hij, not_lt.mpr hij.le, hsymm]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if j < i then f j i else 0 := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
      ring

 

theorem pairCoefficient_norm (Q p : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i < j then pairCoefficient Q p i j ^ 2 else 0) = 1 := by
  have hs := sum_eq_twice_upper (fun i j : Orbital Q => pairCoefficient Q p i j^2)
    (by
      intro i j
      rw [pairCoefficient_sq Q p j i hQ hp, pairCoefficient_sq Q p i j hQ hp]
      by_cases h : i.val+j.val = p+1
      · have h' : j.val+i.val=p+1 := by omega
        simp only [h, h', ite_true, if_true]
        ring
      · have h' : j.val+i.val≠p+1 := by omega
        simp only [h, h', ite_false])
    (by intro i; simp [pairCoefficient_eq])
  rw [pairCoefficient_ordered_norm Q p hQ hp] at hs
  linarith

 

theorem pairCoefficient_orthogonal (Q p r : ℕ) (hpr : p ≠ r) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i < j then pairCoefficient Q p i j * pairCoefficient Q r i j else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs
  · rw [pairCoefficient_eq, pairCoefficient_eq]
    split_ifs <;> first | omega | simp
  · rfl
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FermionOperators
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fermion Operators. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial

theorem annihilator_apply {Q : ℕ} (j : Orbital Q) (A B : Occupation Q) :
    annihilator Q j A B =
      if j ∈ B ∧ A = B.erase j then fermionSign j B else 0 := rfl

private theorem sign_insert_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hi : i ∉ B) (hij : i < j) :
    fermionSign j (insert i B) = -fermionSign j B := by
  simp [fermionSign, Finset.filter_insert, hi, hij, pow_succ]

private theorem sign_insert_not_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hij : ¬ i < j) : fermionSign j (insert i B) = fermionSign j B := by
  simp [fermionSign, Finset.filter_insert, hij]

private theorem sign_erase_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hi : i ∈ B) (hij : i < j) :
    fermionSign j (B.erase i) = -fermionSign j B := by
  have h := sign_insert_lt i j (B.erase i) (Finset.notMem_erase i B) hij
  rw [Finset.insert_erase hi] at h
  rw [h]
  simp

private theorem sign_erase_not_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hij : ¬ i < j) : fermionSign j (B.erase i) = fermionSign j B := by
  by_cases hi : i ∈ B
  · have h := sign_insert_not_lt i j (B.erase i) hij
    rw [Finset.insert_erase hi] at h
    exact h.symm
  · rw [Finset.erase_eq_of_notMem hi]


theorem mul_annihilator_apply {Q : ℕ} (M : FockMatrix Q) (j : Orbital Q)
    (A B : Occupation Q) :
    (M * annihilator Q j) A B =
      if j ∈ B then M A (B.erase j) * fermionSign j B else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ B
  · simp [annihilator, hj, mul_ite, fermionSign]
  · simp [annihilator, hj]

 
theorem mul_creator_apply {Q : ℕ} (M : FockMatrix Q) (j : Orbital Q)
    (A B : Occupation Q) :
    (M * creator Q j) A B =
      if j ∉ B then M A (insert j B) * fermionSign j B else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ B
  · simp [creator, hj]
  · simp [creator, hj, mul_ite]

 
theorem creator_eq_adjoint (Q : ℕ) (j : Orbital Q) :
    creator Q j = (annihilator Q j)ᴴ := by
  classical
  ext A B
  by_cases hc : j ∉ B ∧ A = insert j B
  · rcases hc with ⟨hj, rfl⟩
    simp [creator, annihilator_apply, Matrix.conjTranspose_apply, hj, sign_insert_not_lt j j B (lt_irrefl j)]
  · have hd : ¬ (j ∈ A ∧ B = A.erase j) := by
      rintro ⟨hj, rfl⟩
      apply hc
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase hj).symm⟩
    simp [creator, annihilator, Matrix.conjTranspose_apply, hc, hd]

 
theorem annihilator_square (Q : ℕ) (j : Orbital Q) :
    annihilator Q j * annihilator Q j = 0 := by
  classical
  ext A B
  rw [mul_annihilator_apply]
  by_cases hj : j ∈ B <;> simp [annihilator, hj]

 
theorem annihilator_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * annihilator Q j + annihilator Q j * annihilator Q i = 0 := by
  classical
  by_cases hij : i=j
  · subst j; rw [annihilator_square]; simp
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_annihilator_apply]
  by_cases hi : i ∈ B
  · by_cases hj : j ∈ B
    · simp only [hi, hj, ite_true, if_true, annihilator_apply,
        Finset.mem_erase, ne_eq, hij, Ne.symm hij, not_false_eq_true, true_and, and_true]
      rw [Finset.erase_right_comm]
      by_cases hab : A = (B.erase i).erase j
      · simp only [hab, ite_true, if_true]
        rcases lt_or_gt_of_ne hij with hij | hji
        · rw [sign_erase_lt i j B hi hij,
            sign_erase_not_lt j i B (not_lt.mpr hij.le)]
          ring
        · rw [sign_erase_lt j i B hj hji,
            sign_erase_not_lt i j B (not_lt.mpr hji.le)]
          ring
      · simp [hab]
    · simp [hi, hj, annihilator, Finset.mem_erase]
  · simp [hi, annihilator, Finset.mem_erase]

 
theorem creator_mul_annihilator (Q : ℕ) (j : Orbital Q) :
    creator Q j * annihilator Q j =
      Matrix.diagonal (fun B : Occupation Q => if j ∈ B then (1 : ℂ) else 0) := by
  classical
  ext A B
  rw [mul_annihilator_apply]
  by_cases hAB : A = B
  · subst A
    by_cases hj : j ∈ B <;>
      simp [hj, creator,
        sign_erase_not_lt j j B (lt_irrefl j)]
  · by_cases hj : j ∈ B <;> simp [creator, hj, hAB]

 
theorem annihilator_mul_creator (Q : ℕ) (j : Orbital Q) :
    annihilator Q j * creator Q j =
      Matrix.diagonal (fun B : Occupation Q => if j ∈ B then (0 : ℂ) else 1) := by
  classical
  ext A B
  rw [mul_creator_apply]
  by_cases hAB : A = B
  · subst A
    by_cases hj : j ∈ B <;>
      simp [annihilator_apply, hj,
        sign_insert_not_lt j j B (lt_irrefl j)]
  · by_cases hj : j ∈ B <;> simp [annihilator_apply, hj, hAB]

 
theorem annihilator_creator_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * creator Q j + creator Q j * annihilator Q i =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, annihilator_mul_creator, creator_mul_annihilator]
    ext A B
    by_cases hi : i ∈ A <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hi]
  rw [ite_eq_right hij]
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_annihilator_apply, mul_creator_apply]
  by_cases hi : i ∈ B
  · by_cases hj : j ∈ B
    · simp [hi, hj, creator, Finset.mem_erase, Ne.symm hij]
    · simp only [hi, hj, not_false_eq_true, ite_true, if_true, annihilator_apply, creator,
        Finset.mem_insert, Finset.mem_erase, hij, Ne.symm hij, false_or,
        ne_eq, not_false_eq_true, true_and]
      have he : (insert j B).erase i = insert j (B.erase i) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert]
        by_cases hki : k=i <;> by_cases hkj : k=j <;> simp_all
      rw [he]
      by_cases hAB : A = insert j (B.erase i)
      · simp only [hAB, ite_true, if_true]
        rcases lt_or_gt_of_ne hij with hij | hji
        · rw [sign_insert_not_lt j i B (not_lt.mpr hij.le), sign_erase_lt i j B hi hij]
          ring
        · rw [sign_insert_lt j i B hj hji, sign_erase_not_lt i j B (not_lt.mpr hji.le)]
          ring
      · simp [hAB]
  · by_cases hj : j ∈ B <;> simp [hi, hj, annihilator_apply, hij]

 
theorem annihilator_adjoint_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * (annihilator Q j)ᴴ + (annihilator Q j)ᴴ * annihilator Q i =
      if i = j then 1 else 0 := by
  rw [← creator_eq_adjoint]
  exact annihilator_creator_anticommute Q i j

 

theorem annihilator_norm_sq (Q : ℕ) (j : Orbital Q) (ψ : Occupation Q → ℂ) :
    (∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2) =
      ∑ B : Occupation Q, if j ∈ B then ‖ψ B‖^2 else 0 := by
  classical
  have hg := congrArg Complex.re (gram_quadratic_form (annihilator Q j) ψ)
  rw [← creator_eq_adjoint, creator_mul_annihilator] at hg
  have hs : (star (annihilator Q j *ᵥ ψ) ⬝ᵥ (annihilator Q j *ᵥ ψ)).re =
      ∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2 := by
    simp [dotProduct, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]
  rw [hs] at hg
  rw [← hg]
  simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hj : j ∈ B <;>
    simp [hj, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]

 
theorem annihilator_contracts (Q : ℕ) (j : Orbital Q) (ψ : Occupation Q → ℂ) :
    (∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2) ≤
      ∑ B : Occupation Q, ‖ψ B‖^2 := by
  rw [annihilator_norm_sq]
  apply Finset.sum_le_sum
  intro B _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _



private theorem delta_comm (Q : ℕ) (i j : Orbital Q) (M : FockMatrix Q) :
    M * orbitalDelta Q i j = orbitalDelta Q i j * M := by
  classical
  by_cases hij : i=j <;> simp [orbitalDelta, hij]

private theorem annihilator_creator_swap (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * creator Q j =
      orbitalDelta Q i j - creator Q j * annihilator Q i :=
  eq_sub_of_add_eq (annihilator_creator_anticommute Q i j)

 

theorem pair_normal_order (Q : ℕ) (i j k l : Orbital Q) :
    (annihilator Q j * annihilator Q i) * (creator Q k * creator Q l) =
      orbitalDelta Q i k * orbitalDelta Q j l -
      orbitalDelta Q j k * orbitalDelta Q i l -
      orbitalDelta Q i k * creator Q l * annihilator Q j +
      orbitalDelta Q j k * creator Q l * annihilator Q i +
      orbitalDelta Q i l * creator Q k * annihilator Q j -
      orbitalDelta Q j l * creator Q k * annihilator Q i +
      creator Q k * creator Q l * annihilator Q j * annihilator Q i := by
  classical
  let I := annihilator Q i
  let J := annihilator Q j
  let K := creator Q k
  let L := creator Q l
  let E := orbitalDelta Q i k
  let F := orbitalDelta Q j k
  let G := orbitalDelta Q i l
  let H := orbitalDelta Q j l
  have hIK : I*K = E-K*I := annihilator_creator_swap Q i k
  have hJK : J*K = F-K*J := annihilator_creator_swap Q j k
  have hIL : I*L = G-L*I := annihilator_creator_swap Q i l
  have hJL : J*L = H-L*J := annihilator_creator_swap Q j l
  have hJE : J*E = E*J := delta_comm Q i k J
  have hKJG : (K*J)*G = G*(K*J) := delta_comm Q i l (K*J)
  have hKH : K*H = H*K := delta_comm Q j l K
  change (J*I)*(K*L) = E*H-F*G-E*L*J+F*L*I+G*K*J-H*K*I+K*L*J*I
  calc
    _ = J*(I*K)*L := by noncomm_ring
    _ = J*(E-K*I)*L := by rw [hIK]
    _ = J*E*L-(J*K)*(I*L) := by noncomm_ring
    _ = E*J*L-(F-K*J)*(G-L*I) := by rw [hJE, hJK, hIL]
    _ = E*(J*L)-(F-K*J)*(G-L*I) := by noncomm_ring
    _ = E*(H-L*J)-(F-K*J)*(G-L*I) := by rw [hJL]
    _ = E*H-F*G-E*L*J+F*L*I+(K*J)*G-K*(J*L)*I := by noncomm_ring
    _ = E*H-F*G-E*L*J+F*L*I+G*(K*J)-K*(H-L*J)*I := by rw [hKJG, hJL]
    _ = E*H-F*G-E*L*J+F*L*I+G*K*J-(K*H)*I+K*L*J*I := by noncomm_ring
    _ = _ := by rw [hKH]
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SphereScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sphere Scaling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology

theorem pairAnnihilator_eq_coefficientPairAnnihilator (Q p : ℕ) :
    pairAnnihilator Q p =
      coefficientPairAnnihilator Q (fun i j => (pairCoefficient Q p i j : ℂ)) := rfl


open Filter Topology


theorem scaledDescFactorial_succ {Q s p : ℕ} (hQ : 0 < Q) (hs : s ≤ Q)
    (hp : p ≤ Q-s) :
    scaledDescFactorial Q s (p+1) =
      (1 - ((s : ℝ)+p)/Q) * scaledDescFactorial Q s p := by
  unfold scaledDescFactorial
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hs,
    pow_succ', mul_div_mul_comm]
  congr 1
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  field_simp
  ring

theorem scaledDescFactorial_tendsto (s p : ℕ) :
    Tendsto (fun Q : ℕ => scaledDescFactorial Q s p) atTop (𝓝 1) := by
  induction p with
  | zero => simpa only [scaledDescFactorial, Nat.descFactorial_zero,
      Nat.cast_one, pow_zero, div_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | succ p ih =>
    have hf : Tendsto (fun Q : ℕ => 1 - ((s:ℝ)+p)/Q) atTop (𝓝 1) := by
      convert (tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((s:ℝ)+p)) using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    have ht := hf.mul ih
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (s+p+1)] with Q hQ
    exact (scaledDescFactorial_succ (by omega) (by omega) (by omega)).symm


theorem pairCoefficient_eq_sphericalPairCoefficient (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p i j = sphericalPairCoefficient Q p i.val j.val :=
  pairCoefficient_eq Q p i j

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Energy. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
theorem coefficientPairAnnihilator_smul (L : ℕ) (r : ℂ)
    (a : Orbital L → Orbital L → ℂ) :
    coefficientPairAnnihilator L (fun i j => r * a i j) =
      r • coefficientPairAnnihilator L a := by
  classical
  unfold coefficientPairAnnihilator
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [smul_smul]


theorem star_dotProduct_self {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖^2 : ℝ) : ℂ) := by
  simp [dotProduct, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow,
    Complex.ofReal_sum]

theorem row_isometry_gram_complement {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1) :
    (1 - Sᴴ * S).PosSemidef := by
  have hsq : (Sᴴ * S) * (Sᴴ * S) = Sᴴ * S := by
    calc
      _ = Sᴴ * (S * Sᴴ) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one]
  have heq : (1-Sᴴ*S)ᴴ * (1-Sᴴ*S) = 1-Sᴴ*S := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (Matrix.isHermitian_conjTranspose_mul_self S).eq]
    calc
      _ = 1 - Sᴴ*S - Sᴴ*S + (Sᴴ*S)*(Sᴴ*S) := by noncomm_ring
      _ = _ := by rw [hsq]; abel
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

 
theorem row_isometry_contracts {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1)
    (x : κ → ℂ) :
    (∑ i, ‖(S *ᵥ x) i‖^2) ≤ ∑ j, ‖x j‖^2 := by
  have h := Complex.re_le_re ((row_isometry_gram_complement S hS).dotProduct_mulVec_nonneg x)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, gram_quadratic_form,
    star_dotProduct_self, star_dotProduct_self, Complex.sub_re] at h
  simpa only [Complex.ofReal_re, Complex.zero_re, sub_nonneg] using h

 

theorem row_isometry_contracts_family {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Fintype α] [DecidableEq ι] [DecidableEq κ]
    (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1) (x : κ → α → ℂ) :
    (∑ i, ∑ a, ‖(∑ j, S i j * x j a)‖^2) ≤ ∑ j, ∑ a, ‖x j a‖^2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j a => ‖x j a‖^2)]
  exact Finset.sum_le_sum fun a _ => row_isometry_contracts S hS (fun j => x j a)


open Filter Topology

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Perturbation. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker


theorem stackFamily_kronecker {β ι κ : Type*} [Fintype β] [Fintype ι]
    (A : β → Matrix ι κ ℂ) (M : Matrix β β ℂ) (D : Matrix ι ι ℂ) :
    (stackFamily A)ᴴ * (M ⊗ₖ D) * stackFamily A =
      ∑ b, ∑ c, M b c • ((A b)ᴴ * D * A c) := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    stackFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring



theorem stackFamily_coupled {α β ι κ : Type*} [Fintype β] [Fintype ι]
    (A : β → Matrix ι κ ℂ) (S : Matrix α β ℂ) (D : Matrix ι ι ℂ) :
    stackFamily (fun r => D * (∑ b, S r b • A b)) = (S ⊗ₖ D) * stackFamily A := by
  ext ⟨r,i⟩ j
  simp only [stackFamily, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem stackFamily_mul {β ι κ ν : Type*} [Fintype κ]
    (A : β → Matrix ι κ ℂ) (D : Matrix κ ν ℂ) :
    stackFamily (fun r => A r * D) = stackFamily A * D := rfl

 

theorem quadratic_family_change {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : β → Matrix ι ι ℂ) (S : Matrix α β ℂ) (C : Matrix α α ℂ)
    (D J : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    (∑ r, ∑ s, C r s •
      ((J * (∑ b, S r b • A b) * D)ᴴ * (J * (∑ b, S s b • A b) * D))) =
    D * (∑ b, ∑ c, (Sᴴ * C * S) b c • (A b)ᴴ * (Jᴴ * J) * A c) * D := by
  let B : α → Matrix ι ι ℂ := fun r => J * (∑ b, S r b • A b) * D
  have hB : stackFamily B = (S ⊗ₖ J) * stackFamily A * D := by
    rw [show B = (fun r => (J * (∑ b, S r b • A b)) * D) from rfl,
      stackFamily_mul, stackFamily_coupled]
  have heq : (S ⊗ₖ J)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) * (S ⊗ₖ J) =
      (Sᴴ * C * S) ⊗ₖ (Jᴴ * J) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  calc
    _ = (stackFamily B)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) * stackFamily B := by
      simp only [stackFamily_kronecker, Matrix.mul_one, B]
    _ = D * ((stackFamily A)ᴴ * ((S ⊗ₖ J)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) *
        (S ⊗ₖ J)) * stackFamily A) * D := by
      rw [hB]
      simp only [Matrix.conjTranspose_mul, hD.eq, Matrix.mul_assoc]
    _ = _ := by
      rw [heq, stackFamily_kronecker]
      simp only [Matrix.smul_mul]



theorem quadratic_family_mix {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : β → Matrix ι ι ℂ) (S : Matrix α β ℂ) (C : Matrix α α ℂ) :
    (∑ r, ∑ s, C r s • ((∑ b, S r b • A b)ᴴ * (∑ b, S s b • A b))) =
      ∑ b, ∑ c, (Sᴴ * C * S) b c • ((A b)ᴴ * A c) := by
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.smul_mul]
    using quadratic_family_change A S C 1 1 Matrix.isHermitian_one


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators



theorem annihilatorList_entry_eq_zero (Q : ℕ) (js : List (Orbital Q))
    (A B : Occupation Q) (h : A.card + js.length ≠ B.card) :
    annihilatorList Q js A B = 0 := by
  induction js generalizing A B with
  | nil =>
    have hAB : A ≠ B := by intro hh; subst B; simp at h
    simp [hAB]
  | cons j js ih =>
    rw [annihilatorList_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro C _
    by_cases hCB : C.card + 1 = B.card
    · have hAC : A.card + js.length ≠ C.card := by simp only [List.length_cons] at h; omega
      rw [ih A C hAC, zero_mul]
    · rw [annihilator_entry_eq_zero _ _ _ hCB, mul_zero]

theorem basisAnnihilator_entry_eq_zero (Q : ℕ) (S A B : Occupation Q)
    (h : A.card + S.card ≠ B.card) : basisAnnihilator Q S A B = 0 := by
  apply annihilatorList_entry_eq_zero
  simpa only [Finset.length_sort] using h

theorem annihilatorList_vacuum (Q : ℕ) (js : List (Orbital Q))
    (hs : js.Pairwise (· ≤ ·)) (hd : js.Nodup) (A : Occupation Q) :
    annihilatorList Q js ∅ A = if js.toFinset = A then 1 else 0 := by
  induction js generalizing A with
  | nil => simp only [annihilatorList, Matrix.one_apply, List.toFinset_nil]; rfl
  | cons j js ih =>
    obtain ⟨hjs, hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨hjn, hd⟩ := List.nodup_cons.mp hd
    rw [annihilatorList_cons, mul_annihilator_apply]
    by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA, ih hs hd]
      by_cases he : js.toFinset = A.erase j
      · have heA : insert j js.toFinset = A := by rw [he, Finset.insert_erase hjA]
        have hfilter : A.filter (fun x => x < j) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          rw [← heA, Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact lt_irrefl _
          · exact not_lt_of_ge (hjs x (List.mem_toFinset.mp hx))
        simp only [ite_eq_left he, one_mul, fermionSign, hfilter, Finset.card_empty,
          pow_zero, List.toFinset_cons, ite_eq_left heA]
      · have hneA : insert j js.toFinset ≠ A := by
          intro h
          have hjnot : j ∉ js.toFinset := by simpa using hjn
          apply he
          rw [← h, Finset.erase_insert hjnot]
        simp only [ite_eq_right he, zero_mul, List.toFinset_cons, ite_eq_right hneA]
    · have hneA : insert j js.toFinset ≠ A := by
        intro h; apply hjA; rw [← h]; exact Finset.mem_insert_self _ _
      simp only [ite_eq_right hjA, List.toFinset_cons, ite_eq_right hneA]

 

theorem basisAnnihilator_vacuum (Q : ℕ) (S A : Occupation Q) :
    basisAnnihilator Q S ∅ A = if S=A then 1 else 0 := by
  simpa only [basisAnnihilator, Finset.sort_toFinset] using
    annihilatorList_vacuum Q (S.sort (· ≤ ·)) (S.pairwise_sort _) (S.sort_nodup _) A

theorem basisAnnihilator_same_sector (Q k : ℕ) (S A : SectorOccupation Q k)
    (R : Occupation Q) :
    basisAnnihilator Q S.val R A.val = if R=∅ then if S=A then 1 else 0 else 0 := by
  by_cases hR : R=∅
  · subst R
    rw [basisAnnihilator_vacuum]
    simp only [Subtype.val_inj, ite_true, if_true]
  · rw [ite_eq_right hR]
    apply basisAnnihilator_entry_eq_zero
    rw [S.property, A.property]
    have hcard : R.card ≠ 0 := fun h => hR (Finset.card_eq_zero.mp h)
    omega



theorem exteriorLift_posSemidef (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) (hM : M.PosSemidef) :
    (exteriorLift Q k M).PosSemidef := by
  let A : SectorOccupation Q k → FockMatrix Q := fun S => basisAnnihilator Q S.val
  have hK : (M ⊗ₖ (1 : FockMatrix Q)).PosSemidef := hM.kronecker Matrix.PosSemidef.one
  have h := hK.conjTranspose_mul_mul_same (stackFamily A)
  simpa only [stackFamily_kronecker, Matrix.mul_one, exteriorLift, A] using h

 

theorem exteriorLift_rankOne (Q k : ℕ) (v w : SectorOccupation Q k → ℂ) :
    exteriorLift Q k (Matrix.vecMulVec v (star w)) =
      (wedgeAnnihilator Q k v)ᴴ * wedgeAnnihilator Q k w := by
  unfold exteriorLift wedgeAnnihilator
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [mul_comm]

theorem basisAnnihilator_gram_same_sector (Q k : ℕ) (S T A B : SectorOccupation Q k) :
    ((basisAnnihilator Q S.val)ᴴ * basisAnnihilator Q T.val) A.val B.val =
      (if S=A then (1 : ℂ) else 0) * (if T=B then (1 : ℂ) else 0) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, basisAnnihilator_same_sector]
  rw [Finset.sum_eq_single ∅]
  · simp only [ite_true, if_true, apply_ite star, star_one, star_zero]
  · intro R _ hR
    simp only [ite_eq_right hR, star_zero, zero_mul]
  · simp

 
theorem exteriorLift_same_sector (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    (exteriorLift Q k M).submatrix Subtype.val Subtype.val = M := by
  classical
  apply Matrix.ext
  intro A B
  change exteriorLift Q k M A.val B.val = M A B
  simp only [exteriorLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    basisAnnihilator_gram_same_sector]
  simp [mul_ite]

 
theorem exteriorLift_below_sector (Q k n : ℕ) (hn : n < k)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    (exteriorLift Q k M).submatrix
      (Subtype.val : SectorOccupation Q n → Occupation Q)
      (Subtype.val : SectorOccupation Q n → Occupation Q) = 0 := by
  classical
  ext A B
  simp only [Matrix.submatrix_apply, exteriorLift, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro S _
  apply Finset.sum_eq_zero
  intro T _
  suffices hzero : (∑ R, star (basisAnnihilator Q S.val R A.val) *
      basisAnnihilator Q T.val R B.val) = 0 by rw [hzero, mul_zero]
  apply Finset.sum_eq_zero
  intro R _
  have h : basisAnnihilator Q T.val R B.val = 0 :=
    basisAnnihilator_entry_eq_zero Q _ _ _ (by rw [T.property, B.property]; omega)
  rw [h, mul_zero]

 

theorem annihilator_swap (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * annihilator Q j = -(annihilator Q j * annihilator Q i) :=
  eq_neg_of_add_eq_zero_left (annihilator_anticommute Q i j)

theorem annihilatorList_append (Q : ℕ) (is js : List (Orbital Q)) :
    annihilatorList Q (is ++ js) = annihilatorList Q js * annihilatorList Q is := by
  induction is with
  | nil => simp
  | cons i is ih => simp only [List.cons_append, annihilatorList_cons, ih, Matrix.mul_assoc]

 

theorem annihilatorList_perm (Q : ℕ) {is js : List (Orbital Q)} (h : is.Perm js) :
    ∃ c : ℂ, annihilatorList Q is = c • annihilatorList Q js := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons i h ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, by simp only [annihilatorList_cons, hc, Matrix.smul_mul]⟩
  | swap i j js =>
    refine ⟨-1, ?_⟩
    simp only [annihilatorList_cons, Matrix.mul_assoc, neg_one_smul]
    rw [annihilator_swap Q i j, Matrix.mul_neg]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨c, hc⟩ := ih₁
    obtain ⟨d, hd⟩ := ih₂
    exact ⟨c*d, by rw [hc, hd, smul_smul]⟩

theorem annihilatorList_mul_of_mem (Q : ℕ) (js : List (Orbital Q)) (i : Orbital Q)
    (hi : i ∈ js) : annihilatorList Q js * annihilator Q i = 0 := by
  induction js with
  | nil => simp at hi
  | cons j js ih =>
    rw [annihilatorList_cons, Matrix.mul_assoc]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [annihilator_square, Matrix.mul_zero]
    · rw [annihilator_swap Q j i, Matrix.mul_neg, ← Matrix.mul_assoc,
        ih hi, Matrix.zero_mul, neg_zero]

theorem annihilatorList_eq_zero_of_not_nodup (Q : ℕ) (js : List (Orbital Q))
    (h : ¬ js.Nodup) : annihilatorList Q js = 0 := by
  induction js with
  | nil => simp at h
  | cons i js ih =>
    rw [annihilatorList_cons]
    by_cases hi : i ∈ js
    · exact annihilatorList_mul_of_mem Q js i hi
    · have hjs : ¬ js.Nodup := by intro hj; exact h (List.nodup_cons.mpr ⟨hi,hj⟩)
      rw [ih hjs, Matrix.zero_mul]

 

theorem annihilatorList_expansion (Q : ℕ) (js : List (Orbital Q)) (k : ℕ)
    (hk : js.length=k) :
    annihilatorList Q js = ∑ S : SectorOccupation Q k,
      annihilatorList Q js ∅ S.val • basisAnnihilator Q S.val := by
  classical
  by_cases hd : js.Nodup
  · let T : SectorOccupation Q k := ⟨js.toFinset, by rw [List.toFinset_card_of_nodup hd, hk]⟩
    have hperm : js.Perm (js.toFinset.sort (· ≤ ·)) := by
      apply (List.perm_ext_iff_of_nodup hd (js.toFinset.sort_nodup _)).mpr
      intro i
      simp only [Finset.mem_sort, List.mem_toFinset]
    obtain ⟨c, hc⟩ := annihilatorList_perm Q hperm
    change annihilatorList Q js = c • basisAnnihilator Q T.val at hc
    rw [hc, Finset.sum_eq_single T]
    · simp only [Matrix.smul_apply, basisAnnihilator_vacuum, ite_true, if_true, smul_eq_mul, mul_one]
    · intro S _ hST
      have hne : T.val ≠ S.val := by
        intro hh; exact hST (Subtype.ext hh.symm)
      simp only [Matrix.smul_apply, basisAnnihilator_vacuum, ite_eq_right hne, smul_eq_mul,
        mul_zero, zero_smul]
    · simp
  · rw [annihilatorList_eq_zero_of_not_nodup Q js hd]
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

 

theorem exteriorLift_congruence {α : Type*} [Fintype α] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) α ℂ) (C : Matrix α α ℂ) :
    exteriorLift Q k (W * C * Wᴴ) =
      ∑ r, ∑ s, C r s •
        ((wedgeAnnihilator Q k (fun A => W A r))ᴴ *
          wedgeAnnihilator Q k (fun A => W A s)) := by
  classical
  have h := quadratic_family_mix (fun A : SectorOccupation Q k => basisAnnihilator Q A.val)
    Wᴴ C
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
    exteriorLift, wedgeAnnihilator] using h.symm



theorem basisAnnihilator_mem (Q k : ℕ) (S : SectorOccupation Q k) :
    basisAnnihilator Q S.val ∈ AnnihilationSpace Q k :=
  Submodule.subset_span ⟨S,rfl⟩

theorem annihilatorList_mem (Q : ℕ) (js : List (Orbital Q)) (k : ℕ) (hk : js.length=k) :
    annihilatorList Q js ∈ AnnihilationSpace Q k := by
  rw [annihilatorList_expansion Q js k hk]
  exact Submodule.sum_mem _ (fun S _ => Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S))

theorem annihilationSpace_normal_form (Q k : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    M = ∑ S : SectorOccupation Q k, M ∅ S.val • basisAnnihilator Q S.val := by
  classical
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨T,rfl⟩ := hM
    rw [Finset.sum_eq_single T]
    · simp only [basisAnnihilator_vacuum, ite_true, if_true, one_smul]
    · intro S _ hST
      have hne : T.val ≠ S.val := by intro h; exact hST (Subtype.ext h.symm)
      simp only [basisAnnihilator_vacuum, ite_eq_right hne, zero_smul]
    · simp
  | zero => simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
  | add M N hM hN ihM ihN =>
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← ihM, ← ihN]
  | smul r M hM ihM =>
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← ihM]

 
theorem annihilationSpace_ext (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k)
    (h : ∀ S : SectorOccupation Q k, M ∅ S.val = N ∅ S.val) : M=N := by
  rw [annihilationSpace_normal_form Q k M hM, annihilationSpace_normal_form Q k N hN]
  simp only [h]

 

theorem annihilationSpace_mul (Q k l : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q l) :
    N * M ∈ AnnihilationSpace Q (k+l) := by
  classical
  rw [annihilationSpace_normal_form Q k M hM, annihilationSpace_normal_form Q l N hN]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Submodule.sum_mem
  intro T _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  rw [basisAnnihilator, basisAnnihilator, ← annihilatorList_append]
  apply annihilatorList_mem
  simp only [List.length_append, Finset.length_sort, S.property, T.property]

theorem annihilator_mem (Q : ℕ) (j : Orbital Q) :
    annihilator Q j ∈ AnnihilationSpace Q 1 := by
  simpa only [annihilatorList_cons, annihilatorList_nil, Matrix.one_mul] using
    annihilatorList_mem Q [j] 1 rfl

theorem coefficientPairAnnihilator_mem (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a ∈ AnnihilationSpace Q 2 := by
  classical
  unfold coefficientPairAnnihilator
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  split_ifs
  · apply Submodule.smul_mem
    exact annihilationSpace_mul Q 1 1 (annihilator_mem Q i) (annihilator_mem Q j)
  · exact Submodule.zero_mem _

theorem pairAnnihilator_mem (Q p : ℕ) :
    pairAnnihilator Q p ∈ AnnihilationSpace Q 2 :=
  coefficientPairAnnihilator_mem Q _

theorem wedgeAnnihilator_mem (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k v ∈ AnnihilationSpace Q k := by
  exact Submodule.sum_mem _ (fun S _ =>
    Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S))

theorem wedgeAnnihilator_annihilatorVector (Q k : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    wedgeAnnihilator Q k (annihilatorVector Q k M) = M := by
  have h := annihilationSpace_normal_form Q k M hM
  simpa only [wedgeAnnihilator, annihilatorVector, star_star] using h.symm

 

theorem exteriorLift_annihilator_product (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k) :
    exteriorLift Q k (Matrix.vecMulVec (annihilatorVector Q k M)
      (star (annihilatorVector Q k N))) = Mᴴ * N := by
  rw [exteriorLift_rankOne, wedgeAnnihilator_annihilatorVector Q k M hM,
    wedgeAnnihilator_annihilatorVector Q k N hN]


theorem bodySpace_product (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k) :
    Mᴴ*N ∈ BodySpace Q k :=
  ⟨_, exteriorLift_annihilator_product Q k hM hN⟩

theorem bodySpace_reconstruct (Q k : ℕ) {M : FockMatrix Q} (hM : M ∈ BodySpace Q k) :
    exteriorLift Q k (M.submatrix
      (Subtype.val : SectorOccupation Q k → Occupation Q) Subtype.val) = M := by
  obtain ⟨A,rfl⟩ := hM
  exact congrArg (exteriorLift Q k) (exteriorLift_same_sector Q k A)

theorem bodySpace_below_sector (Q k n : ℕ) (hn : n < k)
    {M : FockMatrix Q} (hM : M ∈ BodySpace Q k) :
    M.submatrix (Subtype.val : SectorOccupation Q n → Occupation Q)
      (Subtype.val : SectorOccupation Q n → Occupation Q) = 0 := by
  obtain ⟨A,rfl⟩ := hM
  exact exteriorLift_below_sector Q k n hn A



theorem annihilator_commutes_pair (Q : ℕ) (i j k : Orbital Q) :
    annihilator Q k * (annihilator Q j * annihilator Q i) =
      (annihilator Q j * annihilator Q i) * annihilator Q k := by
  rw [← Matrix.mul_assoc, annihilator_swap Q k j, Matrix.neg_mul,
    Matrix.mul_assoc, annihilator_swap Q k i, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc]

theorem annihilator_commutes_coefficientPair (Q : ℕ)
    (a : Orbital Q → Orbital Q → ℂ) (k : Orbital Q) :
    annihilator Q k * coefficientPairAnnihilator Q a =
      coefficientPairAnnihilator Q a * annihilator Q k := by
  classical
  unfold coefficientPairAnnihilator
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [Matrix.mul_smul, Matrix.smul_mul, annihilator_commutes_pair]
  · simp

theorem coefficientPairs_commute (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a * coefficientPairAnnihilator Q b =
      coefficientPairAnnihilator Q b * coefficientPairAnnihilator Q a := by
  classical
  conv_lhs => lhs; unfold coefficientPairAnnihilator
  conv_rhs => rhs; unfold coefficientPairAnnihilator
  simp only [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_assoc, annihilator_commutes_coefficientPair,
      ← Matrix.mul_assoc, annihilator_commutes_coefficientPair, Matrix.mul_assoc]
  · simp

theorem pairAnnihilators_commute (Q p r : ℕ) :
    pairAnnihilator Q p * pairAnnihilator Q r =
      pairAnnihilator Q r * pairAnnihilator Q p :=
  coefficientPairs_commute Q _ _

 

theorem annihilationSpace_two_induction (Q : ℕ) (P : FockMatrix Q → Prop)
    (hzero : P 0)
    (hadd : ∀ M N, P M → P N → P (M+N))
    (hsmul : ∀ (c : ℂ) M, P M → P (c • M))
    (hpair : ∀ i j : Orbital Q, P (annihilator Q j * annihilator Q i))
    {M : FockMatrix Q} (hM : M ∈ AnnihilationSpace Q 2) : P M := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨S,rfl⟩ := hM
    have hlen : (S.val.sort (· ≤ ·)).length = 2 := by rw [Finset.length_sort, S.property]
    obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hlen
    simpa only [basisAnnihilator, hij, annihilatorList_cons, annihilatorList_nil,
      Matrix.one_mul] using hpair i j
  | zero => exact hzero
  | add M N _ _ ihM ihN => exact hadd M N ihM ihN
  | smul c M _ ihM => exact hsmul c M ihM

 

theorem pair_monomial_commutator_bodies (Q : ℕ) (i j k l : Orbital Q)
    {M N : FockMatrix Q} (hM : M ∈ AnnihilationSpace Q 2)
    (hN : N ∈ AnnihilationSpace Q 2) :
    Mᴴ * ((annihilator Q j * annihilator Q i) *
        (annihilator Q l * annihilator Q k)ᴴ -
      (annihilator Q l * annihilator Q k)ᴴ *
        (annihilator Q j * annihilator Q i)) * N ∈
      BodySpace Q 2 ⊔ BodySpace Q 3 := by
  let S := BodySpace Q 2 ⊔ BodySpace Q 3
  have htwo : Mᴴ * N ∈ S := Submodule.mem_sup_left (bodySpace_product Q 2 hM hN)
  have hthree (a b : Orbital Q) : Mᴴ * creator Q a * annihilator Q b * N ∈ S := by
    have h := bodySpace_product Q 3
      (annihilationSpace_mul Q 2 1 hM (annihilator_mem Q a))
      (annihilationSpace_mul Q 2 1 hN (annihilator_mem Q b))
    apply Submodule.mem_sup_right
    simpa only [Matrix.conjTranspose_mul, ← creator_eq_adjoint, Matrix.mul_assoc] using h
  have hδtwo (a b c d : Orbital Q) :
      Mᴴ * (orbitalDelta Q a b * orbitalDelta Q c d) * N ∈ S := by
    classical
    by_cases hab : a=b
    · by_cases hcd : c=d
      · simpa only [orbitalDelta, ite_eq_left hab, ite_eq_left hcd, Matrix.one_mul,
          Matrix.mul_one] using htwo
      · simp [orbitalDelta, hab, hcd, S]
    · simp [orbitalDelta, hab, S]
  have hδthree (a b c d : Orbital Q) :
      Mᴴ * (orbitalDelta Q a b * creator Q c * annihilator Q d) * N ∈ S := by
    classical
    by_cases hab : a=b
    · simpa only [orbitalDelta, ite_eq_left hab, Matrix.one_mul, Matrix.mul_assoc] using hthree c d
    · simp only [orbitalDelta, ite_eq_right hab, Matrix.zero_mul, Matrix.mul_zero]
      exact Submodule.zero_mem _
  have hmiddle := pair_normal_order Q i j k l
  have heq : Mᴴ * ((annihilator Q j * annihilator Q i) *
        (annihilator Q l * annihilator Q k)ᴴ -
      (annihilator Q l * annihilator Q k)ᴴ *
        (annihilator Q j * annihilator Q i)) * N =
      (Mᴴ * (orbitalDelta Q i k * orbitalDelta Q j l) * N -
        Mᴴ * (orbitalDelta Q j k * orbitalDelta Q i l) * N) -
        Mᴴ * (orbitalDelta Q i k * creator Q l * annihilator Q j) * N +
        Mᴴ * (orbitalDelta Q j k * creator Q l * annihilator Q i) * N +
        Mᴴ * (orbitalDelta Q i l * creator Q k * annihilator Q j) * N -
        Mᴴ * (orbitalDelta Q j l * creator Q k * annihilator Q i) * N := by
    rw [Matrix.conjTranspose_mul, ← creator_eq_adjoint, ← creator_eq_adjoint, hmiddle]
    noncomm_ring
  rw [heq]
  exact S.sub_mem (S.add_mem (S.add_mem
    (S.sub_mem (S.sub_mem (hδtwo _ _ _ _) (hδtwo _ _ _ _)) (hδthree _ _ _ _))
      (hδthree _ _ _ _)) (hδthree _ _ _ _)) (hδthree _ _ _ _)

 

theorem pair_commutator_bodies (Q : ℕ) {M N P R : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q 2) (hN : N ∈ AnnihilationSpace Q 2)
    (hP : P ∈ AnnihilationSpace Q 2) (hR : R ∈ AnnihilationSpace Q 2) :
    Mᴴ * (P*Rᴴ-Rᴴ*P) * N ∈ BodySpace Q 2 ⊔ BodySpace Q 3 := by
  let S := BodySpace Q 2 ⊔ BodySpace Q 3
  refine annihilationSpace_two_induction Q
    (fun P => ∀ R, R ∈ AnnihilationSpace Q 2 → Mᴴ * (P*Rᴴ-Rᴴ*P) * N ∈ S)
    ?_ ?_ ?_ ?_ hP R hR
  · intro R _
    simpa only [Matrix.zero_mul, Matrix.mul_zero, sub_self] using S.zero_mem
  · intro P P' hP hP' R hR
    have heq : Mᴴ * ((P+P')*Rᴴ-Rᴴ*(P+P')) * N =
        Mᴴ*(P*Rᴴ-Rᴴ*P)*N + Mᴴ*(P'*Rᴴ-Rᴴ*P')*N := by noncomm_ring
    rw [heq]
    exact S.add_mem (hP R hR) (hP' R hR)
  · intro c P hP R hR
    simpa only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub] using
      S.smul_mem c (hP R hR)
  · intro i j R hR
    refine annihilationSpace_two_induction Q
      (fun R => Mᴴ * ((annihilator Q j * annihilator Q i)*Rᴴ -
        Rᴴ*(annihilator Q j * annihilator Q i)) * N ∈ S) ?_ ?_ ?_ ?_ hR
    · simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
        sub_self] using S.zero_mem
    · intro R R' hR hR'
      rw [Matrix.conjTranspose_add]
      have heq : Mᴴ * ((annihilator Q j * annihilator Q i)*(Rᴴ+R'ᴴ) -
          (Rᴴ+R'ᴴ)*(annihilator Q j * annihilator Q i)) * N =
          Mᴴ*((annihilator Q j * annihilator Q i)*Rᴴ-Rᴴ*(annihilator Q j * annihilator Q i))*N +
          Mᴴ*((annihilator Q j * annihilator Q i)*R'ᴴ-R'ᴴ*(annihilator Q j * annihilator Q i))*N :=
        by noncomm_ring
      rw [heq]
      exact S.add_mem hR hR'
    · intro c R hR
      simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_sub] using S.smul_mem (star c) hR
    · intro k l
      exact pair_monomial_commutator_bodies Q i j k l hM hN



theorem hamiltonian_mem_bodySpace (Q : ℕ) : hamiltonian Q ∈ BodySpace Q 2 :=
  Submodule.sum_mem _ (fun p _ => bodySpace_product Q 2
    (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q p))

theorem fourBodyTerm_mem_bodySpace (Q : ℕ) : fourBodyTerm Q ∈ BodySpace Q 4 := by
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  have h := annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q r) (pairAnnihilator_mem Q p)
  exact bodySpace_product Q 4 h h

theorem square_remainder_commutators (Q : ℕ) :
    hamiltonian Q * hamiltonian Q - fourBodyTerm Q =
      ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
        (pairAnnihilator Q p)ᴴ *
          (pairAnnihilator Q p * (pairAnnihilator Q r)ᴴ -
            (pairAnnihilator Q r)ᴴ * pairAnnihilator Q p) * pairAnnihilator Q r := by
  classical
  have hsquare : hamiltonian Q * hamiltonian Q =
      ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
        ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) *
          ((pairAnnihilator Q r)ᴴ * pairAnnihilator Q r) := by
    simp only [hamiltonian, Matrix.sum_mul, Matrix.mul_sum]
    exact Finset.sum_comm
  rw [hsquare, fourBodyTerm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [pairAnnihilators_commute Q p r, Matrix.conjTranspose_mul]
  have hc := pairAnnihilators_commute Q r p
  rw [hc]
  noncomm_ring

theorem square_remainder_mem_bodies (Q : ℕ) :
    hamiltonian Q * hamiltonian Q - fourBodyTerm Q ∈ BodySpace Q 2 ⊔ BodySpace Q 3 := by
  rw [square_remainder_commutators]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  exact pair_commutator_bodies Q (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q r)
    (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q r)

 

theorem normal_square_of_pair_projection (Q : ℕ)
    (hproj : sectorHamiltonian Q 2 * sectorHamiltonian Q 2 = sectorHamiltonian Q 2) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) +
        fourBodyTerm Q := by
  obtain ⟨A,hA,B,hB,hAB⟩ := Submodule.mem_sup.mp (square_remainder_mem_bodies Q)
  have hF2 := bodySpace_below_sector Q 4 2 (by omega) (fourBodyTerm_mem_bodySpace Q)
  have hF3 := bodySpace_below_sector Q 4 3 (by omega) (fourBodyTerm_mem_bodySpace Q)
  have hB2 := bodySpace_below_sector Q 3 2 (by omega) hB
  have hA2 : A.submatrix (Subtype.val : SectorOccupation Q 2 → Occupation Q) Subtype.val =
      sectorHamiltonian Q 2 := by
    have h := congrArg (fun X : FockMatrix Q => X.submatrix
      (Subtype.val : SectorOccupation Q 2 → Occupation Q)
      (Subtype.val : SectorOccupation Q 2 → Occupation Q)) hAB
    simp only [Matrix.submatrix_add, Matrix.submatrix_sub, Pi.add_apply, Pi.sub_apply,
      hB2, hF2, add_zero, sub_zero, sectorHamiltonian_square, hproj] at h
    exact h
  have hAH : A=hamiltonian Q := by
    rw [← bodySpace_reconstruct Q 2 hA, hA2]
    exact bodySpace_reconstruct Q 2 (hamiltonian_mem_bodySpace Q)
  have hB3 : B.submatrix (Subtype.val : SectorOccupation Q 3 → Occupation Q) Subtype.val =
      sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3 := by
    have h := congrArg (fun X : FockMatrix Q => X.submatrix
      (Subtype.val : SectorOccupation Q 3 → Occupation Q)
      (Subtype.val : SectorOccupation Q 3 → Occupation Q)) hAB
    simp only [hAH, Matrix.submatrix_add, Matrix.submatrix_sub, Pi.add_apply, Pi.sub_apply,
      hF3, sub_zero, sectorHamiltonian_square] at h
    change sectorHamiltonian Q 3 + _ = _ at h
    exact eq_sub_of_add_eq' h
  have hBform : B = exteriorLift Q 3
      (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) := by
    rw [← hB3]
    exact (bodySpace_reconstruct Q 3 hB).symm
  rw [hAH,hBform] at hAB
  exact (eq_sub_iff_add_eq.mp hAB).symm


theorem increasingPair_sum {X : Type*} [AddCommMonoid X] (Q : ℕ)
    (f : Orbital Q → Orbital Q → X) :
    (∑ ij : IncreasingPair Q, f ij.val.1 ij.val.2) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, if i<j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun ij : Orbital Q × Orbital Q => ij.1 < ij.2)) (by intro ij; simp)
      (fun ij : Orbital Q × Orbital Q => f ij.1 ij.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem basisAnnihilator_pair {Q : ℕ} (i j : Orbital Q) (hij : i<j) :
    basisAnnihilator Q {i,j} = annihilator Q j * annihilator Q i := by
  simp only [basisAnnihilator, sort_pair i j hij, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem coefficientPair_basis_expansion (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
      a ij.val.1 ij.val.2 • basisAnnihilator Q (increasingPairSector Q ij).val := by
  change coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
    a ij.val.1 ij.val.2 • basisAnnihilator Q {ij.val.1,ij.val.2}
  rw [increasingPair_sum Q (fun i j => a i j • basisAnnihilator Q {i,j})]
  unfold coefficientPairAnnihilator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [basisAnnihilator_pair i j hij]
  · rfl

theorem coefficientPair_vacuum (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ)
    (ij : IncreasingPair Q) :
    coefficientPairAnnihilator Q a ∅ (increasingPairSector Q ij).val = a ij.val.1 ij.val.2 := by
  classical
  rw [coefficientPair_basis_expansion]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, basisAnnihilator_vacuum,
    Subtype.val_inj, (increasingPairSector_injective Q).eq_iff]
  simp



theorem pairVector_increasing (Q p : ℕ) (ij : IncreasingPair Q) :
    pairVector Q p (increasingPairSector Q ij) = pairCoefficient Q p ij.val.1 ij.val.2 := by
  unfold pairVector annihilatorVector
  change star (coefficientPairAnnihilator Q
    (fun i j => (pairCoefficient Q p i j : ℂ)) ∅ (increasingPairSector Q ij).val) = _
  rw [coefficientPair_vacuum]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem pairVector_orthonormal (Q p r : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ S : SectorOccupation Q 2, star (pairVector Q p S) * pairVector Q r S) =
      if p=r then 1 else 0 := by
  classical
  have hs : (∑ S : SectorOccupation Q 2, star (pairVector Q p S) * pairVector Q r S) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, if i<j then
        (pairCoefficient Q p i j : ℂ) * (pairCoefficient Q r i j : ℂ) else 0 := by
    rw [← (increasingPairEquiv Q).sum_comp
      (fun S => star (pairVector Q p S) * pairVector Q r S)]
    simp only [increasingPairEquiv_apply, pairVector_increasing,
      Complex.star_def, Complex.conj_ofReal]
    exact increasingPair_sum Q (fun i j =>
      (pairCoefficient Q p i j : ℂ) * (pairCoefficient Q r i j : ℂ))
  rw [hs]
  by_cases hpr : p=r
  · subst r
    simp only [ite_true, if_true]
    have h := congrArg (fun x : ℝ => (x : ℂ)) (pairCoefficient_norm Q p hQ hp)
    simpa only [Complex.ofReal_sum, Complex.ofReal_one, Complex.ofReal_pow,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero, pow_two, Complex.ofReal_mul] using h
  · rw [ite_eq_right hpr]
    have h := congrArg (fun x : ℝ => (x : ℂ)) (pairCoefficient_orthogonal Q p r hpr)
    simpa only [Complex.ofReal_sum, Complex.ofReal_zero, Complex.ofReal_mul,
      apply_ite (fun x : ℝ => (x : ℂ))] using h

theorem pairWedgeMatrix_gram (Q : ℕ) (hQ : 1 ≤ Q) :
    (pairWedgeMatrix Q)ᴴ * pairWedgeMatrix Q = 1 := by
  classical
  ext p r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pairWedgeMatrix,
    pairVector_orthonormal Q p.val r.val hQ (by have := p.isLt; omega), Matrix.one_apply,
    Fin.val_inj]

theorem hamiltonian_exteriorLift (Q : ℕ) :
    exteriorLift Q 2 (pairWedgeMatrix Q * (pairWedgeMatrix Q)ᴴ) = hamiltonian Q := by
  have h := exteriorLift_congruence Q 2 (pairWedgeMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true] at h
  rw [h]
  simp only [pairWedgeMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
  exact Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) _

theorem sectorHamiltonian_two (Q : ℕ) :
    sectorHamiltonian Q 2 = pairWedgeMatrix Q * (pairWedgeMatrix Q)ᴴ := by
  rw [sectorHamiltonian, ← hamiltonian_exteriorLift]
  exact exteriorLift_same_sector Q 2 _

 

theorem sectorHamiltonian_two_projection (Q : ℕ) (hQ : 1 ≤ Q) :
    sectorHamiltonian Q 2 * sectorHamiltonian Q 2 = sectorHamiltonian Q 2 := by
  rw [sectorHamiltonian_two]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (pairWedgeMatrix Q)ᴴ,
    pairWedgeMatrix_gram Q hQ, Matrix.one_mul]

 

theorem normal_square (Q : ℕ) (hQ : 1 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) +
        fourBodyTerm Q :=
  normal_square_of_pair_projection Q (sectorHamiltonian_two_projection Q hQ)


theorem basisAnnihilator_singleton (Q : ℕ) (j : Orbital Q) :
    basisAnnihilator Q {j} = annihilator Q j := by
  simp only [basisAnnihilator, Finset.sort_singleton, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem annihilator_vacuum (Q : ℕ) (j : Orbital Q) (A : Occupation Q) :
    annihilator Q j ∅ A = if {j}=A then 1 else 0 := by
  rw [← basisAnnihilator_singleton, basisAnnihilator_vacuum]

theorem annihilator_mul_vacuum (Q : ℕ) (j : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (annihilator Q j * M) ∅ A = M {j} A := by
  classical
  simp only [Matrix.mul_apply, annihilator_vacuum, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem sum_singleton_support {X : Type*} [AddCommMonoid X] (Q : ℕ)
    (f : Occupation Q → X) (hf : ∀ A, A.card ≠ 1 → f A=0) :
    ∑ A, f A = ∑ j : Orbital Q, f {j} := by
  classical
  calc
    _ = ∑ A ∈ Finset.univ.filter (fun A : Occupation Q => A.card=1), f A := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      exact hf A (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hA)
    _ = ∑ A : SectorOccupation Q 1, f A.val := Finset.sum_subtype _ (by intro A; simp) _
    _ = _ := (singletonSectorEquiv Q).sum_comp (fun A => f A.val) |>.symm

theorem threeWedgeMatrix_apply (Q : ℕ) (S : SectorOccupation Q 3)
    (pj : PairLabel Q × Orbital Q) :
    threeWedgeMatrix Q S pj = star (pairAnnihilator Q pj.1.val {pj.2} S.val) := by
  exact congrArg star (annihilator_mul_vacuum Q pj.2 (pairAnnihilator Q pj.1.val) S.val)

 

theorem sectorHamiltonian_three (Q : ℕ) :
    sectorHamiltonian Q 3 = threeWedgeMatrix Q * (threeWedgeMatrix Q)ᴴ := by
  classical
  ext A B
  change hamiltonian Q A.val B.val = _
  simp only [hamiltonian, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    threeWedgeMatrix_apply, star_star, Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun p => ∑ j : Orbital Q,
    star (pairAnnihilator Q p {j} A.val) * pairAnnihilator Q p {j} B.val)]
  apply Finset.sum_congr rfl
  intro p _
  apply sum_singleton_support
  intro C hC
  have hc : C.card + 2 ≠ B.val.card := by rw [B.property]; omega
  rw [pairAnnihilator_entry_eq_zero p C B.val hc, mul_zero]

 

theorem fourBodyTerm_exteriorLift (Q : ℕ) :
    exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) = fourBodyTerm Q := by
  have h := exteriorLift_congruence Q 4 (fourWedgeMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true] at h
  rw [h]
  simp only [fourWedgeMatrix, wedgeAnnihilator_annihilatorVector Q 4 _
    (annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q _) (pairAnnihilator_mem Q _)),
    Fintype.sum_prod_type]
  simp_rw [pairAnnihilators_commute Q]
  rw [Fin.sum_univ_eq_sum_range (fun p => ∑ r : PairLabel Q,
    (pairAnnihilator Q p * pairAnnihilator Q r.val)ᴴ *
      (pairAnnihilator Q p * pairAnnihilator Q r.val))]
  unfold fourBodyTerm
  apply Finset.sum_congr rfl
  intro p _
  exact Fin.sum_univ_eq_sum_range (fun r =>
    (pairAnnihilator Q p * pairAnnihilator Q r)ᴴ * (pairAnnihilator Q p * pairAnnihilator Q r)) _

 

theorem normal_ordered_square (Q : ℕ) (hQ : 1 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (threeWedgeMatrix Q *
        ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1) * (threeWedgeMatrix Q)ᴴ) +
      exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  rw [fourBodyTerm_exteriorLift, normal_square Q hQ, sectorHamiltonian_three]
  congr 2
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PositiveIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Integrals. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators Matrix.Norms.Elementwise
open MeasureTheory


attribute [local instance] OAI.LaughlinFock.instContinuousENormMatrixComplexOfFintype_solutions
theorem matrixIntegral_apply {G ι κ : Type*} [MeasurableSpace G] [Fintype ι] [Fintype κ]
    (μ : Measure G) {M : G → Matrix ι κ ℂ} (hM : Integrable M μ) (i : ι) (j : κ) :
    (∫ g, M g ∂μ) i j = ∫ g, M g i j ∂μ := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (L.toContinuousLinearMap.integral_comp_comm hM).symm

 

theorem matrixIntegral_isHermitian {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ)
    (hH : ∀ᵐ g ∂μ, (M g).IsHermitian) : (∫ g, M g ∂μ).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [matrixIntegral_apply μ hM, RCLike.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hH] with g hg
  exact Matrix.IsHermitian.ext_iff.mp hg i j

theorem quadraticEvaluation_integral {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ) (x : ι → ℂ) :
    star x ⬝ᵥ ((∫ g, M g ∂μ) *ᵥ x) = ∫ g, star x ⬝ᵥ (M g *ᵥ x) ∂μ :=
  (LinearMap.toContinuousLinearMap (quadraticEvaluation x)).integral_comp_comm hM |>.symm

 

theorem matrixIntegral_posSemidef {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ)
    (hP : ∀ᵐ g ∂μ, (M g).PosSemidef) : (∫ g, M g ∂μ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (matrixIntegral_isHermitian μ hM (hP.mono (fun _ h => h.isHermitian)))
  intro x
  rw [quadraticEvaluation_integral μ hM]
  apply integral_nonneg_of_ae
  exact hP.mono (fun _ h => h.dotProduct_mulVec_nonneg x)



theorem conjugationIntegral_posSemidef {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) (U : G → Matrix ι ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (∫ g, U g * M * (U g)ᴴ ∂μ).PosSemidef :=
  matrixIntegral_posSemidef μ hI (Filter.Eventually.of_forall
    (fun g => hM.mul_mul_conjTranspose_same (U g)))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_AveragedOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Operators. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder BigOperators
open MeasureTheory


attribute [local instance] OAI.LaughlinFock.averagedOperatorsContinuousENorm
theorem matrixIntegral_mul_left_right {G ι κ α β : Type*}
    [MeasurableSpace G] [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (μ : Measure G) {M : G → Matrix ι κ ℂ} (hM : Integrable M μ)
    (A : Matrix α ι ℂ) (B : Matrix κ β ℂ) :
    A * (∫ g, M g ∂μ) * B = ∫ g, A * M g * B ∂μ := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] Matrix α β ℂ :=
    { toFun := fun X => A * X * B
      map_add' _ _ := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' _ _ := by simp [Matrix.mul_smul, Matrix.smul_mul] }
  exact (L.toContinuousLinearMap.integral_comp_comm hM).symm

 
theorem matrixIntegral_trace {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ) :
    (∫ g, M g ∂μ).trace = ∫ g, (M g).trace ∂μ :=
  ((Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.integral_comp_comm hM).symm



theorem matrixConjugationAverage_posSemidef {G ι : Type*}
    [MeasurableSpace G] [Fintype ι] (μ : Measure G) (U : G → Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (matrixConjugationAverage μ U M).PosSemidef :=
  conjugationIntegral_posSemidef μ U M hM hI

 
theorem matrixConjugationAverage_invariant {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : G →* Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) (h : G) :
    U h * matrixConjugationAverage μ U M * (U h)ᴴ =
      matrixConjugationAverage μ U M := by
  unfold matrixConjugationAverage
  rw [matrixIntegral_mul_left_right μ hI]
  calc
    _ = ∫ g, U (h*g) * M * (U (h*g))ᴴ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun g => U g * M * (U g)ᴴ) h

 

theorem matrixConjugationAverage_commutes {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : G →* Matrix ι ι ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix ι ι ℂ)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) (h : G) :
    matrixConjugationAverage μ U M * U h = U h * matrixConjugationAverage μ U M := by
  have hv := congrArg (fun A => A * U h) (matrixConjugationAverage_invariant μ U M hI h)
  simpa only [Matrix.mul_assoc, hU, Matrix.mul_one] using hv.symm

 
theorem matrixConjugationAverage_trace {G ι : Type*}
    [MeasurableSpace G] [Fintype ι] [DecidableEq ι]
    (μ : Measure G) [IsProbabilityMeasure μ] (U : G → Matrix ι ι ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (M : Matrix ι ι ℂ)
    (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (matrixConjugationAverage μ U M).trace = M.trace := by
  rw [matrixConjugationAverage, matrixIntegral_trace μ hI]
  have ht (g : G) : (U g * M * (U g)ᴴ).trace = M.trace := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp only [ht, integral_const, probReal_univ, one_smul]


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeGram
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Gram. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem pair_creator_commutator (Q : ℕ) (i j k : Orbital Q) :
    (annihilator Q j * annihilator Q i) * creator Q k =
      creator Q k * (annihilator Q j * annihilator Q i) +
        (if i=k then annihilator Q j else 0) -
        (if j=k then annihilator Q i else 0) := by
  have hi := eq_sub_of_add_eq (annihilator_creator_anticommute Q i k)
  have hj := eq_sub_of_add_eq (annihilator_creator_anticommute Q j k)
  rw [Matrix.mul_assoc, hi, Matrix.mul_sub, ← Matrix.mul_assoc _ (creator Q k), hj]
  split_ifs <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.sub_mul] <;> noncomm_ring


theorem coefficientPair_creator_commutator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ)
    (ha : ∀ i j, a j i = -a i j) (k : Orbital Q) :
    coefficientPairAnnihilator Q a * creator Q k =
      creator Q k * coefficientPairAnnihilator Q a + pairPartialAnnihilator Q a k := by
  classical
  have hdiag : a k k = 0 := by have h := ha k k; linear_combination (1 / 2 : ℂ) * h
  have hsum : (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i<j then a i j • ((if i=k then annihilator Q j else 0) -
        (if j=k then annihilator Q i else 0)) else 0) = pairPartialAnnihilator Q a k := by
    have ht (i j : Orbital Q) :
        (if i<j then a i j • ((if i=k then annihilator Q j else 0) -
          (if j=k then annihilator Q i else 0)) else 0) =
        (if i=k then (if i<j then a i j • annihilator Q j else 0) else 0) -
        (if j=k then (if i<j then a i j • annihilator Q i else 0) else 0) := by
      split_ifs <;> simp only [smul_sub, smul_zero, smul_neg, zero_sub, sub_zero]
    simp only [ht, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j : Orbital Q =>
      if i=k then (if i<j then a i j • annihilator Q j else 0) else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, ← Finset.sum_sub_distrib]
    unfold pairPartialAnnihilator
    apply Finset.sum_congr rfl
    intro i _
    rcases lt_trichotomy k i with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le, ha k i]
  calc
    _ = creator Q k * coefficientPairAnnihilator Q a +
        ∑ i : Orbital Q, ∑ j : Orbital Q,
          if i<j then a i j • ((if i=k then annihilator Q j else 0) -
            (if j=k then annihilator Q i else 0)) else 0 := by
      unfold coefficientPairAnnihilator
      simp only [Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i<j
      · simp only [ite_eq_left hij, Matrix.smul_mul, Matrix.mul_smul, pair_creator_commutator]
        module
      · simp [hij]
    _ = _ := by rw [hsum]

 

theorem pairCoefficient_antisymm (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p j i = -pairCoefficient Q p i j := by
  simp only [pairCoefficient_eq, Nat.add_comm j.val i.val]
  split_ifs
  · have hs : ((Q.descFactorial j.val : ℝ)*(Q.descFactorial i.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(j.val.factorial : ℝ)*(i.val.factorial : ℝ)) =
      ((Q.descFactorial i.val : ℝ)*(Q.descFactorial j.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(i.val.factorial : ℝ)*(j.val.factorial : ℝ)) := by ring
    rw [hs]
    ring
  · simp

 
theorem annihilationSpace_entry_eq_zero (Q d : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q d) (A B : Occupation Q) (h : A.card+d ≠ B.card) :
    M A B = 0 := by
  classical
  rw [annihilationSpace_normal_form Q d M hM]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro S _
  rw [basisAnnihilator_entry_eq_zero Q S.val A B (by rwa [S.property]), mul_zero]

 

theorem annihilatorVector_gram (Q d : ℕ) (M N : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q d) :
    (∑ S : SectorOccupation Q d,
      star (annihilatorVector Q d M S) * annihilatorVector Q d N S) = (M*Nᴴ) ∅ ∅ := by
  classical
  simp only [annihilatorVector, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    _ = ∑ S ∈ Finset.univ.filter (fun S : Occupation Q => S.card=d), M ∅ S * star (N ∅ S) :=
      (Finset.sum_subtype _ (by intro S; simp) _).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S _ hS
      rw [annihilationSpace_entry_eq_zero Q d M hM ∅ S (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_empty, zero_add, eq_comm] using hS), zero_mul]

 
theorem creator_mul_vacuum_zero (Q : ℕ) (k : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (creator Q k * M) ∅ A = 0 := by
  classical
  have hz (B : Occupation Q) : creator Q k ∅ B = 0 := by
    apply ite_eq_right
    rintro ⟨_, h⟩
    have := congrArg (fun S : Occupation Q => k ∈ S) h
    simp at this
  simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero]

 
theorem mul_annihilator_vacuum_zero (Q : ℕ) (k : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (M * annihilator Q k) A ∅ = 0 := by
  rw [mul_annihilator_apply]
  simp

 
theorem annihilator_creator_vacuum (Q : ℕ) (i j : Orbital Q) :
    (annihilator Q i * creator Q j) ∅ ∅ = if i=j then 1 else 0 := by
  rw [annihilator_mul_vacuum]
  simp [creator, fermionSign]

 
theorem pairPartial_vacuum_gram (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ)
    (j k : Orbital Q) :
    (pairPartialAnnihilator Q a k * (pairPartialAnnihilator Q b j)ᴴ) ∅ ∅ =
      ∑ i, a k i * star (b j i) := by
  classical
  simp only [pairPartialAnnihilator, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← creator_eq_adjoint,
    annihilator_creator_vacuum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, mul_comm]

 

theorem coefficientTriple_vacuum_gram (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ)
    (ha : ∀ i j, a j i = -a i j) (hb : ∀ i j, b j i = -b i j)
    (j k : Orbital Q) :
    ((annihilator Q j * coefficientPairAnnihilator Q a) *
      (annihilator Q k * coefficientPairAnnihilator Q b)ᴴ) ∅ ∅ =
      (if j=k then (coefficientPairAnnihilator Q a * (coefficientPairAnnihilator Q b)ᴴ) ∅ ∅ else 0) -
        ∑ i, a k i * star (b j i) := by
  classical
  let M := coefficientPairAnnihilator Q a
  let N := coefficientPairAnnihilator Q b
  have hb' : annihilator Q j * Nᴴ = Nᴴ * annihilator Q j + (pairPartialAnnihilator Q b j)ᴴ := by
    have h := congrArg Matrix.conjTranspose (coefficientPair_creator_commutator Q b hb j)
    simpa only [creator_eq_adjoint, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose] using h
  have hex : (M * creator Q k * annihilator Q j * Nᴴ) ∅ ∅ =
      (pairPartialAnnihilator Q a k * (pairPartialAnnihilator Q b j)ᴴ) ∅ ∅ := by
    rw [show M * creator Q k = creator Q k * M + pairPartialAnnihilator Q a k from
      coefficientPair_creator_commutator Q a ha k]
    simp only [Matrix.add_mul, Matrix.add_apply]
    rw [Matrix.mul_assoc (creator Q k), Matrix.mul_assoc (creator Q k), creator_mul_vacuum_zero]
    rw [zero_add, Matrix.mul_assoc, hb', Matrix.mul_add, Matrix.add_apply,
      ← Matrix.mul_assoc _ Nᴴ, mul_annihilator_vacuum_zero, zero_add]
  have hJn : (annihilator Q k * N)ᴴ = creator Q k * Nᴴ := by
    rw [annihilator_commutes_coefficientPair, Matrix.conjTranspose_mul, ← creator_eq_adjoint]
  change ((annihilator Q j * M) * (annihilator Q k * N)ᴴ) ∅ ∅ = _
  rw [hJn, annihilator_commutes_coefficientPair, Matrix.mul_assoc M,
    ← Matrix.mul_assoc (annihilator Q j),
    eq_sub_of_add_eq (annihilator_creator_anticommute Q j k)]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply]
  rw [← Matrix.mul_assoc M (creator Q k * annihilator Q j),
    ← Matrix.mul_assoc M (creator Q k), hex, pairPartial_vacuum_gram]
  congr 1
  split_ifs <;> simp [M, N]

 
theorem threeWedgeMatrix_gram_apply (Q : ℕ) (hQ : 1 ≤ Q)
    (pj rk : PairLabel Q × Orbital Q) :
    ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) pj rk =
      (if pj=rk then 1 else 0) -
        ∑ i : Orbital Q, (pairCoefficient Q pj.1.val rk.2 i : ℂ) *
          (pairCoefficient Q rk.1.val pj.2 i : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, threeWedgeMatrix]
  rw [annihilatorVector_gram Q 3 _ _
    (annihilationSpace_mul Q 2 1 (pairAnnihilator_mem Q _)
      (annihilator_mem Q _))]
  have ha (p : ℕ) (i j : Orbital Q) :
      (pairCoefficient Q p j i : ℂ) = -(pairCoefficient Q p i j : ℂ) := by
    rw [pairCoefficient_antisymm, Complex.ofReal_neg]
  rw [pairAnnihilator_eq_coefficientPairAnnihilator,
    pairAnnihilator_eq_coefficientPairAnnihilator, coefficientTriple_vacuum_gram Q _ _ (ha _) (ha _)]
  simp only [Complex.star_def, Complex.conj_ofReal]
  simp only [← pairAnnihilator_eq_coefficientPairAnnihilator]
  rw [← annihilatorVector_gram Q 2 (pairAnnihilator Q pj.1.val) (pairAnnihilator Q rk.1.val)
    (pairAnnihilator_mem Q _)]
  change (if pj.2=rk.2 then
    (∑ S, star (pairVector Q pj.1.val S) * pairVector Q rk.1.val S) else 0) - _ = _
  rw [pairVector_orthonormal Q _ _ hQ (by have := pj.1.isLt; omega)]
  congr 1
  simp only [Prod.ext_iff, Fin.val_inj, ← ite_and, and_comm]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Covariance
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



theorem annihilator_oneBody_unit_commutator (Q : ℕ) (k i j : Orbital Q) :
    annihilator Q k * ((annihilator Q i)ᴴ * annihilator Q j) -
      ((annihilator Q i)ᴴ * annihilator Q j) * annihilator Q k =
        if k=i then annihilator Q j else 0 := by
  have h1 := congrArg (fun X : FockMatrix Q => X * annihilator Q j)
    (annihilator_adjoint_anticommute Q k i)
  have h2 := congrArg (fun X : FockMatrix Q => (annihilator Q i)ᴴ * X)
    (annihilator_anticommute Q k j)
  simp only [Matrix.add_mul, Matrix.mul_assoc, ite_mul, Matrix.one_mul,
    Matrix.zero_mul] at h1
  simp only [Matrix.mul_add, Matrix.mul_zero] at h2
  calc
    _ = annihilator Q k * ((annihilator Q i)ᴴ * annihilator Q j) +
          (annihilator Q i)ᴴ * (annihilator Q k * annihilator Q j) -
          ((annihilator Q i)ᴴ * (annihilator Q k * annihilator Q j) +
          (annihilator Q i)ᴴ * (annihilator Q j * annihilator Q k)) := by noncomm_ring
    _ = _ := by rw [h1, h2, sub_zero]

theorem annihilator_oneBody_commutator (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (k : Orbital Q) :
    annihilator Q k * oneBodyLift Q A - oneBodyLift Q A * annihilator Q k =
      ∑ j, A k j • annihilator Q j := by
  classical
  simp only [oneBodyLift, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  simp_rw [annihilator_oneBody_unit_commutator, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp


theorem matrix_commutator_mul {ι : Type*} [Fintype ι]
    (X Y Z : Matrix ι ι ℂ) :
    X * (Y*Z) - (Y*Z) * X =
      (X*Y-Y*X)*Z + Y*(X*Z-Z*X) := by noncomm_ring

 

theorem oneBody_annihilator_commutator_mem (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (j : Orbital Q) :
    oneBodyLift Q A * annihilator Q j - annihilator Q j * oneBodyLift Q A ∈
      AnnihilationSpace Q 1 := by
  rw [← neg_sub, annihilator_oneBody_commutator]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (annihilator_mem Q i)

theorem oneBody_annihilatorList_commutator_mem (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (js : List (Orbital Q)) :
    oneBodyLift Q A * annihilatorList Q js - annihilatorList Q js * oneBodyLift Q A ∈
      AnnihilationSpace Q js.length := by
  induction js with
  | nil => simp only [annihilatorList_nil, Matrix.mul_one, Matrix.one_mul, sub_self]; exact Submodule.zero_mem _
  | cons j js ih =>
    rw [annihilatorList_cons, matrix_commutator_mul]
    apply Submodule.add_mem
    · simpa only [List.length_cons, Nat.add_comm] using
        annihilationSpace_mul Q 1 js.length (annihilator_mem Q j) ih
    · simpa only [List.length_cons, Nat.add_comm] using
        annihilationSpace_mul Q 1 js.length
          (oneBody_annihilator_commutator_mem Q A j) (annihilatorList_mem Q js _ rfl)

theorem oneBody_annihilationSpace_commutator_mem (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    oneBodyLift Q A * M - M * oneBodyLift Q A ∈ AnnihilationSpace Q k := by
  rw [annihilationSpace_normal_form Q k M hM]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_sub_distrib, ← smul_sub]
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  have h := oneBody_annihilatorList_commutator_mem Q A (S.val.sort (· ≤ ·))
  simpa only [Finset.length_sort, S.property, basisAnnihilator] using h

 
theorem oneBodyLift_vacuum_row (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (S : Occupation Q) : oneBodyLift Q A ∅ S = 0 := by
  simp only [oneBodyLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← creator_eq_adjoint, creator_mul_vacuum_zero, mul_zero, Finset.sum_const_zero]



theorem oneBody_basis_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (T : SectorOccupation Q k) :
    oneBodyLift Q A * basisAnnihilator Q T.val -
      basisAnnihilator Q T.val * oneBodyLift Q A =
      -∑ S, sectorOneBody Q k A T S • basisAnnihilator Q S.val := by
  classical
  apply annihilationSpace_ext Q k
    (oneBody_annihilationSpace_commutator_mem Q k A _ (basisAnnihilator_mem Q k T))
    (Submodule.neg_mem _ (Submodule.sum_mem _ fun S _ =>
      Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S)))
  intro S
  simp only [Matrix.sub_apply, Matrix.mul_apply, oneBodyLift_vacuum_row,
    zero_mul, Finset.sum_const_zero, zero_sub, basisAnnihilator_vacuum,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Subtype.val_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  rfl

 
theorem oneBody_basisCreator_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (T : SectorOccupation Q k) :
    oneBodyLift Q A * (basisAnnihilator Q T.val)ᴴ -
      (basisAnnihilator Q T.val)ᴴ * oneBodyLift Q A =
      ∑ S, sectorOneBody Q k A S T • (basisAnnihilator Q S.val)ᴴ := by
  have h := congrArg Matrix.conjTranspose (oneBody_basis_commutator Q k Aᴴ T)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, oneBodyLift_adjoint,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul] at h
  rw [← neg_sub, h, neg_neg]
  congr 1
  funext S
  congr 1
  rw [← sectorOneBody_adjoint, Matrix.conjTranspose_apply, star_star]

 

theorem oneBody_wedgeAnnihilator_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (v : SectorOccupation Q k → ℂ) :
    oneBodyLift Q A * wedgeAnnihilator Q k v -
      wedgeAnnihilator Q k v * oneBodyLift Q A =
      -wedgeAnnihilator Q k ((sectorOneBody Q k A)ᴴ *ᵥ v) := by
  classical
  simp only [wedgeAnnihilator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub,
    oneBody_basis_commutator, smul_neg, Finset.sum_neg_distrib, Matrix.mulVec,
    dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul, star_star,
    Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

 

theorem oneBody_exteriorLift_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    oneBodyLift Q A * exteriorLift Q k M - exteriorLift Q k M * oneBodyLift Q A =
      exteriorLift Q k (sectorOneBody Q k A * M - M * sectorOneBody Q k A) := by
  classical
  let R := sectorOneBody Q k A
  let C (S T : SectorOccupation Q k) :=
    (basisAnnihilator Q S.val)ᴴ * basisAnnihilator Q T.val
  have hprod (S T : SectorOccupation Q k) :
      oneBodyLift Q A * C S T - C S T * oneBodyLift Q A =
        (∑ U, R U S • C U T) - ∑ U, R T U • C S U := by
    dsimp only [C]
    rw [matrix_commutator_mul, oneBody_basisCreator_commutator, oneBody_basis_commutator]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_neg,
      Matrix.mul_sum, Matrix.mul_smul, sub_eq_add_neg, R]
  have hleft : (∑ S, ∑ T, ∑ U, (M S T * R U S) • C U T) =
      exteriorLift Q k (R*M) := by
    unfold exteriorLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext T
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro S _
    rw [mul_comm]
  have hright : (∑ S, ∑ T, ∑ U, (M S T * R T U) • C S U) =
      exteriorLift Q k (M*R) := by
    unfold exteriorLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro S _
    exact Finset.sum_comm
  calc
    _ = ∑ S, ∑ T, M S T •
        (oneBodyLift Q A * C S T - C S T * oneBodyLift Q A) := by
      simp only [exteriorLift, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul, ← Finset.sum_sub_distrib, smul_sub, C]
    _ = exteriorLift Q k (R*M) - exteriorLift Q k (M*R) := by
      simp only [hprod, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
      rw [hleft, hright]
    _ = _ := ((exteriorLiftLinear Q k).map_sub (R*M) (M*R)).symm



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Flow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flow. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Operator ComplexConjugate ComplexOrder
open NormedSpace

 
theorem matrixExp_conjugation_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A M : Matrix ι ι ℂ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => exp (u • A) * M * exp (u • (-A)))
      (A * (exp (t • A) * M * exp (t • (-A))) -
        (exp (t • A) * M * exp (t • (-A))) * A) t := by
  have h := ((hasDerivAt_exp_smul_const' A t).mul_const M).mul
    (hasDerivAt_exp_smul_const (-A) t)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  noncomm_ring

 

theorem matrixExp_conjugation_naturality {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ)
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hL : ∀ M, L (X*M-M*X) = Y*L M-L M*Y)
    (M : Matrix ι ι ℂ) (t : ℂ) :
    L (exp (t • X) * M * exp (t • (-X))) =
      exp (t • Y) * L M * exp (t • (-Y)) := by
  let m (u : ℂ) := exp (u • X) * M * exp (u • (-X))
  let f (u : ℂ) := exp (u • (-Y)) * L (m u) * exp (u • Y)
  have hd (u : ℂ) : HasDerivAt f 0 u := by
    have hm : HasDerivAt (fun v => L (m v)) (Y*L (m u)-L (m u)*Y) u := by
      have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
        (matrixExp_conjugation_hasDerivAt X M u)
      change HasDerivAt (fun v => L (m v)) (L (X*m u-m u*X)) u at h
      rwa [hL] at h
    have h := ((hasDerivAt_exp_smul_const (-Y) u).mul hm).mul
      (hasDerivAt_exp_smul_const' Y u)
    simp only [Pi.mul_apply] at h
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    noncomm_ring
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  have he' : exp (t • (-Y)) * L (m t) * exp (t • Y) = L M := by
    simpa only [f, m, zero_smul, exp_zero, Matrix.one_mul, Matrix.mul_one] using he
  have hi₁ : exp (t • Y) * exp (t • (-Y)) = 1 := by
    have h := (exp_add_of_commute (Commute.refl (t • Y)).neg_right).symm
    simpa only [← smul_neg, ← smul_add, add_neg_cancel, smul_zero, exp_zero] using! h
  calc
    L (m t) = 1 * L (m t) * 1 := by simp
    _ = (exp (t • Y) * exp (t • (-Y))) * L (m t) *
          (exp (t • Y) * exp (t • (-Y))) := by rw [hi₁]
    _ = exp (t • Y) * (exp (t • (-Y)) * L (m t) * exp (t • Y)) *
          exp (t • (-Y)) := by noncomm_ring
    _ = _ := by rw [he']



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Rotations
attribute [-instance] _root_.OAI.LaughlinFock.rotationHaar_leftInvariant _root_.OAI.LaughlinFock.rotationHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

section Simultaneous
variable {J : Type*} (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]



section Closed
open scoped Matrix.Norms.Elementwise

 

theorem covarianceSubgroup_isClosed {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ) :
    IsClosed (covarianceSubgroup I L : Set (UnitaryFamily I)) := by
  have hL : Continuous L := L.toContinuousLinearMap.continuous
  change IsClosed {g : UnitaryFamily I | ∀ M,
    L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M)}
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro M
  apply isClosed_eq
  · apply hL.comp
    unfold unitaryConjugation
    fun_prop
  · unfold unitaryConjugation
    fun_prop

end Closed

end Simultaneous

section Flows
open scoped Matrix.Norms.Operator
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]


theorem rotationFlow_conjugation
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) (j : J)
    (M : Matrix (I j) (I j) ℂ) :
    unitaryConjugation (rotationFlow X hX s t j) M =
      exp ((t : ℂ) • X s j) * M * exp ((t : ℂ) • (-X s j)) := by
  unfold unitaryConjugation rotationFlow
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hX]
  simp



theorem rotationFlow_mem_group (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) :
    rotationFlow X hX s t ∈ rotationGroup X hX :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨(s,t), rfl⟩)

 

theorem rotationGroup_covariance (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ)
    (hL : ∀ s M, L (X s i * M - M * X s i) = X s j * L M - L M * X s j)
    (g : rotationGroup X hX) (M : Matrix (I i) (I i) ℂ) :
    L (unitaryConjugation (g.val i) M) = unitaryConjugation (g.val j) (L M) := by
  have hle : rotationGroup X hX ≤ covarianceSubgroup I L := by
    apply Subgroup.topologicalClosure_minimal
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨⟨s,t⟩,rfl⟩ M
      simp only [rotationFlow_conjugation]
      exact matrixExp_conjugation_naturality _ _ L (hL s) M t
    · exact covarianceSubgroup_isClosed I L
  exact hle g.property M

end Flows
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open NormedSpace MeasureTheory Topology

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)

attribute [local instance] OAI.LaughlinFock.averagingRotationMeasurableSpace
attribute [local instance] OAI.LaughlinFock.averagingRotationBorelSpace
theorem rotationEvaluation_unitary (j : J) (g : rotationGroup X hX) :
    (rotationEvaluation X hX j g)ᴴ * rotationEvaluation X hX j g = 1 := by
  exact Unitary.star_mul_self_of_mem (g.val j).property



theorem rotationAverage_posSemidef (j : J) (M : Matrix (I j) (I j) ℂ)
    (hM : M.PosSemidef) : (rotationAverage X hX j M).PosSemidef :=
  matrixConjugationAverage_posSemidef _ _ _ hM (rotationOrbit_integrable X hX j M)

theorem rotationAverage_trace (j : J) (M : Matrix (I j) (I j) ℂ) :
    (rotationAverage X hX j M).trace = M.trace :=
  matrixConjugationAverage_trace _ _ (rotationEvaluation_unitary X hX j) M
    (rotationOrbit_integrable X hX j M)

theorem rotationAverage_commutes (j : J) (M : Matrix (I j) (I j) ℂ)
    (g : rotationGroup X hX) :
    rotationAverage X hX j M * rotationEvaluation X hX j g =
      rotationEvaluation X hX j g * rotationAverage X hX j M :=
  matrixConjugationAverage_commutes _ _ (rotationEvaluation_unitary X hX j) M
    (rotationOrbit_integrable X hX j M) g

 

theorem rotationAverage_covariance {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ)
    (hL : ∀ s M, L (X s i * M - M * X s i) = X s j * L M - L M * X s j)
    (M : Matrix (I i) (I i) ℂ) :
    L (rotationAverage X hX i M) = rotationAverage X hX j (L M) := by
  unfold rotationAverage matrixConjugationAverage
  refine (L.toContinuousLinearMap.integral_comp_comm
    (rotationOrbit_integrable X hX i M)).symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => rotationGroup_covariance X hX L hL g M

end
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteCoupling
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology



theorem spin_complement_ratio_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop)
    (h : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r)) :
    Tendsto (fun Q => (n Q : ℝ) / (n Q + m Q)) atTop (𝓝 (1-r)) := by
  apply ((tendsto_const_nhds (x := (1 : ℝ))).sub h).congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with Q hQ
  have hnQ : (n Q : ℝ) > 0 := by exact_mod_cast hQ
  field_simp
  ring

 

theorem highestWeight_factorization {n m z p : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmz : z ≤ m) (hp : p ≤ z) :
    (highestWeight n m z p : ℝ) / ((n : ℝ)+m)^z =
      (z.choose p : ℝ) * scaledDescFactorial n p (z-p) *
        scaledDescFactorial m (z-p) p *
        ((n : ℝ)/(n+m))^(z-p) * ((m : ℝ)/(n+m))^p := by
  have hs : m-z+p = m-(z-p) := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN : (n : ℝ)+m ≠ 0 := ne_of_gt (by positivity)
  have hpw : ((n : ℝ)+m)^z = ((n : ℝ)+m)^(z-p) * ((n : ℝ)+m)^p := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  simp only [highestWeight, Nat.cast_mul, hs, scaledDescFactorial, div_pow]
  rw [hpw]
  field_simp

 

theorem highestWeight_scaled_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun Q => (highestWeight (n Q) (m Q) z p : ℝ) /
      ((n Q : ℝ)+m Q)^z) atTop (𝓝 ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)) := by
  have hc := spin_complement_ratio_tendsto n m r hn hr
  have h := (((((tendsto_const_nhds (x := (z.choose p : ℝ))).mul
    ((scaledDescFactorial_tendsto p (z-p)).comp hn)).mul
    ((scaledDescFactorial_tendsto (z-p) p).comp hm)).mul (hc.pow (z-p))).mul (hr.pow p))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1),
    hm.eventually (eventually_ge_atTop (z+1))] with Q hnQ hmQ
  exact (highestWeight_factorization (by omega) (by omega) (by omega) hp).symm

 

theorem highestTotal_scaled_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r)) (z : ℕ) :
    Tendsto (fun Q => (highestTotal (n Q) (m Q) z : ℝ) /
      ((n Q : ℝ)+m Q)^z) atTop (𝓝 1) := by
  have h := tendsto_finsetSum (Finset.range (z+1))
    (fun p hp => highestWeight_scaled_tendsto n m r hn hm hr z p (by
      have := Finset.mem_range.mp hp; omega))
  have hsum : ∑ p ∈ Finset.range (z+1),
      (z.choose p : ℝ) * (1-r)^(z-p) * r^p = 1 := by
    calc
      _ = (r + (1-r))^z := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = 1 := by simp
  simpa only [hsum, ← Finset.sum_div, highestTotal, Nat.cast_sum] using h

 

theorem highestCoefficient_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun Q => highestCoefficient (n Q) (m Q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p))) := by
  have hratio := (highestWeight_scaled_tendsto n m r hn hm hr z p hp).div
    (highestTotal_scaled_tendsto n m r hn hm hr z) (by norm_num)
  simp only [div_one] at hratio
  have hrat : Tendsto (fun Q => (highestWeight (n Q) (m Q) z p : ℝ) /
      highestTotal (n Q) (m Q) z) atTop
      (𝓝 ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)) := by
    apply hratio.congr'
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with Q hnQ
    have hn' : (n Q : ℝ) > 0 := by exact_mod_cast hnQ
    have hN : ((n Q : ℝ)+m Q)^z ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
    exact div_div_div_cancel_right₀ hN _ _
  exact (Real.continuous_sqrt.tendsto _ |>.comp hrat).const_mul ((-1 : ℝ)^(z-p))

 
theorem highestCoefficient_tendsto_all (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) :
    Tendsto (fun Q => highestCoefficient (n Q) (m Q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p))) := by
  by_cases hp : p ≤ z
  · exact highestCoefficient_tendsto n m r hn hm hr z p hp
  · simpa only [highestCoefficient_zero _ _ _ _ (by omega : z < p),
      Nat.choose_eq_zero_of_lt (by omega : z < p), Nat.cast_zero, zero_mul,
      Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

 

theorem root_affine_ratio_tendsto (N a : ℕ → ℕ) (r b c : ℝ)
    (hN : Tendsto N atTop atTop)
    (ha : Tendsto (fun Q => (a Q : ℝ) / N Q) atTop (𝓝 r)) :
    Tendsto (fun Q => Real.sqrt (b*((a Q : ℝ)+c)) / Real.sqrt (N Q))
      atTop (𝓝 (Real.sqrt (b*r))) := by
  have hlim := (ha.add ((tendsto_const_div_atTop_nhds_zero_nat c).comp hN)).const_mul b
  simp only [add_zero] at hlim
  have hscaled := Real.continuous_sqrt.tendsto _ |>.comp hlim
  convert hscaled using 1
  all_goals try with_reducible_and_instances rfl
  funext Q
  rw [← Real.sqrt_div' _ (Nat.cast_nonneg (N Q)), mul_div_assoc, add_div]
  rfl



theorem oscillatorCoefficient_zero (r : ℝ) (z k p : ℕ) (hp : z+k < p) :
    oscillatorCoefficient r z k p = 0 := by
  induction k generalizing p with
  | zero =>
    simp [oscillatorCoefficient, Nat.choose_eq_zero_of_lt (by omega : z < p)]
  | succ k ih =>
    rw [oscillatorCoefficient, ih p (by omega)]
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [ite_eq_right hp0, ih (p-1) (by omega)]
      simp

 

theorem coupledCoefficient_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z k p : ℕ) :
    Tendsto (fun Q => coupledCoefficient (n Q) (m Q) z k p)
      atTop (𝓝 (oscillatorCoefficient r z k p)) := by
  let N : ℕ → ℕ := fun Q => n Q + m Q
  have hN : Tendsto N atTop atTop := hn.atTop_add_atTop hm
  have hNratio : Tendsto (fun Q => (N Q : ℝ) / N Q) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with Q hQ
    exact (div_self (by exact_mod_cast (by omega : N Q ≠ 0))).symm
  have hr' : Tendsto (fun Q => (m Q : ℝ) / N Q) atTop (𝓝 r) := by simpa [N] using hr
  have hc' : Tendsto (fun Q => (n Q : ℝ) / N Q) atTop (𝓝 (1-r)) := by
    simpa [N] using spin_complement_ratio_tendsto n m r hn hr
  induction k generalizing p with
  | zero => exact highestCoefficient_tendsto_all n m r hn hm hr z p
  | succ k ih =>
    have hfirst : Tendsto (fun Q =>
        (if p = 0 then 0 else
          (Real.sqrt ((p : ℝ)*((n Q : ℝ)+1-p)) / Real.sqrt (N Q)) *
            coupledCoefficient (n Q) (m Q) z k (p-1))) atTop
        (𝓝 (if p = 0 then 0 else
          Real.sqrt ((p : ℝ)*(1-r)) * oscillatorCoefficient r z k (p-1))) := by
      by_cases hp : p = 0
      · simp only [hp, ite_true, if_true]
        exact tendsto_const_nhds
      · simp only [hp, ite_false]
        have h := (root_affine_ratio_tendsto N n (1-r) p (1-p) hN hc').mul (ih (p-1))
        simpa only [add_sub_assoc] using h
    have hsecond : Tendsto (fun Q =>
        (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) *
          (Real.sqrt ((m Q : ℝ)+p-z-k) / Real.sqrt (N Q))) *
          coupledCoefficient (n Q) (m Q) z k p) atTop
        (𝓝 (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * Real.sqrt r *
          oscillatorCoefficient r z k p)) := by
      have h := root_affine_ratio_tendsto N m r 1 ((p : ℝ)-z-k) hN hr'
      simp only [one_mul] at h
      have h' := (h.const_mul (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p))).mul (ih p)
      simpa only [← add_sub_assoc] using h'
    have hden : Tendsto (fun Q =>
        Real.sqrt (((k+1 : ℕ) : ℝ)*((n Q : ℝ)+m Q-2*z-k)) / Real.sqrt (N Q))
        atTop (𝓝 (Real.sqrt (k+1 : ℕ))) := by
      have h := root_affine_ratio_tendsto N N 1 (k+1 : ℕ) (-2*z-k) hN hNratio
      simp only [mul_one] at h
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext Q
      congr 2
      simp only [N, Nat.cast_add]
      ring
    have hden0 : Real.sqrt (k+1 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have h := (hfirst.add hsecond).div hden hden0
    apply h.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with Q hQ
    have hN0 : Real.sqrt (N Q) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast (by omega : 0 < N Q))
    simp only [Pi.div_apply, coupledCoefficient]
    by_cases hp : p = 0
    · simp only [hp, ite_true, if_true, zero_add]
      field_simp [hN0]
    · simp only [hp, ite_false]
      field_simp [hN0]

 

theorem highestWeight_mul_descFactorial (n m z p : ℕ) (hp : p ≤ z) :
    highestWeight n m z p * n.descFactorial p =
      highestWeight n m z 0 * (z.choose p * (m-z+p).descFactorial p) := by
  simp only [highestWeight, Nat.sub_zero, Nat.choose_zero_right, one_mul,
    Nat.add_zero, Nat.descFactorial_zero, mul_one]
  calc
    _ = (z.choose p * (m-z+p).descFactorial p) *
        ((n-p).descFactorial (z-p) * n.descFactorial p) := by ring
    _ = _ := by rw [Nat.descFactorial_mul_descFactorial hp]; ring

 

theorem highestCoefficient_ratio {n m z p : ℕ} (hz : z ≤ n) (hp : p ≤ z) :
    highestCoefficient n m z p = (-1 : ℝ)^p *
      Real.sqrt ((z.choose p : ℝ) * (m-z+p).descFactorial p /
        n.descFactorial p) * highestCoefficient n m z 0 := by
  have hnp : (n.descFactorial p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (hp.trans hz)).ne'
  have he : (highestWeight n m z p : ℝ) / highestTotal n m z =
      ((z.choose p : ℝ) * (m-z+p).descFactorial p / n.descFactorial p) *
        ((highestWeight n m z 0 : ℝ) / highestTotal n m z) := by
    have h := congrArg (fun a : ℕ => (a : ℝ))
      (highestWeight_mul_descFactorial n m z p hp)
    push_cast at h
    have heq : (highestWeight n m z p : ℝ) =
        (z.choose p : ℝ) * (m-z+p).descFactorial p * highestWeight n m z 0 /
          n.descFactorial p := (eq_div_iff hnp).mpr (by nlinarith only [h])
    rw [heq]
    ring
  have hsign : (-1 : ℝ)^p * (-1 : ℝ)^z = (-1 : ℝ)^(z-p) := by
    calc
      _ = (-1 : ℝ)^p * ((-1 : ℝ)^(z-p) * (-1 : ℝ)^p) := by
        rw [← pow_add (-1 : ℝ) (z-p) p, Nat.sub_add_cancel hp]
      _ = ((-1 : ℝ)^p * (-1 : ℝ)^p) * (-1 : ℝ)^(z-p) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  simp only [highestCoefficient, Nat.sub_zero]
  rw [he, Real.sqrt_mul (by positivity)]
  calc
    _ = ((-1 : ℝ)^p * (-1 : ℝ)^z) *
        (Real.sqrt ((z.choose p : ℝ) * (m-z+p).descFactorial p /
          n.descFactorial p) *
        Real.sqrt ((highestWeight n m z 0 : ℝ) / highestTotal n m z)) := by rw [hsign]
    _ = _ := by ring

 
theorem highestCoefficient_last {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    highestCoefficient n m z z = (-1 : ℝ)^z *
      Real.sqrt ((m.descFactorial z : ℝ) / n.descFactorial z) *
        highestCoefficient n m z 0 := by
  simpa only [Nat.sub_add_cancel hm, Nat.choose_self, Nat.cast_one, one_mul] using
    highestCoefficient_ratio (m := m) hn (le_refl z)

 
theorem highestCoefficient_penultimate {n m z : ℕ} (hn : z ≤ n)
    (hm : z ≤ m) (hz : 1 ≤ z) :
    highestCoefficient n m z (z-1) = (-1 : ℝ)^(z-1) *
      Real.sqrt ((z : ℝ) * (m-1).descFactorial (z-1) /
        n.descFactorial (z-1)) * highestCoefficient n m z 0 := by
  have hs : m-z+(z-1) = m-1 := by omega
  simpa only [hs, Nat.choose_symm hz, Nat.choose_one_right] using
    highestCoefficient_ratio (m := m) hn (Nat.sub_le z 1)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_OscillatorLimit
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oscillator Limit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial
open Filter Topology



theorem monomialWeight_left (T p : ℕ) :
    monomialWeight (T+1) (p+1) = Real.sqrt (p+1 : ℕ) * monomialWeight T p := by
  unfold monomialWeight
  rw [Nat.add_sub_add_right, Nat.factorial_succ, Nat.cast_mul, mul_assoc,
    Real.sqrt_mul (Nat.cast_nonneg _)]

theorem monomialWeight_right {T p : ℕ} (hp : p ≤ T) :
    monomialWeight (T+1) p = Real.sqrt (((T+1 : ℕ) : ℝ)-p) * monomialWeight T p := by
  have hs : T+1-p = (T-p)+1 := by omega
  unfold monomialWeight
  rw [hs, Nat.factorial_succ, Nat.cast_mul]
  have ht : (((T-p+1 : ℕ) : ℝ)) = ((T+1 : ℕ) : ℝ)-p := by
    rw [Nat.cast_add, Nat.cast_sub hp, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring
  rw [ht, mul_left_comm, Real.sqrt_mul (sub_nonneg.mpr (by
    exact_mod_cast (by omega : p ≤ T+1)))]

 

theorem monomialCoefficient_linear (P : Polynomial ℝ) (T : ℕ)
    (hP : P.natDegree ≤ T) (u v : ℝ) (p : ℕ) :
    monomialCoefficient (T+1) ((C v * X + C u) * P) p =
      (if p = 0 then 0 else Real.sqrt (p : ℝ) * v * monomialCoefficient T P (p-1)) +
        Real.sqrt (((T+1 : ℕ) : ℝ)-p) * u * monomialCoefficient T P p := by
  cases p with
  | zero =>
    simp only [monomialCoefficient, Nat.cast_zero, sub_zero, ite_true, if_true, zero_add,
      add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul_zero, mul_zero]
    rw [monomialWeight_right (by omega : 0 ≤ T)]
    simp only [Nat.cast_zero, sub_zero]
    ring
  | succ p =>
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false,
      monomialCoefficient, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]
    by_cases hp : p+1 ≤ T
    · have hl := monomialWeight_left T p
      have hr := monomialWeight_right hp
      calc
        _ = monomialWeight (T+1) (p+1) * (v * P.coeff p) +
            monomialWeight (T+1) (p+1) * (u * P.coeff (p+1)) := by ring
        _ = (Real.sqrt (p+1 : ℕ) * monomialWeight T p) * (v * P.coeff p) +
            (Real.sqrt (((T+1 : ℕ) : ℝ)-(p+1 : ℕ)) * monomialWeight T (p+1)) *
              (u * P.coeff (p+1)) := by
          exact congrArg₂ (· + ·) (congrArg (fun x => x * (v * P.coeff p)) hl)
            (congrArg (fun x => x * (u * P.coeff (p+1))) hr)
        _ = _ := by ring
    · have hc : P.coeff (p+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [hc, mul_zero, add_zero, monomialWeight_left]
      ring



theorem couplingPolynomial_degree (u v : ℝ) (z k : ℕ) :
    (couplingPolynomial u v z k).natDegree ≤ z+k := by
  have h1 : (C u * X - C v).natDegree ≤ 1 := by
    change _ ≤ max 1 1
    apply natDegree_sub_le_of_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  have h2 : (C v * X + C u).natDegree ≤ 1 := by
    change _ ≤ max 1 1
    apply natDegree_add_le_of_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  exact natDegree_mul_le.trans (add_le_add
    (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left z h1))
    (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k h2)))

theorem polynomialCouplingCoefficient_zero (u v : ℝ) (z k p : ℕ) (hp : z+k < p) :
    polynomialCouplingCoefficient u v z k p = 0 := by
  have h := coeff_eq_zero_of_natDegree_lt ((couplingPolynomial_degree u v z k).trans_lt hp)
  simp only [polynomialCouplingCoefficient, monomialCoefficient, h, mul_zero, zero_div]

theorem couplingPolynomial_succ (u v : ℝ) (z k : ℕ) :
    couplingPolynomial u v z (k+1) =
      (C v * X + C u) * couplingPolynomial u v z k := by
  unfold couplingPolynomial
  rw [pow_succ]
  ring

theorem coefficient_scale_succ (z k : ℕ) :
    Real.sqrt ((z.factorial : ℝ) * (k+1).factorial) =
      Real.sqrt (k+1 : ℕ) * Real.sqrt ((z.factorial : ℝ) * k.factorial) := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_left_comm, Real.sqrt_mul (Nat.cast_nonneg _)]

 
theorem polynomialCouplingCoefficient_succ (u v : ℝ) (z k p : ℕ) :
    polynomialCouplingCoefficient u v z (k+1) p =
      ((if p = 0 then 0 else Real.sqrt (p : ℝ) * v * polynomialCouplingCoefficient u v z k (p-1)) +
        Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * u * polynomialCouplingCoefficient u v z k p) /
        Real.sqrt (k+1 : ℕ) := by
  unfold polynomialCouplingCoefficient
  rw [couplingPolynomial_succ, show z+(k+1) = z+k+1 by omega,
    monomialCoefficient_linear _ _ (couplingPolynomial_degree u v z k),
    coefficient_scale_succ]
  split_ifs <;> ring

theorem coeff_linear_pow (u v : ℝ) (z p : ℕ) :
    ((C u * X - C v)^z).coeff p = (-v)^(z-p) * (z.choose p : ℝ) * u^p := by
  have h : (C u * X - C v)^z = ((X + C (-v))^z).comp (C u * X) := by simp [sub_eq_add_neg]
  rw [h, comp_C_mul_X_coeff, coeff_X_add_C_pow]

theorem sqrt_nat_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a^n) = (Real.sqrt a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih, pow_succ]

 

theorem binomial_monomialWeight {z p : ℕ} (hp : p ≤ z) :
    (z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ) =
      Real.sqrt (z.choose p : ℝ) := by
  have hfac : (z.choose p : ℝ) * (p.factorial : ℝ) * (z-p).factorial =
      (z.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hfac0 : (z.factorial : ℝ) ≠ 0 := by positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ ((p.factorial : ℝ) * (z-p).factorial))
  have hsq : ((z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ))^2 =
      (Real.sqrt (z.choose p : ℝ))^2 := by
    rw [div_pow, mul_pow, monomialWeight, hs, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    apply (div_eq_iff hfac0).mpr
    nlinarith only [hfac]
  have hleft : 0 ≤ ((z.choose p : ℝ) * monomialWeight z p / Real.sqrt (z.factorial : ℝ)) := by
    unfold monomialWeight
    positivity
  nlinarith [Real.sqrt_nonneg (z.choose p : ℝ)]

 
theorem polynomialCouplingCoefficient_top (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (z p : ℕ) :
    polynomialCouplingCoefficient (Real.sqrt r) (Real.sqrt (1-r)) z 0 p =
      oscillatorCoefficient r z 0 p := by
  by_cases hp : p ≤ z
  · simp only [polynomialCouplingCoefficient, couplingPolynomial, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, monomialCoefficient, Nat.add_zero, coeff_linear_pow,
      oscillatorCoefficient]
    rw [neg_pow, Real.sqrt_mul (by positivity : 0 ≤ (z.choose p : ℝ) * (1-r)^(z-p)),
      Real.sqrt_mul (Nat.cast_nonneg _), sqrt_nat_pow (by linarith : 0 ≤ 1-r), sqrt_nat_pow hr]
    calc
      _ = (-1 : ℝ)^(z-p) * ((z.choose p : ℝ) * monomialWeight z p /
          Real.sqrt (z.factorial : ℝ)) * (Real.sqrt (1-r))^(z-p) * (Real.sqrt r)^p := by ring
      _ = _ := by rw [binomial_monomialWeight hp]; ring
  · rw [polynomialCouplingCoefficient_zero _ _ _ _ _ (by omega),
      oscillatorCoefficient_zero _ _ _ _ (by omega)]

 

theorem oscillatorCoefficient_eq_polynomial (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (z k p : ℕ) :
    oscillatorCoefficient r z k p =
      polynomialCouplingCoefficient (Real.sqrt r) (Real.sqrt (1-r)) z k p := by
  induction k generalizing p with
  | zero => exact (polynomialCouplingCoefficient_top r hr hr1 z p).symm
  | succ k ih =>
    rw [oscillatorCoefficient, polynomialCouplingCoefficient_succ, ih p, ih (p-1)]
    rw [Real.sqrt_mul (Nat.cast_nonneg p)]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Coefficients. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology


theorem affineSpin_atTop (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-b) atTop atTop := by
  refine tendsto_atTop.mpr fun k => ?_
  filter_upwards [eventually_ge_atTop (k+b)] with Q hQ
  have hm : Q ≤ a*Q := by nlinarith only [ha]
  omega

 

theorem affineSpin_scaled_tendsto (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => ((a*Q-b : ℕ) : ℝ) / Q) atTop (𝓝 (a : ℝ)) := by
  have h := tendsto_const_nhds (x := (a : ℝ)) |>.sub
    (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (b+1)] with Q hQ
  have hm : Q ≤ a*Q := by nlinarith only [ha]
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  rw [Nat.cast_sub (by omega : b ≤ a*Q), Nat.cast_mul]
  field_simp

 

theorem affineSpin_ratio_tendsto (a b c d : ℕ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun Q : ℕ => ((c*Q-d : ℕ) : ℝ) /
      (((a*Q-b : ℕ) : ℝ) + ((c*Q-d : ℕ) : ℝ))) atTop
        (𝓝 ((c : ℝ) / (a+c : ℕ))) := by
  have h1 := affineSpin_scaled_tendsto a b ha
  have h2 := affineSpin_scaled_tendsto c d hc
  have h := h2.div (h1.add h2) (by positivity : (a : ℝ)+(c : ℝ) ≠ 0)
  simp only [Nat.cast_add]
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  simp only [Pi.div_apply]
  rw [← add_div]
  exact div_div_div_cancel_right₀ hQ0 _ _

 
theorem threeCoupling_tendsto (z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient (2*Q-2) Q z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => 2*Q-2) (fun Q => Q) (1/3)
    (affineSpin_atTop 2 2 (by norm_num)) tendsto_id
    (by simpa using affineSpin_ratio_tendsto 2 2 1 0 (by norm_num) (by norm_num)) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/3 = 2/3 by norm_num] at h
  exact h



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TensorBasis
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 
theorem highestWeight_swap {n z p : ℕ} (hn : z ≤ n) (hp : p ≤ z) :
    highestWeight n n z (z-p) = highestWeight n n z p := by
  unfold highestWeight
  rw [Nat.choose_symm hp, Nat.sub_sub_self hp,
    show n-(z-p) = n-z+p by omega, show n-z+(z-p) = n-p by omega]
  ring

 
theorem highestCoefficient_swap {n z p : ℕ} (hn : z ≤ n) (hp : p ≤ z) :
    highestCoefficient n n z (z-p) = (-1 : ℝ)^z * highestCoefficient n n z p := by
  have hs : (-1 : ℝ)^z * (-1 : ℝ)^(z-p) = (-1 : ℝ)^p := by
    calc
      _ = ((-1 : ℝ)^(z-p) * (-1 : ℝ)^(z-p)) * (-1 : ℝ)^p := by
        conv_lhs => lhs; rw [← Nat.sub_add_cancel hp, pow_add]
        ring
      _ = _ := by rw [← mul_pow]; norm_num
  unfold highestCoefficient
  rw [highestWeight_swap hn hp, Nat.sub_sub_self hp, ← mul_assoc, hs]

 

theorem coupledVector_swap {n z : ℕ} (hn : z ≤ n) (k p q : ℕ) :
    coupledVector n n z k q p = (-1 : ℝ)^z * coupledVector n n z k p q := by
  induction k generalizing p q with
  | zero =>
    by_cases h : p+q = z
    · have hp : p ≤ z := by omega
      have hq : q = z-p := by omega
      simp only [coupledVector, Nat.add_zero, coupledCoefficient,
        ite_eq_left h, ite_eq_left (by omega : q+p = z)]
      rw [hq, highestCoefficient_swap hn hp]
    · simp [coupledVector, h, show q+p ≠ z by omega]
  | succ k ih =>
    rw [coupledVector_succ (by omega : 2*z ≤ n+n)]
    simp only [Pi.smul_apply, smul_eq_mul, gridLower]
    rw [ih p (q-1), ih (p-1) q]
    ring



theorem coupledVector_antisymm {n z : ℕ} (hn : z ≤ n) (hz : Odd z) (k p q : ℕ) :
    coupledVector n n z k q p = -coupledVector n n z k p q := by
  rw [coupledVector_swap hn, hz.neg_one_pow, neg_one_mul]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CreationRows
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation Rows. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder Kronecker BigOperators

 

theorem creationRow_product (Q : ℕ) (i k : Orbital Q) (X Y : FockMatrix Q) :
    ((annihilator Q i)ᴴ * X)ᴴ * ((annihilator Q k)ᴴ * Y) =
      (if i = k then Xᴴ * Y else 0) -
        (annihilator Q k * X)ᴴ * (annihilator Q i * Y) := by
  have hCAR := eq_sub_of_add_eq (annihilator_adjoint_anticommute Q i k)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul]
  calc
    _ = Xᴴ * (annihilator Q i * (annihilator Q k)ᴴ) * Y := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * ((if i = k then 1 else 0) - (annihilator Q k)ᴴ * annihilator Q i) * Y := by
      rw [hCAR]
    _ = _ := by
      split_ifs <;> simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc]

 

theorem square_sum_expansion {β : Type*} [Fintype β] (Q : ℕ) (B : FockMatrix Q)
    (Y : β → FockMatrix Q) (ℓ : ℝ) (a : β → ℝ) :
    (ℓ • B + ∑ b, a b • Y b)ᴴ * (ℓ • B + ∑ b, a b • Y b) =
      ℓ^2 • (Bᴴ * B) +
      ∑ b, (ℓ * a b) • (Bᴴ * Y b + (Y b)ᴴ * B) +
      ∑ b, ∑ c, (a b * a c) • ((Y b)ᴴ * Y c) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, star_trivial, Matrix.add_mul, Matrix.mul_add,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum, pow_two]
  have hcomm : ∑ c, ∑ b, (a c * a b) • ((Y b)ᴴ * Y c) =
      ∑ b, ∑ c, (a b * a c) • ((Y b)ᴴ * Y c) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hcomm]
  simp only [mul_comm ℓ]
  abel



theorem auxiliaryRow_square {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) :
    (auxiliaryRow Q t ℓ p i j a)ᴴ * auxiliaryRow Q t ℓ p i j a =
      rowTwoBody Q t ℓ + rowThreeBody Q t ℓ p i j a + rowFourBody Q p i j a := by
  rw [auxiliaryRow, square_sum_expansion]
  simp_rw [creationRow_product]
  simp only [rowTwoBody, rowThreeBody, rowFourBody,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]
  abel



theorem orbitalPair_mem (Q p : ℕ) (j : Orbital Q) :
    annihilator Q j * pairAnnihilator Q p ∈ AnnihilationSpace Q 3 :=
  annihilationSpace_mul Q 2 1 (pairAnnihilator_mem Q p) (annihilator_mem Q j)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairIdentification
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Identification. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem spinStep_mul_choose (n p : ℕ) :
    spinStep n p * Real.sqrt (n.choose (p-1) : ℝ) =
      (p : ℝ) * Real.sqrt (n.choose p : ℝ) := by
  rcases p with _ | p
  · simp
  by_cases hp : p+1 ≤ n
  · have hc : ((n.choose (p+1) : ℝ)) * (p+1 : ℕ) =
        ((n.choose p : ℝ)) * (n-p : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n p
    apply (sq_eq_sq₀ (by unfold spinStep; positivity : 0 ≤ spinStep n (p+1) * Real.sqrt (n.choose ((p+1)-1) : ℝ))
      (by positivity : 0 ≤ ((p+1 : ℕ) : ℝ)*Real.sqrt (n.choose (p+1) : ℝ))).mp
    rw [mul_pow, mul_pow, spinStep_sq (by omega), Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [Nat.add_sub_cancel]
    rw [Nat.cast_sub (by omega : p ≤ n)] at hc
    push_cast at hc ⊢
    have h := congrArg (fun x : ℝ => ((p:ℝ)+1)*x) hc
    nlinarith only [h]
  · rw [spinStep_cutoff n (p+1) (by omega), Nat.choose_eq_zero_of_lt (by omega : n < p+1)]
    simp



theorem rawPairGrid_layer (Q p : ℕ) : GridLayer (p+1) (rawPairGrid Q p) := by
  intro i j hij
  exact ite_eq_right hij

 

theorem rawPairGrid_lower (Q p : ℕ) :
    gridLower Q Q (rawPairGrid Q p) = ((p+1 : ℕ) : ℝ) • rawPairGrid Q (p+1) := by
  funext i j
  by_cases ht : i+j=p+2
  · change spinStep Q i * rawPairGrid Q p (i-1) j +
      spinStep Q j * rawPairGrid Q p i (j-1) =
        ((p+1 : ℕ) : ℝ) * rawPairGrid Q (p+1) i j
    conv_rhs => rw [rawPairGrid, ite_eq_left (by omega : i+j=p+1+1)]
    have ht' : (i:ℝ)+j = (p:ℝ)+2 := by exact_mod_cast ht
    by_cases hi : i=0
    · subst i
      simp only [spinStep_zero, zero_mul, zero_add, rawPairGrid,
        ite_eq_left (by omega : (j-1)=p+1), Nat.cast_zero, zero_sub, Nat.choose_zero_right,
        Nat.cast_one, Real.sqrt_one, mul_one]
      rw [show spinStep Q j * (-((j-1:ℕ):ℝ) * Real.sqrt (Q.choose (j-1) : ℝ)) =
        -((j-1:ℕ):ℝ) * (spinStep Q j * Real.sqrt (Q.choose (j-1) : ℝ)) by ring,
        spinStep_mul_choose]
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      have he : (j:ℝ)=(p:ℝ)+2 := by exact_mod_cast (show j=p+2 by omega)
      rw [he]
      ring
    · by_cases hj : j=0
      · subst j
        simp only [spinStep_zero, zero_mul, add_zero, rawPairGrid,
          ite_eq_left (by omega : i-1=p+1), Nat.cast_zero, sub_zero,
          Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one, mul_one]
        rw [show spinStep Q i * (((i-1:ℕ):ℝ) * Real.sqrt (Q.choose (i-1) : ℝ)) =
          ((i-1:ℕ):ℝ) * (spinStep Q i * Real.sqrt (Q.choose (i-1) : ℝ)) by ring,
          spinStep_mul_choose]
        rw [Nat.cast_sub (by omega : 1 ≤ i)]
        push_cast
        have he : (i:ℝ)=(p:ℝ)+2 := by exact_mod_cast (show i=p+2 by omega)
        rw [he]
        ring
      · simp only [rawPairGrid, ite_eq_left (by omega : i-1+j=p+1),
          ite_eq_left (by omega : i+(j-1)=p+1)]
        rw [show spinStep Q i * ((((i-1:ℕ):ℝ)-j) *
            Real.sqrt (Q.choose (i-1) : ℝ) * Real.sqrt (Q.choose j : ℝ)) =
          (((i-1:ℕ):ℝ)-j) * (spinStep Q i * Real.sqrt (Q.choose (i-1) : ℝ)) *
            Real.sqrt (Q.choose j : ℝ) by ring,
          show spinStep Q j * (((i:ℝ)-(j-1:ℕ)) *
            Real.sqrt (Q.choose i : ℝ) * Real.sqrt (Q.choose (j-1) : ℝ)) =
          ((i:ℝ)-(j-1:ℕ)) * Real.sqrt (Q.choose i : ℝ) *
            (spinStep Q j * Real.sqrt (Q.choose (j-1) : ℝ)) by ring,
          spinStep_mul_choose, spinStep_mul_choose,
          Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_sub (by omega : 1 ≤ j)]
        push_cast
        have he : (p:ℝ)+1=(i:ℝ)+j-1 := by linarith
        rw [he]
        ring
  · have h := gridLower_layer (n := Q) (m := Q) (rawPairGrid_layer Q p) i j (by omega)
    simp only [h, Pi.smul_apply, smul_eq_mul, rawPairGrid,
      ite_eq_right (by omega : i+j≠p+1+1), mul_zero]


theorem pairTensorNormalizer_pos {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    0 < pairTensorNormalizer Q p := by
  unfold pairTensorNormalizer
  apply Real.sqrt_pos.mpr
  have hq : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hc : 0 < ((2*Q-2).choose p : ℝ) := by exact_mod_cast Nat.choose_pos hp
  positivity

theorem pairTensorNormalizer_recurrence {Q p : ℕ} (hp : p < 2*Q-2) :
    spinStep (2*Q-2) (p+1) * pairTensorNormalizer Q p =
      ((p+1 : ℕ):ℝ) * pairTensorNormalizer Q (p+1) := by
  apply (sq_eq_sq₀ (by unfold spinStep pairTensorNormalizer; positivity)
    (by unfold pairTensorNormalizer; positivity)).mp
  rw [mul_pow, mul_pow, spinStep_sq (by omega)]
  rw [pairTensorNormalizer, pairTensorNormalizer,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hc : (((2*Q-2).choose (p+1) : ℝ)) * (p+1 : ℕ) =
      (((2*Q-2).choose p : ℝ)) * ((2*Q-2)-p : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq (2*Q-2) p
  rw [Nat.cast_sub (by omega : p ≤ 2*Q-2)] at hc
  have h := congrArg (fun x : ℝ => 2*(Q:ℝ)*((p+1:ℕ):ℝ)*x) hc
  push_cast at h ⊢
  nlinarith only [h]


theorem normalizedPairGrid_succ {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p < 2*Q-2) :
    normalizedPairGrid Q (p+1) = (spinStep (2*Q-2) (p+1))⁻¹ •
      gridLower Q Q (normalizedPairGrid Q p) := by
  rw [normalizedPairGrid, normalizedPairGrid, gridLower_smul,
    rawPairGrid_lower, smul_smul, smul_smul]
  have h1 := (pairTensorNormalizer_pos hQ (by omega : p ≤ 2*Q-2)).ne'
  have h2 := (pairTensorNormalizer_pos hQ (by omega : p+1 ≤ 2*Q-2)).ne'
  have h3 := (spinStep_pos (by omega : 0 < p+1) (by omega : p+1 ≤ 2*Q-2)).ne'
  congr 1
  field_simp [h1, h2, h3]
  simpa only [mul_comm] using pairTensorNormalizer_recurrence hp

 
theorem normalizedPairGrid_top {Q : ℕ} (hQ : 1 ≤ Q) :
    normalizedPairGrid Q 0 = coupledVector Q Q 1 0 := by
  have hpred : Q-1+1 = Q := by omega
  have htotal : highestTotal Q Q 1 = 2*Q := by
    simp [highestTotal, Finset.sum_range_succ, highestWeight, hpred, two_mul]
  funext i j
  by_cases ht : i+j=1
  · have hcases : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      simp [normalizedPairGrid, rawPairGrid, pairTensorNormalizer, coupledVector,
        coupledCoefficient, highestCoefficient, highestWeight, htotal, hpred,
        Real.sqrt_div (Nat.cast_nonneg Q)]
      ring
  · simp [normalizedPairGrid, rawPairGrid, coupledVector, ht]

 

theorem normalizedPairGrid_eq_coupled {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    normalizedPairGrid Q p = coupledVector Q Q 1 p := by
  induction p with
  | zero => exact normalizedPairGrid_top hQ
  | succ p ih =>
    rw [normalizedPairGrid_succ hQ (by omega), ih (by omega),
      coupledVector_succ (by omega : 2*1 ≤ Q+Q)]
    simp only [two_mul, mul_one]

 

theorem sphericalPairCoefficient_eq_normalized {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    sphericalPairCoefficient Q p i j = Real.sqrt 2 * normalizedPairGrid Q p i j := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hf : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hr : ((Q.descFactorial i : ℝ)*(Q.descFactorial j : ℝ)*(p.factorial : ℝ)) /
      ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(i.factorial : ℝ)*(j.factorial : ℝ)) =
      ((Q.choose i : ℝ)*(Q.choose j : ℝ)) / ((Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold sphericalPairCoefficient normalizedPairGrid rawPairGrid
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs with hw
  · rw [hr, Real.sqrt_div (by positivity),
      Real.sqrt_mul (Nat.cast_nonneg (Q.choose i))]
    unfold pairTensorNormalizer
    rw [mul_assoc (2 : ℝ), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
  · simp

 

theorem pairCoefficient_eq_coupled {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : Orbital Q) :
    pairCoefficient Q p i j = Real.sqrt 2 * coupledVector Q Q 1 p i j := by
  rw [pairCoefficient_eq_sphericalPairCoefficient,
    sphericalPairCoefficient_eq_normalized hQ hp, normalizedPairGrid_eq_coupled hQ hp]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SpinTails
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology


theorem fallingRatio_nonneg (Q z : ℕ) : 0 ≤ fallingRatio Q z := by
  unfold fallingRatio
  positivity

theorem fallingRatio_succ {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q (z + 1) =
      ((Q : ℝ) - z) / (2 * Q - 2 - z) * fallingRatio Q z := by
  unfold fallingRatio
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm,
    Nat.cast_sub hz, Nat.cast_sub (show z ≤ 2*Q-2 by omega),
    Nat.cast_sub (show 2 ≤ 2*Q by omega)]
  push_cast
  rfl


private theorem affineRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => ((Q : ℝ)-z)/(2*Q-2-z)) atTop (𝓝 (1/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (z : ℝ)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 + (z : ℝ))
  have hh : Tendsto (fun Q : ℕ => (1 - (z : ℝ)/Q)/(2 - (2+z)/Q))
      atTop (𝓝 (1/2)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2)
      (show (2:ℝ)-0 ≠ 0 by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hzr : (z : ℝ) + 2 ≤ Q := by exact_mod_cast hQ
  have hd : 2 * (Q:ℝ) - 2 - z ≠ 0 := by have := Nat.cast_nonneg (α:=ℝ) z; linarith
  have hd' : 2 - (2 + (z:ℝ)) / Q ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  field_simp [hn, hd, hd']
  ring

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  induction z with
  | zero => simp [fallingRatio]
  | succ z ih =>
    have h := (affineRatio_tendsto z).mul ih
    simp only [← pow_succ'] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
    exact (fallingRatio_succ (by omega) (by omega)).symm

 
theorem gramShift_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramShift Q z) atTop
      (𝓝 ((3 * (z : ℝ) - 1) * (-1/2)^z)) := by
  have h := ((fallingRatio_tendsto z).const_mul ((-1:ℝ)^z)).mul
    ((tendsto_const_nhds (x := (3*(z:ℝ)-1))).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z:ℝ)*(z+1))))
  convert h using 1
  · simp [gramShift]
  · simp only [sub_zero]
    rw [mul_assoc, mul_comm ((3*(z:ℝ)-1)), ← mul_assoc, ← mul_pow]
    congr 1
    norm_num


theorem spinRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => spinRatio Q z) atTop (𝓝 (3/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1+2*(z:ℝ))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hh : Tendsto (fun Q : ℕ => (3 - (1+2*(z:ℝ))/Q)/(2 - 1/(Q:ℝ)))
      atTop (𝓝 (3/2)) := by
    convert ((tendsto_const_nhds (x := (3:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2) (show (2:ℝ)-0 ≠ 0 by norm_num)
      using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hqr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : 2*(Q:ℝ)-1 ≠ 0 := by linarith
  have hd' : 2 - 1/(Q:ℝ) ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  unfold spinRatio
  field_simp [hn, hd, hd']
  ring



private theorem tailBound_summable :
    Summable (fun m : ℕ =>
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m)) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h : Summable (fun z : ℕ => 6*(z:ℝ)*(z+1)*(2/3)^z) := by
    apply ((h2.mul_left 6).add (h1.mul_left 6)).congr
    intro z
    ring
  exact h.comp_injective (fun i j hij => by omega)


theorem tailCoefficient_eq_odd_sum (Q : ℕ) :
    tailCoefficient Q =
      ∑ z ∈ (Finset.range (Q+1)).filter (fun z => 17 ≤ z ∧ Odd z),
        spinRatio Q z * |gramShift Q z| * (z+1) := by
  classical
  unfold tailCoefficient
  simp only [tailTerm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _ => 17+2*m)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact ⟨by omega, by omega, Nat.odd_iff.mpr (by omega)⟩
  · intro m hm n hn hmn
    omega
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hz
    refine ⟨(z-17)/2, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ScalarAction
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar Action. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem gridInner_self_eq_zero {n m : ℕ} {f : GridVector}
    (hf : GridSupported n m f) (h : gridInner n m f f = 0) : f = 0 := by
  funext p q
  by_cases hp : p ≤ n
  · by_cases hq : q ≤ m
    · have hi : f p q * f p q ≤ gridInner n m f f := by
        apply le_trans (Finset.single_le_sum (fun a _ => mul_self_nonneg (f p a))
          (Finset.mem_range.mpr (by omega : q < m+1)))
        exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => mul_self_nonneg (f a b)))
          (Finset.mem_range.mpr (by omega : p < n+1))
      rw [h] at hi
      exact (mul_self_eq_zero.mp (le_antisymm hi (mul_self_nonneg (f p q))))
    · exact hf p q (Or.inr (by omega))
  · exact hf p q (Or.inl (by omega))

 

theorem coupledVector_lowest {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridLower n m (coupledVector n m z (n+m-2*z)) = 0 := by
  have hz : 2*z ≤ n+m := by omega
  let k := n+m-2*z
  have hLR : gridLower n m (gridRaise n m (coupledVector n m z k)) =
      spinStep k k ^ 2 • coupledVector n m z k := by
    rw [coupledVector_raise hn hm (by rfl : k ≤ n+m-2*z), gridLower_smul]
    change spinStep k k • gridLower n m (coupledVector n m z (k-1)) = _
    by_cases hk : k=0
    · simp [hk]
    · rw [coupledVector_lower hz (by dsimp [k] at *; omega),
        show k-1+1=k by omega, smul_smul, ← pow_two]
  have hsq : spinStep k k ^ 2 + (((n+m-2*z : ℕ) : ℝ)-2*k) = 0 := by
    rw [spinStep_sq (by omega : k ≤ k+1)]
    change (k:ℝ)*((k:ℝ)+1-k) + ((k:ℝ)-2*k) = 0
    ring
  have hRL := coupledVector_commutator hn hm k
  rw [hLR, ← add_smul, hsq, zero_smul] at hRL
  apply gridInner_self_eq_zero (gridLower_supported (coupledVector_supported hn hm k))
  rw [grid_adjoint, hRL, gridInner_zero_right]

 
theorem coupledVector_outside_ladder {n m z k : ℕ} (hz : 2*z ≤ n+m)
    (hk : n+m-2*z < k) : coupledVector n m z k = 0 := by
  have he : k=(k-1)+1 := by omega
  conv_lhs => rw [he, coupledVector_succ hz]
  rw [← he, spinStep_cutoff _ _ hk, inv_zero, zero_smul]

 

theorem coupledVector_lower_all {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridLower n m (coupledVector n m z k) =
      spinStep (n+m-2*z) (k+1) • coupledVector n m z (k+1) := by
  rcases lt_trichotomy k (n+m-2*z) with hk | rfl | hk
  · exact coupledVector_lower (by omega) hk
  · rw [coupledVector_lowest hn hm, spinStep_last, zero_smul]
  · rw [coupledVector_outside_ladder (by omega) hk,
      gridLower_zero, spinStep_cutoff _ _ (by omega), zero_smul]

 
theorem coupledVector_raise_all {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridRaise n m (coupledVector n m z k) =
      spinStep (n+m-2*z) k • coupledVector n m z (k-1) := by
  by_cases hk : k ≤ n+m-2*z
  · exact coupledVector_raise hn hm hk
  · rw [coupledVector_outside_ladder (by omega) (by omega),
      gridRaise_zero, spinStep_cutoff _ _ (by omega), zero_smul]

 

theorem grid_highest_eq_of_first {n m z : ℕ} (hz : z ≤ n) {f g : GridVector}
    (hf : GridLayer z f) (hg : GridLayer z g)
    (hRf : gridRaise n m f = 0) (hRg : gridRaise n m g = 0)
    (hfirst : f 0 z = g 0 z) : f = g := by
  have hc : ∀ p, p ≤ z → f p (z-p) = g p (z-p) := by
    intro p
    induction p with
    | zero => simpa using fun (_ : 0 ≤ z) => hfirst
    | succ p ih =>
      intro hp
      have heF := congrArg (fun h : GridVector => h p (z-(p+1))) hRf
      have heG := congrArg (fun h : GridVector => h p (z-(p+1))) hRg
      simp only [gridRaise, Pi.zero_apply,
        show z-(p+1)+1 = z-p by omega] at heF heG
      rw [ih (by omega)] at heF
      apply mul_left_cancel₀ (spinStep_pos (by omega : 0 < p+1) (by omega : p+1 ≤ n)).ne'
      linarith only [heF, heG]
  funext p q
  by_cases h : p+q=z
  · rw [show q=z-p by omega]
    exact hc p (by omega)
  · rw [hf p q h, hg p q h]

 

theorem highestCoefficient_first_ne_zero {n m z : ℕ} (hn : z ≤ n) :
    highestCoefficient n m z 0 ≠ 0 := by
  have hpos : 0 < highestCoefficient n m z 0 ^ 2 := by
    rw [highestCoefficient_sq]
    apply div_pos
    · simpa [highestWeight] using (show (0:ℝ) < n.descFactorial z by
        exact_mod_cast Nat.descFactorial_pos.mpr hn)
    · exact_mod_cast highestTotal_pos (m := m) hn
  exact fun h => by simp [h] at hpos

 

theorem grid_highest_unique {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    {f : GridVector} (hf : GridLayer z f) (hRf : gridRaise n m f = 0) :
    f = (f 0 z / highestCoefficient n m z 0) • coupledVector n m z 0 := by
  apply grid_highest_eq_of_first (m := m) hn hf
  · intro p q hpq
    simp [coupledVector_layer n m z 0 p q (by simpa using hpq)]
  · exact hRf
  · rw [gridRaise_smul, coupledVector_highest hn hm, smul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, coupledVector, zero_add, add_zero,
      ite_true, if_true, coupledCoefficient]
    exact (div_mul_cancel₀ _ (highestCoefficient_first_ne_zero hn)).symm

 

theorem coupledVector_intertwiner {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (A : GridVector →ₗ[ℝ] GridVector)
    (hL : ∀ f, A (gridLower n m f) = gridLower n m (A f))
    (hR : ∀ f, A (gridRaise n m f) = gridRaise n m (A f))
    (hLayer : ∀ T f, GridLayer T f → GridLayer T (A f)) (k : ℕ) :
    A (coupledVector n m z k) =
      (A (coupledVector n m z 0) 0 z / highestCoefficient n m z 0) •
        coupledVector n m z k := by
  induction k with
  | zero =>
    apply grid_highest_unique hn hm
    · exact hLayer z _ (by simpa using coupledVector_layer n m z 0)
    · rw [← hR, coupledVector_highest hn hm, map_zero]
  | succ k ih =>
    rw [coupledVector_succ (by omega : 2*z ≤ n+m), map_smul, hL, ih,
      gridLower_smul]
    exact smul_comm _ _ _

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SwapCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swap Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

theorem pairCoupled_lower {Q : ℕ} (hQ : 1 ≤ Q) (p : ℕ) :
    gridLower Q Q (coupledVector Q Q 1 p) =
      spinStep (2*Q-2) (p+1) • coupledVector Q Q 1 (p+1) := by
  simpa only [two_mul, mul_one] using coupledVector_lower_all hQ hQ p

theorem pairCoupled_raise {Q : ℕ} (hQ : 1 ≤ Q) (p : ℕ) :
    gridRaise Q Q (coupledVector Q Q 1 p) =
      spinStep (2*Q-2) p • coupledVector Q Q 1 (p-1) := by
  simpa only [two_mul, mul_one] using coupledVector_raise_all hQ hQ p

theorem gridInner_add_right (n m : ℕ) (f g h : GridVector) :
    gridInner n m f (g+h) = gridInner n m f g + gridInner n m f h := by
  simp only [gridInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem grid_raise_adjoint (n m : ℕ) (f g : GridVector) :
    gridInner n m (gridRaise n m f) g = gridInner n m f (gridLower n m g) := by
  rw [gridInner_comm, ← grid_adjoint, gridInner_comm]

theorem pairTensorProject_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) :
    pairTensorProject Q (cubeLower Q f) = gridLower (2*Q-2) Q (pairTensorProject Q f) := by
  funext p k
  change gridInner Q Q (coupledVector Q Q 1 p)
      (gridLower Q Q (fun i j => f i j k) + spinStep Q k • (fun i j => f i j (k-1))) = _
  rw [gridInner_add_right, gridInner_smul_right, ← grid_raise_adjoint,
    pairCoupled_raise hQ, gridInner_smul_left]
  rfl

theorem pairTensorProject_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) :
    pairTensorProject Q (cubeRaise Q f) = gridRaise (2*Q-2) Q (pairTensorProject Q f) := by
  funext p k
  change gridInner Q Q (coupledVector Q Q 1 p)
      (gridRaise Q Q (fun i j => f i j k) + spinStep Q (k+1) • (fun i j => f i j (k+1))) = _
  rw [gridInner_add_right, gridInner_smul_right, ← grid_adjoint,
    pairCoupled_lower hQ, gridInner_smul_left]
  rfl

theorem pairTensorEmbed_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairTensorEmbed Q (gridLower (2*Q-2) Q f) = cubeLower Q (pairTensorEmbed Q f) := by
  funext i j k
  have hp (p : ℕ) : gridLower Q Q (coupledVector Q Q 1 p) i j =
      spinStep (2*Q-2) (p+1) * coupledVector Q Q 1 (p+1) i j :=
    congrArg (fun g : GridVector => g i j) (pairCoupled_lower hQ p)
  calc
    _ = (∑ p ∈ Finset.range (2*Q-2+1),
        (spinStep (2*Q-2) p * f (p-1) k) * coupledVector Q Q 1 p i j) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk, gridLower,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring
    _ = (∑ p ∈ Finset.range (2*Q-2+1), f p k *
        (spinStep (2*Q-2) (p+1) * coupledVector Q Q 1 (p+1) i j)) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      rw [spinStep_sum_adjoint (2*Q-2) (fun p => f p k) (fun p => coupledVector Q Q 1 p i j)]
    _ = (∑ p ∈ Finset.range (2*Q-2+1), f p k * gridLower Q Q (coupledVector Q Q 1 p) i j) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      simp only [hp]
    _ = _ := by
      simp only [cubeLower, pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk,
        gridLower, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

theorem pairTensorEmbed_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairTensorEmbed Q (gridRaise (2*Q-2) Q f) = cubeRaise Q (pairTensorEmbed Q f) := by
  funext i j k
  have hp (p : ℕ) : gridRaise Q Q (coupledVector Q Q 1 p) i j =
      spinStep (2*Q-2) p * coupledVector Q Q 1 (p-1) i j :=
    congrArg (fun g : GridVector => g i j) (pairCoupled_raise hQ p)
  calc
    _ = (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j *
        (spinStep (2*Q-2) (p+1) * f (p+1) k)) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk, gridRaise,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (∑ p ∈ Finset.range (2*Q-2+1),
        (spinStep (2*Q-2) p * coupledVector Q Q 1 (p-1) i j) * f p k) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      rw [spinStep_sum_adjoint (2*Q-2) (fun p => coupledVector Q Q 1 p i j) (fun p => f p k)]
    _ = (∑ p ∈ Finset.range (2*Q-2+1), gridRaise Q Q (coupledVector Q Q 1 p) i j * f p k) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      simp only [hp]
    _ = _ := by
      simp only [cubeRaise, pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk,
        gridRaise, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

theorem swap23_lower (Q : ℕ) (f : CubeVector) :
    swap23 (cubeLower Q f) = cubeLower Q (swap23 f) := by
  funext i j k
  simp only [swap23, cubeLower, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem swap23_raise (Q : ℕ) (f : CubeVector) :
    swap23 (cubeRaise Q f) = cubeRaise Q (swap23 f) := by
  funext i j k
  simp only [swap23, cubeRaise, LinearMap.coe_mk, AddHom.coe_mk]
  ring

 

theorem pairSwapCompression_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairSwapCompression Q (gridLower (2*Q-2) Q f) =
      gridLower (2*Q-2) Q (pairSwapCompression Q f) := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorEmbed_lower hQ,
    swap23_lower, pairTensorProject_lower hQ]

theorem pairSwapCompression_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairSwapCompression Q (gridRaise (2*Q-2) Q f) =
      gridRaise (2*Q-2) Q (pairSwapCompression Q f) := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorEmbed_raise hQ,
    swap23_raise, pairTensorProject_raise hQ]

theorem pairTensorEmbed_layer {Q T : ℕ} {f : GridVector} (hf : GridLayer T f) :
    CubeLayer (T+1) (pairTensorEmbed Q f) := by
  intro i j k hijk
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hij : i+j=1+p
  · rw [hf p k (by omega), mul_zero]
  · rw [coupledVector_layer Q Q 1 p i j hij, zero_mul]

theorem swap23_layer {T : ℕ} {f : CubeVector} (hf : CubeLayer T f) :
    CubeLayer T (swap23 f) := by
  intro i j k h
  exact hf i k j (by omega)

theorem pairTensorProject_layer {Q T : ℕ} {f : CubeVector} (hf : CubeLayer (T+1) f) :
    GridLayer T (pairTensorProject Q f) := by
  intro p k hpk
  simp only [pairTensorProject, LinearMap.coe_mk, AddHom.coe_mk, gridInner]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i+j=1+p
  · rw [hf i j k (by omega), mul_zero]
  · rw [coupledVector_layer Q Q 1 p i j hij, zero_mul]

theorem pairSwapCompression_layer (Q T : ℕ) (f : GridVector) (hf : GridLayer T f) :
    GridLayer T (pairSwapCompression Q f) :=
  pairTensorProject_layer (swap23_layer (pairTensorEmbed_layer hf))

 

theorem pairSwapCompression_coupled {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z k) =
      (pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z /
        highestCoefficient (2*Q-2) Q z 0) • coupledVector (2*Q-2) Q z k := by
  exact coupledVector_intertwiner (by omega) hz _
    (pairSwapCompression_lower (by omega)) (pairSwapCompression_raise (by omega))
    (pairSwapCompression_layer Q) k

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ExchangeSpectrum
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exchange Spectrum. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

theorem sphericalPairCoefficient_coupled {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    Real.sqrt 2 * coupledVector Q Q 1 p i j = sphericalPairCoefficient Q p i j := by
  rw [sphericalPairCoefficient_eq_normalized hQ hp, normalizedPairGrid_eq_coupled hQ hp]

theorem sphericalPairCoefficient_top {Q : ℕ} (hQ : 1 ≤ Q) (i j : ℕ) :
    sphericalPairCoefficient Q 0 i j =
      (if i=1 ∧ j=0 then 1 else 0) - (if i=0 ∧ j=1 then 1 else 0) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  by_cases ht : i+j=1
  · have hcases : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [sphericalPairCoefficient, hq]
  · simp only [sphericalPairCoefficient, zero_add, ite_eq_right ht]
    rw [ite_eq_right (by omega : ¬(i=1 ∧ j=0)), ite_eq_right (by omega : ¬(i=0 ∧ j=1))]
    ring

theorem pairCoupled_top {Q : ℕ} (hQ : 1 ≤ Q) (i j : ℕ) :
    coupledVector Q Q 1 0 i j =
      ((if i=1 ∧ j=0 then 1 else 0) - (if i=0 ∧ j=1 then 1 else 0)) / Real.sqrt 2 := by
  apply (eq_div_iff (by positivity : Real.sqrt (2:ℝ) ≠ 0)).mpr
  rw [mul_comm, sphericalPairCoefficient_coupled hQ (by omega), sphericalPairCoefficient_top hQ]

 

theorem pairTensorProject_top {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) (k : ℕ) :
    pairTensorProject Q f 0 k = (f 1 0 k - f 0 1 k) / Real.sqrt 2 := by
  simp only [pairTensorProject, LinearMap.coe_mk, AddHom.coe_mk, gridInner, pairCoupled_top hQ]
  simp only [sub_div, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_and, ite_div, zero_div, ite_mul, zero_mul, one_div]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_range,
    show 0 < Q+1 by omega, show 1 < Q+1 by omega, ite_true, if_true, Finset.sum_const_zero]
  ring

 
theorem pairTensorEmbed_apply {Q p i j : ℕ} (hij : i+j=p+1) (hp : p ≤ 2*Q-2)
    (f : GridVector) (k : ℕ) :
    pairTensorEmbed Q f i j k = coupledVector Q Q 1 p i j * f p k := by
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_single p
  · intro r _ hr
    rw [coupledVector_layer Q Q 1 r i j (by omega), zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem pairTensorEmbed_zero_zero (Q : ℕ) (f : GridVector) (k : ℕ) :
    pairTensorEmbed Q f 0 0 k = 0 := by
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_zero
  intro p _
  rw [coupledVector_layer Q Q 1 p 0 0 (by omega), zero_mul]

 

theorem pairSwapCompression_highest {Q z : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hz0 : 1 ≤ z) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z =
      (sphericalPairCoefficient Q z 1 z * highestCoefficient (2*Q-2) Q z z -
        sphericalPairCoefficient Q (z-1) 0 z * highestCoefficient (2*Q-2) Q z (z-1))/2 := by
  have h2 : Real.sqrt (2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject_top (by omega : 1 ≤ Q),
    swap23, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pairTensorEmbed_apply (by omega : 1+z=z+1) (by omega),
    pairTensorEmbed_apply (by omega : 0+z=(z-1)+1) (by omega)]
  rw [show coupledVector (2*Q-2) Q z 0 z 0 = highestCoefficient (2*Q-2) Q z z by
        simp [coupledVector, coupledCoefficient],
    show coupledVector (2*Q-2) Q z 0 (z-1) 1 = highestCoefficient (2*Q-2) Q z (z-1) by
      simp [coupledVector, coupledCoefficient, show z-1+1=z by omega]]
  rw [← sphericalPairCoefficient_coupled (by omega : 1 ≤ Q) (by omega),
    ← sphericalPairCoefficient_coupled (by omega : 1 ≤ Q) (by omega)]
  field_simp
  rw [h2]

 
theorem pairSwapCompression_highest_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q 0 0) 0 0 =
      highestCoefficient (2*Q-2) Q 0 0 / 2 := by
  have h2 : Real.sqrt (2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject_top (by omega : 1 ≤ Q),
    swap23, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pairTensorEmbed_apply (p := 0) (i := 1) (j := 0) rfl (by omega), pairTensorEmbed_zero_zero,
    pairCoupled_top (by omega : 1 ≤ Q)]
  simp only [coupledVector, coupledCoefficient, add_zero, ite_true, if_true, sub_zero, and_self,
    zero_ne_one, and_false, ite_false, div_mul_eq_mul_div]
  field_simp
  rw [h2]

 
theorem sphericalPairCoefficient_edge_one {Q : ℕ} (hQ : 1 ≤ Q) (z : ℕ) :
    sphericalPairCoefficient Q z 1 z = (1-z : ℝ) * Real.sqrt (fallingRatio Q z) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hz : (z.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero z
  simp only [sphericalPairCoefficient, add_comm 1 z, ite_true, if_true,
    Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, mul_one]
  congr 2
  unfold fallingRatio
  field_simp

 

theorem sphericalPairCoefficient_edge_zero {Q z : ℕ} (hQ : 1 ≤ Q) (hz0 : 1 ≤ z) :
    sphericalPairCoefficient Q (z-1) 0 z = -(z:ℝ) *
      Real.sqrt ((((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1)) / z) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hf : ((z-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (z-1)
  have he : Q.descFactorial z = Q * (Q-1).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hQ, ← Nat.sub_add_cancel hz0]
    rw [Nat.succ_descFactorial_succ, Nat.sub_add_cancel hQ]
  have hez : z.factorial = z * (z-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hz0]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hz0]
  simp only [sphericalPairCoefficient, Nat.zero_add, Nat.sub_add_cancel hz0, ite_true, if_true,
    Nat.cast_zero, zero_sub, Nat.descFactorial_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
  congr 2
  rw [he, hez, Nat.cast_mul, Nat.cast_mul]
  field_simp

 
theorem sqrt_mul_sqrt_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt (y*x) * Real.sqrt (x/y) = x := by
  rw [← Real.sqrt_mul (mul_nonneg hy.le hx)]
  convert Real.sqrt_mul_self hx using 2
  all_goals try with_reducible_and_instances rfl
  field_simp

 

theorem fallingRatio_penultimate {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (hz0 : 1 ≤ z) :
    ((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1) =
      fallingRatio Q z * ((2*Q-1-z : ℝ)/Q) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hd : ((2*Q-2).descFactorial (z-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (show z-1 ≤ 2*Q-2 by omega)).ne'
  have he : Q.descFactorial z = Q * (Q-1).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ Q), ← Nat.sub_add_cancel hz0]
    rw [Nat.succ_descFactorial_succ, Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have he' : (2*Q-2).descFactorial z = (2*Q-2-(z-1)) * (2*Q-2).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hz0]
    rw [Nat.descFactorial_succ]
  have hw : (2*Q-2-(z-1) : ℕ) = 2*Q-1-z := by omega
  have hc : ((2*Q-1-z : ℕ) : ℝ) = 2*(Q:ℝ)-1-z := by
    rw [Nat.cast_sub (by omega : z ≤ 2*Q-1), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
    push_cast
    rfl
  have hdz : (2*(Q:ℝ)-1-z) ≠ 0 := by
    rw [← hc]
    exact_mod_cast (show 2*Q-1-z ≠ 0 by omega)
  rw [fallingRatio, he, he', hw, Nat.cast_mul, Nat.cast_mul, hc]
  field_simp [hq, hd, hdz, mul_comm (Q:ℝ) 2]

 

theorem pairSwapCompression_scalar {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z =
      (-gramShift Q z / 2) * highestCoefficient (2*Q-2) Q z 0 := by
  by_cases hz0 : z=0
  · subst z
    rw [pairSwapCompression_highest_zero hQ]
    simp [gramShift, fallingRatio, div_eq_mul_inv, mul_comm]
  · have hzp : 1 ≤ z := by omega
    have hzn : z ≤ 2*Q-2 := by omega
    rw [pairSwapCompression_highest hQ hz hzp, sphericalPairCoefficient_edge_one (by omega),
      sphericalPairCoefficient_edge_zero (by omega) hzp,
      highestCoefficient_last hzn hz, highestCoefficient_penultimate hzn hz hzp]
    let x : ℝ := ((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hroot : Real.sqrt ((z:ℝ) * (Q-1).descFactorial (z-1) / (2*Q-2).descFactorial (z-1)) =
        Real.sqrt ((z:ℝ)*x) := by congr 1; dsimp [x]; ring
    rw [hroot]
    change ((1-(z:ℝ))*Real.sqrt (fallingRatio Q z) *
        ((-1:ℝ)^z * Real.sqrt (fallingRatio Q z) * highestCoefficient (2*Q-2) Q z 0) -
      (-(z:ℝ)*Real.sqrt (x/z)) * ((-1:ℝ)^(z-1) * Real.sqrt ((z:ℝ)*x) *
        highestCoefficient (2*Q-2) Q z 0)) / 2 = _
    have hsign : (-1:ℝ)^(z-1) = -(-1:ℝ)^z := by
      conv_rhs => rw [← Nat.sub_add_cancel hzp, pow_succ]
      ring
    have hs : Real.sqrt (fallingRatio Q z) ^ 2 = fallingRatio Q z :=
      Real.sq_sqrt (fallingRatio_nonneg Q z)
    have hs' : Real.sqrt ((z:ℝ)*x) * Real.sqrt (x/z) = x :=
      sqrt_mul_sqrt_div hx (by exact_mod_cast hzp)
    calc
      _ = ((-1:ℝ)^z * ((1-(z:ℝ)) * Real.sqrt (fallingRatio Q z)^2 -
          (z:ℝ)*(Real.sqrt ((z:ℝ)*x)*Real.sqrt (x/z)))) / 2 *
            highestCoefficient (2*Q-2) Q z 0 := by rw [hsign]; ring
      _ = ((-1:ℝ)^z * ((1-(z:ℝ))*fallingRatio Q z - (z:ℝ)*x)) / 2 *
            highestCoefficient (2*Q-2) Q z 0 := by rw [hs, hs']
      _ = _ := by
        rw [show x = fallingRatio Q z * ((2*Q-1-z : ℝ)/Q) from fallingRatio_penultimate hQ hz hzp]
        unfold gramShift
        have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
        field_simp
        ring

 

theorem pairSwapCompression_eigenvector {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z k) =
      (-gramShift Q z / 2) • coupledVector (2*Q-2) Q z k := by
  rw [pairSwapCompression_coupled hQ hz, pairSwapCompression_scalar hQ hz,
    mul_div_cancel_right₀ _ (highestCoefficient_first_ne_zero (by omega))]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeSpectrum
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spectrum. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

theorem pairSwapCompression_apply (Q : ℕ) (f : GridVector) (p j : ℕ) :
    pairSwapCompression Q f p j =
      ∑ r ∈ Finset.range (2*Q-2+1), ∑ k ∈ Finset.range (Q+1),
        (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r i j) * f r k := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject,
    pairTensorEmbed, swap23, LinearMap.coe_mk, AddHom.coe_mk, gridInner,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range (Q+1)) (t := Finset.range (2*Q-2+1))]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

 
theorem pairSwapCompression_apply_fin (Q : ℕ) (hQ : 1 ≤ Q)
    (f : GridVector) (p j : ℕ) :
    pairSwapCompression Q f p j =
      ∑ r : PairLabel Q, ∑ k : Orbital Q,
        (∑ i : Orbital Q,
          coupledVector Q Q 1 p i.val k.val * coupledVector Q Q 1 r.val i.val j) * f r.val k.val := by
  rw [pairSwapCompression_apply]
  symm
  calc
    _ = ∑ r : PairLabel Q, ∑ k ∈ Finset.range (Q+1),
        (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r.val i j) * f r.val k := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ∑ k : Orbital Q, (∑ i ∈ Finset.range (Q+1),
            coupledVector Q Q 1 p i k.val * coupledVector Q Q 1 r.val i j) * f r.val k.val := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          exact Fin.sum_univ_eq_sum_range
            (fun i => coupledVector Q Q 1 p i k.val * coupledVector Q Q 1 r.val i j) (Q+1)
        _ = _ := Fin.sum_univ_eq_sum_range
          (fun k => (∑ i ∈ Finset.range (Q+1),
            coupledVector Q Q 1 p i k * coupledVector Q Q 1 r.val i j) * f r.val k) (Q+1)
    _ = _ := by
      rw [show 2*Q-2+1 = 2*Q-1 by omega]
      exact Fin.sum_univ_eq_sum_range
        (fun r => ∑ k ∈ Finset.range (Q+1), (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r i j) * f r k) (2*Q-1)

 

theorem threeWedgeMatrix_gram_mulVec_grid (Q : ℕ) (hQ : 1 ≤ Q)
    (f : GridVector) (pj : PairLabel Q × Orbital Q) :
    (((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ
      (fun rk => (f rk.1.val rk.2.val : ℂ))) pj =
        (f pj.1.val pj.2.val : ℂ) - 2 *
          (pairSwapCompression Q f pj.1.val pj.2.val : ℂ) := by
  classical
  have hc (p : PairLabel Q) (j i : Orbital Q) :
      (pairCoefficient Q p.val j i : ℂ) =
        -(Real.sqrt 2 : ℂ) * (coupledVector Q Q 1 p.val i.val j.val : ℂ) := by
    rw [pairCoefficient_antisymm, pairCoefficient_eq_coupled hQ (by have := p.isLt; omega)]
    push_cast
    ring
  have htwo : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hex (rk : PairLabel Q × Orbital Q) :
      (∑ i : Orbital Q, (pairCoefficient Q pj.1.val rk.2 i : ℂ) *
          (pairCoefficient Q rk.1.val pj.2 i : ℂ)) =
        2 * (∑ i : Orbital Q, (coupledVector Q Q 1 pj.1.val i.val rk.2.val : ℂ) *
          (coupledVector Q Q 1 rk.1.val i.val pj.2.val : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, hc]
    calc
      _ = ((Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)) *
          ((coupledVector Q Q 1 pj.1.val i.val rk.2.val : ℂ) *
           (coupledVector Q Q 1 rk.1.val i.val pj.2.val : ℂ)) := by ring
      _ = _ := by rw [htwo]
  simp only [Matrix.mulVec, dotProduct, threeWedgeMatrix_gram_apply Q hQ, hex,
    sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ rk : PairLabel Q × Orbital Q,
      (if pj=rk then (1:ℂ) else 0) * (f rk.1.val rk.2.val : ℂ)) = f pj.1.val pj.2.val by simp]
  congr 1
  rw [pairSwapCompression_apply_fin Q hQ, Fintype.sum_prod_type]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring



theorem threeWedgeMatrix_gram_eigenvector {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ threeCoupledColumn Q z k =
      (1 + gramShift Q z : ℂ) • threeCoupledColumn Q z k := by
  funext pj
  unfold threeCoupledColumn
  rw [threeWedgeMatrix_gram_mulVec_grid Q (by omega),
    pairSwapCompression_eigenvector hQ hz]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

 

theorem coupledVector_resolution (n m : ℕ)
    (pq rs : Fin (n+1) × Fin (m+1)) :
    (∑ c : CoupledIndex n m,
      coupledVector n m c.1.val c.2.val pq.1.val pq.2.val *
        coupledVector n m c.1.val c.2.val rs.1.val rs.2.val) =
      if pq=rs then 1 else 0 := by
  classical
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, coupledBasis_apply, coupledEuclidean, gridEuclidean,
    PiLp.single_apply, eq_comm] using
      (coupledBasis n m).sum_inner_mul_inner
        (EuclideanSpace.single pq 1) (EuclideanSpace.single rs 1)



theorem threeCouplingMatrix_complete (Q : ℕ) (hQ : 1 ≤ Q) :
    threeCouplingMatrix Q * (threeCouplingMatrix Q)ᴴ = 1 := by
  classical
  ext pj rk
  have hdim : 2*Q-1 = 2*Q-2+1 := by omega
  let pq : Fin (2*Q-2+1) × Fin (Q+1) := (Fin.cast hdim pj.1, pj.2)
  let rs : Fin (2*Q-2+1) × Fin (Q+1) := (Fin.cast hdim rk.1, rk.2)
  have h := congrArg (fun t : ℝ => (t : ℂ)) (coupledVector_resolution (2*Q-2) Q pq rs)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    threeCouplingMatrix, threeCoupledColumn, Complex.star_def, Complex.conj_ofReal,
    Matrix.one_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    pq, rs, Fin.val_cast, Prod.mk.injEq, Fin.cast_inj, ← Prod.ext_iff,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h

 
theorem threeWedgeMatrix_gram_diagonal (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1 =
      threeCouplingMatrix Q *
        Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) *
          (threeCouplingMatrix Q)ᴴ := by
  classical
  have he : ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) * threeCouplingMatrix Q =
      threeCouplingMatrix Q * Matrix.diagonal
        (fun c : CoupledIndex (2*Q-2) Q => (1+gramShift Q c.1.val : ℂ)) := by
    ext pj c
    rw [Matrix.mul_diagonal]
    change (((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ
      threeCoupledColumn Q c.1.val c.2.val) pj =
        threeCoupledColumn Q c.1.val c.2.val pj * (1+gramShift Q c.1.val : ℂ)
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      congrArg (fun v => v pj)
        (threeWedgeMatrix_gram_eigenvector hQ (coupledIndex_bounds c).2.1 c.2.val)
  have he' := congrArg (fun M => M * (threeCouplingMatrix Q)ᴴ) he
  rw [Matrix.mul_assoc, threeCouplingMatrix_complete Q (by omega), Matrix.mul_one] at he'
  rw [he']
  have hsum : Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (1+gramShift Q c.1.val : ℂ)) =
      1 + Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
  rw [hsum, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    threeCouplingMatrix_complete Q (by omega)]
  abel



theorem threeSpinProjection_posSemidef (Q z : ℕ) : (threeSpinProjection Q z).PosSemidef := by
  classical
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro c
  split_ifs <;> norm_num



theorem threeWedgeMatrix_gram_spectral (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1 =
      ∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z := by
  classical
  rw [threeWedgeMatrix_gram_diagonal Q hQ]
  have hd : Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) =
      ∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) •
        Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) := by
    ext c d
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : c=d
    · subst d
      simp only [ite_true, if_true, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by have := coupledIndex_bounds c; omega))]
    · simp [h]
  rw [hd]
  simp only [threeSpinProjection, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_HighestTails
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem sum_gram_comparison {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : α → Matrix ι ι ℂ) (B : β → Matrix ι ι ℂ)
    (h : ∀ ψ : ι → ℂ, (∑ a, ∑ i, ‖(A a *ᵥ ψ) i‖^2) ≤
      ∑ b, ∑ i, ‖(B b *ᵥ ψ) i‖^2) :
    ((∑ b, (B b)ᴴ * B b) - ∑ a, (A a)ᴴ * A a).PosSemidef := by
  classical
  have hA : (∑ a, (A a)ᴴ * A a).IsHermitian :=
    (Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hB : (∑ b, (B b)ᴴ * B b).IsHermitian :=
    (Matrix.posSemidef_sum _ fun b _ => Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hH := hB.sub hA
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro ψ
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self ψ).symm⟩
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
    gram_quadratic_form, star_dotProduct_self, Complex.sub_re,
    Complex.re_sum, Complex.ofReal_re]
  exact sub_nonneg.mpr (h ψ)



theorem unit_vector_contracts_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (hs : ∑ i, s i ^ 2 = 1) (x : ι → κ → ℂ) :
    (∑ k, ‖∑ i, (s i : ℂ) * x i k‖^2) ≤ ∑ i, ∑ k, ‖x i k‖^2 := by
  classical
  let S : Matrix Unit ι ℂ := fun _ i => s i
  have hS : S * Sᴴ = 1 := by
    ext u v
    have hu : u=() := by cases u; rfl
    have hv : v=() := by cases v; rfl
    subst u v
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hs
    change (∑ i, (s i : ℂ) * star (s i : ℂ)) = 1
    simpa only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum,
      Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_mul, pow_two] using hc
  have h := row_isometry_contracts_family S hS x
  simpa only [S, Fintype.sum_unique] using h



theorem highestThreeAnnihilator_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ A, ‖(highestThreeAnnihilator Q z hz *ᵥ ψ) A‖^2) ≤
      ∑ p : Fin (z+1), ∑ A, ‖(pairAnnihilator Q p.val *ᵥ ψ) A‖^2 := by
  have hn : ∑ p : Fin (z+1), highestCoefficient (2*Q-2) Q z p.val ^ 2 = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient (2*Q-2) Q z p ^ 2) (z+1)]
    exact highestCoefficient_norm (by omega)
  have h := unit_vector_contracts_family _ hn
    (fun p A => ((annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val) *ᵥ ψ) A)
  calc
    _ ≤ ∑ p : Fin (z+1), ∑ A,
        ‖((annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val) *ᵥ ψ) A‖^2 := by
      simpa only [highestThreeAnnihilator, Matrix.sum_mulVec, Matrix.smul_mulVec,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Matrix.mulVec_mulVec] using
        annihilator_contracts Q ⟨z-p.val, by omega⟩ (pairAnnihilator Q p.val *ᵥ ψ)

 

theorem highestThreeAnnihilator_pair_posSemidef {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((∑ p : Fin (z+1), (pairAnnihilator Q p.val)ᴴ * pairAnnihilator Q p.val) -
      (highestThreeAnnihilator Q z hz)ᴴ * highestThreeAnnihilator Q z hz).PosSemidef := by
  have h : ∀ ψ : Occupation Q → ℂ,
      (∑ _ : Unit, ∑ A, ‖(highestThreeAnnihilator Q z hz *ᵥ ψ) A‖^2) ≤
        ∑ p : Fin (z+1), ∑ A, ‖(pairAnnihilator Q p.val *ᵥ ψ) A‖^2 := by
    simpa only [Fintype.sum_unique] using highestThreeAnnihilator_bound hQ hz
  simpa only [Fintype.sum_unique] using
    sum_gram_comparison (fun _ : Unit => highestThreeAnnihilator Q z hz)
      (fun p : Fin (z+1) => pairAnnihilator Q p.val) h

 

theorem wedgeAnnihilator_mulVec {ι : Type*} [Fintype ι] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) ι ℂ) (s : ι → ℂ) :
    wedgeAnnihilator Q k (W *ᵥ s) =
      ∑ i, star (s i) • wedgeAnnihilator Q k (fun A => W A i) := by
  classical
  simp only [wedgeAnnihilator, Matrix.mulVec, dotProduct, star_sum, star_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

 

theorem threeWedgeMatrix_annihilator_column (Q : ℕ) (pj : PairLabel Q × Orbital Q) :
    wedgeAnnihilator Q 3 (fun A => threeWedgeMatrix Q A pj) =
      annihilator Q pj.2 * pairAnnihilator Q pj.1.val := by
  apply wedgeAnnihilator_annihilatorVector
  exact orbitalPair_mem Q pj.1.val pj.2

 

theorem highestThreeAnnihilator_eq_wedge {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestThreeAnnihilator Q z hz =
      wedgeAnnihilator Q 3 (threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z 0) := by
  classical
  rw [wedgeAnnihilator_mulVec]
  simp_rw [threeWedgeMatrix_annihilator_column]
  let e : Fin (z+1) → PairLabel Q × Orbital Q :=
    fun p => (⟨p.val, by have := p.isLt; omega⟩, ⟨z-p.val, by omega⟩)
  have he : Function.Injective e := by
    intro p q h
    exact Fin.ext (congrArg (fun b => b.1.val) h)
  unfold highestThreeAnnihilator
  apply Fintype.sum_of_injective e he
  · intro pj hpj
    have hn : pj.1.val+pj.2.val ≠ z := by
      intro h
      apply hpj
      refine ⟨⟨pj.1.val, by omega⟩, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp [e]
        omega
    simp [threeCoupledColumn, coupledVector, hn]
  · intro p
    have hp : p.val+(z-p.val) = z := by have := p.isLt; omega
    simp only [e, threeCoupledColumn, coupledVector, Nat.add_zero, ite_eq_left hp,
      coupledCoefficient, Complex.star_def, Complex.conj_ofReal]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Vectors. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder


theorem annihilatorVector_wedgeAnnihilator (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    annihilatorVector Q k (wedgeAnnihilator Q k v) = v := by
  classical
  funext A
  simp only [annihilatorVector, wedgeAnnihilator, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, basisAnnihilator_vacuum, Subtype.val_inj, mul_ite, mul_one, mul_zero]
  simp

 
theorem wedgeAnnihilator_injective (Q k : ℕ) : Function.Injective (wedgeAnnihilator Q k) := by
  intro v w h
  have hv := congrArg (annihilatorVector Q k) h
  simpa only [annihilatorVector_wedgeAnnihilator] using hv



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SpinSchur
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Schur. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory

section Derivative
open scoped Matrix.Norms.Operator

 
theorem matrix_commutes_generator_of_flow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ)
    (h : ∀ t : ℝ, A * exp ((t : ℂ) • X) = exp ((t : ℂ) • X) * A) :
    A * X = X * A := by
  have hc (t : ℝ) : (t : ℂ) • X = t • X := by
    exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) t X).symm
  simp_rw [hc] at h
  have he : (fun t : ℝ => A * exp (t • X)) = (fun t => exp (t • X) * A) := funext h
  have hd := hasDerivAt_exp_smul_const X (0 : ℝ)
  have h₁ : HasDerivAt (fun t : ℝ => A * exp (t • X))
      (A * (exp ((0 : ℝ) • X) * X)) 0 := hd.const_mul A
  have h₂ := hd.mul_const A
  rw [he] at h₁
  simpa only [zero_smul, exp_zero, Matrix.one_mul] using! h₁.unique h₂

 

theorem rotationAverage_commutes_generator {J σ : Type*} {I : J → Type*}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j)
    (j : J) (M : Matrix (I j) (I j) ℂ) (s : σ) :
    rotationAverage X hX j M * X s j = X s j * rotationAverage X hX j M := by
  apply matrix_commutes_generator_of_flow
  intro t
  exact rotationAverage_commutes X hX j M
    ⟨rotationFlow X hX s t, rotationFlow_mem_group X hX s t⟩

end Derivative



theorem spinGenerator_intertwiner {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator m s) :
    spinLowerMatrix n * A = A * spinLowerMatrix m ∧
    (spinLowerMatrix n)ᴴ * A = A * (spinLowerMatrix m)ᴴ ∧
    spinWeightMatrix n * A = A * spinWeightMatrix m := by
  have h₀ : (spinLowerMatrix n - (spinLowerMatrix n)ᴴ) * A =
      A * (spinLowerMatrix m - (spinLowerMatrix m)ᴴ) := by
    simpa [spinGenerator] using hA 0
  have h₁ : (Complex.I • (spinLowerMatrix n + (spinLowerMatrix n)ᴴ)) * A =
      A * (Complex.I • (spinLowerMatrix m + (spinLowerMatrix m)ᴴ)) := by
    simpa [spinGenerator] using hA 1
  have h₂ : (Complex.I • spinWeightMatrix n) * A =
      A * (Complex.I • spinWeightMatrix m) := by
    simpa [spinGenerator] using hA 2
  simp only [Matrix.smul_mul, Matrix.mul_smul] at h₁ h₂
  have hi : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have he₁ := smul_right_injective _ hi h₁
  have he₂ := smul_right_injective _ hi h₂
  refine ⟨?_, ?_, he₂⟩
  · ext i j
    have he := congrArg (fun M => M i j) h₀
    have hf := congrArg (fun M => M i j) he₁
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_apply, Matrix.add_apply] at he hf
    linear_combination (he + hf) / 2
  · ext i j
    have he := congrArg (fun M => M i j) h₀
    have hf := congrArg (fun M => M i j) he₁
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_apply, Matrix.add_apply] at he hf
    linear_combination (hf - he) / 2

 

theorem mul_spinLower_succ {κ : Type*} {n : ℕ}
    (A : Matrix κ (Fin (n+1)) ℂ) (i : κ) (j : ℕ) (hj : j < n) :
    (A * spinLowerMatrix n) i ⟨j, by omega⟩ =
      A i ⟨j+1, by omega⟩ * (spinStep n (j+1) : ℂ) := by
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨j+1, by omega⟩ : Fin (n+1))]
  · simp [spinLowerMatrix]
  · intro b _ hb
    have hne : b.val ≠ j+1 := fun he => hb (Fin.ext he)
    simp [spinLowerMatrix, hne]
  · simp

 
theorem mul_spinRaise_zero {κ : Type*} {n : ℕ}
    (A : Matrix κ (Fin (n+1)) ℂ) (i : κ) :
    (A * (spinLowerMatrix n)ᴴ) i 0 = 0 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, spinLowerMatrix]

 
theorem spinRaise_mul_pred {κ : Type*} {n : ℕ}
    (A : Matrix (Fin (n+1)) κ ℂ) (i : Fin (n+1)) (hi : 0 < i.val) (j : κ) :
    ((spinLowerMatrix n)ᴴ * A) ⟨i.val-1, by omega⟩ j =
      (spinStep n i.val : ℂ) * A i j := by
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.conjTranspose_apply, spinLowerMatrix, Nat.sub_add_cancel hi]
  · intro b _ hb
    have hne : b.val ≠ i.val := fun he => hb (Fin.ext he)
    simp [Matrix.conjTranspose_apply, spinLowerMatrix, Nat.sub_add_cancel hi, hne]
  · simp

 

theorem spin_intertwiner_zero_of_first_column {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hL : spinLowerMatrix n * A = A * spinLowerMatrix m)
    (h₀ : ∀ i, A i 0 = 0) : A = 0 := by
  have hc (k : ℕ) (hk : k ≤ m) : ∀ i, A i ⟨k, by omega⟩ = 0 := by
    induction k with
    | zero => exact h₀
    | succ k ih =>
      have ih' := ih (by omega)
      intro i
      have he := congrArg (fun R => R i (⟨k, by omega⟩ : Fin (m+1))) hL
      rw [mul_spinLower_succ A i k (by omega)] at he
      have hz : (spinLowerMatrix n * A) i ⟨k, by omega⟩ = 0 := by
        simp only [Matrix.mul_apply, ih', mul_zero, Finset.sum_const_zero]
      rw [hz] at he
      have hs : (spinStep m (k+1) : ℂ) ≠ 0 := by
        exact_mod_cast (spinStep_pos (by omega) hk).ne'
      exact (mul_eq_zero.mp he.symm).resolve_right hs
  ext i j
  exact hc j.val (by omega) i

theorem spin_intertwiner_first_column {n m : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hR : (spinLowerMatrix n)ᴴ * A = A * (spinLowerMatrix m)ᴴ)
    (i : Fin (n+1)) (hi : 0 < i.val) : A i 0 = 0 := by
  have he := congrArg (fun R => R (⟨i.val-1, by omega⟩ : Fin (n+1)) 0) hR
  rw [spinRaise_mul_pred A i hi, mul_spinRaise_zero] at he
  have hs : (spinStep n i.val : ℂ) ≠ 0 := by
    exact_mod_cast (spinStep_pos hi (by omega)).ne'
  exact (mul_eq_zero.mp he).resolve_left hs

 

theorem spin_intertwiner_scalar {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator n s) :
    A = A 0 0 • 1 := by
  obtain ⟨hL,hR,_⟩ := spinGenerator_intertwiner A hA
  have he : A - A 0 0 • 1 = 0 := by
    apply spin_intertwiner_zero_of_first_column
    · simp [Matrix.mul_sub, Matrix.sub_mul, hL]
    · intro i
      by_cases hi : i = 0
      · subst i; simp
      · have hip : 0 < i.val := by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega
        simp [Matrix.sub_apply, Matrix.smul_apply, hi,
          spin_intertwiner_first_column A hR i hip]
  exact sub_eq_zero.mp he

 

theorem spin_intertwiner_zero_of_ne {n m : ℕ} (hnm : n ≠ m)
    (A : Matrix (Fin (n+1)) (Fin (m+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator m s) : A = 0 := by
  obtain ⟨hL,hR,hW⟩ := spinGenerator_intertwiner A hA
  apply spin_intertwiner_zero_of_first_column A hL
  intro i
  by_cases hi : i = 0
  · subst i
    have he := congrArg (fun R => R 0 0) hW
    simp [spinWeightMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : ((n : ℂ)-(m : ℂ)) * A 0 0 = 0 := by linear_combination he
    have hn : (n : ℂ)-(m : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
    exact (mul_eq_zero.mp hz).resolve_left hn
  · have hip : 0 < i.val := by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    exact spin_intertwiner_first_column A hR i hip

theorem spin_intertwiner_trace_scalar {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hA : ∀ s, spinGenerator n s * A = A * spinGenerator n s) :
    A = (A.trace / (n+1 : ℂ)) • 1 := by
  have he := spin_intertwiner_scalar A hA
  have ht := congrArg Matrix.trace he
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz : A 0 0 = A.trace / (n+1 : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa [Matrix.trace_smul, Matrix.trace_one] using ht.symm
  rwa [hz] at he

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FockRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fock Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem fockAverage_exteriorLift (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    fockAverage Q (exteriorLift Q k M) = exteriorLift Q k (sectorAverage Q k M) := by
  exact (rotationAverage_covariance (fockRotationGenerator Q) (fockRotationGenerator_skew Q)
    (i:=.sector k) (j:=.fock) (exteriorLiftLinear Q k)
    (fun s M => (oneBody_exteriorLift_commutator Q k (spinGenerator Q s) M).symm) M).symm

theorem fockAverage_posSemidef (Q : ℕ) (M : FockMatrix Q) (hM : M.PosSemidef) :
    (fockAverage Q M).PosSemidef :=
  rotationAverage_posSemidef (fockRotationGenerator Q) (fockRotationGenerator_skew Q) .fock M hM



theorem spinRotationAverage (Q n : ℕ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M =
      (M.trace / (n+1 : ℂ)) • 1 := by
  have he := spin_intertwiner_trace_scalar
    (rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M)
    (fun s => (rotationAverage_commutes_generator (fockRotationGenerator Q)
      (fockRotationGenerator_skew Q) (.spin n) M s).symm)
  rw [rotationAverage_trace] at he
  exact he



theorem congruenceLinear_commutator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (hC : Y*C = C*X)
    (M : Matrix ι ι ℂ) :
    congruenceLinear C (X*M-M*X) = Y * congruenceLinear C M - congruenceLinear C M * Y := by
  have hC' : Cᴴ * Y = X * Cᴴ := by
    have hh := congrArg Matrix.conjTranspose hC
    simpa only [Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg, Matrix.neg_mul,
      neg_inj] using hh
  change C * (X*M-M*X) * Cᴴ = Y*(C*M*Cᴴ) - (C*M*Cᴴ)*Y
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y C, hC, Matrix.mul_assoc, hC']

 

theorem sectorAverage_spin_sandwich {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    sectorAverage Q k (C*M*Cᴴ) = (M.trace / (n+1 : ℂ)) • (C*Cᴴ) := by
  have hc := rotationAverage_covariance (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.sector k)
    (congruenceLinear C) (fun s M => congruenceLinear_commutator _ _ C
      (spinGenerator_skew n s) (fockRotationGenerator_skew Q s (.sector k)) (hC s) M) M
  change C * rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M * Cᴴ =
    rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k) (C*M*Cᴴ) at hc
  change rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k) (C*M*Cᴴ) = _
  rw [← hc, spinRotationAverage]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

 

theorem fockAverage_spin_sandwich {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    fockAverage Q (exteriorLift Q k (C*M*Cᴴ)) =
      (M.trace / (n+1 : ℂ)) • exteriorLift Q k (C*Cᴴ) := by
  rw [fockAverage_exteriorLift, sectorAverage_spin_sandwich C hC]
  exact (exteriorLiftLinear Q k).map_smul _ _

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_WedgeLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem wedgeAnnihilator_neg (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k (-v) = -wedgeAnnihilator Q k v := by
  simp only [wedgeAnnihilator, Pi.neg_apply, star_neg, neg_smul, Finset.sum_neg_distrib]

 

theorem oneBody_wedgeAnnihilator_commutator_skew (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (v : SectorOccupation Q k → ℂ) :
    oneBodyLift Q A * wedgeAnnihilator Q k v -
      wedgeAnnihilator Q k v * oneBodyLift Q A =
      wedgeAnnihilator Q k (sectorOneBody Q k A *ᵥ v) := by
  rw [oneBody_wedgeAnnihilator_commutator, sectorOneBody_adjoint, hA]
  have hn := (sectorOneBodyLinear Q k).map_neg A
  change sectorOneBody Q k (-A) = -sectorOneBody Q k A at hn
  rw [hn, Matrix.neg_mulVec, wedgeAnnihilator_neg, neg_neg]

 

theorem sector_intertwiner_of_commutators {ι : Type*} [Fintype ι] (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (C : Matrix (SectorOccupation Q k) ι ℂ)
    (B : ι → FockMatrix Q)
    (hB : ∀ i, wedgeAnnihilator Q k (fun T => C T i) = B i)
    (hcomm : ∀ j, oneBodyLift Q A * B j - B j * oneBodyLift Q A =
      ∑ i, star (X i j) • B i) :
    sectorOneBody Q k A * C = C*X := by
  ext T j
  have he : wedgeAnnihilator Q k (sectorOneBody Q k A *ᵥ (fun T => C T j)) =
      wedgeAnnihilator Q k (C *ᵥ (fun i => X i j)) := by
    rw [← oneBody_wedgeAnnihilator_commutator_skew Q k A hA, hB,
      wedgeAnnihilator_mulVec]
    simp only [hB]
    exact hcomm j
  exact congrFun (wedgeAnnihilator_injective Q k he) T

 
theorem wedge_intertwiner_commutator {ι : Type*} [Fintype ι] (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (C : Matrix (SectorOccupation Q k) ι ℂ)
    (hC : sectorOneBody Q k A * C = C*X) (j : ι) :
    oneBodyLift Q A * wedgeAnnihilator Q k (fun T => C T j) -
      wedgeAnnihilator Q k (fun T => C T j) * oneBodyLift Q A =
      ∑ i, star (X i j) • wedgeAnnihilator Q k (fun T => C T i) := by
  rw [oneBody_wedgeAnnihilator_commutator_skew Q k A hA]
  have hh : sectorOneBody Q k A *ᵥ (fun T => C T j) = C *ᵥ (fun i => X i j) := by
    exact congrArg (fun M => fun T => M T j) hC
  rw [hh, wedgeAnnihilator_mulVec]


theorem tensorSum_apply {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (i j : ι × κ) :
    tensorSum X Y i j = (if i.2=j.2 then X i.1 j.1 else 0) +
      (if i.1=j.1 then Y i.2 j.2 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [tensorSum, Matrix.add_apply, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]



theorem wedgeProductMatrix_contraction {ι κ : Type*} (Q k l : ℕ)
    (V : Matrix (SectorOccupation Q k) ι ℂ) (W : Matrix (SectorOccupation Q l) κ ℂ)
    (ij : ι × κ) :
    wedgeAnnihilator Q (k+l) (fun T => wedgeProductMatrix Q k l V W T ij) =
      wedgeAnnihilator Q l (fun T => W T ij.2) *
        wedgeAnnihilator Q k (fun T => V T ij.1) := by
  apply wedgeAnnihilator_annihilatorVector
  exact annihilationSpace_mul Q k l (wedgeAnnihilator_mem Q k _) (wedgeAnnihilator_mem Q l _)

 

theorem wedgeProductMatrix_intertwines {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Q k l : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ)
    (V : Matrix (SectorOccupation Q k) ι ℂ) (W : Matrix (SectorOccupation Q l) κ ℂ)
    (hV : sectorOneBody Q k A * V = V*X) (hW : sectorOneBody Q l A * W = W*Y) :
    sectorOneBody Q (k+l) A * wedgeProductMatrix Q k l V W =
      wedgeProductMatrix Q k l V W * tensorSum X Y := by
  apply sector_intertwiner_of_commutators Q (k+l) A hA (tensorSum X Y)
    (wedgeProductMatrix Q k l V W)
    (fun ij => wedgeAnnihilator Q l (fun T => W T ij.2) *
      wedgeAnnihilator Q k (fun T => V T ij.1))
    (wedgeProductMatrix_contraction Q k l V W)
  intro ij
  rw [matrix_commutator_mul, wedge_intertwiner_commutator Q l A hA Y W hW,
    wedge_intertwiner_commutator Q k A hA X V hV]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    tensorSum_apply, star_add, apply_ite star, star_zero, add_smul, Finset.sum_add_distrib,
    Fintype.sum_prod_type, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  exact add_comm _ _


theorem oneParticleMatrix_contraction (Q : ℕ) (i : Orbital Q) :
    wedgeAnnihilator Q 1 (fun S => oneParticleMatrix Q S i) = annihilator Q i := by
  have he : (fun S => oneParticleMatrix Q S i) = annihilatorVector Q 1 (annihilator Q i) := by
    funext S
    simp [oneParticleMatrix, annihilatorVector, annihilator_vacuum, eq_comm]
  rw [he, wedgeAnnihilator_annihilatorVector Q 1 _ (annihilator_mem Q i)]

 
theorem oneParticleMatrix_intertwines (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A) :
    sectorOneBody Q 1 A * oneParticleMatrix Q = oneParticleMatrix Q * A := by
  apply sector_intertwiner_of_commutators Q 1 A hA A (oneParticleMatrix Q)
    (annihilator Q) (oneParticleMatrix_contraction Q)
  intro j
  rw [← neg_sub, annihilator_oneBody_commutator]
  have hh (i : Orbital Q) : star (A i j) = -A j i := by
    exact congrArg (fun M => M j i) hA
  simp only [hh, neg_smul, Finset.sum_neg_distrib]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CoupledLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupled Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem spinLower_sum (n : ℕ) (i : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), spinLowerMatrix n i a * f a.val) =
      (spinStep n i.val : ℂ) * f (i.val-1) := by
  classical
  by_cases hi : i.val=0
  · simp [spinLowerMatrix, hi]
  · have hip : 0 < i.val := by omega
    rw [Finset.sum_eq_single (⟨i.val-1, by omega⟩ : Fin (n+1))]
    · simp [spinLowerMatrix, Nat.sub_add_cancel hip]
    · intro b _ hb
      have hn : i.val ≠ b.val+1 := by
        intro he; apply hb; apply Fin.ext; dsimp only; omega
      simp [spinLowerMatrix, hn]
    · simp

theorem spinRaise_sum (n : ℕ) (i : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), (spinLowerMatrix n)ᴴ i a * f a.val) =
      (spinStep n (i.val+1) : ℂ) * f (i.val+1) := by
  classical
  by_cases hi : i.val < n
  · rw [Finset.sum_eq_single (⟨i.val+1, by omega⟩ : Fin (n+1))]
    · simp [Matrix.conjTranspose_apply, spinLowerMatrix]
    · intro b _ hb
      have hn : b.val ≠ i.val+1 := fun he => hb (Fin.ext he)
      simp [Matrix.conjTranspose_apply, spinLowerMatrix, hn]
    · simp
  · have he : i.val=n := by omega
    have hz (b : Fin (n+1)) : b.val ≠ i.val+1 := by omega
    simp only [Matrix.conjTranspose_apply, spinLowerMatrix, ite_eq_right (hz _)]
    simp [he]

theorem sum_spinLower (n : ℕ) (j : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), f a.val * spinLowerMatrix n a j) =
      (spinStep n (j.val+1) : ℂ) * f (j.val+1) := by
  have he (a : Fin (n+1)) : spinLowerMatrix n a j = (spinLowerMatrix n)ᴴ j a := by
    simp only [spinLowerMatrix, Matrix.conjTranspose_apply]
    split_ifs <;> simp
  simpa only [he, mul_comm] using spinRaise_sum n j f

theorem sum_spinRaise (n : ℕ) (j : Fin (n+1)) (f : ℕ → ℂ) :
    (∑ a : Fin (n+1), f a.val * (spinLowerMatrix n)ᴴ a j) =
      (spinStep n j.val : ℂ) * f (j.val-1) := by
  have he (a : Fin (n+1)) : (spinLowerMatrix n)ᴴ a j = spinLowerMatrix n j a := by
    simp only [spinLowerMatrix, Matrix.conjTranspose_apply]
    split_ifs <;> simp
  simpa only [he, mul_comm] using spinLower_sum n j f

theorem tensorSum_mul_apply {ι κ β : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix (ι × κ) β ℂ)
    (i : ι) (j : κ) (k : β) :
    (tensorSum X Y * C) (i,j) k =
      (∑ a, X i a * C (a,j) k) + ∑ b, Y j b * C (i,b) k := by
  classical
  simp only [Matrix.mul_apply, tensorSum_apply, add_mul, Finset.sum_add_distrib,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  congr 1
  rw [Finset.sum_comm]
  simp



theorem tensorLower_coupled_apply (n m z : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (k : Fin (n+m-2*z+1)) :
    (tensorSum (spinLowerMatrix n) (spinLowerMatrix m) * coupledSpinMatrix n m z) (i,j) k =
      (gridLower n m (coupledVector n m z k.val) i.val j.val : ℂ) := by
  rw [tensorSum_mul_apply]
  change (∑ a : Fin (n+1), spinLowerMatrix n i a *
      (coupledVector n m z k.val a.val j.val : ℂ)) +
    (∑ a : Fin (m+1), spinLowerMatrix m j a *
      (coupledVector n m z k.val i.val a.val : ℂ)) = _
  rw [spinLower_sum n i (fun a => (coupledVector n m z k.val a j.val : ℂ)),
    spinLower_sum m j (fun a => (coupledVector n m z k.val i.val a : ℂ))]
  by_cases hi : i.val=0 <;> by_cases hj : j.val=0 <;>
    simp [gridLower, hi, hj]

theorem tensorRaise_coupled_apply (n m z : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (k : Fin (n+m-2*z+1)) :
    (tensorSum (spinLowerMatrix n)ᴴ (spinLowerMatrix m)ᴴ * coupledSpinMatrix n m z) (i,j) k =
      (gridRaise n m (coupledVector n m z k.val) i.val j.val : ℂ) := by
  rw [tensorSum_mul_apply]
  change (∑ a : Fin (n+1), (spinLowerMatrix n)ᴴ i a *
      (coupledVector n m z k.val a.val j.val : ℂ)) +
    (∑ a : Fin (m+1), (spinLowerMatrix m)ᴴ j a *
      (coupledVector n m z k.val i.val a.val : ℂ)) = _
  rw [spinRaise_sum n i (fun a => (coupledVector n m z k.val a j.val : ℂ)),
    spinRaise_sum m j (fun a => (coupledVector n m z k.val i.val a : ℂ))]
  simp [gridRaise]

theorem coupledSpinMatrix_lower {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinLowerMatrix n) (spinLowerMatrix m) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinLowerMatrix (n+m-2*z) := by
  ext ⟨i,j⟩ k
  rw [tensorLower_coupled_apply, coupledVector_lower_all hn hm]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.mul_apply,
    coupledSpinMatrix]
  exact (sum_spinLower (n+m-2*z) k (fun t => (coupledVector n m z t i.val j.val : ℂ))).symm

theorem coupledSpinMatrix_raise {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinLowerMatrix n)ᴴ (spinLowerMatrix m)ᴴ * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * (spinLowerMatrix (n+m-2*z))ᴴ := by
  ext ⟨i,j⟩ k
  rw [tensorRaise_coupled_apply, coupledVector_raise_all hn hm]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.mul_apply,
    coupledSpinMatrix]
  exact (sum_spinRaise (n+m-2*z) k (fun t => (coupledVector n m z t i.val j.val : ℂ))).symm

theorem coupledSpinMatrix_weight {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    tensorSum (spinWeightMatrix n) (spinWeightMatrix m) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinWeightMatrix (n+m-2*z) := by
  ext ⟨i,j⟩ k
  rw [tensorSum_mul_apply]
  simp only [spinWeightMatrix, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Matrix.mul_diagonal, coupledSpinMatrix]
  by_cases hl : i.val+j.val=z+k.val
  · have he : (n : ℂ) - 2*i.val + ((m : ℂ)-2*j.val) =
        ((n+m-2*z : ℕ) : ℂ) - 2*k.val := by
      push_cast [Nat.cast_sub (show 2*z ≤ n+m by omega)]
      have hh : (i.val : ℂ)+j.val = z+k.val := by exact_mod_cast hl
      linear_combination -2 * hh
    rw [← add_mul, he, mul_comm]
  · simp [coupledVector, hl]

theorem tensorSum_add {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X X' : Matrix ι ι ℂ) (Y Y' : Matrix κ κ ℂ) :
    tensorSum (X+X') (Y+Y') = tensorSum X Y + tensorSum X' Y' := by
  ext i j
  simp only [tensorSum_apply, Matrix.add_apply]
  split_ifs <;> ring

theorem tensorSum_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (c : ℂ) :
    tensorSum (c•X) (c•Y) = c • tensorSum X Y := by
  ext i j
  simp only [tensorSum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem tensorSum_sub {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X X' : Matrix ι ι ℂ) (Y Y' : Matrix κ κ ℂ) :
    tensorSum (X-X') (Y-Y') = tensorSum X Y - tensorSum X' Y' := by
  ext i j
  simp only [tensorSum_apply, Matrix.sub_apply]
  split_ifs <;> ring

 
theorem coupledSpinMatrix_intertwines {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (s : Fin 3) :
    tensorSum (spinGenerator n s) (spinGenerator m s) * coupledSpinMatrix n m z =
      coupledSpinMatrix n m z * spinGenerator (n+m-2*z) s := by
  fin_cases s <;> simp only [spinGenerator, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  · rw [tensorSum_sub, Matrix.sub_mul, coupledSpinMatrix_lower hn hm,
      coupledSpinMatrix_raise hn hm, Matrix.mul_sub]
  · rw [tensorSum_smul, tensorSum_add, Matrix.smul_mul, Matrix.add_mul,
      coupledSpinMatrix_lower hn hm, coupledSpinMatrix_raise hn hm,
      Matrix.mul_smul, Matrix.mul_add]
  · rw [tensorSum_smul, Matrix.smul_mul, coupledSpinMatrix_weight hn hm, Matrix.mul_smul]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RectangularOrbit
attribute [-instance] _root_.OAI.LaughlinFock.rotationHaar_leftInvariant _root_.OAI.LaughlinFock.rotationHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

section Exponential
open scoped Matrix.Norms.Operator

 

theorem matrix_exp_intertwiner {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (h : Y*C = C*X) : exp Y * C = C * exp X := by
  have hp (n : ℕ) : Y^n*C = C*X^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hL := (mulRightLinearMap κ ℂ C).toContinuousLinearMap.hasSum
    (exp_series_hasSum_exp' (𝕂:=ℂ) Y)
  have hR := (mulLeftLinearMap ι ℂ C).toContinuousLinearMap.hasSum
    (exp_series_hasSum_exp' (𝕂:=ℂ) X)
  simp only [LinearMap.coe_toContinuousLinearMap', mulRightLinearMap_apply,
    mulLeftLinearMap_apply, Matrix.smul_mul, Matrix.mul_smul, hp] at hL hR
  exact hL.unique hR

 

theorem matrix_intertwiner_generator_of_flow {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (h : ∀ t : ℝ, exp ((t:ℂ) • Y) * C = C * exp ((t:ℂ) • X)) :
    Y*C = C*X := by
  have he : (fun t : ℝ => exp (t • Y) * C) = (fun t : ℝ => C * exp (t • X)) := by
    funext t
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact h t
  have hL := (mulRightLinearMap κ ℂ C).toContinuousLinearMap.restrictScalars ℝ |>.hasFDerivAt
    |>.comp_hasDerivAt (0:ℝ) (hasDerivAt_exp_smul_const Y (0:ℝ))
  have hR := (mulLeftLinearMap ι ℂ C).toContinuousLinearMap.restrictScalars ℝ |>.hasFDerivAt
    |>.comp_hasDerivAt (0:ℝ) (hasDerivAt_exp_smul_const X (0:ℝ))
  change HasDerivAt (fun t : ℝ => exp (t • Y) * C) ((exp (0 • Y) * Y)*C) 0 at hL
  change HasDerivAt (fun t : ℝ => C * exp (t • X)) (C*(exp (0 • X)*X)) 0 at hR
  rw [he] at hL
  simpa only [zero_smul, exp_zero, Matrix.one_mul] using! hL.unique hR

end Exponential

section Groups
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]


open scoped Matrix.Norms.Elementwise

theorem intertwinerSubgroup_isClosed {i j : J} (C : Matrix (I j) (I i) ℂ) :
    IsClosed (intertwinerSubgroup C : Set (UnitaryFamily I)) := by
  change IsClosed {g : UnitaryFamily I | (g j).val*C = C*(g i).val}
  apply isClosed_eq <;> fun_prop

 

theorem rotationGroup_intertwiner
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) {i j : J}
    (C : Matrix (I j) (I i) ℂ) (hC : ∀ s, X s j*C = C*X s i)
    (g : rotationGroup X hX) : (g.val j).val*C = C*(g.val i).val := by
  have hle : rotationGroup X hX ≤ intertwinerSubgroup C := by
    apply Subgroup.topologicalClosure_minimal
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨⟨s,t⟩,rfl⟩
      change exp ((t:ℂ) • X s j)*C = C*exp ((t:ℂ) • X s i)
      exact matrix_exp_intertwiner _ _ C (by simp only [Matrix.smul_mul, Matrix.mul_smul, hC s])
    · exact intertwinerSubgroup_isClosed C
  exact hle g.property

end Groups
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CrossOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open MeasureTheory Topology

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)
attribute [local instance] OAI.LaughlinFock.crossOrbitRotationMeasurableSpace
local instance crossOrbitRotationBorelSpace : BorelSpace (rotationGroup X hX) := ⟨rfl⟩


attribute [local instance] OAI.LaughlinFock.crossOrbitContinuousENorm
theorem rotationCrossOrbit_integrable (i j : J) (M : Matrix (I i) (I j) ℂ) :
    Integrable (fun g => rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ)
      (rotationHaar X hX) := by
  have hc : Continuous (fun g => rotationEvaluation X hX i g * M *
      (rotationEvaluation X hX j g)ᴴ) :=
    ((rotationEvaluation_continuous X hX i).matrix_mul continuous_const).matrix_mul
      (rotationEvaluation_continuous X hX j).matrix_conjTranspose
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

 
theorem rotationCrossAverage_invariant (i j : J) (M : Matrix (I i) (I j) ℂ)
    (h : rotationGroup X hX) :
    rotationEvaluation X hX i h * rotationCrossAverage X hX i j M *
      (rotationEvaluation X hX j h)ᴴ = rotationCrossAverage X hX i j M := by
  unfold rotationCrossAverage
  rw [matrixIntegral_mul_left_right _ (rotationCrossOrbit_integrable X hX i j M)]
  calc
    _ = ∫ g, rotationEvaluation X hX i (h*g) * M * (rotationEvaluation X hX j (h*g))ᴴ
          ∂rotationHaar X hX := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ:=rotationHaar X hX)
      (fun g => rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ) h

theorem rotationCrossAverage_intertwines (i j : J) (M : Matrix (I i) (I j) ℂ)
    (h : rotationGroup X hX) :
    rotationEvaluation X hX i h * rotationCrossAverage X hX i j M =
      rotationCrossAverage X hX i j M * rotationEvaluation X hX j h := by
  have he := congrArg (fun A => A * rotationEvaluation X hX j h)
    (rotationCrossAverage_invariant X hX i j M h)
  simpa only [Matrix.mul_assoc, rotationEvaluation_unitary, Matrix.mul_one] using he

 

theorem rotationCrossAverage_intertwines_generator (i j : J) (M : Matrix (I i) (I j) ℂ)
    (s : σ) : X s i * rotationCrossAverage X hX i j M =
      rotationCrossAverage X hX i j M * X s j := by
  apply matrix_intertwiner_generator_of_flow
  intro t
  exact rotationCrossAverage_intertwines X hX i j M
    ⟨rotationFlow X hX s t, rotationFlow_mem_group X hX s t⟩

 

theorem rotationAverage_mixed_sandwich {i j k : J}
    (C : Matrix (I k) (I i) ℂ) (D : Matrix (I k) (I j) ℂ)
    (hC : ∀ s, X s k*C = C*X s i) (hD : ∀ s, X s k*D = D*X s j)
    (M : Matrix (I i) (I j) ℂ) :
    rotationAverage X hX k (C*M*Dᴴ) = C * rotationCrossAverage X hX i j M * Dᴴ := by
  unfold rotationAverage matrixConjugationAverage rotationCrossAverage
  rw [matrixIntegral_mul_left_right _ (rotationCrossOrbit_integrable X hX i j M)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have hc := rotationGroup_intertwiner X hX C hC g
  have hd : Dᴴ * (rotationEvaluation X hX k g)ᴴ =
      (rotationEvaluation X hX j g)ᴴ * Dᴴ := by
    have he := congrArg Matrix.conjTranspose (rotationGroup_intertwiner X hX D hD g)
    simp only [Matrix.conjTranspose_mul] at he
    exact he
  change rotationEvaluation X hX k g*C = C*rotationEvaluation X hX i g at hc
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rotationEvaluation X hX k g) C, hc]
  simp only [Matrix.mul_assoc, hd]

end

 
theorem spinRotationCrossAverage_zero {Q n m : ℕ} (hnm : n ≠ m)
    (M : Matrix (Fin (n+1)) (Fin (m+1)) ℂ) :
    rotationCrossAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q)
      (.spin n) (.spin m) M = 0 := by
  apply spin_intertwiner_zero_of_ne hnm
  intro s
  exact rotationCrossAverage_intertwines_generator
    (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) (.spin m) M s

 

theorem sectorAverage_spin_mixed_sandwich {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    sectorAverage Q k (C*M*Dᴴ) = (M.trace / (n+1 : ℂ)) • (C*Dᴴ) := by
  have h := rotationAverage_mixed_sandwich (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.spin n) (k:=.sector k) C D hC hD M
  change sectorAverage Q k (C*M*Dᴴ) = C * rotationAverage (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (.spin n) M * Dᴴ at h
  rw [h, spinRotationAverage]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

 
theorem sectorAverage_spin_cross_sandwich {Q k n m : ℕ} (hnm : n ≠ m)
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (D : Matrix (SectorOccupation Q k) (Fin (m+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator m s)
    (M : Matrix (Fin (n+1)) (Fin (m+1)) ℂ) :
    sectorAverage Q k (C*M*Dᴴ) = 0 := by
  have h := rotationAverage_mixed_sandwich (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.spin m) (k:=.sector k) C D hC hD M
  rw [spinRotationCrossAverage_zero hnm, Matrix.mul_zero, Matrix.zero_mul] at h
  exact h


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NullComponents
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null Components. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

theorem gramShift_zero (Q : ℕ) : gramShift Q 0 = -1 := by
  simp [gramShift, fallingRatio]

theorem gramShift_one {Q : ℕ} (hQ : 2 ≤ Q) : gramShift Q 1 = -1 := by
  have hq : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : 2 * (Q : ℝ) - 2 ≠ 0 := by linarith
  unfold gramShift
  rw [fallingRatio_succ (z:=0) hQ (by omega)]
  norm_num only [Nat.cast_one, Nat.cast_zero, pow_one, fallingRatio,
    Nat.descFactorial_zero, div_one, sub_zero, mul_one]
  field_simp (disch := linarith)

theorem gramShift_three {Q : ℕ} (hQ : 3 ≤ Q) : gramShift Q 3 = -1 := by
  have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : 2 * (Q : ℝ) - 2 ≠ 0 := by linarith
  have h2 : 2 * (Q : ℝ) - 2 - 1 ≠ 0 := by linarith
  have h3 : 2 * (Q : ℝ) - 2 - 2 ≠ 0 := by linarith
  unfold gramShift
  rw [fallingRatio_succ (z:=2) (by omega) (by omega),
    fallingRatio_succ (z:=1) (by omega) (by omega),
    fallingRatio_succ (z:=0) (by omega) (by omega)]
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    fallingRatio, Nat.descFactorial_zero, div_one, sub_zero, mul_one]
  field_simp (disch := linarith)
  ring

 

theorem threeWedgeMatrix_null_column {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hnull : z=0 ∨ z=1 ∨ z=3) (k : ℕ) :
    threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z k = 0 := by
  have hshift : gramShift Q z = -1 := by
    rcases hnull with rfl | rfl | rfl
    · exact gramShift_zero Q
    · exact gramShift_one hQ
    · exact gramShift_three hz
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp
  rw [threeWedgeMatrix_gram_eigenvector hQ hz k, hshift]
  simp

 

theorem threeWedgeMatrix_null_projection {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hnull : z=0 ∨ z=1 ∨ z=3) :
    threeWedgeMatrix Q * threeSpinProjection Q z = 0 := by
  classical
  have hn : threeWedgeMatrix Q * threeCouplingMatrix Q *
      Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) = 0 := by
    ext S c
    rw [Matrix.mul_diagonal]
    split_ifs with hc
    · rw [mul_one]
      change (threeWedgeMatrix Q *ᵥ threeCoupledColumn Q c.1.val c.2.val) S = 0
      simpa only [hc, Pi.zero_apply] using congrArg (fun v => v S)
        (threeWedgeMatrix_null_column hQ (show c.1.val ≤ Q by omega)
          (by simpa only [hc] using hnull) c.2.val)
    · simp
  unfold threeSpinProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hn, Matrix.zero_mul]

 
theorem threeSpinProjection_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z ∈ Finset.range (Q+1), threeSpinProjection Q z) = 1 := by
  classical
  have hd : (∑ z ∈ Finset.range (Q+1), Matrix.diagonal
      (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0)) = 1 := by
    ext c d
    simp only [Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases h : c=d
    · subst d
      simp only [ite_true, if_true]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by have := coupledIndex_bounds c; omega))]
    · simp [h]
  simp only [threeSpinProjection, ← Matrix.sum_mul, ← Matrix.mul_sum]
  rw [hd, Matrix.mul_one, threeCouplingMatrix_complete Q (by omega)]

 

theorem normal_ordered_square_spectral (Q : ℕ) (hQ : 2 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (threeWedgeMatrix Q *
        (∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
          (threeWedgeMatrix Q)ᴴ) +
      exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  rw [← threeWedgeMatrix_gram_spectral Q hQ]
  exact normal_ordered_square Q (by omega)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem exteriorLift_single_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q k : ℕ) (W : Matrix (SectorOccupation Q k) ι ℂ) (b c : ι) :
    exteriorLift Q k (W * Matrix.single b c (1 : ℂ) * Wᴴ) =
      (wedgeAnnihilator Q k (fun A => W A b))ᴴ *
        wedgeAnnihilator Q k (fun A => W A c) := by
  rw [exteriorLift_congruence]
  simp [Matrix.single_apply, ite_smul, ite_and]

 

theorem rowThreePrewedge_lift {β : Type*} [Fintype β]
    (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ) (p : β → PairLabel Q)
    (i j : β → Orbital Q) (a : β → ℝ) :
    exteriorLift Q 3 (threeWedgeMatrix Q * rowThreePrewedge Q t ℓ p i j a *
      (threeWedgeMatrix Q)ᴴ) = rowThreeBody Q t.val ℓ (fun b => (p b).val) i j a := by
  classical
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 3) (SectorOccupation Q 3) ℂ) :
      exteriorLift Q 3 (c • M) = c • exteriorLift Q 3 M :=
    (exteriorLiftLinear Q 3).map_smul c M
  simp only [rowThreePrewedge, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, exteriorLift_add, exteriorLift_sum, hs]
  simp_rw [exteriorLift_single_congruence, threeWedgeMatrix_annihilator_column]
  unfold rowThreeBody
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b _
    ext A B
    simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul, mul_add]
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs
    · rw [exteriorLift_single_congruence,
        threeWedgeMatrix_annihilator_column, threeWedgeMatrix_annihilator_column]
      ext A B
      simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    · simp [exteriorLift]

 
theorem single_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : ι) (x y : ι → ℂ) :
    star x ⬝ᵥ (Matrix.single b c 1 *ᵥ y) = star (x b) * y c := by
  simp [dotProduct, Matrix.mulVec, Matrix.single_apply, ite_mul, ite_and]

 

theorem rowThreePrewedge_bilinear {β : Type*} [Fintype β]
    (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ) (p : β → PairLabel Q)
    (i j : β → Orbital Q) (a : β → ℝ) (x y : PairLabel Q × Orbital Q → ℝ) :
    star (fun b => (x b : ℂ)) ⬝ᵥ (rowThreePrewedge Q t ℓ p i j a *ᵥ
      fun b => (y b : ℂ)) =
      ((∑ b, ℓ*a b * (x (t,i b)*y (p b,j b) + x (p b,j b)*y (t,i b))) +
        ∑ b, ∑ c, if i b = i c then a b*a c*x (p b,j b)*y (p c,j c) else 0 : ℝ) := by
  classical
  simp only [rowThreePrewedge, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec, dotProduct_add, dotProduct_sum, dotProduct_smul]
  simp_rw [single_bilinear, Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b _
    ring
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp [single_bilinear, Matrix.zero_mulVec, dotProduct_zero, mul_assoc]



theorem rowI_eq_iff {t : ℕ} (b c : RowEntry t) :
    rowI b = rowI c ↔ rowP b+rowJ b = rowP c+rowJ c := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  omega


theorem sphericalThreeCoefficient_tendsto (z T p : ℕ) :
    Tendsto (fun Q => sphericalThreeCoefficient Q z T p) atTop
      (𝓝 (planarThreeCoefficient z T p)) := by
  unfold sphericalThreeCoefficient planarThreeCoefficient
  split_ifs
  · exact threeCoupling_tendsto z (T-z) p
  · exact tendsto_const_nhds



theorem rowThreeTrace_tendsto (z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    Tendsto (fun Q => rowThreeTrace Q z t ℓ a) atTop (𝓝 (planarRowThreeTrace z t ℓ a)) := by
  unfold rowThreeTrace planarRowThreeTrace
  apply tendsto_finsetSum
  intro T _
  split_ifs
  · have hX : Tendsto (fun Q => ∑ b : RowEntry t, if rowP b+rowJ b=T then
        a b*sphericalThreeCoefficient Q z T (rowP b) else 0) atTop
        (𝓝 (∑ b : RowEntry t, if rowP b+rowJ b=T then
          a b*planarThreeCoefficient z T (rowP b) else 0)) := by
      apply tendsto_finsetSum
      intro b _
      split_ifs
      · exact (sphericalThreeCoefficient_tendsto z T (rowP b)).const_mul (a b)
      · exact tendsto_const_nhds
    exact (((sphericalThreeCoefficient_tendsto z T t).const_mul (2*ℓ)).mul hX).add (hX.pow 2)
  · exact tendsto_const_nhds



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteComparison
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology


theorem rowsThreeTrace_tendsto {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (z : ℕ) :
    Tendsto (fun Q => rowsThreeTrace rows Q z) atTop (𝓝 (planarRowsThreeTrace rows z)) :=
  tendsto_finsetSum Finset.univ (fun i _ =>
    rowThreeTrace_tendsto z (rows i).t.val (rows i).ell (rows i).alpha)



theorem rowsThreeTrace_eventual_bound {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hCertificate : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2) ^ z.val.val) :
    ∀ᶠ Q in atTop, ∀ z : ComparedThreeBlock,
      rowsThreeTrace rows Q z.val.val / spinRatio Q z.val.val < gramShift Q z.val.val := by
  apply eventually_all.mpr
  intro z
  have hlim : Tendsto (fun Q => spinRatio Q z.val.val * gramShift Q z.val.val)
      atTop (𝓝 ((3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)) := by
    simpa only [mul_assoc] using
      (spinRatio_tendsto z.val.val).mul (gramShift_tendsto z.val.val)
  have he := (rowsThreeTrace_tendsto rows z.val.val).eventually_lt hlim (hCertificate z)
  filter_upwards [he, eventually_ge_atTop 16] with Q hlt hQ
  have hn : (z.val.val : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : z.val.val ≤ Q)
  have hq : (16 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hp : 0 < spinRatio Q z.val.val := by
    unfold spinRatio
    apply div_pos <;> linarith
  rw [div_lt_iff₀ hp]
  simpa only [mul_comm] using hlt


theorem threeWedgeMatrix_null_sandwich {Q z : ℕ} (hQ : 3 ≤ Q)
    (hz : z=0 ∨ z=1 ∨ z=3) (a : ℂ) :
    threeWedgeMatrix Q * (a • threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ = 0 := by
  have hle : z ≤ Q := by rcases hz with rfl | rfl | rfl <;> omega
  rw [Matrix.mul_smul, threeWedgeMatrix_null_projection (by omega) hle hz,
    smul_zero, Matrix.zero_mul]

 

theorem threeTraceForm_le_finite_of_coefficients {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q)
    (hbound : ∀ z : ComparedThreeBlock,
      rowsThreeTrace rows Q z.val.val / spinRatio Q z.val.val ≤ gramShift Q z.val.val) :
    (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef := by
  classical
  unfold finiteThreeTarget threeTraceForm
  rw [← exteriorLift_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Finset.sum_sub_distrib]
  apply exteriorLift_posSemidef
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Matrix.posSemidef_sum
  intro z hz
  rw [← sub_smul, ← Complex.ofReal_div, ← Complex.ofReal_sub]
  by_cases hn : z=0 ∨ z=1 ∨ z=3
  · rw [threeWedgeMatrix_null_sandwich (by omega) hn]
    exact Matrix.PosSemidef.zero
  · have hzlt : z < 16 := Finset.mem_range.mp hz
    have hg : z=2 ∨ 4 ≤ z := by omega
    have h := hbound ⟨⟨z,hzlt⟩,hg⟩
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact (threeSpinProjection_posSemidef Q z).smul (by exact_mod_cast sub_nonneg.mpr h)

 

theorem threeTraceForm_eventual_bound {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hCertificate : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val) :
    ∀ᶠ Q in atTop, (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef := by
  filter_upwards [rowsThreeTrace_eventual_bound rows hCertificate, eventually_ge_atTop 16] with Q h hQ
  exact threeTraceForm_le_finite_of_coefficients rows hQ (fun z => (h z).le)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem wedgeAnnihilator_smul (Q k : ℕ) (c : ℂ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k (c • v) = star c • wedgeAnnihilator Q k v := by
  unfold wedgeAnnihilator
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  change (star (c * v S)) • basisAnnihilator Q S.val = _
  rw [star_mul, smul_smul, mul_comm]

 
theorem symmetric_sum_upper {ι V : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid V] (f : ι → ι → V)
    (hsymm : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) + ∑ i, ∑ j, if i < j then f i j else 0 := by
  have ht (i j : ι) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le, hsymm]
  calc
    _ = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact ht i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f:=fun i j => if j < i then f j i else 0)]

 

theorem tensorWedge_contraction (Q : ℕ) (s : Orbital Q × Orbital Q → ℂ)
    (hs : ∀ i j, s (j,i) = -s (i,j)) :
    wedgeAnnihilator Q 2
        (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ s) =
      (2:ℂ) • coefficientPairAnnihilator Q (fun i j => star (s (i,j))) := by
  rw [wedgeAnnihilator_mulVec]
  have hc (ij : Orbital Q × Orbital Q) := wedgeProductMatrix_contraction Q 1 1
    (oneParticleMatrix Q) (oneParticleMatrix Q) ij
  simp only [oneParticleMatrix_contraction] at hc
  simp only [hc, Fintype.sum_prod_type]
  have hh := symmetric_sum_upper (fun i j : Orbital Q => star (s (i,j)) •
    (annihilator Q j * annihilator Q i))
    (by
      intro i j
      have ha := eq_neg_of_add_eq_zero_left (annihilator_anticommute Q i j)
      rw [hs, star_neg, ha, neg_smul, smul_neg, neg_neg])
    (by intro i; simp only [annihilator_square, smul_zero])
  simpa only [coefficientPairAnnihilator, two_smul ℂ] using hh

 
theorem tensorWedge_intertwines (Q : ℕ) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) *
        wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) =
      wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
        tensorSum (spinGenerator Q s) (spinGenerator Q s) :=
  wedgeProductMatrix_intertwines Q 1 1 _ (spinGenerator_skew Q s) _ _ _ _
    (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s))
    (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s))



theorem tensorWedge_pairSpinMatrix {Q : ℕ} (hQ : 1 ≤ Q) :
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
      coupledSpinMatrix Q Q 1) =
      (Real.sqrt 2 : ℂ) •
        (pairSpinMatrix Q).submatrix id (Fin.cast (by omega)) := by
  ext S p
  have hv : wedgeAnnihilator Q 2
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ
        (fun ij => coupledSpinMatrix Q Q 1 ij p)) =
      wedgeAnnihilator Q 2 ((Real.sqrt 2 : ℂ) • pairVector Q p.val) := by
    rw [tensorWedge_contraction]
    · rw [wedgeAnnihilator_smul]
      simp only [pairVector, wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
        Complex.star_def, Complex.conj_ofReal]
      unfold coupledSpinMatrix
      simp only [Complex.conj_ofReal]
      have he (i j : Orbital Q) :
          (coupledVector Q Q 1 p.val i.val j.val : ℂ) =
            (Real.sqrt 2 : ℂ)⁻¹ * (pairCoefficient Q p.val i j : ℂ) := by
        rw [pairCoefficient_eq_coupled hQ (by have := p.isLt; omega)]
        push_cast
        have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
        field_simp
      simp_rw [he]
      rw [coefficientPairAnnihilator_smul, smul_smul]
      congr 1
      have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
      field_simp
      linear_combination -hs
    · intro i j
      dsimp [coupledSpinMatrix]
      rw [coupledVector_antisymm hQ (by decide : Odd 1)]
      simp
  exact congrFun (wedgeAnnihilator_injective Q 2 hv) S

 
theorem pairSpinMatrix_intertwines {Q : ℕ} (hQ : 1 ≤ Q) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) * pairSpinMatrix Q =
      pairSpinMatrix Q * spinGenerator (2*Q-2) s := by
  have h := coupledSpinMatrix_intertwines hQ hQ s
  have he : sectorOneBody Q 2 (spinGenerator Q s) *
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q 1) =
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q 1) *
      spinGenerator (Q+Q-2*1) s := by
    rw [← Matrix.mul_assoc, tensorWedge_intertwines, Matrix.mul_assoc, h, Matrix.mul_assoc]
  rw [tensorWedge_pairSpinMatrix hQ] at he
  have hdim : Q+Q-2*1 = 2*Q-2 := by omega
  simp only [Matrix.mul_smul, Matrix.smul_mul] at he
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hf := smul_right_injective _ hn he
  have hc (n : ℕ) (e : n = 2*Q-2)
      (hc : sectorOneBody Q 2 (spinGenerator Q s) *
          (pairSpinMatrix Q).submatrix id (Fin.cast (congrArg (·+1) e)) =
        (pairSpinMatrix Q).submatrix id (Fin.cast (congrArg (·+1) e)) * spinGenerator n s) :
      sectorOneBody Q 2 (spinGenerator Q s) * pairSpinMatrix Q =
        pairSpinMatrix Q * spinGenerator (2*Q-2) s := by
    subst n
    simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hc
  exact hc _ hdim hf

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem fockAverage_spin_column {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (p : Fin (n+1)) :
    fockAverage Q ((wedgeAnnihilator Q k (fun A => C A p))ᴴ *
      wedgeAnnihilator Q k (fun A => C A p)) =
      (1/(n+1 : ℂ)) • exteriorLift Q k (C*Cᴴ) := by
  rw [← exteriorLift_single_congruence Q k C p p,
    fockAverage_spin_sandwich C hC, Matrix.trace_single_eq_same]

 
theorem pairSpinMatrix_lift {Q : ℕ} (hQ : 1 ≤ Q) :
    exteriorLift Q 2 (pairSpinMatrix Q * (pairSpinMatrix Q)ᴴ) = hamiltonian Q := by
  have h := exteriorLift_congruence Q 2 (pairSpinMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true] at h
  rw [h]
  simp only [pairSpinMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
  rw [Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) (2*Q-2+1)]
  have hd : 2*Q-2+1 = 2*Q-1 := by omega
  rw [hd]
  rfl

 

theorem fockAverage_pair_energy {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    fockAverage Q ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) =
      (1 / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  have h := fockAverage_spin_column (pairSpinMatrix Q) (pairSpinMatrix_intertwines hQ)
    (⟨p,by omega⟩ : Fin (2*Q-2+1))
  simp only [pairSpinMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
    pairSpinMatrix_lift hQ] at h
  have hd : ((2*Q-2 : ℕ) : ℂ) + 1 = ((2*Q-1 : ℕ) : ℂ) := by
    norm_cast
    omega
  simpa only [hd] using h



theorem fockAverage_pair_energy_scaled {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) =
      hamiltonian Q := by
  rw [fockAverage_pair_energy hQ hp, smul_smul]
  have hd : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  rw [one_div, mul_inv_cancel₀ hd, one_smul]

 

theorem fockAverage_pair_family {ι : Type*} [Fintype ι] {Q : ℕ}
    (hQ : 1 ≤ Q) (p : ι → ℕ) (hp : ∀ i, p i ≤ 2*Q-2) :
    fockAverage Q (∑ i, (pairAnnihilator Q (p i))ᴴ * pairAnnihilator Q (p i)) =
      ((Fintype.card ι : ℂ) / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  rw [map_sum]
  simp_rw [fockAverage_pair_energy hQ (hp _)]
  rw [← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem threeSpinProjection_columns {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinProjection Q z = threeSpinColumns Q z * (threeSpinColumns Q z)ᴴ := by
  classical
  let r : Fin (min (2*Q-2) Q+1) := ⟨z, by omega⟩
  ext i j
  unfold threeSpinProjection
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, threeCouplingMatrix,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · simp only [r, ite_true, if_true]
    rfl
  · intro a _ ha
    have han : a.val ≠ z := by
      intro h; apply ha; exact Fin.ext h
    simp only [ite_eq_right han, Finset.sum_const_zero]
  · simp



theorem threeSpinWedge_eq_tensor {Q : ℕ} (hQ : 1 ≤ Q) (z : ℕ) :
    threeSpinWedge Q z =
      wedgeProductMatrix Q 2 1 (pairSpinMatrix Q) (oneParticleMatrix Q) *
        coupledSpinMatrix (2*Q-2) Q z := by
  classical
  let e : (Fin (2*Q-2+1) × Orbital Q) ≃ (PairLabel Q × Orbital Q) :=
    Equiv.prodCongr (finCongr (by omega)) (Equiv.refl _)
  ext S k
  change (∑ pj, threeWedgeMatrix Q S pj * threeCoupledColumn Q z k.val pj) = _
  rw [← e.sum_comp (fun pj => threeWedgeMatrix Q S pj * threeCoupledColumn Q z k.val pj)]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro pj _
  have hv : (fun T => wedgeProductMatrix Q 2 1 (pairSpinMatrix Q) (oneParticleMatrix Q) T pj) =
      (fun T => threeWedgeMatrix Q T (e pj)) := by
    apply wedgeAnnihilator_injective Q 3
    rw [wedgeProductMatrix_contraction Q 2 1, oneParticleMatrix_contraction,
      threeWedgeMatrix_annihilator_column]
    simp only [pairSpinMatrix, pairVector,
      wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
    rfl
  rw [congrFun hv S]
  rfl

 
theorem threeSpinWedge_intertwines {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (s : Fin 3) :
    sectorOneBody Q 3 (spinGenerator Q s) * threeSpinWedge Q z =
      threeSpinWedge Q z * spinGenerator (2*Q-2+Q-2*z) s := by
  rw [threeSpinWedge_eq_tensor (by omega)]
  rw [← Matrix.mul_assoc,
    wedgeProductMatrix_intertwines Q 2 1 _ (spinGenerator_skew Q s) _ _ _ _
      (pairSpinMatrix_intertwines (by omega) s)
      (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s)),
    Matrix.mul_assoc, coupledSpinMatrix_intertwines (by omega : z ≤ 2*Q-2) hz,
    Matrix.mul_assoc]

 
theorem threeSpinWedge_gram {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinWedge Q z * (threeSpinWedge Q z)ᴴ =
      threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ := by
  rw [threeSpinProjection_columns hQ hz, threeSpinWedge, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

 

theorem fockAverage_highestThree {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    fockAverage Q ((highestThreeAnnihilator Q z hz)ᴴ * highestThreeAnnihilator Q z hz) =
      (1 / ((3*Q-1-2*z : ℕ) : ℂ)) •
        exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) := by
  have h := fockAverage_spin_column (threeSpinWedge Q z) (threeSpinWedge_intertwines hQ hz)
    (⟨0,by omega⟩ : Fin (2*Q-2+Q-2*z+1))
  have hc : (fun A => threeSpinWedge Q z A (⟨0,by omega⟩ : Fin (2*Q-2+Q-2*z+1))) =
      threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z 0 := rfl
  rw [hc, ← highestThreeAnnihilator_eq_wedge hQ hz, threeSpinWedge_gram hQ hz] at h
  have hd : ((2*Q-2+Q-2*z : ℕ) : ℂ)+1 = ((3*Q-1-2*z : ℕ) : ℂ) := by
    rw [← Nat.cast_add_one]
    congr 1
    omega
  simpa only [hd] using h

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology


theorem sourceRowThreeKernel_lift {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    exteriorLift Q 3 (threeWedgeMatrix Q * sourceRowThreeKernel hQ ht ℓ a *
      (threeWedgeMatrix Q)ᴴ) =
      rowThreeBody Q t ℓ rowP (sourceRowI hQ) (sourceRowJ hQ) a :=
  rowThreePrewedge_lift Q (sourceRowT hQ ht) ℓ (sourceRowP hQ) (sourceRowI hQ) (sourceRowJ hQ) a


theorem coupledVector_eq_sphericalThree (Q z k p j : ℕ) :
    coupledVector (2*Q-2) Q z k p j =
      if p+j=z+k then sphericalThreeCoefficient Q z (z+k) p else 0 := by
  simp [coupledVector, sphericalThreeCoefficient]

 

theorem sourceRowThreeKernel_diagonal {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) (z k : ℕ) :
    star (threeCoupledColumn Q z k) ⬝ᵥ
      (sourceRowThreeKernel hQ ht ℓ a *ᵥ threeCoupledColumn Q z k) =
      ((2*ℓ*sphericalThreeCoefficient Q z (z+k) t * sphericalRowAmplitude Q z t (z+k) a +
        (sphericalRowAmplitude Q z t (z+k) a)^2 : ℝ) : ℂ) := by
  classical
  rw [sourceRowThreeKernel]
  unfold threeCoupledColumn
  rw [rowThreePrewedge_bilinear]
  have hi (b : RowEntry t) : t+rowI b=rowP b+rowJ b := (rowEntry_bounds b).2.2.2
  have hh (b c : RowEntry t) : sourceRowI hQ b=sourceRowI hQ c ↔ rowI b=rowI c := by
    exact Fin.ext_iff
  simp only [sourceRowT, sourceRowP, sourceRowJ, sourceRowI, coupledVector_eq_sphericalThree, hi]
  apply congrArg (fun x : ℝ => (x : ℂ))
  apply congrArg₂ (· + ·)
  · unfold sphericalRowAmplitude
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  · unfold sphericalRowAmplitude
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    have he : (⟨rowI b, by have := (rowEntry_bounds b).2.2.1; omega⟩ : Orbital Q) =
        (⟨rowI c, by have := (rowEntry_bounds c).2.2.1; omega⟩ : Orbital Q) ↔
        rowP b+rowJ b=rowP c+rowJ c := by
      rw [Fin.mk.injEq, rowI_eq_iff]
    simp only [he]
    split_ifs <;> ring_nf
    omega

 
theorem sphericalRowAmplitude_zero {Q z t T : ℕ} (a : RowEntry t → ℝ)
    (h : T < t ∨ 15 < T) : sphericalRowAmplitude Q z t T a = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  have hb := rowEntry_bounds b
  omega


theorem rowThreeLevelTrace_lower_zero (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ)
    (T : ℕ) (hT : T < z) : rowThreeLevelTrace Q z t ℓ a T = 0 := by
  simp [rowThreeLevelTrace, Nat.not_le.mpr hT]

theorem rowThreeLevelTrace_upper_zero (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ)
    (T : ℕ) (hT : 15 < T) : rowThreeLevelTrace Q z t ℓ a T = 0 := by
  simp [rowThreeLevelTrace, sphericalRowAmplitude_zero a (Or.inr hT)]

theorem sourceRowThreeKernel_diagonal_level {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) (z k : ℕ) :
    star (threeCoupledColumn Q z k) ⬝ᵥ
      (sourceRowThreeKernel hQ ht ℓ a *ᵥ threeCoupledColumn Q z k) =
      (rowThreeLevelTrace Q z t ℓ a (z+k) : ℂ) := by
  rw [sourceRowThreeKernel_diagonal]
  unfold rowThreeLevelTrace
  split_ifs with h
  · rfl
  · have ht' : z+k < t := by omega
    rw [sphericalRowAmplitude_zero a (Or.inl ht')]
    simp

 

theorem sum_shifted_of_support {K L z : ℕ} (hKL : L ≤ z+K) (f : ℕ → ℝ)
    (hlo : ∀ T, T < z → f T=0) (hhi : ∀ T, L ≤ T → f T=0) :
    (∑ k ∈ Finset.range K, f (z+k)) = ∑ T ∈ Finset.range L, f T := by
  have hl : ∑ T ∈ Finset.range z, f T = 0 := by
    exact Finset.sum_eq_zero fun T hT => hlo T (Finset.mem_range.mp hT)
  have hu : (∑ T ∈ Finset.range L, f T) = ∑ T ∈ Finset.range (z+K), f T := by
    apply Finset.sum_subset (Finset.range_mono hKL)
    intro T _ hT
    exact hhi T (by simpa using hT)
  rw [hu, Finset.sum_range_add, hl, zero_add]

 

theorem sourceRowThreeKernel_spinTrace {Q t z : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (hz : z ≤ Q) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    (∑ k : Fin (2*Q-2+Q-2*z+1), star (threeCoupledColumn Q z k.val) ⬝ᵥ
      (sourceRowThreeKernel (by omega : 8 ≤ Q) ht ℓ a *ᵥ threeCoupledColumn Q z k.val)) =
      (rowThreeTrace Q z t ℓ a : ℂ) := by
  simp only [sourceRowThreeKernel_diagonal_level]
  rw [← Complex.ofReal_sum]
  apply congrArg (fun x : ℝ => (x : ℂ))
  rw [Fin.sum_univ_eq_sum_range
    (fun k => rowThreeLevelTrace Q z t ℓ a (z+k)) (2*Q-2+Q-2*z+1)]
  exact sum_shifted_of_support (by omega : 16 ≤ z+(2*Q-2+Q-2*z+1))
    (rowThreeLevelTrace Q z t ℓ a)
    (rowThreeLevelTrace_lower_zero Q z t ℓ a)
    (fun T hT => rowThreeLevelTrace_upper_zero Q z t ℓ a T (by omega))

 

theorem threeSpinProjection_kernel_trace {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (M : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ) :
    (threeSpinProjection Q z * M).trace =
      ∑ k : Fin (2*Q-2+Q-2*z+1), star (threeCoupledColumn Q z k.val) ⬝ᵥ
        (M *ᵥ threeCoupledColumn Q z k.val) := by
  classical
  have hz' : z < min (2*Q-2) Q+1 := by omega
  let r : Fin (min (2*Q-2) Q+1) := ⟨z,hz'⟩
  unfold threeSpinProjection
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · simp only [r, ite_true, if_true]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, threeCouplingMatrix,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro a _ ha
    have han : a.val ≠ z := by
      intro h
      exact ha (Fin.ext h)
    simp [han]
  · simp

 

theorem sourceRowThreeKernel_projectionTrace {Q t z : ℕ} (hQ : 16 ≤ Q)
    (ht : t ≤ 7) (hz : z ≤ Q) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    (threeSpinProjection Q z * sourceRowThreeKernel (by omega : 8 ≤ Q) ht ℓ a).trace =
      (rowThreeTrace Q z t ℓ a : ℂ) := by
  rw [threeSpinProjection_kernel_trace (by omega) hz,
    sourceRowThreeKernel_spinTrace hQ ht hz]

 

theorem rowThreeTrace_above_support {Q z t : ℕ} (hz : 15 < z)
    (ℓ : ℝ) (a : RowEntry t → ℝ) : rowThreeTrace Q z t ℓ a = 0 := by
  apply Finset.sum_eq_zero
  intro T hT
  have hT' := Finset.mem_range.mp hT
  simp only [show ¬ (z ≤ T ∧ t ≤ T) by omega, ite_false]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Rows. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem matrix_complete_column_sandwich {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : ι → ℕ) (C : ∀ i, Matrix κ (Fin (n i+1)) ℂ)
    (hC : ∑ i, C i * (C i)ᴴ = 1)
    (W : Matrix ν κ ℂ) (M : Matrix κ κ ℂ) :
    W*M*Wᴴ = ∑ i, ∑ j, (W*C i)*((C i)ᴴ*M*C j)*(W*C j)ᴴ := by
  calc
    _ = W * (∑ i, C i * (C i)ᴴ) * M * (∑ j, C j * (C j)ᴴ) * Wᴴ := by
      rw [hC, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [Finset.sum_comm]

 

theorem sectorAverage_of_complete_spin {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] {Q k : ℕ}
    (n : ι → ℕ) (hn : Function.Injective n) (C : ∀ i, Matrix κ (Fin (n i+1)) ℂ)
    (hC : ∑ i, C i * (C i)ᴴ = 1)
    (W : Matrix (SectorOccupation Q k) κ ℂ)
    (hW : ∀ i s, sectorOneBody Q k (spinGenerator Q s)*(W*C i) =
      (W*C i)*spinGenerator (n i) s)
    (M : Matrix κ κ ℂ) :
    sectorAverage Q k (W*M*Wᴴ) =
      ∑ i, (((C i)ᴴ*M*C i).trace / (n i+1:ℂ)) • ((W*C i)*(W*C i)ᴴ) := by
  classical
  rw [matrix_complete_column_sandwich n C hC W M, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, Finset.sum_eq_single i]
  · exact sectorAverage_spin_mixed_sandwich (W*C i) (W*C i) (hW i) (hW i) _
  · intro j _ hji
    exact sectorAverage_spin_cross_sandwich (fun hij => hji (hn hij).symm)
      (W*C i) (W*C j) (hW i) (hW j) _
  · simp

 
theorem threeSpinColumns_complete {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), threeSpinColumns Q z.val * (threeSpinColumns Q z.val)ᴴ) = 1 := by
  have h := threeSpinProjection_sum Q hQ
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [threeSpinProjection_columns hQ (Nat.le_of_lt_succ (Fin.isLt _))] using h

 

theorem sectorAverage_three_kernel {Q : ℕ} (hQ : 2 ≤ Q)
    (M : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ) :
    sectorAverage Q 3 (threeWedgeMatrix Q*M*(threeWedgeMatrix Q)ᴴ) =
      threeWedgeMatrix Q * (∑ z ∈ Finset.range (Q+1),
        ((threeSpinProjection Q z*M).trace / ((3*Q-1-2*z : ℕ) : ℂ)) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ := by
  have hn : Function.Injective (fun z : Fin (Q+1) => 2*Q-2+Q-2*z.val) := by
    intro z w h
    have hz := z.isLt
    have hw := w.isLt
    apply Fin.ext
    dsimp only at h
    omega
  have h := sectorAverage_of_complete_spin _ hn (fun z : Fin (Q+1) => threeSpinColumns Q z.val)
    (threeSpinColumns_complete hQ) (threeWedgeMatrix Q)
    (fun z => threeSpinWedge_intertwines hQ (by have := z.isLt; omega)) M
  rw [h, ← Fin.sum_univ_eq_sum_range, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have hz : z.val ≤ Q := Nat.le_of_lt_succ z.isLt
  have hd : ((2*Q-2+Q-2*z.val : ℕ) : ℂ)+1 = ((3*Q-1-2*z.val : ℕ) : ℂ) := by
    rw [← Nat.cast_add_one]
    congr 1
    omega
  have ht : ((threeSpinColumns Q z.val)ᴴ * M * threeSpinColumns Q z.val).trace =
      (threeSpinProjection Q z.val*M).trace := by
    rw [threeSpinProjection_columns hQ hz, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [hd, ht]
  exact congrArg (_ • ·) (threeSpinWedge_gram hQ hz)

 

theorem fockAverage_rowThreeBody {Q t : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    fockAverage Q (rowThreeBody Q t ℓ rowP (sourceRowI (by omega : 8 ≤ Q))
      (sourceRowJ (by omega : 8 ≤ Q)) a) =
      exteriorLift Q 3 (threeWedgeMatrix Q * (∑ z ∈ Finset.range 16,
        ((rowThreeTrace Q z t ℓ a : ℂ) / ((3*Q-1-2*z : ℕ) : ℂ)) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ) := by
  rw [← sourceRowThreeKernel_lift (by omega : 8 ≤ Q) ht ℓ a,
    fockAverage_exteriorLift, sectorAverage_three_kernel (by omega)]
  congr 2
  congr 1
  calc
    _ = ∑ z ∈ Finset.range (Q+1),
        ((rowThreeTrace Q z t ℓ a : ℂ) / ((3*Q-1-2*z : ℕ) : ℂ)) • threeSpinProjection Q z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [sourceRowThreeKernel_projectionTrace hQ ht (by have := Finset.mem_range.mp hz; omega)]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro z hz hnz
      rw [rowThreeTrace_above_support (by simp only [Finset.mem_range] at hnz; omega) ℓ a]
      simp

theorem spinRatio_eq_dimensions {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    spinRatio Q z = ((3*Q-1-2*z : ℕ) : ℝ) / ((2*Q-1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ 3*Q := by omega
  have h2 : 2*z ≤ 3*Q-1 := by omega
  have h3 : 1 ≤ 2*Q := by omega
  simp only [spinRatio, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

 
theorem fockAverage_rowThreeBody_scaled {Q t : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
      (rowThreeBody Q t ℓ rowP (sourceRowI (by omega : 8 ≤ Q))
        (sourceRowJ (by omega : 8 ≤ Q)) a) =
      exteriorLift Q 3 (threeWedgeMatrix Q * (∑ z ∈ Finset.range 16,
        ((rowThreeTrace Q z t ℓ a / spinRatio Q z : ℝ) : ℂ) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ) := by
  rw [fockAverage_rowThreeBody hQ ht]
  change ((2*Q-1 : ℕ) : ℂ) • (exteriorLiftLinear Q 3) _ = (exteriorLiftLinear Q 3) _
  rw [← map_smul]
  congr 1
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, Finset.smul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  rw [smul_smul, Complex.ofReal_div, spinRatio_eq_dimensions (by omega)
    (by have := Finset.mem_range.mp hz; omega), Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_natCast]
  congr 1
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  rw [div_div_eq_mul_div]
  ring



theorem fockAverage_rowsThreeBody {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
      (∑ i, rowThreeBody Q (rows i).t.val (rows i).ell rowP
        (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) (rows i).alpha) =
      threeTraceForm rows Q := by
  rw [map_sum, Finset.smul_sum]
  have hi (i : ι) := fockAverage_rowThreeBody_scaled hQ
    (Nat.le_of_lt_succ (rows i).t.isLt) (rows i).ell (rows i).alpha
  simp_rw [hi]
  unfold threeTraceForm rowsThreeTrace
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    exteriorLift_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, exteriorLift_sum,
    Complex.ofReal_div]

 

theorem averagedRows_positive {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q) :
    (rowsEta rows • hamiltonian Q + threeTraceForm rows Q +
      averagedRowsFour (by omega : 8 ≤ Q) rows).PosSemidef := by
  classical
  let F (i : ι) := auxiliaryRow Q (rows i).t.val (rows i).ell rowP
    (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) (rows i).alpha
  have hp := fockAverage_posSemidef Q _
    (Matrix.posSemidef_sum Finset.univ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (F i)))
  have h := hp.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
  dsimp [F] at h
  simp_rw [auxiliaryRow_square] at h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, map_add, map_add,
    smul_add, smul_add, fockAverage_rowsThreeBody rows hQ] at h
  have he : ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ i, rowTwoBody Q (rows i).t.val (rows i).ell) =
      rowsEta rows • hamiltonian Q := by
    rw [map_sum, Finset.smul_sum]
    unfold rowTwoBody rowsEta
    have hh (i : ι) : ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
        ((rows i).ell^2 • ((pairAnnihilator Q (rows i).t.val)ᴴ * pairAnnihilator Q (rows i).t.val)) =
        (rows i).ell^2 • hamiltonian Q := by
      rw [(fockAverage Q).map_smul_of_tower, smul_comm _ ((rows i).ell^2),
        fockAverage_pair_energy_scaled (by omega) (by have := (rows i).t.isLt; omega)]
    simp_rw [hh]
    exact Finset.sum_smul.symm
  rw [he] at h
  exact h

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SquareSplitting
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Splitting. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem fullThreeTarget_split {Q : ℕ} (hQ : 16 ≤ Q+1) :
    fullThreeTarget Q = finiteThreeTarget Q + tailThreeTarget Q := by
  unfold fullThreeTarget finiteThreeTarget tailThreeTarget
  rw [← Finset.sum_range_add_sum_Ico _ hQ, Matrix.mul_add, Matrix.add_mul, exteriorLift_add]

 

theorem normal_ordered_square_split {Q : ℕ} (hQ : 16 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      finiteThreeTarget Q + tailThreeTarget Q +
        exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  have h := normal_ordered_square_spectral Q (by omega)
  change _ = hamiltonian Q + fullThreeTarget Q + _ at h
  rw [fullThreeTarget_split (by omega), ← add_assoc] at h
  exact h

 

theorem threeSpinProjection_lift_posSemidef (Q z : ℕ) :
    (exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z *
      (threeWedgeMatrix Q)ᴴ)).PosSemidef :=
  exteriorLift_posSemidef Q 3 _
    ((threeSpinProjection_posSemidef Q z).mul_mul_conjTranspose_same _)



theorem fockInequality_of_finite_comparisons {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q)
    (A4 : FockMatrix Q) (δ e : ℝ)
    (hK : (rowsEta rows • hamiltonian Q + threeTraceForm rows Q + A4).PosSemidef)
    (h3 : (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef)
    (h4 : (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) +
      e • hamiltonian Q - A4).PosSemidef)
    (htail : (tailThreeTarget Q + δ • hamiltonian Q).PosSemidef) :
    FockInequality Q (1-rowsEta rows-δ-e) := by
  have h := ((hK.add h3).add h4).add htail
  unfold FockInequality
  rw [normal_ordered_square_split hQ]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sub_smul, one_smul]
  abel



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TailOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem threeSpinProjection_relative_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (((spinRatio Q z * (z+1) : ℝ) : ℂ) • hamiltonian Q -
      exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z *
        (threeWedgeMatrix Q)ᴴ)).PosSemidef := by
  have ha := fockAverage_posSemidef Q _ (highestThreeAnnihilator_pair_posSemidef hQ hz)
  rw [map_sub, fockAverage_highestThree hQ hz,
    fockAverage_pair_family (by omega : 1 ≤ Q) (fun p : Fin (z+1) => p.val)
      (by intro p; have := p.isLt; omega), Fintype.card_fin] at ha
  have hn : ((3*Q-1-2*z : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 3*Q-1-2*z ≠ 0 by omega)
  have hc : ((3*Q-1-2*z : ℕ) : ℂ) *
      ((z+1 : ℕ) / ((2*Q-1 : ℕ) : ℂ)) = ((spinRatio Q z * (z+1) : ℝ) : ℂ) := by
    push_cast [spinRatio, Nat.cast_sub (show 2*z ≤ 3*Q-1 by omega),
      Nat.cast_sub (show 1 ≤ 3*Q by omega), Nat.cast_sub (show 1 ≤ 2*Q by omega)]
    ring
  have hh := ha.smul (show (0:ℂ) ≤ ((3*Q-1-2*z : ℕ) : ℂ) by exact_mod_cast (Nat.zero_le _))
  simpa only [smul_sub, smul_smul, hc, one_div, mul_inv_cancel₀ hn, one_smul] using hh

 

theorem gramShift_even_nonneg {Q z : ℕ} (hQ : 1 ≤ Q) (hz₁ : 1 ≤ z)
    (hz : z ≤ Q) (he : Even z) : 0 ≤ gramShift Q z := by
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hzr : (1:ℝ) ≤ z := by exact_mod_cast hz₁
  have hzQ : (z:ℝ) ≤ Q := by exact_mod_cast hz
  have hdiv : (z:ℝ)*(z+1)/Q ≤ z+1 := by
    rw [div_le_iff₀ hQr]
    nlinarith
  have hb : 0 ≤ 3*(z:ℝ)-1-z*(z+1)/Q := by linarith
  rw [gramShift, he.neg_pow, one_pow, one_mul]
  exact mul_nonneg (fallingRatio_nonneg Q z) hb

 

theorem threeSpinProjection_negative_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((gramShift Q z : ℂ) •
        exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) +
      ((spinRatio Q z * |gramShift Q z| * (z+1) : ℝ) : ℂ) • hamiltonian Q).PosSemidef := by
  let X := exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ)
  have h₁ := (threeSpinProjection_relative_bound hQ hz).smul
    (show (0:ℂ) ≤ (|gramShift Q z| : ℝ) by exact_mod_cast abs_nonneg (gramShift Q z))
  have h₂ := (threeSpinProjection_lift_posSemidef Q z).smul
    (show (0:ℂ) ≤ ((gramShift Q z + |gramShift Q z| : ℝ) : ℂ) by
      exact_mod_cast (show 0 ≤ gramShift Q z + |gramShift Q z| by linarith [neg_le_abs (gramShift Q z)]))
  have he : ((|gramShift Q z| : ℝ) : ℂ) • (((spinRatio Q z * (z+1) : ℝ) : ℂ) • hamiltonian Q-X) +
      ((gramShift Q z+|gramShift Q z| : ℝ) : ℂ) • X =
    (gramShift Q z : ℂ) • X + ((spinRatio Q z * |gramShift Q z| * (z+1) : ℝ) : ℂ) • hamiltonian Q := by
    push_cast
    simp only [smul_sub, smul_smul, add_smul]
    rw [show ((|gramShift Q z| : ℝ) : ℂ) * ((spinRatio Q z : ℂ)*((z:ℂ)+1)) =
      (spinRatio Q z : ℂ)*((|gramShift Q z| : ℝ) : ℂ)*((z:ℂ)+1) by ring]
    abel
  exact he ▸ h₁.add h₂

 

theorem tailCoefficient_eq_Ico (Q : ℕ) :
    tailCoefficient Q = ∑ z ∈ Finset.Ico 16 (Q+1),
      if Odd z then spinRatio Q z * |gramShift Q z| * (z+1) else 0 := by
  classical
  rw [tailCoefficient_eq_odd_sum, ← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hz, hz₁, ho⟩; exact ⟨⟨by omega,hz⟩,ho⟩
  · rintro ⟨⟨hz₁,hz⟩,ho⟩
    have hp := Nat.odd_iff.mp ho
    exact ⟨hz,by omega,ho⟩

 

theorem tailThreeTarget_relative_bound {Q : ℕ} (hQ : 2 ≤ Q) :
    (tailThreeTarget Q + (tailCoefficient Q : ℂ) • hamiltonian Q).PosSemidef := by
  classical
  have hm (c : ℂ) (M : Matrix (SectorOccupation Q 3) (SectorOccupation Q 3) ℂ) :
      exteriorLift Q 3 (c • M) = c • exteriorLift Q 3 M :=
    (exteriorLiftLinear Q 3).map_smul c M
  have hs : tailThreeTarget Q + (tailCoefficient Q : ℂ) • hamiltonian Q =
      ∑ z ∈ Finset.Ico 16 (Q+1),
        ((gramShift Q z : ℂ) • exteriorLift Q 3
          (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) +
        ((if Odd z then spinRatio Q z * |gramShift Q z| * (z+1) else 0 : ℝ) : ℂ) • hamiltonian Q) := by
    simp only [tailThreeTarget, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, exteriorLift_sum, hm,
      tailCoefficient_eq_Ico, Complex.ofReal_sum, ← Finset.sum_smul, Finset.sum_add_distrib]
  rw [hs]
  apply Matrix.posSemidef_sum
  intro z hm
  have hz : z ≤ Q := by have := (Finset.mem_Ico.mp hm).2; omega
  have hz₁ : 1 ≤ z := by have := (Finset.mem_Ico.mp hm).1; omega
  by_cases ho : Odd z
  · rw [ite_eq_left ho]
    exact threeSpinProjection_negative_bound hQ hz
  · rw [ite_eq_right ho, Complex.ofReal_zero, zero_smul, add_zero]
    exact (threeSpinProjection_lift_posSemidef Q z).smul
      (by exact_mod_cast gramShift_even_nonneg (by omega : 1 ≤ Q) hz₁ hz (Nat.not_odd_iff_even.mp ho))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Bound. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology



theorem fockInequality_eventual_of_certificates_oai {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (hε : 0 ≤ ε)
    (hThree : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)
    (hFour : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, FockInequality Q (1-rowsEta rows-tailCoefficient Q-1222*ε-e Q) := by
  obtain ⟨e, hepos, helim, he⟩ := averagedRowsFour_eventual_bound rows ε hε hFour
  refine ⟨e, hepos, helim, ?_⟩
  filter_upwards [threeTraceForm_eventual_bound rows hThree, eventually_ge_atTop 24] with Q h3 hQ
  have htail : (tailThreeTarget Q + tailCoefficient Q • hamiltonian Q).PosSemidef := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.ofReal_eq_complex_ofReal]
    exact tailThreeTarget_relative_bound (Q:=Q) (by omega)
  have hf := fockInequality_of_finite_comparisons rows (by omega : 16 ≤ Q)
    (averagedRowsFour (by omega : 8 ≤ Q) rows) (tailCoefficient Q) (1222*ε+e Q)
    (averagedRows_positive rows (by omega)) h3 (he Q hQ) htail
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  ring



end LaughlinFock
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinFock.fockInequality_eventual_of_certificates_oai.{u_1} := @OAI.LaughlinFock.fockInequality_eventual_of_certificates_oai.{u_1}
