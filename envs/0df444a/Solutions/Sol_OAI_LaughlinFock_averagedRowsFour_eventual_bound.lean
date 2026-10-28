-- Prove2me | solution 1 for OAI.LaughlinFock.averagedRowsFour_eventual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:52:53.602459+00:00
-- url     : https://prove2.me/submissions/d3fb9f2b-2eeb-4c74-9031-d7ca94d07727

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L035
import Definitions.Def_OAIQ084L043

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
theorem adjoint_mulVec_mem_gram_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix ι κ ℂ) (x : ι → ℂ) :
    ∃ y : κ → ℂ, (Wᴴ * W) *ᵥ y = Wᴴ *ᵥ x := by
  classical
  have hx : (WithLp.toLp 2 (Wᴴ *ᵥ x)) ∈ W.toEuclideanLin.adjoint.range := by
    refine ⟨WithLp.toLp 2 x, ?_⟩
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.toLpLin_apply]
  rw [← LinearMap.range_adjoint_comp_self] at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨y.ofLp, ?_⟩
  have := congrArg WithLp.ofLp hy
  simpa only [LinearMap.comp_apply, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec] using this

theorem sandwich_quadratic_form {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (C : Matrix ι ι ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (Aᴴ * C * A) *ᵥ x = star (A *ᵥ x) ⬝ᵥ C *ᵥ (A *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

 
theorem gram_compression_posSemidef_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) (hC : C.IsHermitian) :
    ((Wᴴ * W) * C * (Wᴴ * W)).PosSemidef ↔ (W * C * Wᴴ).PosSemidef := by
  classical
  let G := Wᴴ * W
  have hg : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  constructor
  · intro h
    have h' : (Gᴴ * C * G).PosSemidef := by rwa [hg.eq]
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · change (W * C * Wᴴ)ᴴ = W * C * Wᴴ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC.eq,
        Matrix.mul_assoc]
    · intro x
      obtain ⟨y, hy⟩ := adjoint_mulVec_mem_gram_range W x
      have hn := h'.dotProduct_mulVec_nonneg y
      rw [sandwich_quadratic_form] at hn
      change 0 ≤ star ((Wᴴ * W) *ᵥ y) ⬝ᵥ C *ᵥ ((Wᴴ * W) *ᵥ y) at hn
      rw [hy] at hn
      rwa [← sandwich_quadratic_form, Matrix.conjTranspose_conjTranspose] at hn
  · intro h
    have := h.conjTranspose_mul_mul_same W
    simpa only [Matrix.mul_assoc] using this
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Model
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
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


theorem gram_quadratic_form {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (ψ : κ → ℂ) :
    star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) = star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]



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



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SphereScaling
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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

theorem occupationDiagonal_inv_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonalInv Q d * occupationDiagonal Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext A
  exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

theorem occupationDiagonal_mul_inv (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonal Q d * occupationDiagonalInv Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext A
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

 
theorem annihilator_mul_occupationDiagonal (Q : ℕ) (d : Orbital Q → ℂ)
    (j : Orbital Q) :
    annihilator Q j * occupationDiagonal Q d =
      d j • (occupationDiagonal Q d * annihilator Q j) := by
  ext A B
  simp only [occupationDiagonal, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.diagonal_mul, smul_eq_mul]
  by_cases h : j ∈ B ∧ A = B.erase j
  · obtain ⟨hj, rfl⟩ := h
    simp only [annihilator, hj, and_self, ite_true, if_true]
    rw [← Finset.mul_prod_erase B d hj]
    ring
  · simp [annihilator, h]


theorem diagonalConjugate_annihilator (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (j : Orbital Q) :
    diagonalConjugate Q d (annihilator Q j) = d j • annihilator Q j := by
  rw [diagonalConjugate, Matrix.mul_assoc, annihilator_mul_occupationDiagonal,
    Matrix.mul_smul, ← Matrix.mul_assoc, occupationDiagonal_inv_mul Q d hd,
    Matrix.one_mul]

theorem diagonalConjugate_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (A B : FockMatrix Q) :
    diagonalConjugate Q d (A * B) =
      diagonalConjugate Q d A * diagonalConjugate Q d B := by
  symm
  unfold diagonalConjugate
  calc
    _ = occupationDiagonalInv Q d * A *
        (occupationDiagonal Q d * occupationDiagonalInv Q d) * B *
        occupationDiagonal Q d := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [occupationDiagonal_mul_inv Q d hd]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]

theorem diagonalConjugate_sum (Q : ℕ) (d : Orbital Q → ℂ) {ι : Type*}
    (s : Finset ι) (A : ι → FockMatrix Q) :
    diagonalConjugate Q d (∑ i ∈ s, A i) = ∑ i ∈ s, diagonalConjugate Q d (A i) := by
  simp only [diagonalConjugate, Matrix.mul_sum, Matrix.sum_mul]

theorem diagonalConjugate_smul (Q : ℕ) (d : Orbital Q → ℂ) (a : ℂ) (A : FockMatrix Q) :
    diagonalConjugate Q d (a • A) = a • diagonalConjugate Q d A := by
  simp only [diagonalConjugate, Matrix.mul_smul, Matrix.smul_mul]


theorem diagonalConjugate_pair (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (a : Orbital Q → Orbital Q → ℂ) :
    diagonalConjugate Q d (coefficientPairAnnihilator Q a) =
      coefficientPairAnnihilator Q (fun i j => a i j * d i * d j) := by
  unfold coefficientPairAnnihilator
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [diagonalConjugate_smul, diagonalConjugate_mul Q d hd,
      diagonalConjugate_annihilator Q d hd, diagonalConjugate_annihilator Q d hd,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · exact diagonalConjugate_zero Q d

open Filter Topology


theorem scaledDescFactorial_nonneg (Q s p : ℕ) :
    0 ≤ scaledDescFactorial Q s p := by unfold scaledDescFactorial; positivity

theorem scaledDescFactorial_pos {Q s p : ℕ} (hQ : 0 < Q) (hp : p ≤ Q-s) :
    0 < scaledDescFactorial Q s p := by
  unfold scaledDescFactorial
  exact div_pos (by exact_mod_cast Nat.descFactorial_pos.mpr hp)
    (pow_pos (by exact_mod_cast hQ) _)

theorem scaledDescFactorial_le_one {Q : ℕ} (hQ : 0 < Q) (s p : ℕ) :
    scaledDescFactorial Q s p ≤ 1 := by
  unfold scaledDescFactorial
  rw [div_le_one (pow_pos (by exact_mod_cast hQ) _)]
  exact_mod_cast (Nat.descFactorial_le_pow (Q-s) p).trans
    (Nat.pow_le_pow_left (Nat.sub_le Q s) p)

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


theorem modeScale_nonneg (Q x : ℕ) : 0 ≤ modeScale Q x := Real.sqrt_nonneg _

theorem modeScale_pos {Q x : ℕ} (hQ : 0 < Q) (hx : x ≤ Q) :
    0 < modeScale Q x := by
  apply Real.sqrt_pos.mpr
  exact scaledDescFactorial_pos hQ (by simpa using hx)

theorem modeScale_le_one {Q : ℕ} (hQ : 0 < Q) (x : ℕ) : modeScale Q x ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact scaledDescFactorial_le_one hQ 0 x

theorem modeScale_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeScale Q x) atTop (𝓝 1) := by
  simpa only [modeScale, Real.sqrt_one] using (scaledDescFactorial_tendsto 0 x).sqrt

theorem pairScale_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairScale Q p) atTop (𝓝 1) := by
  have hd : Tendsto (fun Q : ℕ => 2*Q) atTop atTop :=
    tendsto_atTop_mono (fun Q => by change Q ≤ 2*Q; omega) tendsto_id
  have h := ((scaledDescFactorial_tendsto 2 p).comp hd).inv₀ (by norm_num : (1:ℝ) ≠ 0)
  simpa only [pairScale, inv_one, Real.sqrt_one, Function.comp_apply] using h.sqrt

theorem pairScale_one_le {Q p : ℕ} (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    1 ≤ pairScale Q p := by
  apply Real.one_le_sqrt.mpr
  have hpos := scaledDescFactorial_pos (by omega : 0 < 2*Q) hp
  rw [one_le_inv₀ hpos]
  exact scaledDescFactorial_le_one (by omega) 2 p


theorem pairCoefficient_eq_sphericalPairCoefficient (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p i j = sphericalPairCoefficient Q p i.val j.val :=
  pairCoefficient_eq Q p i j

private theorem radicand_factorization {Q p i j : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hw : i+j=p+1) :
    ((Q.descFactorial i:ℝ)*(Q.descFactorial j:ℝ)*(p.factorial:ℝ)) /
       ((Q:ℝ)*((2*Q-2).descFactorial p:ℝ)*(i.factorial:ℝ)*(j.factorial:ℝ)) =
      (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i *
        scaledDescFactorial Q 0 j *
        ((p.factorial:ℝ) / (2^p * i.factorial * j.factorial)) := by
  have hQR : (Q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  have hd : ((2*Q-2).descFactorial p:ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.descFactorial_pos.mpr hp))
  have hi : (i.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hpow : (Q:ℝ)^i * (Q:ℝ)^j = (Q:ℝ) * (Q:ℝ)^p := by
    rw [← pow_add, hw, pow_succ']
  unfold scaledDescFactorial
  simp only [Nat.sub_zero, inv_div, Nat.cast_mul, Nat.cast_ofNat]
  symm
  calc
    _ = ((2*(Q:ℝ))^p * (Q.descFactorial i:ℝ) * (Q.descFactorial j:ℝ) * p.factorial) /
      (((2*Q-2).descFactorial p:ℝ) * ((Q:ℝ)^i * (Q:ℝ)^j) *
        (2^p * i.factorial * j.factorial)) := by
      field_simp
    _ = _ := by
      rw [hpow, mul_pow]
      field_simp

 

theorem sphericalPairCoefficient_factorization {Q p : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    sphericalPairCoefficient Q p i j = pairScale Q p * modeScale Q i *
      modeScale Q j * limitPairCoefficient p i j := by
  unfold sphericalPairCoefficient limitPairCoefficient
  split_ifs with hw
  · have h1 := scaledDescFactorial_nonneg (2*Q) 2 p
    have h2 := scaledDescFactorial_nonneg Q 0 i
    have h3 := scaledDescFactorial_nonneg Q 0 j
    rw [radicand_factorization hQ hp hw]
    rw [Real.sqrt_mul (by positivity : 0 ≤
        (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i *
         scaledDescFactorial Q 0 j)]
    rw [Real.sqrt_mul (by positivity : 0 ≤
        (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i)]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (scaledDescFactorial (2*Q) 2 p)⁻¹)]
    unfold pairScale modeScale
    ring
  · simp


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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


theorem localDelta_factor_ne_zero {L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (j : Orbital L) : (modeScale Q j.val : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (modeScale_pos hQ (j.is_le.trans hL))

theorem localDelta_mul_inv {L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q) :
    localDelta L Q * localDeltaInv L Q = 1 :=
  occupationDiagonal_mul_inv L _ (localDelta_factor_ne_zero hQ hL)

 
theorem localPair_conjugation {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) :
    localPairAnnihilator L Q p = (pairScale Q p : ℂ) •
      (localDeltaInv L Q * limitPairAnnihilator L p * localDelta L Q) := by
  change localPairAnnihilator L Q p = (pairScale Q p : ℂ) •
    diagonalConjugate L (fun j => (modeScale Q j.val : ℂ)) (limitPairAnnihilator L p)
  rw [limitPairAnnihilator, diagonalConjugate_pair L _
    (localDelta_factor_ne_zero hQ hL), ← coefficientPairAnnihilator_smul]
  unfold localPairAnnihilator
  congr 1
  funext i j
  rw [sphericalPairCoefficient_factorization hQ hp]
  push_cast
  ring

 
theorem localFour_conjugation {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) (j k : Orbital L) :
    annihilator L k * annihilator L j * localPairAnnihilator L Q p =
      ((pairScale Q p : ℂ) / ((modeScale Q j.val : ℂ) * modeScale Q k.val)) •
        (localDeltaInv L Q *
          (annihilator L k * annihilator L j * limitPairAnnihilator L p) *
          localDelta L Q) := by
  let d : Orbital L → ℂ := fun j => modeScale Q j.val
  have hd : ∀ j, d j ≠ 0 := localDelta_factor_ne_zero hQ hL
  change _ = ((pairScale Q p : ℂ) / (d j * d k)) •
    diagonalConjugate L d (annihilator L k * annihilator L j * limitPairAnnihilator L p)
  rw [diagonalConjugate_mul L d hd, diagonalConjugate_mul L d hd,
    diagonalConjugate_annihilator L d hd, diagonalConjugate_annihilator L d hd]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [localPair_conjugation hQ hL hp, Matrix.mul_smul]
  congr 1
  field_simp [hd j, hd k]



theorem localDeltaInv_tendsto (L : ℕ) :
    Tendsto (fun Q : ℕ => localDeltaInv L Q) atTop (𝓝 1) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro A
  apply tendsto_pi_nhds.mpr
  intro B
  dsimp only [localDeltaInv, occupationDiagonalInv]
  by_cases h : A=B
  · subst B
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have ht : Tendsto (fun Q : ℕ => ∏ j ∈ A, (modeScale Q j.val : ℂ)) atTop (𝓝 1) := by
      have ht := tendsto_finsetProd A (fun j _ =>
        Complex.continuous_ofReal.continuousAt.tendsto.comp (modeScale_tendsto j.val))
      simpa using ht
    simpa only [inv_one] using ht.inv₀ (by norm_num : (1:ℂ) ≠ 0)
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    exact tendsto_const_nhds

theorem localDelta_posSemidef (L Q : ℕ) : (localDelta L Q).PosSemidef := by
  classical
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro A
  rw [← Complex.ofReal_prod]
  exact_mod_cast Finset.prod_nonneg (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)

theorem localDelta_contraction {L Q : ℕ} (hQ : 0 < Q) :
    (1 - (localDelta L Q)ᴴ * localDelta L Q).PosSemidef := by
  classical
  rw [(localDelta_posSemidef L Q).isHermitian.eq]
  rw [localDelta, occupationDiagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one, Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro A
  rw [← Complex.ofReal_one, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub]
  have h0 := Finset.prod_nonneg (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)
  have h1 := Finset.prod_le_one (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)
    (fun j _ => modeScale_le_one hQ j.val)
  have hs : (∏ j ∈ A, modeScale Q j.val) * (∏ j ∈ A, modeScale Q j.val) ≤ (1:ℝ) := by
    simpa only [mul_one] using mul_self_le_mul_self h0 h1
  exact_mod_cast sub_nonneg.mpr hs

 
theorem gram_bound_of_scaled_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (D : Matrix ι ι ℂ) (B C : Matrix ι κ ℂ) (r : ℝ)
    (hD : (1 - Dᴴ * D).PosSemidef) (hr : 1 ≤ r)
    (hDB : D * B = (r:ℂ) • C) : (Bᴴ * B - Cᴴ * C).PosSemidef := by
  classical
  have hgram : Bᴴ * (Dᴴ * D) * B = (r:ℂ)^2 • (Cᴴ * C) := by
    calc
      _ = (D * B)ᴴ * (D * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hDB]
        simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  have hs : (0:ℝ) ≤ r^2-1 := by nlinarith
  have hs' : (0:ℂ) ≤ (r:ℂ)^2-1 := by exact_mod_cast hs
  have h := (hD.conjTranspose_mul_mul_same B).add
    ((Matrix.posSemidef_conjTranspose_mul_self C).smul hs')
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hgram] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sub_smul, one_smul]
  abel


theorem localPair_energy_transfer {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) :
    ((localPairAnnihilator L Q p)ᴴ * localPairAnnihilator L Q p -
      localDelta L Q * ((limitPairAnnihilator L p)ᴴ * limitPairAnnihilator L p) *
        localDelta L Q).PosSemidef := by
  classical
  have hDB : localDelta L Q * localPairAnnihilator L Q p =
      (pairScale Q p : ℂ) • (limitPairAnnihilator L p * localDelta L Q) := by
    rw [localPair_conjugation hQ hL hp, Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, localDelta_mul_inv hQ hL,
      Matrix.one_mul]
  have h := gram_bound_of_scaled_contraction (localDelta L Q)
    (localPairAnnihilator L Q p) (limitPairAnnihilator L p * localDelta L Q)
    (pairScale Q p) (localDelta_contraction hQ) (pairScale_one_le hQ hp) hDB
  simpa only [Matrix.conjTranspose_mul, (localDelta_posSemidef L Q).isHermitian.eq,
    Matrix.mul_assoc] using h

 
theorem localHamiltonian_energy_transfer {L P Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hP : P ≤ 2*Q-1) :
    (localHamiltonian L P Q -
      localDelta L Q * limitHamiltonian L P * localDelta L Q).PosSemidef := by
  classical
  unfold localHamiltonian limitHamiltonian
  rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro p hp
  exact localPair_energy_transfer hQ hL (by have := Finset.mem_range.mp hp; omega)

 
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

 
theorem twoAnnihilators_contract (L : ℕ) (j k : Orbital L) (B : FockMatrix L)
    (ψ : Occupation L → ℂ) :
    (∑ A, ‖((annihilator L k * annihilator L j * B) *ᵥ ψ) A‖^2) ≤
      ∑ A, ‖(B *ᵥ ψ) A‖^2 := by
  have hk := annihilator_contracts L k (annihilator L j *ᵥ (B *ᵥ ψ))
  have hj := annihilator_contracts L j (B *ᵥ ψ)
  simpa only [← Matrix.mulVec_mulVec] using hk.trans hj

theorem limitHamiltonian_quadratic_form (L P : ℕ) (ψ : Occupation L → ℂ) :
    (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).re =
      ∑ p ∈ Finset.range P, ∑ A, ‖(limitPairAnnihilator L p *ᵥ ψ) A‖^2 := by
  classical
  simp only [limitHamiltonian, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    gram_quadratic_form, star_dotProduct_self, Complex.ofReal_re]

 

theorem finite_annihilator_family_bound {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (ψ : Occupation L → ℂ) :
    (∑ b, ∑ A,
      ‖((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)) *ᵥ ψ) A‖^2)
    ≤ (Fintype.card β : ℝ) * (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).re := by
  classical
  rw [limitHamiltonian_quadratic_form]
  calc
    _ ≤ ∑ b : β, ∑ q ∈ Finset.range P, ∑ A, ‖(limitPairAnnihilator L q *ᵥ ψ) A‖^2 := by
      apply Finset.sum_le_sum
      intro b _
      refine (twoAnnihilators_contract L (j b) (k b) _ ψ).trans ?_
      exact Finset.single_le_sum
        (f := fun q => ∑ A : Occupation L, ‖(limitPairAnnihilator L q *ᵥ ψ) A‖^2)
        (fun q _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.mem_range.mpr (hp b))
    _ = _ := by simp



theorem entryNormBound_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι κ ℂ) : 0 ≤ entryNormBound R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem entryNormBound_quadratic_form {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℂ) (x : ι → ℂ) :
    |(star x ⬝ᵥ (R *ᵥ x)).re| ≤ entryNormBound R * ∑ i, ‖x i‖^2 := by
  classical
  have hp (i j : ι) : ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖^2 := by
    have hi := Finset.single_le_sum (f := fun k : ι => ‖x k‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f := fun k : ι => ‖x k‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖x i‖-‖x j‖)]
  refine (Complex.abs_re_le_norm _).trans ?_
  calc
    ‖star x ⬝ᵥ (R *ᵥ x)‖ = ‖∑ i, ∑ j, star (x i) * (R i j * x j)‖ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖R i j‖ * ∑ k, ‖x k‖^2 := by
      apply norm_sum_le_of_le
      intro i _
      apply norm_sum_le_of_le
      intro j _
      calc
        _ = ‖R i j‖ * (‖x i‖ * ‖x j‖) := by simp only [norm_mul, norm_star]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hp i j) (norm_nonneg _)
    _ = _ := by simp only [entryNormBound, Finset.sum_mul]

 

theorem entryNormBound_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (hR : R.IsHermitian) :
    (R + entryNormBound R • 1).PosSemidef := by
  have hH : (R + entryNormBound R • 1).IsHermitian :=
    hR.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h := (abs_le.mp (entryNormBound_quadratic_form R x)).1
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, star_dotProduct_self, Complex.add_re, Complex.smul_re,
    Complex.ofReal_re, smul_eq_mul]
  linarith

open Filter Topology

theorem entryNormBound_tendsto_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    {R : ℕ → Matrix ι κ ℂ} (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun Q => entryNormBound (R Q)) atTop (𝓝 0) := by
  have ht : ∀ i j, Tendsto (fun Q => ‖R Q i j‖) atTop (𝓝 0) := by
    intro i j
    simpa only [Matrix.zero_apply, norm_zero] using
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hR i) j).norm)
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => ht i j))
  simpa only [entryNormBound, Finset.sum_const_zero] using h

 

theorem relative_compression_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℂ) (D : Matrix ι ι ℂ)
    (hD : D.IsHermitian) (M R : Matrix κ κ ℂ) (hR : R.IsHermitian)
    (Hstar HQ : Matrix ι ι ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hLimit : (Aᴴ * M * A).PosSemidef)
    (hMajorant : (C • Hstar - Aᴴ * A).PosSemidef)
    (hEnergy : (HQ - D * Hstar * D).PosSemidef) :
    (D * (Aᴴ * (M + R) * A) * D +
      (C * entryNormBound R) • HQ).PosSemidef := by
  have h1 := (entryNormBound_lower_bound R hR).conjTranspose_mul_mul_same (A * D)
  have h2 := hLimit.conjTranspose_mul_mul_same D
  have h3 := (hMajorant.conjTranspose_mul_mul_same D).smul (entryNormBound_nonneg R)
  have h4 := hEnergy.smul (mul_nonneg hC (entryNormBound_nonneg R))
  convert ((h1.add h2).add h3).add h4 using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Matrix.conjTranspose_mul, hD.eq, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_assoc, smul_sub, smul_smul]
  rw [mul_comm (entryNormBound R) C]
  abel
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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

theorem isHermitian_kronecker {β ι : Type*} (M : Matrix β β ℂ) (D : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (hD : D.IsHermitian) : (M ⊗ₖ D).IsHermitian := by
  change (M ⊗ₖ D)ᴴ = _
  rw [Matrix.conjTranspose_kronecker, hM.eq, hD.eq]

 
theorem family_gram_majorant {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P) :
    ((Fintype.card β : ℝ) • limitHamiltonian L P -
      (stackFamily (fun b => annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
      stackFamily (fun b => annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))).PosSemidef := by
  classical
  have hH : (limitHamiltonian L P).IsHermitian :=
    (Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hH.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_conjTranspose_mul_self _))
  intro ψ
  have h := finite_annihilator_family_bound L P p j k hp ψ
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    gram_quadratic_form, star_dotProduct_self, Fintype.sum_prod_type]
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa only [Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul,
      stackFamily_mulVec, sub_nonneg] using h
  · simp only [Complex.sub_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul,
]
    have him : (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).im = 0 :=
      hH.im_star_dotProduct_mulVec_self ψ
    rw [him, mul_zero, sub_self]



theorem localBlockError_hermitian {β : Type*} [Fintype β] (L Q : ℕ)
    (M Mstar : Matrix β β ℂ) (hM : M.IsHermitian) (hS : Mstar.IsHermitian) :
    (localBlockError L Q M Mstar).IsHermitian :=
  (isHermitian_kronecker _ _ hM (Matrix.isHermitian_conjTranspose_mul_self _)).sub
    (isHermitian_kronecker _ _ hS Matrix.isHermitian_one)

theorem localBlockError_tendsto {β : Type*} [Fintype β] (L : ℕ)
    (M : ℕ → Matrix β β ℂ) (Mstar : Matrix β β ℂ)
    (hM : Tendsto M atTop (𝓝 Mstar)) :
    Tendsto (fun Q => localBlockError L Q (M Q) Mstar) atTop (𝓝 0) := by
  have hD : Tendsto (fun Q => (localDeltaInv L Q)ᴴ * localDeltaInv L Q)
      atTop (𝓝 1) := by
    have hc := ((continuous_id (X := FockMatrix L)).matrix_conjTranspose.tendsto 1).comp
      (localDeltaInv_tendsto L)
    simpa using hc.mul (localDeltaInv_tendsto L)
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have hm := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM a.1) b.1
  have hd := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hD a.2) b.2
  simpa only [localBlockError, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.zero_apply,
    sub_self] using (hm.mul hd).sub_const (Mstar a.1 b.1 * (1 : FockMatrix L) a.2 b.2)

 

theorem local_relative_error {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (M : ℕ → Matrix β β ℂ) (Mstar : Matrix β β ℂ)
    (hMH : ∀ Q, (M Q).IsHermitian) (hSH : Mstar.IsHermitian)
    (hM : Tendsto M atTop (𝓝 Mstar))
    (hLimit : (∑ b, ∑ c, Mstar b c •
      ((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b))ᴴ *
        (annihilator L (k c) * annihilator L (j c) * limitPairAnnihilator L (p c)))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 0 < Q → L ≤ Q → P ≤ 2*Q-1 →
      (localDelta L Q *
        (∑ b, ∑ c, (M Q) b c •
          ((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b))ᴴ *
            ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) *
            (annihilator L (k c) * annihilator L (j c) * limitPairAnnihilator L (p c)))) *
          localDelta L Q + ρ Q • localHamiltonian L P Q).PosSemidef := by
  classical
  let A : β → FockMatrix L := fun b =>
    annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)
  let C : ℝ := Fintype.card β
  let ρ : ℕ → ℝ := fun Q => C * entryNormBound (localBlockError L Q (M Q) Mstar)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  refine ⟨ρ, (fun Q => mul_nonneg hC (entryNormBound_nonneg _)), ?_, ?_⟩
  · simpa only [mul_zero] using
      (entryNormBound_tendsto_zero (localBlockError_tendsto L M Mstar hM)).const_mul C
  · intro Q hQ hL hP
    have hLim : ((stackFamily A)ᴴ * (Mstar ⊗ₖ (1 : FockMatrix L)) * stackFamily A).PosSemidef := by
      simpa only [stackFamily_kronecker, Matrix.mul_one] using hLimit
    have h := relative_compression_bound (stackFamily A) (localDelta L Q)
      (localDelta_posSemidef L Q).isHermitian (Mstar ⊗ₖ (1 : FockMatrix L))
      (localBlockError L Q (M Q) Mstar)
      (localBlockError_hermitian L Q _ _ (hMH Q) hSH)
      (limitHamiltonian L P) (localHamiltonian L P Q) C hC hLim
      (family_gram_majorant L P p j k hp)
      (localHamiltonian_energy_transfer hQ hL hP)
    have heq : (Mstar ⊗ₖ (1 : FockMatrix L)) + localBlockError L Q (M Q) Mstar =
        (M Q) ⊗ₖ ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) := by
      unfold localBlockError
      abel
    rw [heq, stackFamily_kronecker] at h
    exact h

 

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

 
theorem tendsto_matrix_mul {α β ι : Type*} [Fintype β]
    {A : ℕ → Matrix α β ℂ} {B : ℕ → Matrix β ι ℂ}
    {Astar : Matrix α β ℂ} {Bstar : Matrix β ι ℂ}
    (hA : Tendsto A atTop (𝓝 Astar)) (hB : Tendsto B atTop (𝓝 Bstar)) :
    Tendsto (fun Q => A Q * B Q) atTop (𝓝 (Astar * Bstar)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finsetSum Finset.univ (fun b _ =>
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) b).mul
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hB b) j))

theorem tendsto_matrix_adjoint {α β : Type*} {A : ℕ → Matrix α β ℂ}
    {Astar : Matrix α β ℂ} (hA : Tendsto A atTop (𝓝 Astar)) :
    Tendsto (fun Q => (A Q)ᴴ) atTop (𝓝 Astarᴴ) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_pi_nhds.mpr
  intro i
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) j).star

theorem hermitian_congruence {α β : Type*} [Fintype α] (S : Matrix α β ℂ)
    (C : Matrix α α ℂ) (hC : C.IsHermitian) : (Sᴴ * C * S).IsHermitian := by
  change (Sᴴ * C * S)ᴴ = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC.eq,
    Matrix.mul_assoc]

 

theorem quadratic_family_mix {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : β → Matrix ι ι ℂ) (S : Matrix α β ℂ) (C : Matrix α α ℂ) :
    (∑ r, ∑ s, C r s • ((∑ b, S r b • A b)ᴴ * (∑ b, S s b • A b))) =
      ∑ b, ∑ c, (Sᴴ * C * S) b c • ((A b)ᴴ * A c) := by
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.smul_mul]
    using quadratic_family_change A S C 1 1 Matrix.isHermitian_one


theorem localFourScale_tendsto (p j k : ℕ) :
    Tendsto (fun Q => localFourScale Q p j k) atTop (𝓝 1) := by
  simpa only [localFourScale, Pi.div_def, mul_one, div_one] using
    (pairScale_tendsto p).div ((modeScale_tendsto j).mul (modeScale_tendsto k)) (by norm_num)

 

theorem local_transfer_of_limitpositive {α β : Type*} [Fintype α] [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (S : ℕ → Matrix α β ℂ) (Sstar : Matrix α β ℂ)
    (C : ℕ → Matrix α α ℂ) (Cstar : Matrix α α ℂ)
    (hS : Tendsto S atTop (𝓝 Sstar)) (hC : Tendsto C atTop (𝓝 Cstar))
    (hCH : ∀ Q, (C Q).IsHermitian) (hCSH : Cstar.IsHermitian)
    (hLimit : (∑ r, ∑ s, Cstar r s •
      ((∑ b, Sstar r b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
       (∑ b, Sstar s b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 0 < Q → L ≤ Q → P ≤ 2*Q-1 →
      ((∑ r, ∑ s, (C Q) r s •
        ((∑ b, (S Q) r b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b)))ᴴ *
         (∑ b, (S Q) s b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b))))) + ρ Q • localHamiltonian L P Q).PosSemidef := by
  classical
  let A : β → FockMatrix L := fun b =>
    annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)
  let B : ℕ → Matrix α β ℂ := fun Q r b =>
    S Q r b * (localFourScale Q (p b) (j b).val (k b).val : ℂ)
  have hB : Tendsto B atTop (𝓝 Sstar) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro b
    have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (localFourScale_tendsto (p b) (j b).val (k b).val)
    simpa only [B, Function.comp_apply, Complex.ofReal_one, mul_one] using
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hS r) b).mul hb
  let M : ℕ → Matrix β β ℂ := fun Q => (B Q)ᴴ * C Q * B Q
  let Mstar : Matrix β β ℂ := Sstarᴴ * Cstar * Sstar
  have hM : Tendsto M atTop (𝓝 Mstar) :=
    tendsto_matrix_mul (tendsto_matrix_mul (tendsto_matrix_adjoint hB) hC) hB
  have hMH : ∀ Q, (M Q).IsHermitian := fun Q => hermitian_congruence _ _ (hCH Q)
  have hMS : Mstar.IsHermitian := hermitian_congruence _ _ hCSH
  rw [quadratic_family_mix] at hLimit
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := local_relative_error L P p j k hp M Mstar hMH hMS hM hLimit
  refine ⟨ρ, hρ0, hρlim, ?_⟩
  intro Q hQ hL hP
  have hb (r : α) :
      (∑ b, (S Q) r b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b))) =
        localDeltaInv L Q * (∑ b, (B Q) r b • A b) * localDelta L Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [localFour_conjugation hQ hL (by have := hp b; omega), smul_smul]
    simp only [B, A, localFourScale, Complex.ofReal_div, Complex.ofReal_mul]
  simp_rw [hb]
  rw [quadratic_family_change _ _ _ _ _ (localDelta_posSemidef L Q).isHermitian]
  simpa only [Matrix.smul_mul] using hρ Q hQ hL hP


theorem occupationMerge_apply (L R : ℕ) (A : Occupation L) (S : Finset (Fin R)) :
    occupationMerge L R (A,S) = (A.disjSum S).map (orbitalMerge L R).toEmbedding := rfl

@[simp] theorem localOrbital_mem_occupationMerge (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    localOrbital L R j ∈ occupationMerge L R (A,S) ↔ j ∈ A := by
  simp only [occupationMerge_apply, localOrbital,
    Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inl_mem_disjSum]

theorem occupationMerge_erase (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    (occupationMerge L R (A,S)).erase (localOrbital L R j) =
      occupationMerge L R (A.erase j,S) := by
  rw [occupationMerge_apply, occupationMerge_apply, localOrbital]
  change ((A.disjSum S).map (orbitalMerge L R).toEmbedding).erase
    ((orbitalMerge L R).toEmbedding (Sum.inl j)) = _
  rw [← Finset.map_erase]
  congr 1
  ext x
  cases x <;> simp

 
theorem occupationMerge_lower_count (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    ((occupationMerge L R (A,S)).filter (fun x => x < localOrbital L R j)).card =
      (A.filter (fun x => x < j)).card := by
  rw [occupationMerge_apply, Finset.filter_map, Finset.card_map]
  have heq : (A.disjSum S).filter (fun x => orbitalMerge L R x < localOrbital L R j) =
      (A.filter (fun x => x < j)).disjSum (∅ : Finset (Fin R)) := by
    ext x
    cases x with
    | inl i => simp only [Finset.mem_filter, Finset.inl_mem_disjSum]; rfl
    | inr i =>
      have hn : ¬ orbitalMerge L R (Sum.inr i) < localOrbital L R j := by
        change ¬ L+1+i.val < j.val
        omega
      simp [hn]
  change ((A.disjSum S).filter
    (fun x => orbitalMerge L R x < localOrbital L R j)).card = _
  rw [heq, Finset.card_disjSum, Finset.card_empty, add_zero]

 

theorem annihilator_spectator_factorization (L R : ℕ) (j : Orbital L) :
    (annihilator (L+R) (localOrbital L R j)).submatrix
      (occupationMerge L R) (occupationMerge L R) =
        annihilator L j ⊗ₖ (1 : Matrix (Finset (Fin R)) (Finset (Fin R)) ℂ) := by
  ext ⟨A,S⟩ ⟨B,T⟩
  simp only [Matrix.submatrix_apply, annihilator, localOrbital_mem_occupationMerge,
    occupationMerge_erase, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
    occupationMerge_lower_count, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : S=T <;> by_cases hB : j ∈ B ∧ A=B.erase j <;> simp_all


theorem spectatorExtension_annihilator (L R : ℕ) (j : Orbital L) :
    spectatorExtension L R (annihilator L j) = annihilator (L+R) (localOrbital L R j) := by
  ext A B
  have h := congrArg (fun M => M ((occupationMerge L R).symm A) ((occupationMerge L R).symm B))
    (annihilator_spectator_factorization L R j)
  simpa only [spectatorExtension, Matrix.submatrix_apply, Equiv.apply_symm_apply] using h.symm

theorem spectatorExtension_mul (L R : ℕ) (A B : FockMatrix L) :
    spectatorExtension L R (A*B) = spectatorExtension L R A * spectatorExtension L R B := by
  unfold spectatorExtension
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem spectatorExtension_adjoint (L R : ℕ) (M : FockMatrix L) :
    spectatorExtension L R Mᴴ = (spectatorExtension L R M)ᴴ := by
  simp only [spectatorExtension, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem spectatorExtension_sum (L R : ℕ) {β : Type*} (s : Finset β) (M : β → FockMatrix L) :
    spectatorExtension L R (∑ b ∈ s, M b) = ∑ b ∈ s, spectatorExtension L R (M b) := by
  ext A B
  simp only [spectatorExtension, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Finset.sum_mul]

theorem spectatorExtension_add (L R : ℕ) (M N : FockMatrix L) :
    spectatorExtension L R (M+N) = spectatorExtension L R M + spectatorExtension L R N := by
  ext A B
  simp only [spectatorExtension, Matrix.add_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, add_mul]

theorem spectatorExtension_smul (L R : ℕ) (c : ℂ) (M : FockMatrix L) :
    spectatorExtension L R (c • M) = c • spectatorExtension L R M := by
  ext A B
  simp only [spectatorExtension, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul, mul_assoc]

theorem spectatorExtension_real_smul (L R : ℕ) (c : ℝ) (M : FockMatrix L) :
    spectatorExtension L R (c • M) = c • spectatorExtension L R M := by
  ext A B
  simp only [spectatorExtension, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Algebra.smul_mul_assoc]

theorem spectatorExtension_posSemidef (L R : ℕ) (M : FockMatrix L) (hM : M.PosSemidef) :
    (spectatorExtension L R M).PosSemidef := by
  exact (hM.kronecker Matrix.PosSemidef.one).submatrix _



theorem spectatorExtension_pair {L p : ℕ} (R : ℕ) (hp : p+1 ≤ L) :
    spectatorExtension L R (localPairAnnihilator L (L+R) p) = pairAnnihilator (L+R) p := by
  classical
  let f : Orbital (L+R) → Orbital (L+R) → FockMatrix (L+R) := fun i j =>
    if i < j then (pairCoefficient (L+R) p i j : ℂ) •
      (annihilator (L+R) j * annihilator (L+R) i) else 0
  have hloc (i j : Orbital L) :
      f (localOrbital L R i) (localOrbital L R j) =
        spectatorExtension L R (if i < j then
          (sphericalPairCoefficient (L+R) p i.val j.val : ℂ) •
            (annihilator L j * annihilator L i) else 0) := by
    unfold f
    have he : localOrbital L R i < localOrbital L R j ↔ i < j := Iff.rfl
    simp only [he]
    split_ifs
    · rw [spectatorExtension_smul, spectatorExtension_mul,
        spectatorExtension_annihilator, spectatorExtension_annihilator]
      rw [pairCoefficient_eq_sphericalPairCoefficient]
      rfl
    · simp
  have hsleft (i : Fin R) (j : Orbital (L+R)) : f (spectatorOrbital L R i) j = 0 := by
    have he : (spectatorOrbital L R i).val + j.val ≠ p+1 := by
      rw [spectatorOrbital_val]; omega
    simp only [f, pairCoefficient_eq_sphericalPairCoefficient, sphericalPairCoefficient,
      ite_eq_right he, Complex.ofReal_zero, zero_smul, ite_self]
  have hsright (i : Orbital (L+R)) (j : Fin R) : f i (spectatorOrbital L R j) = 0 := by
    have he : i.val + (spectatorOrbital L R j).val ≠ p+1 := by
      rw [spectatorOrbital_val]; omega
    simp only [f, pairCoefficient_eq_sphericalPairCoefficient, sphericalPairCoefficient,
      ite_eq_right he, Complex.ofReal_zero, zero_smul, ite_self]
  change _ = ∑ i, ∑ j, f i j
  rw [← (orbitalMerge L R).sum_comp (fun i => ∑ j, f i j), Fintype.sum_sum_type]
  have hright : (∑ i : Fin R, ∑ j, f (orbitalMerge L R (Sum.inr i)) j) = 0 := by
    change (∑ i : Fin R, ∑ j, f (spectatorOrbital L R i) j) = 0
    simp only [hsleft, Finset.sum_const_zero]
  rw [hright, add_zero]
  unfold localPairAnnihilator coefficientPairAnnihilator
  rw [spectatorExtension_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∑ j, f (localOrbital L R i) j
  rw [spectatorExtension_sum, ← (orbitalMerge L R).sum_comp (f (localOrbital L R i)),
    Fintype.sum_sum_type]
  simp only [localOrbital, spectatorOrbital] at hsright hloc
  simp only [hsright, Finset.sum_const_zero, add_zero, hloc, localOrbital]



theorem partialHamiltonian_posSemidef (Q P : ℕ) :
    (partialHamiltonian Q P).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)

theorem spectatorExtension_localHamiltonian {L P : ℕ} (R : ℕ) (hP : P ≤ L) :
    spectatorExtension L R (localHamiltonian L P (L+R)) = partialHamiltonian (L+R) P := by
  unfold localHamiltonian partialHamiltonian
  rw [spectatorExtension_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [spectatorExtension_mul, spectatorExtension_adjoint,
    spectatorExtension_pair R (by have := Finset.mem_range.mp hp; omega)]

 

theorem fock_transfer_of_limitpositive {α β : Type*} [Fintype α] [Fintype β]
    (L P : ℕ) (hL : 1 ≤ L) (hP : P ≤ L)
    (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (S : ℕ → Matrix α β ℂ) (Sstar : Matrix α β ℂ)
    (C : ℕ → Matrix α α ℂ) (Cstar : Matrix α α ℂ)
    (hS : Tendsto S atTop (𝓝 Sstar)) (hC : Tendsto C atTop (𝓝 Cstar))
    (hCH : ∀ Q, (C Q).IsHermitian) (hCSH : Cstar.IsHermitian)
    (hLimit : (∑ r, ∑ s, Cstar r s •
      ((∑ b, Sstar r b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
       (∑ b, Sstar s b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ R, ((∑ r, ∑ s, C (L+R) r s •
        ((∑ b, S (L+R) r b •
           (annihilator (L+R) (localOrbital L R (k b)) *
            annihilator (L+R) (localOrbital L R (j b)) * pairAnnihilator (L+R) (p b)))ᴴ *
         (∑ b, S (L+R) s b •
           (annihilator (L+R) (localOrbital L R (k b)) *
            annihilator (L+R) (localOrbital L R (j b)) * pairAnnihilator (L+R) (p b))))) +
        ρ (L+R) • partialHamiltonian (L+R) P).PosSemidef := by
  classical
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := local_transfer_of_limitpositive L P p j k hp
    S Sstar C Cstar hS hC hCH hCSH hLimit
  refine ⟨ρ, hρ0, hρlim, fun R => ?_⟩
  have h := spectatorExtension_posSemidef L R _
    (hρ (L+R) (by omega) (by omega) (by omega))
  simp only [spectatorExtension_add, spectatorExtension_sum,
    spectatorExtension_smul, spectatorExtension_real_smul, spectatorExtension_mul,
    spectatorExtension_adjoint, spectatorExtension_annihilator,
    spectatorExtension_localHamiltonian R hP] at h
  have hb (b : β) : spectatorExtension L R (localPairAnnihilator L (L+R) (p b)) =
      pairAnnihilator (L+R) (p b) := spectatorExtension_pair R (by have := hp b; omega)
  simpa only [hb] using h
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

 

theorem exteriorLift_of_gram_certificate {α : Type*} [Fintype α] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) α ℂ) (C : Matrix α α ℂ) (hC : C.IsHermitian)
    (hG : ((Wᴴ*W) * C * (Wᴴ*W)).PosSemidef) :
    (∑ r, ∑ s, C r s •
        ((wedgeAnnihilator Q k (fun A => W A r))ᴴ *
          wedgeAnnihilator Q k (fun A => W A s))).PosSemidef := by
  rw [← exteriorLift_congruence]
  apply exteriorLift_posSemidef
  exact (gram_compression_posSemidef_iff W C hC).mp hG



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

theorem limitPairAnnihilator_mem (L p : ℕ) :
    limitPairAnnihilator L p ∈ AnnihilationSpace L 2 :=
  coefficientPairAnnihilator_mem L _

theorem wedgeAnnihilator_mem (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k v ∈ AnnihilationSpace Q k := by
  exact Submodule.sum_mem _ (fun S _ =>
    Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S))

theorem wedgeAnnihilator_annihilatorVector (Q k : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    wedgeAnnihilator Q k (annihilatorVector Q k M) = M := by
  have h := annihilationSpace_normal_form Q k M hM
  simpa only [wedgeAnnihilator, annihilatorVector, star_star] using h.symm



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

theorem basisAnnihilator_singleton (Q : ℕ) (j : Orbital Q) :
    basisAnnihilator Q {j} = annihilator Q j := by
  simp only [basisAnnihilator, Finset.sort_singleton, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem annihilator_vacuum (Q : ℕ) (j : Orbital Q) (A : Occupation Q) :
    annihilator Q j ∅ A = if {j}=A then 1 else 0 := by
  rw [← basisAnnihilator_singleton, basisAnnihilator_vacuum]

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



theorem singlePairCoupling_tendsto (z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient Q Q z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => Q) (fun Q => Q) (1/2)
    tendsto_id tendsto_id
    (by simpa using affineSpin_ratio_tendsto 1 0 1 0 (by norm_num) (by norm_num)) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num] at h
  exact h

 

theorem doublePairCoupling_tendsto (r z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient (2*Q-2) (2*Q-2*r) z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affineSpin_atTop 2 2 (by norm_num)) (affineSpin_atTop 2 (2*r) (by norm_num))
    (by convert affineSpin_ratio_tendsto 2 2 2 (2*r) (by norm_num) (by norm_num) using 1; norm_num) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num] at h
  exact h



theorem sphericalCopyCoefficient_tendsto (D T r p j k : ℕ) :
    Tendsto (fun Q => sphericalCopyCoefficient Q D T r p j k) atTop
      (𝓝 (planarCopyCoefficient D T r p j k)) := by
  unfold sphericalCopyCoefficient planarCopyCoefficient
  split_ifs
  · exact ((singlePairCoupling_tendsto r (j+k-r) j).const_mul (Real.sqrt 2)).mul
      (doublePairCoupling_tendsto r (D-r) (T-D) p)
  · exact tendsto_const_nhds

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
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyNormalization
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem antisymmetric_wedge_inner (Q : ℕ) (f g : Orbital Q → Orbital Q → ℝ)
    (hf : ∀ i j, f j i = -f i j) (hg : ∀ i j, g j i = -g i j) :
    (∑ ij : IncreasingPair Q,
      (Real.sqrt 2 * f ij.val.1 ij.val.2) * (Real.sqrt 2 * g ij.val.1 ij.val.2)) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, f i j * g i j := by
  have hdiag (i : Orbital Q) : f i i = 0 := by have h := hf i i; linarith
  have hterm (i j : Orbital Q) : f i j * g i j =
      (if i < j then f i j * g i j else 0) + (if j < i then f j i * g j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), zero_add, hf i j, hg i j, neg_mul_neg]
  have hsum : (∑ i : Orbital Q, ∑ j : Orbital Q, f i j * g i j) =
      2 * ∑ i : Orbital Q, ∑ j : Orbital Q, if i < j then f i j * g i j else 0 := by
    calc
      _ = ∑ i : Orbital Q, ∑ j : Orbital Q,
          ((if i < j then f i j * g i j else 0) + (if j < i then f j i * g j i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hterm i j
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Orbital Q => if j < i then f j i * g j i else 0)]
        ring
  rw [increasingPair_sum Q (fun i j => (Real.sqrt 2 * f i j) * (Real.sqrt 2 * g i j)), hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · calc
      _ = (Real.sqrt 2)^2 * (f i j * g i j) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · simp



theorem gridInner_eq_fin_sum (n m : ℕ) (f g : GridVector) :
    gridInner n m f g = ∑ p : Fin (n+1), ∑ q : Fin (m+1), f p.val q.val * g p.val q.val := by
  symm
  calc
    _ = ∑ p : Fin (n+1), ∑ q ∈ Finset.range (m+1), f p.val q * g p.val q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Fin.sum_univ_eq_sum_range (fun q => f p.val q * g p.val q) (m+1)
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun p => ∑ q ∈ Finset.range (m+1), f p q * g p q) (n+1)

 

theorem wedgeCoupledCoefficient_gram {Q r s k l : ℕ}
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (hk : k ≤ 2*Q-2*r) (hl : l ≤ 2*Q-2*s) :
    (∑ ij : IncreasingPair Q, wedgeCoupledCoefficient Q r k ij *
      wedgeCoupledCoefficient Q s l ij) = if r=s ∧ k=l then 1 else 0 := by
  unfold wedgeCoupledCoefficient
  rw [antisymmetric_wedge_inner Q
    (fun i j => coupledVector Q Q r k i.val j.val)
    (fun i j => coupledVector Q Q s l i.val j.val)
    (fun i j => coupledVector_antisymm hr hor k i.val j.val)
    (fun i j => coupledVector_antisymm hs hos l i.val j.val)]
  rw [← gridInner_eq_fin_sum]
  exact coupledVector_gram hr hr hs hs (by omega) (by omega)

 

theorem tensor_contraction_inner {P I A B : Type*}
    [Fintype P] [Fintype I] [Fintype A] [Fintype B]
    (x : P → A → ℝ) (y : P → B → ℝ) (u : A → I → ℝ) (v : B → I → ℝ) :
    (∑ p, ∑ i, (∑ a, x p a * u a i) * (∑ b, y p b * v b i)) =
      ∑ p, ∑ a, ∑ b, (x p a * y p b) * (∑ i, u a i * v b i) := by
  apply Finset.sum_congr rfl
  intro p _
  have ht (i : I) : (∑ a, x p a * u a i) * (∑ b, y p b * v b i) =
      ∑ a, ∑ b, (x p a * u a i) * (y p b * v b i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  simp only [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring



theorem composedCoupledVector_gram {Q r s z w k l : ℕ}
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (hz₁ : z ≤ 2*Q-2) (hz₂ : z ≤ 2*Q-2*r)
    (hw₁ : w ≤ 2*Q-2) (hw₂ : w ≤ 2*Q-2*s)
    (hk : k ≤ (2*Q-2)+(2*Q-2*r)-2*z)
    (hl : l ≤ (2*Q-2)+(2*Q-2*s)-2*w) :
    (∑ b : Fin (2*Q-2+1) × IncreasingPair Q,
      composedCoupledVector Q r z k b * composedCoupledVector Q s w l b) =
        if r=s ∧ z=w ∧ k=l then 1 else 0 := by
  classical
  simp only [Fintype.sum_prod_type, composedCoupledVector]
  rw [tensor_contraction_inner]
  simp_rw [wedgeCoupledCoefficient_gram hr hs hor hos
    (Nat.le_of_lt_succ (Fin.isLt _)) (Nat.le_of_lt_succ (Fin.isLt _))]
  by_cases hrs : r=s
  · subst s
    have hsimp (p : Fin (2*Q-2+1)) (a : Fin (2*Q-2*r+1)) :
        (∑ b : Fin (2*Q-2*r+1),
          (coupledVector (2*Q-2) (2*Q-2*r) z k p.val a.val *
           coupledVector (2*Q-2) (2*Q-2*r) w l p.val b.val) *
            (if a.val=b.val then (1:ℝ) else 0)) =
          coupledVector (2*Q-2) (2*Q-2*r) z k p.val a.val *
            coupledVector (2*Q-2) (2*Q-2*r) w l p.val a.val := by
      simp only [Fin.val_inj, mul_ite, mul_one, mul_zero]
      simp
    simp only [true_and, hsimp]
    rw [← gridInner_eq_fin_sum, coupledVector_gram hz₁ hz₂ hw₁ hw₂ hk hl]
  · simp [hrs]

 

theorem composedCoupledVector_eq_sphericalCopy {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hT : T ≤ Q) (hor : Odd r)
    (b : Fin (2*Q-2+1) × IncreasingPair Q) :
    composedCoupledVector Q r (D-r) (T-D) b =
      sphericalCopyCoefficient Q D T r b.1.val b.2.val.1.val b.2.val.2.val := by
  classical
  let p := b.1.val
  let j := b.2.val.1.val
  let k := b.2.val.2.val
  change (∑ a : Fin (2*Q-2*r+1),
    coupledVector (2*Q-2) (2*Q-2*r) (D-r) (T-D) p a.val *
    (Real.sqrt 2 * coupledVector Q Q r a.val j k)) =
      sphericalCopyCoefficient Q D T r p j k
  by_cases hjk : r ≤ j+k
  · by_cases ht : p+j+k=T
    · let a : Fin (2*Q-2*r+1) := ⟨j+k-r, by omega⟩
      rw [Finset.sum_eq_single a]
      · rw [sphericalCopyCoefficient, ite_eq_left ⟨hor, hr, hD, hjk, ht⟩]
        rw [coupledVector, ite_eq_left (show p+a.val = D-r+(T-D) by dsimp [a]; omega),
          coupledVector, ite_eq_left (show j+k = r+a.val by dsimp [a]; omega)]
        dsimp [a]
        ring
      · intro a' _ hne
        have he : j+k ≠ r+a'.val := by
          intro he
          apply hne
          apply Fin.ext
          dsimp [a]
          omega
        simp only [coupledVector, ite_eq_right he, mul_zero]
      · simp
    · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
      apply Finset.sum_eq_zero
      intro a _
      by_cases he : j+k = r+a.val
      · have he' : p+a.val ≠ D-r+(T-D) := by omega
        simp only [coupledVector, ite_eq_right he', zero_mul]
      · simp only [coupledVector, ite_eq_right he, mul_zero]
  · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
    apply Finset.sum_eq_zero
    intro a _
    have he : j+k ≠ r+a.val := by omega
    simp only [coupledVector, ite_eq_right he, mul_zero]

 

theorem sphericalCopyCoefficient_highest_gram {Q D r s : ℕ}
    (hD : D ≤ Q) (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s) :
    (∑ b : Fin (2*Q-2+1) × IncreasingPair Q,
      sphericalCopyCoefficient Q D D r b.1.val b.2.val.1.val b.2.val.2.val *
      sphericalCopyCoefficient Q D D s b.1.val b.2.val.1.val b.2.val.2.val) =
        if r=s then 1 else 0 := by
  have hr0 : 1 ≤ r := by obtain ⟨a, ha⟩ := hor; omega
  have hs0 : 1 ≤ s := by obtain ⟨a, ha⟩ := hos; omega
  simp_rw [← composedCoupledVector_eq_sphericalCopy hr (le_refl D) hD hor,
    ← composedCoupledVector_eq_sphericalCopy hs (le_refl D) hD hos]
  rw [composedCoupledVector_gram (by omega) (by omega) hor hos
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  split_ifs <;> simp_all

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_BesselComparison
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bessel Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder


theorem sum_subtype_support {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (f : ι → M)
    (hf : ∀ i, ¬P i → f i=0) : (∑ i : {i // P i}, f i.val) = ∑ i, f i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · exact (hf i h).symm



theorem highestCopyMatrix_gram {Q D : ℕ} (hD : D ≤ Q) :
    highestCopyMatrix Q D * (highestCopyMatrix Q D)ᴴ = 1 := by
  classical
  ext r s
  have h := sphericalCopyCoefficient_highest_gram hD
    (Nat.le_of_lt_succ r.val.isLt) (Nat.le_of_lt_succ s.val.isLt) r.property s.property
  have he : (r.val.val=s.val.val) ↔ r=s := by
    constructor
    · intro h
      exact Subtype.ext (Fin.ext h)
    · rintro rfl
      rfl
  simp only [he] at h
  rw [← sum_subtype_support
    (fun b : FourUncoupled Q => b.1.val+b.2.val.1.val+b.2.val.2.val=D)
    (fun b => sphericalCopyCoefficient Q D D r.val.val b.1.val b.2.val.1.val b.2.val.2.val *
      sphericalCopyCoefficient Q D D s.val.val b.1.val b.2.val.1.val b.2.val.2.val)] at h
  · have hc := congrArg (fun t : ℝ => (t : ℂ)) h
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, highestCopyMatrix,
      Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul,
      Matrix.one_apply, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using hc
  · intro b hb
    simp [sphericalCopyCoefficient, hb]



theorem highestFourAnnihilator_bessel {Q D : ℕ} (hD : D ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ r : CopyLabel D, ∑ A, ‖(highestFourAnnihilator Q D r *ᵥ ψ) A‖^2) ≤
      ∑ b : FourHighestShell Q D, ∑ A, ‖(shellFourAnnihilator Q D b *ᵥ ψ) A‖^2 := by
  have h := row_isometry_contracts_family (highestCopyMatrix Q D) (highestCopyMatrix_gram hD)
    (fun b A => (shellFourAnnihilator Q D b *ᵥ ψ) A)
  simpa only [highestFourAnnihilator, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

 

theorem highestFourAnnihilator_pair_bound {Q D : ℕ} (hD : D ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ r : CopyLabel D, ∑ A, ‖(highestFourAnnihilator Q D r *ᵥ ψ) A‖^2) ≤
      ∑ b : FourHighestShell Q D, ∑ A,
        ‖(pairAnnihilator Q b.val.1.val *ᵥ ψ) A‖^2 := by
  refine (highestFourAnnihilator_bessel hD ψ).trans ?_
  exact Finset.sum_le_sum fun b _ =>
    twoAnnihilators_contract Q b.val.2.val.1 b.val.2.val.2 _ ψ



theorem fourHighestShell_card_sum {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    Fintype.card (FourHighestShell Q D) = ∑ n ∈ Finset.range (D+1), (n+1)/2 := by
  rw [Fintype.card_congr (fourHighestShellEquiv hQ hD)]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n => (n+1)/2) (D+1)

 
theorem shell_count_formula (D : ℕ) :
    (∑ n ∈ Finset.range (D+1), (n+1)/2) = (D+1)^2/4 := by
  induction D using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more D ih _ =>
    rw [show D+2+1 = (D+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have he : (D+2)/2 + (D+3)/2 = D+2 := by omega
    have hh : (D+3)^2 = (D+1)^2 + (D+2)*4 := by ring
    rw [show D+1+1 = D+2 by omega, show D+1+1+1 = D+3 by omega,
      add_assoc, he, hh, Nat.add_mul_div_right]
    norm_num

theorem fourHighestShell_card {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    Fintype.card (FourHighestShell Q D) = (D+1)^2/4 := by
  rw [fourHighestShell_card_sum hQ hD, shell_count_formula]

 

theorem fourHighestShell_count {Q : ℕ} (hQ : 23 ≤ Q) :
    (∑ D ∈ Finset.Icc 1 23, Fintype.card (FourHighestShell Q D)) = 1222 := by
  calc
    _ = ∑ D ∈ Finset.Icc 1 23, (D+1)^2/4 := by
      apply Finset.sum_congr rfl
      intro D hD
      exact fourHighestShell_card (by omega) (by have := (Finset.mem_Icc.mp hD).2; omega)
    _ = 1222 := by norm_num [Finset.sum_Icc_succ_top]

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


theorem creator_mul_vacuum_zero (Q : ℕ) (k : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (creator Q k * M) ∅ A = 0 := by
  classical
  have hz (B : Occupation Q) : creator Q k ∅ B = 0 := by
    apply ite_eq_right
    rintro ⟨_, h⟩
    have := congrArg (fun S : Occupation Q => k ∈ S) h
    simp at this
  simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero]


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

 

theorem highestFourAnnihilator_pair_posSemidef {Q D : ℕ} (hD : D ≤ Q) :
    ((∑ b : FourHighestShell Q D,
      (pairAnnihilator Q b.val.1.val)ᴴ * pairAnnihilator Q b.val.1.val) -
      ∑ r : CopyLabel D, (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r).PosSemidef :=
  sum_gram_comparison _ _ (highestFourAnnihilator_pair_bound hD)



theorem wedgeAnnihilator_mulVec {ι : Type*} [Fintype ι] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) ι ℂ) (s : ι → ℂ) :
    wedgeAnnihilator Q k (W *ᵥ s) =
      ∑ i, star (s i) • wedgeAnnihilator Q k (fun A => W A i) := by
  classical
  simp only [wedgeAnnihilator, Matrix.mulVec, dotProduct, star_sum, star_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairDecomposition
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



theorem fourCouplingMatrix_complete (Q : ℕ) (hQ : 1 ≤ Q) :
    fourCouplingMatrix Q * (fourCouplingMatrix Q)ᴴ = 1 := by
  classical
  ext pq rs
  have hdim : 2*Q-1 = 2*Q-2+1 := by omega
  let x : Fin (2*Q-2+1) × Fin (2*Q-2+1) :=
    (Fin.cast hdim pq.1, Fin.cast hdim pq.2)
  let y : Fin (2*Q-2+1) × Fin (2*Q-2+1) :=
    (Fin.cast hdim rs.1, Fin.cast hdim rs.2)
  have h := congrArg (fun t : ℝ => (t : ℂ))
    (coupledVector_resolution (2*Q-2) (2*Q-2) x y)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    fourCouplingMatrix, Complex.star_def, Complex.conj_ofReal,
    Matrix.one_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    x, y, Fin.val_cast, Prod.mk.injEq, Fin.cast_inj, ← Prod.ext_iff,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h


theorem fourCoupledWedgeMatrix_target (Q : ℕ) (hQ : 1 ≤ Q) :
    fourCoupledWedgeMatrix Q * (fourCoupledWedgeMatrix Q)ᴴ =
      fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ := by
  unfold fourCoupledWedgeMatrix
  rw [Matrix.conjTranspose_mul]
  calc
    _ = fourWedgeMatrix Q * (fourCouplingMatrix Q * (fourCouplingMatrix Q)ᴴ) *
        (fourWedgeMatrix Q)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [fourCouplingMatrix_complete Q hQ, Matrix.mul_one]



theorem discardedFourTarget_posSemidef (Q L : ℕ) (hQ : 1 ≤ Q) :
    (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ - retainedFourTarget Q L).PosSemidef := by
  classical
  rw [← fourCoupledWedgeMatrix_target Q hQ]
  have hd : (1 - Matrix.diagonal
      (fun c : CoupledIndex (2*Q-2) (2*Q-2) => if c.1.val+1 ≤ L then (1 : ℂ) else 0)).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro c
    split_ifs <;> norm_num
  convert hd.mul_mul_conjTranspose_same (fourCoupledWedgeMatrix Q) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, retainedFourTarget]

 

theorem discardedFourTarget_lift_posSemidef (Q L : ℕ) (hQ : 1 ≤ Q) :
    (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) -
      exteriorLift Q 4 (retainedFourTarget Q L)).PosSemidef := by
  rw [← exteriorLift_sub]
  exact exteriorLift_posSemidef Q 4 _ (discardedFourTarget_posSemidef Q L hQ)


theorem fourWedgeMatrix_annihilator_column (Q : ℕ) (pq : PairLabel Q × PairLabel Q) :
    wedgeAnnihilator Q 4 (fun A => fourWedgeMatrix Q A pq) =
      pairAnnihilator Q pq.2.val * pairAnnihilator Q pq.1.val := by
  apply wedgeAnnihilator_annihilatorVector
  exact annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q pq.1.val)
    (pairAnnihilator_mem Q pq.2.val)

 

theorem fourCoupledAnnihilator_eq_wedge (Q : ℕ)
    (c : CoupledIndex (2*Q-2) (2*Q-2)) :
    fourCoupledAnnihilator Q c.1.val c.2.val =
      wedgeAnnihilator Q 4 (fun A => fourCoupledWedgeMatrix Q A c) := by
  change _ = wedgeAnnihilator Q 4
    (fourWedgeMatrix Q *ᵥ fun pq => fourCouplingMatrix Q pq c)
  rw [wedgeAnnihilator_mulVec]
  simp only [fourWedgeMatrix_annihilator_column, fourCouplingMatrix,
    Complex.star_def, Complex.conj_ofReal, Fintype.sum_prod_type, fourCoupledAnnihilator]

 

theorem retainedFourTarget_lift (Q L : ℕ) :
    exteriorLift Q 4 (retainedFourTarget Q L) =
      ∑ c : CoupledIndex (2*Q-2) (2*Q-2), if c.1.val+1 ≤ L then
        (fourCoupledAnnihilator Q c.1.val c.2.val)ᴴ *
          fourCoupledAnnihilator Q c.1.val c.2.val else 0 := by
  classical
  unfold retainedFourTarget
  rw [exteriorLift_congruence]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ c)]
  rw [← fourCoupledAnnihilator_eq_wedge]
  split_ifs <;> simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyVectors
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Vectors. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem pairAnnihilator_increasing (Q p : ℕ) :
    pairAnnihilator Q p = ∑ ij : IncreasingPair Q,
      (pairCoefficient Q p ij.val.1 ij.val.2 : ℂ) •
        (annihilator Q ij.val.2 * annihilator Q ij.val.1) := by
  rw [increasingPair_sum Q (fun i j =>
    (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i))]
  rfl

 

theorem wedgeCoupledCoefficient_one_eq_pair {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (ij : IncreasingPair Q) :
    wedgeCoupledCoefficient Q 1 p ij = pairCoefficient Q p ij.val.1 ij.val.2 := by
  rw [pairCoefficient_eq_coupled hQ hp]
  rfl



theorem wideFourAnnihilator_mem (Q : ℕ) (b : FourUncoupled Q) :
    annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val ∈
      AnnihilationSpace Q 4 :=
  annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q b.1.val)
    (annihilationSpace_mul Q 1 1 (annihilator_mem Q b.2.val.1) (annihilator_mem Q b.2.val.2))

theorem wideFourWedgeMatrix_annihilator_column (Q : ℕ) (b : FourUncoupled Q) :
    wedgeAnnihilator Q 4 (fun A => wideFourWedgeMatrix Q A b) =
      annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val :=
  wedgeAnnihilator_annihilatorVector Q 4 _ (wideFourAnnihilator_mem Q b)



theorem composedFourAnnihilator_eq_wedge (Q r z k : ℕ) :
    composedFourAnnihilator Q r z k = wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r z k) := by
  unfold composedFourWedgeColumn
  rw [wedgeAnnihilator_mulVec]
  simp only [wideFourWedgeMatrix_annihilator_column, Complex.star_def,
    Complex.conj_ofReal, composedFourAnnihilator]

 

theorem highestFourAnnihilator_eq_composed {Q D : ℕ} (hD : D ≤ Q) (r : CopyLabel D) :
    highestFourAnnihilator Q D r = composedFourAnnihilator Q r.val.val (D-r.val.val) 0 := by
  classical
  have hr : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
  have h := sum_subtype_support
    (fun b : FourUncoupled Q => b.1.val+b.2.val.1.val+b.2.val.2.val=D)
    (fun b : FourUncoupled Q =>
      (sphericalCopyCoefficient Q D D r.val.val b.1.val b.2.val.1.val b.2.val.2.val : ℂ) •
        (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val))
    (by intro b hb; simp [sphericalCopyCoefficient, hb])
  change (∑ b : FourHighestShell Q D,
    (sphericalCopyCoefficient Q D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val : ℂ) •
      (annihilator Q b.val.2.val.2 * annihilator Q b.val.2.val.1 * pairAnnihilator Q b.val.1.val)) = _
  rw [h]
  unfold composedFourAnnihilator
  apply Finset.sum_congr rfl
  intro b _
  rw [← composedCoupledVector_eq_sphericalCopy hr (le_refl D) hD r.property b]
  simp only [Nat.sub_self]

 
theorem highestFourAnnihilator_eq_wedge {Q D : ℕ} (hD : D ≤ Q) (r : CopyLabel D) :
    highestFourAnnihilator Q D r =
      wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r.val.val (D-r.val.val) 0) := by
  rw [highestFourAnnihilator_eq_composed hD, composedFourAnnihilator_eq_wedge]

 

theorem composedFourAnnihilator_one {Q : ℕ} (hQ : 1 ≤ Q) (z k : ℕ) :
    composedFourAnnihilator Q 1 z k = fourCoupledAnnihilator Q z k := by
  classical
  calc
    _ = ∑ p : Fin (2*Q-2+1), ∑ a : Fin (2*Q-2+1),
        (coupledVector (2*Q-2) (2*Q-2) z k p.val a.val : ℂ) •
          (pairAnnihilator Q a.val * pairAnnihilator Q p.val) := by
      simp only [composedFourAnnihilator, Fintype.sum_prod_type, composedCoupledVector,
        Nat.mul_one, Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [pairAnnihilator_increasing Q a.val, Matrix.sum_mul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ij _
      rw [wedgeCoupledCoefficient_one_eq_pair hQ (Nat.le_of_lt_succ a.isLt)]
      simp only [Matrix.smul_mul, smul_smul]
    _ = _ := by
      rw [show 2*Q-2+1 = 2*Q-1 by omega]
      rfl

 
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
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

theorem rowFourLevel_le {t : ℕ} (b c : RowEntry t) : rowFourLevel b c ≤ 23 := by
  have hb := rowEntry_bounds b
  have hc := rowEntry_bounds c
  dsimp [rowFourLevel]
  omega



theorem rowFourTrace_tendsto (D t : ℕ) (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    Tendsto (fun Q => rowFourTrace Q D t a r s) atTop (𝓝 (planarRowFourTrace D t a r s)) := by
  unfold rowFourTrace planarRowFourTrace
  apply Filter.Tendsto.neg
  apply tendsto_finsetSum
  intro b _
  apply tendsto_finsetSum
  intro c _
  exact ((sphericalCopyCoefficient_tendsto D (rowFourLevel b c) r.val.val
    (rowP b) (rowJ b) (rowI c)).const_mul (a b*a c)).mul
      (sphericalCopyCoefficient_tendsto D (rowFourLevel b c) s.val.val
        (rowP c) (rowJ c) (rowI b))

 

theorem rowFourTrace_symmetric (Q D t : ℕ) (a : RowEntry t → ℝ) :
    (rowFourTrace Q D t a).IsSymm := by
  ext r s
  change rowFourTrace Q D t a s r = rowFourTrace Q D t a r s
  unfold rowFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b]
  ring

theorem planarRowFourTrace_symmetric (D t : ℕ) (a : RowEntry t → ℝ) :
    (planarRowFourTrace D t a).IsSymm := by
  ext r s
  change planarRowFourTrace D t a s r = planarRowFourTrace D t a r s
  unfold planarRowFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b]
  ring

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
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativeTransfer
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Transfer. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem fourSpinRatio_tendsto (D : ℕ) :
    Tendsto (fun Q => fourSpinRatio Q D) atTop (𝓝 2) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1+2*(D:ℝ))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hh : Tendsto (fun Q : ℕ => (4-(1+2*(D:ℝ))/Q)/(2-1/(Q:ℝ))) atTop (𝓝 2) := by
    convert ((tendsto_const_nhds (x := (4:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2) (show (2:ℝ)-0 ≠ 0 by norm_num)
      using 1 <;> first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hqr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : 2*(Q:ℝ)-1 ≠ 0 := by linarith
  have hd' : 2-1/(Q:ℝ) ≠ 0 := by rw [ne_eq, sub_eq_zero, eq_div_iff hn]; linarith
  unfold fourSpinRatio
  field_simp [hn, hd, hd']
  ring

theorem fourSpinRatio_eq_dimensions {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    fourSpinRatio Q D = ((4*Q-1-2*D : ℕ) : ℝ) / ((2*Q-1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ 4*Q := by omega
  have h2 : 2*D ≤ 4*Q-1 := by omega
  have h3 : 1 ≤ 2*Q := by omega
  simp only [fourSpinRatio, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]


theorem targetCopy_hermitian (D : ℕ) : (targetCopy D).IsHermitian := by
  classical
  ext r s
  simp [targetCopy, Matrix.conjTranspose_apply, and_comm]



theorem fourComparison_hermitian {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q D : ℕ) : (fourComparison rows ε Q D).IsHermitian := by
  have h : (Matrix.of (fun r s => ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ))).IsHermitian := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]
    apply congrArg (fun x : ℝ => (x : ℂ))
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (rowFourTrace_symmetric Q D (rows i).t.val (rows i).alpha) r) s
  exact ((targetCopy_hermitian D).smul (show IsSelfAdjoint (fourSpinRatio Q D : ℂ) by simp [IsSelfAdjoint])).sub h |>.add
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (ε : ℂ) by simp [IsSelfAdjoint]))

theorem planarFourComparison_hermitian {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (D : ℕ) :
    (planarFourComparison rows ε D).IsHermitian := by
  have h : (Matrix.of (fun r s => ((∑ i, planarRowFourTrace D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ))).IsHermitian := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]
    apply congrArg (fun x : ℝ => (x : ℂ))
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (planarRowFourTrace_symmetric D (rows i).t.val (rows i).alpha) r) s
  exact ((targetCopy_hermitian D).smul (show IsSelfAdjoint (2 : ℂ) by norm_num)).sub h |>.add
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (ε : ℂ) by simp [IsSelfAdjoint]))

theorem fourComparison_tendsto {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ) :
    Tendsto (fun Q => fourComparison rows ε Q D) atTop (𝓝 (planarFourComparison rows ε D)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp (fourSpinRatio_tendsto D)
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_finsetSum Finset.univ (fun i _ => rowFourTrace_tendsto D (rows i).t.val (rows i).alpha r s))
  simpa only [fourComparison, planarFourComparison, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Function.comp_apply, Complex.ofReal_ofNat] using
      ((hf.mul_const (targetCopy D r s)).sub ht).add_const ((ε : ℂ)*(1 : Matrix (CopyLabel D) (CopyLabel D) ℂ) r s)



theorem localCopyMatrix_tendsto (D : ℕ) : Tendsto (localCopyMatrix D) atTop (𝓝 (planarLocalCopyMatrix D)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro b
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (sphericalCopyCoefficient_tendsto D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val)



theorem planarHighestFourAnnihilator_mem (D : ℕ) (r : CopyLabel D) :
    planarHighestFourAnnihilator D r ∈ AnnihilationSpace 24 4 := by
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  exact annihilationSpace_mul 24 2 2 (limitPairAnnihilator_mem 24 b.val.1.val)
    (annihilationSpace_mul 24 1 1 (annihilator_mem 24 b.val.2.val.1) (annihilator_mem 24 b.val.2.val.2))



theorem planarFourWedgeMatrix_annihilator_column (D : ℕ) (r : CopyLabel D) :
    wedgeAnnihilator 24 4 (fun A => planarFourWedgeMatrix D A r) =
      planarHighestFourAnnihilator D r :=
  wedgeAnnihilator_annihilatorVector 24 4 _ (planarHighestFourAnnihilator_mem D r)

 

theorem planarFourCertificate_lift {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ)
    (h : (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    (∑ r, ∑ s, planarFourComparison rows ε D r s •
      ((planarHighestFourAnnihilator D r)ᴴ * planarHighestFourAnnihilator D s)).PosSemidef := by
  have hh := exteriorLift_of_gram_certificate 24 4 (planarFourWedgeMatrix D)
    (planarFourComparison rows ε D) (planarFourComparison_hermitian rows ε D) h
  simpa only [planarFourWedgeMatrix_annihilator_column] using hh



theorem fourShellExtension_injective (D R : ℕ) : Function.Injective (fourShellExtension D R) := by
  intro b c he
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun x => x.val.1.val) he
  · apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x => x.val.2.val.1.val) he
    · apply Fin.ext
      exact congrArg (fun x => x.val.2.val.2.val) he

theorem fourShellExtension_surjective {D : ℕ} (hD : D ≤ 23) (R : ℕ) :
    Function.Surjective (fourShellExtension D R) := by
  intro b
  have hb := b.property
  let c : FourHighestShell 24 D :=
    ⟨(⟨b.val.1.val, by omega⟩,
      ⟨(⟨b.val.2.val.1.val, by omega⟩, ⟨b.val.2.val.2.val, by omega⟩),
        b.val.2.property⟩), hb⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl

 

theorem highestFourAnnihilator_local_sum {D : ℕ} (hD : D ≤ 23) (R : ℕ) (r : CopyLabel D) :
    highestFourAnnihilator (24+R) D r =
      ∑ b : FourHighestShell 24 D, localCopyMatrix D (24+R) r b •
        (annihilator (24+R) (localOrbital 24 R b.val.2.val.2) *
         annihilator (24+R) (localOrbital 24 R b.val.2.val.1) * pairAnnihilator (24+R) b.val.1.val) := by
  classical
  unfold highestFourAnnihilator
  let e : FourHighestShell 24 D ≃ FourHighestShell (24+R) D :=
    Equiv.ofBijective (fourShellExtension D R)
      ⟨fourShellExtension_injective D R, fourShellExtension_surjective hD R⟩
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rfl

 

theorem fourComparison_relative_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) {D : ℕ} (hD : D ≤ 23)
    (hCertificate : (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 24 ≤ Q →
        ((∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
            ρ Q • partialHamiltonian Q 24).PosSemidef := by
  have hb (b : FourHighestShell 24 D) : b.val.1.val < 24 := by
    have := b.property
    omega
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := fock_transfer_of_limitpositive 24 24 (by norm_num) le_rfl
    (fun b : FourHighestShell 24 D => b.val.1.val)
    (fun b => b.val.2.val.1) (fun b => b.val.2.val.2) hb
    (localCopyMatrix D) (planarLocalCopyMatrix D)
    (fun Q => fourComparison rows ε Q D) (planarFourComparison rows ε D)
    (localCopyMatrix_tendsto D) (fourComparison_tendsto rows ε D)
    (fun Q => fourComparison_hermitian rows ε Q D) (planarFourComparison_hermitian rows ε D)
    (planarFourCertificate_lift rows ε D hCertificate)
  refine ⟨ρ, hρ0, hρlim, ?_⟩
  intro Q hQ
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le hQ
  simpa only [← highestFourAnnihilator_local_sum hD R] using hρ R

 

theorem fourComparison_uniform_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ D, 1 ≤ D → D ≤ 23 → ∀ Q, 24 ≤ Q →
        ((∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
            ρ Q • partialHamiltonian Q 24).PosSemidef := by
  classical
  have hh (d : Fin 23) := fourComparison_relative_transfer rows ε
    (by omega : d.val+1 ≤ 23) (hCertificate (d.val+1) (by omega) (by omega))
  choose ρ hρpos hρlim hρbound using hh
  refine ⟨fun Q => ∑ d, ρ d Q, ?_, ?_, ?_⟩
  · intro Q
    exact Finset.sum_nonneg (fun d _ => hρpos d Q)
  · simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun d _ => hρlim d)
  · intro D hD0 hD Q hQ
    let d : Fin 23 := ⟨D-1, by omega⟩
    have hd : d.val+1 = D := by dsimp [d]; omega
    have hle : ρ d Q ≤ ∑ e, ρ e Q :=
      Finset.single_le_sum (fun e _ => hρpos e Q) (Finset.mem_univ d)
    have h := hρbound d Q hQ
    rw [hd] at h
    have h' := h.add ((partialHamiltonian_posSemidef Q 24).smul (sub_nonneg.mpr hle))
    convert h' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [sub_smul]
    abel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_AllowanceOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Allowance Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology

 

theorem fockAverage_partialHamiltonian {Q P : ℕ} (hQ : 1 ≤ Q) (hP : P ≤ 2*Q-1) :
    fockAverage Q (partialHamiltonian Q P) =
      ((P : ℂ) / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  have h := fockAverage_pair_family hQ (fun p : Fin P => p.val)
    (by intro p; have := p.isLt; omega)
  simpa only [Fintype.card_fin, partialHamiltonian,
    Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) P] using h

 

theorem fockAverage_local_error {Q : ℕ} (hQ : 24 ≤ Q) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (partialHamiltonian Q 24) = (24 : ℂ) • hamiltonian Q := by
  rw [fockAverage_partialHamiltonian (by omega) (by omega), smul_smul]
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  congr 1
  field_simp
  norm_num



theorem fourCopyAllowance_bound {Q : ℕ} (hQ : 24 ≤ Q) :
    ((1222 : ℂ) • hamiltonian Q - fourCopyAllowance Q).PosSemidef := by
  have hb (D : ℕ) (hD : D ∈ Finset.Icc 1 23) :
      ((Fintype.card (FourHighestShell Q D) : ℂ) • hamiltonian Q -
        ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ r : CopyLabel D,
          (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r)).PosSemidef := by
    have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
    have he := fockAverage_posSemidef Q _ (highestFourAnnihilator_pair_posSemidef hd)
    rw [map_sub, fockAverage_pair_family (by omega : 1 ≤ Q)
      (fun b : FourHighestShell Q D => b.val.1.val)
      (by intro b; have := b.val.1.isLt; omega)] at he
    have hs := he.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
    have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
    simpa only [smul_sub, smul_smul, mul_div_cancel₀ _ hn] using hs
  have hs := Matrix.posSemidef_sum (Finset.Icc 1 23) hb
  have hc := congrArg (fun n : ℕ => (n : ℂ)) (fourHighestShell_count (by omega : 23 ≤ Q))
  push_cast at hc
  simpa only [Finset.sum_sub_distrib, ← Finset.sum_smul, hc, ← Finset.smul_sum,
    fourCopyAllowance] using hs



theorem averagedFourComparison_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Q, 24 ≤ Q → (averagedFourComparison rows ε Q + e Q • hamiltonian Q).PosSemidef := by
  obtain ⟨ρ, hρpos, hρlim, hρ⟩ := fourComparison_uniform_transfer rows ε hCertificate
  refine ⟨fun Q => 552 * ρ Q, fun Q => mul_nonneg (by norm_num) (hρpos Q), ?_, ?_⟩
  · simpa using hρlim.const_mul 552
  intro Q hQ
  have he (D : ℕ) (hD : D ∈ Finset.Icc 1 23) :
      (((2*Q-1 : ℕ) : ℂ) • fockAverage Q
        (∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
        (24*ρ Q : ℝ) • hamiltonian Q).PosSemidef := by
    have hs := fockAverage_posSemidef Q _
      (hρ D (Finset.mem_Icc.mp hD).1 (Finset.mem_Icc.mp hD).2 Q hQ)
    rw [map_add, (fockAverage Q).map_smul_of_tower] at hs
    have ht := hs.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
    rw [smul_add, smul_comm _ (ρ Q), fockAverage_local_error hQ] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (ρ Q), smul_smul,
      RCLike.real_smul_eq_coe_smul (K:=ℂ) (24*ρ Q)]
    push_cast
    congr 1
    ring_nf
  have hs := Matrix.posSemidef_sum (Finset.Icc 1 23) he
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const,
    Nat.card_Icc, show 23+1-1=23 by omega] at hs
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have hc : (24*ρ Q : ℝ)*23 = 552*ρ Q := by ring
  simpa only [hc, averagedFourComparison] using hs

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourBasis
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem wedgeCoupledCoefficient_resolution (Q : ℕ) (ij kl : IncreasingPair Q) :
    (∑ r : CopyLabel Q, ∑ k : Fin (2*Q-2*r.val.val+1),
      wedgeCoupledCoefficient Q r.val.val k.val ij *
        wedgeCoupledCoefficient Q r.val.val k.val kl) = if ij=kl then 1 else 0 := by
  classical
  have h₁ := coupledVector_resolution Q Q ij.val kl.val
  have h₂ := coupledVector_resolution Q Q (ij.val.2,ij.val.1) kl.val
  have hn : (ij.val.2,ij.val.1) ≠ kl.val := by
    intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    have hi := ij.property
    have hk := kl.property
    dsimp only [Prod.fst, Prod.snd] at ha hb
    rw [← ha, ← hb] at hk
    exact lt_asymm hi hk
  rw [ite_eq_right hn] at h₂
  have hv := congrArg₂ (fun x y : ℝ => x-y) h₁ h₂
  rw [← Finset.sum_sub_distrib] at hv
  have ht (c : CoupledIndex Q Q) :
      coupledVector Q Q c.1.val c.2.val ij.val.1.val ij.val.2.val *
          coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val -
        coupledVector Q Q c.1.val c.2.val ij.val.2.val ij.val.1.val *
          coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val =
      if Odd c.1.val then wedgeCoupledCoefficient Q c.1.val c.2.val ij *
          wedgeCoupledCoefficient Q c.1.val c.2.val kl else 0 := by
    rw [coupledVector_swap (coupledIndex_bounds c).1 c.2.val ij.val.1.val ij.val.2.val]
    by_cases ho : Odd c.1.val
    · rw [ite_eq_left ho, ho.neg_one_pow]
      unfold wedgeCoupledCoefficient
      have hs := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
      linear_combination -(coupledVector Q Q c.1.val c.2.val ij.val.1.val ij.val.2.val *
        coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val) * hs
    · rw [ite_eq_right ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
      ring
  simp only [ht, sub_zero, Subtype.val_inj] at hv
  rw [Fintype.sum_sigma] at hv
  rw [Nat.min_self, ← two_mul Q] at hv
  have he : (∑ r : CopyLabel Q, ∑ k : Fin (2*Q-2*r.val.val+1),
      wedgeCoupledCoefficient Q r.val.val k.val ij *
        wedgeCoupledCoefficient Q r.val.val k.val kl) =
      ∑ r : Fin (Q+1), if Odd r.val then ∑ k : Fin (2*Q-2*r.val+1),
        wedgeCoupledCoefficient Q r.val k.val ij *
          wedgeCoupledCoefficient Q r.val k.val kl else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin (Q+1) => Odd r.val))
      (by intro r; simp) (fun r : Fin (Q+1) => ∑ k : Fin (2*Q-2*r.val+1),
        wedgeCoupledCoefficient Q r.val k.val ij * wedgeCoupledCoefficient Q r.val k.val kl)]
    rw [Finset.sum_filter]
  rw [he]
  simpa only [Nat.min_self, Finset.sum_ite_irrel, Finset.sum_const_zero, two_mul] using hv


theorem fullCouplingMatrix_complete (n m : ℕ) :
    fullCouplingMatrix n m * (fullCouplingMatrix n m)ᴴ = 1 := by
  classical
  ext b c
  have h := congrArg (fun x : ℝ => (x : ℂ)) (coupledVector_resolution n m b c)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, fullCouplingMatrix,
    Complex.star_def, Complex.conj_ofReal, Matrix.one_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero] using h


theorem oddPairColumns_complete (Q : ℕ) :
    (∑ r : CopyLabel Q, oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ) = 1 := by
  classical
  ext ij kl
  have h := congrArg (fun x : ℝ => (x : ℂ)) (wedgeCoupledCoefficient_resolution Q ij kl)
  simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, oddPairColumns,
    Complex.star_def, Complex.conj_ofReal, Matrix.one_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero] using h


theorem composedCouplingMatrix_eq_product (Q r : ℕ) :
    composedCouplingMatrix Q r =
      fourFactorEmbedding Q r * fullCouplingMatrix (2*Q-2) (2*Q-2*r) := by
  classical
  ext b c
  simp only [Matrix.mul_apply, fourFactorEmbedding, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Fintype.sum_prod_type, fullCouplingMatrix]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    composedCouplingMatrix, composedCoupledVector, Complex.ofReal_sum, Complex.ofReal_mul,
    oddPairColumns]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

theorem composedCouplingMatrix_complete (Q : ℕ) :
    (∑ r : CopyLabel Q, composedCouplingMatrix Q r.val.val *
      (composedCouplingMatrix Q r.val.val)ᴴ) = 1 := by
  simp_rw [composedCouplingMatrix_eq_product, Matrix.conjTranspose_mul]
  conv_lhs => arg 2; ext r; rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (fullCouplingMatrix _ _), fullCouplingMatrix_complete, Matrix.one_mul]
  simp only [fourFactorEmbedding, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have hs : (∑ r : CopyLabel Q, Matrix.kronecker 1
      (oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ)) =
      Matrix.kronecker (1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ)
        (∑ r : CopyLabel Q, oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ) := by
    ext b c
    simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum]
  simp only [Matrix.kronecker] at hs
  rw [hs, oddPairColumns_complete]
  exact Matrix.one_kronecker_one

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem oddPairSpinMatrix_contraction (Q r : ℕ) (k : Fin (2*Q-2*r+1)) :
    wedgeAnnihilator Q 2 (fun S => oddPairSpinMatrix Q r S k) =
      (Real.sqrt 2 : ℂ) • coefficientPairAnnihilator Q
        (fun i j => (coupledVector Q Q r k.val i.val j.val : ℂ)) := by
  classical
  rw [coefficientPair_basis_expansion, Finset.smul_sum]
  unfold wedgeAnnihilator
  rw [← (increasingPairEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro ij _
  have hi : (increasingPairEquiv Q).symm (increasingPairSector Q ij) = ij :=
    (increasingPairEquiv Q).symm_apply_apply ij
  simp only [oddPairSpinMatrix, increasingPairEquiv_apply, hi, wedgeCoupledCoefficient,
    Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal, smul_smul, mul_comm]

 

theorem tensorWedge_oddPairSpinMatrix {Q r : ℕ} (hr : r ≤ Q) (hor : Odd r) :
    wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
        coupledSpinMatrix Q Q r =
      (Real.sqrt 2 : ℂ) •
        (oddPairSpinMatrix Q r).submatrix id (Fin.cast (by omega)) := by
  ext S k
  have hv : wedgeAnnihilator Q 2
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ
        (fun ij => coupledSpinMatrix Q Q r ij k)) =
      wedgeAnnihilator Q 2 ((Real.sqrt 2 : ℂ) •
        fun T => oddPairSpinMatrix Q r T (Fin.cast (by omega) k)) := by
    rw [tensorWedge_contraction]
    · rw [wedgeAnnihilator_smul]
      rw [oddPairSpinMatrix_contraction Q r (Fin.cast (by omega) k)]
      rw [smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal, coupledSpinMatrix, Fin.val_cast]
      have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        exact_mod_cast (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
      rw [hs]
    · intro i j
      dsimp [coupledSpinMatrix]
      rw [coupledVector_antisymm hr hor]
      simp
  exact congrFun (wedgeAnnihilator_injective Q 2 hv) S

 
theorem oddPairSpinMatrix_intertwines {Q r : ℕ} (hr : r ≤ Q) (hor : Odd r) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) * oddPairSpinMatrix Q r =
      oddPairSpinMatrix Q r * spinGenerator (2*Q-2*r) s := by
  have he : sectorOneBody Q 2 (spinGenerator Q s) *
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q r) =
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q r) *
      spinGenerator (Q+Q-2*r) s := by
    rw [← Matrix.mul_assoc, tensorWedge_intertwines, Matrix.mul_assoc,
      coupledSpinMatrix_intertwines hr hr, Matrix.mul_assoc]
  rw [tensorWedge_oddPairSpinMatrix hr hor] at he
  simp only [Matrix.mul_smul, Matrix.smul_mul] at he
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hf := smul_right_injective _ hn he
  have hc (n : ℕ) (e : n = 2*Q-2*r)
      (hc : sectorOneBody Q 2 (spinGenerator Q s) *
          (oddPairSpinMatrix Q r).submatrix id (Fin.cast (congrArg (·+1) e)) =
        (oddPairSpinMatrix Q r).submatrix id (Fin.cast (congrArg (·+1) e)) * spinGenerator n s) :
      sectorOneBody Q 2 (spinGenerator Q s) * oddPairSpinMatrix Q r =
        oddPairSpinMatrix Q r * spinGenerator (2*Q-2*r) s := by
    subst n
    simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hc
  exact hc _ (by omega) hf


theorem oddPairSpinMatrix_contraction_increasing (Q r : ℕ) (k : Fin (2*Q-2*r+1)) :
    wedgeAnnihilator Q 2 (fun S => oddPairSpinMatrix Q r S k) =
      ∑ ij : IncreasingPair Q, (wedgeCoupledCoefficient Q r k.val ij : ℂ) •
        (annihilator Q ij.val.2 * annihilator Q ij.val.1) := by
  rw [oddPairSpinMatrix_contraction, coefficientPair_basis_expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [show (increasingPairSector Q ij).val = {ij.val.1,ij.val.2} from rfl,
    basisAnnihilator_pair _ _ ij.property, smul_smul]
  simp only [wedgeCoupledCoefficient, Complex.ofReal_mul]

 

theorem fourSpinWedge_eq_tensor (Q r z : ℕ) :
    fourSpinWedge Q r z =
      wedgeProductMatrix Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) *
        coupledSpinMatrix (2*Q-2) (2*Q-2*r) z := by
  ext S k
  have hv : wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r z k.val) =
      wedgeAnnihilator Q 4
        (wedgeProductMatrix Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) *ᵥ
          fun b => coupledSpinMatrix (2*Q-2) (2*Q-2*r) z b k) := by
    rw [← composedFourAnnihilator_eq_wedge, wedgeAnnihilator_mulVec]
    have hh (b : Fin (2*Q-2+1) × Fin (2*Q-2*r+1)) :=
      wedgeProductMatrix_contraction Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) b
    have ho (a : Fin (2*Q-2*r+1)) := oddPairSpinMatrix_contraction_increasing Q r a
    simp only [hh, ho,
      pairSpinMatrix, pairVector,
      wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
      coupledSpinMatrix, Complex.star_def, Complex.conj_ofReal,
      composedFourAnnihilator, composedCoupledVector, Fintype.sum_prod_type,
      Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul,
      Matrix.sum_mul, Matrix.smul_mul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  exact congrFun (wedgeAnnihilator_injective Q 4 hv) S

 

theorem fourSpinWedge_intertwines {Q r z : ℕ} (hQ : 1 ≤ Q)
    (hr : r ≤ Q) (hor : Odd r) (hz₁ : z ≤ 2*Q-2) (hz₂ : z ≤ 2*Q-2*r) (s : Fin 3) :
    sectorOneBody Q 4 (spinGenerator Q s) * fourSpinWedge Q r z =
      fourSpinWedge Q r z * spinGenerator ((2*Q-2)+(2*Q-2*r)-2*z) s := by
  rw [fourSpinWedge_eq_tensor]
  rw [← Matrix.mul_assoc,
    wedgeProductMatrix_intertwines Q 2 2 _ (spinGenerator_skew Q s) _ _ _ _
      (pairSpinMatrix_intertwines hQ s) (oddPairSpinMatrix_intertwines hr hor s),
    Matrix.mul_assoc, coupledSpinMatrix_intertwines hz₁ hz₂, Matrix.mul_assoc]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourSpinColumns_eq_copy {Q : ℕ} (hQ : 1 ≤ Q) (b : FourSpinIndex Q) :
    fourSpinColumns Q b =
      (fourCopyColumns Q (fourSpinCopyEquiv hQ b).val.1.val
        (fourSpinCopyEquiv hQ b).val.2).submatrix id (Fin.cast (by
          have := b.1.val.isLt
          have := b.2.isLt
          have := b.1.property.pos
          dsimp [fourSpinDegree, fourSpinCopyEquiv]
          omega)) := by
  have hd := (fourSpinCopyEquiv hQ b).property
  rw [fourCopyColumns]
  erw [ite_eq_left hd]
  ext x k
  simp only [fourSpinCopyEquiv, Equiv.coe_fn_mk, fourSpinColumns, Nat.add_sub_cancel_left]
  rfl



theorem fourCopyWedge_intertwines {Q D : ℕ} (hQ : 1 ≤ Q) (r : CopyLabel D) (s : Fin 3) :
    sectorOneBody Q 4 (spinGenerator Q s)*fourCopyWedge Q D r =
      fourCopyWedge Q D r*spinGenerator (fourSpinDegree Q D) s := by
  by_cases hd : D+r.val.val ≤ 2*Q
  · have hr := r.val.isLt
    have hr0 := r.property.pos
    have he : (2*Q-2)+(2*Q-2*r.val.val)-2*(D-r.val.val) = fourSpinDegree Q D := by
      dsimp [fourSpinDegree]
      omega
    have hw : fourCopyWedge Q D r =
        (fourSpinWedge Q r.val.val (D-r.val.val)).submatrix id
          (Fin.cast (congrArg (·+1) he.symm)) := by
      rw [fourCopyWedge, fourCopyColumns]
      erw [ite_eq_left hd]
      ext S k
      simp only [Matrix.submatrix_apply, id_eq, Fin.val_cast, fourSpinWedge,
        composedFourWedgeColumn, Matrix.mulVec, dotProduct]
      rfl
    rw [hw]
    have hi := fourSpinWedge_intertwines hQ (by omega : r.val.val ≤ Q) r.property
      (by omega : D-r.val.val ≤ 2*Q-2) (by omega : D-r.val.val ≤ 2*Q-2*r.val.val) s
    have hc (n m : ℕ) (he : n=m)
        (C : Matrix (SectorOccupation Q 4) (Fin (n+1)) ℂ)
        (hi : sectorOneBody Q 4 (spinGenerator Q s)*C = C*spinGenerator n s) :
        sectorOneBody Q 4 (spinGenerator Q s)*C.submatrix id (Fin.cast (congrArg (·+1) he.symm)) =
          C.submatrix id (Fin.cast (congrArg (·+1) he.symm))*spinGenerator m s := by
      subst m
      simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hi
    exact hc _ _ he _ hi
  · simp [fourCopyWedge, fourCopyColumns, hd]

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

 
theorem fockAverage_spin_mixed_sandwich {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    fockAverage Q (exteriorLift Q k (C*M*Dᴴ)) =
      (M.trace / (n+1 : ℂ)) • exteriorLift Q k (C*Dᴴ) := by
  rw [fockAverage_exteriorLift, sectorAverage_spin_mixed_sandwich C D hC hD]
  exact (exteriorLiftLinear Q k).map_smul _ _

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



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Average. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem sectorAverage_of_complete_copies {ι μ : Type*} [Fintype ι]
    [Fintype μ] [DecidableEq μ] (κ : ι → Type*) [∀ i, Fintype (κ i)]
    {Q k : ℕ} (n : ι → ℕ) (hn : Function.Injective n)
    (C : ∀ i, κ i → Matrix μ (Fin (n i+1)) ℂ)
    (hC : ∑ i, ∑ r, C i r * (C i r)ᴴ = 1)
    (W : Matrix (SectorOccupation Q k) μ ℂ)
    (hW : ∀ i r s, sectorOneBody Q k (spinGenerator Q s)*(W*C i r) =
      (W*C i r)*spinGenerator (n i) s)
    (M : Matrix μ μ ℂ) :
    sectorAverage Q k (W*M*Wᴴ) = ∑ i, ∑ r, ∑ s,
      (((C i r)ᴴ*M*C i s).trace / (n i+1 : ℂ)) • ((W*C i r)*(W*C i s)ᴴ) := by
  classical
  have hh : (∑ b : Sigma κ, C b.1 b.2 * (C b.1 b.2)ᴴ) = 1 := by
    simpa only [Fintype.sum_sigma] using hC
  rw [matrix_complete_column_sandwich (fun b : Sigma κ => n b.1)
    (fun b => C b.1 b.2) hh W M]
  simp only [Fintype.sum_sigma, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    exact sectorAverage_spin_mixed_sandwich (W*C i r) (W*C i s) (hW i r) (hW i s) _
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s _
    exact sectorAverage_spin_cross_sandwich (fun hij => hji (hn hij).symm)
      (W*C i r) (W*C j s) (hW i r) (hW j s) _
  · simp

 
theorem full_column_gram_cast {ι : Type*} {n m : ℕ} (h : n=m)
    (C : Matrix ι (Fin m) ℂ) :
    C.submatrix id (Fin.cast h) * (C.submatrix id (Fin.cast h))ᴴ = C*Cᴴ := by
  subst m
  rfl

 

theorem fourSpinColumns_complete {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ b : FourSpinIndex Q, fourSpinColumns Q b * (fourSpinColumns Q b)ᴴ) = 1 := by
  classical
  rw [Fintype.sum_sigma]
  have hi (r : CopyLabel Q) :
      (∑ z : Fin (2*Q-2*r.val.val+1), fourSpinColumns Q ⟨r,z⟩ *
        (fourSpinColumns Q ⟨r,z⟩)ᴴ) =
      composedCouplingMatrix Q r.val.val * (composedCouplingMatrix Q r.val.val)ᴴ := by
    have hr := r.val.isLt
    have hr0 := r.property.pos
    have hmin : min (2*Q-2) (2*Q-2*r.val.val) = 2*Q-2*r.val.val := by omega
    ext x y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      composedCouplingMatrix, fourSpinColumns, CoupledIndex, Fintype.sum_sigma]
    rw [hmin]
  simp_rw [hi]
  exact composedCouplingMatrix_complete Q

 

theorem fourCopyColumns_complete {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ D : Fin (2*Q), ∑ r : CopyLabel D.val,
      fourCopyColumns Q D.val r * (fourCopyColumns Q D.val r)ᴴ) = 1 := by
  classical
  let f : ((D : Fin (2*Q)) × CopyLabel D.val) →
      Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
    fun b => fourCopyColumns Q b.1.val b.2 * (fourCopyColumns Q b.1.val b.2)ᴴ
  change (∑ D, ∑ r, f ⟨D,r⟩) = 1
  rw [← Fintype.sum_sigma f]
  rw [← sum_subtype_support (fun b : (D : Fin (2*Q)) × CopyLabel D.val =>
    b.1.val+b.2.val.val ≤ 2*Q) f]
  · rw [← (fourSpinCopyEquiv hQ).sum_comp]
    have hh (b : FourSpinIndex Q) : f (fourSpinCopyEquiv hQ b).val =
        fourSpinColumns Q b * (fourSpinColumns Q b)ᴴ := by
      rw [fourSpinColumns_eq_copy hQ, full_column_gram_cast]
    simp_rw [hh]
    exact fourSpinColumns_complete hQ
  · intro b hb
    simp [f, fourCopyColumns, hb]

 
theorem fourSpinDegree_injective {Q : ℕ} (_hQ : 1 ≤ Q) :
    Function.Injective (fun D : Fin (2*Q) => fourSpinDegree Q D.val) := by
  intro a b hab
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  dsimp [fourSpinDegree] at hab
  omega

 

theorem sectorAverage_four_kernel {Q : ℕ} (hQ : 1 ≤ Q)
    (M : Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ) :
    sectorAverage Q 4 (wideFourWedgeMatrix Q*M*(wideFourWedgeMatrix Q)ᴴ) =
      ∑ D : Fin (2*Q), ∑ r : CopyLabel D.val, ∑ s : CopyLabel D.val,
        (((fourCopyColumns Q D.val r)ᴴ*M*fourCopyColumns Q D.val s).trace /
          (fourSpinDegree Q D.val+1 : ℂ)) •
            (fourCopyWedge Q D.val r*(fourCopyWedge Q D.val s)ᴴ) := by
  exact sectorAverage_of_complete_copies (fun D : Fin (2*Q) => CopyLabel D.val)
    (fun D => fourSpinDegree Q D.val) (fourSpinDegree_injective hQ)
    (fun D => fourCopyColumns Q D.val) (fourCopyColumns_complete hQ)
    (wideFourWedgeMatrix Q) (fun D r s => fourCopyWedge_intertwines hQ r s) M

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

theorem composedCoupledVector_eq_sphericalCopy_all {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hrQ : r ≤ Q) (hor : Odd r)
    (b : FourUncoupled Q) :
    composedCoupledVector Q r (D-r) (T-D) b =
      sphericalCopyCoefficient Q D T r b.1.val b.2.val.1.val b.2.val.2.val := by
  classical
  let p := b.1.val
  let j := b.2.val.1.val
  let k := b.2.val.2.val
  change (∑ a : Fin (2*Q-2*r+1),
    coupledVector (2*Q-2) (2*Q-2*r) (D-r) (T-D) p a.val *
    (Real.sqrt 2 * coupledVector Q Q r a.val j k)) =
      sphericalCopyCoefficient Q D T r p j k
  by_cases hjk : r ≤ j+k
  · by_cases ht : p+j+k=T
    · by_cases ha : j+k-r ≤ 2*Q-2*r
      · let a : Fin (2*Q-2*r+1) := ⟨j+k-r, by omega⟩
        rw [Finset.sum_eq_single a]
        · rw [sphericalCopyCoefficient, ite_eq_left ⟨hor, hr, hD, hjk, ht⟩]
          rw [coupledVector, ite_eq_left (show p+a.val = D-r+(T-D) by dsimp [a]; omega),
            coupledVector, ite_eq_left (show j+k = r+a.val by dsimp [a]; omega)]
          dsimp [a]
          ring
        · intro a' _ hne
          have he : j+k ≠ r+a'.val := by
            intro he
            apply hne
            apply Fin.ext
            dsimp [a]
            omega
          simp only [coupledVector, ite_eq_right he, mul_zero]
        · simp
      · have hc : coupledCoefficient Q Q r (j+k-r) j = 0 := by
          have h := congrFun (congrFun (coupledVector_outside_ladder
            (by omega : 2*r ≤ Q+Q) (by omega : Q+Q-2*r < j+k-r)) j) k
          dsimp only [coupledVector] at h
          rw [ite_eq_left (by omega : j+k = r+(j+k-r))] at h
          exact h
        rw [sphericalCopyCoefficient, ite_eq_left ⟨hor, hr, hD, hjk, ht⟩, hc, mul_zero, zero_mul]
        apply Finset.sum_eq_zero
        intro a _
        have hn : j+k ≠ r+a.val := by have := a.isLt; omega
        simp only [coupledVector, ite_eq_right hn, mul_zero]
    · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
      apply Finset.sum_eq_zero
      intro a _
      by_cases he : j+k = r+a.val
      · have he' : p+a.val ≠ D-r+(T-D) := by omega
        simp only [coupledVector, ite_eq_right he', zero_mul]
      · simp only [coupledVector, ite_eq_right he, mul_zero]
  · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
    apply Finset.sum_eq_zero
    intro a _
    have he : j+k ≠ r+a.val := by omega
    simp only [coupledVector, ite_eq_right he, mul_zero]

 

theorem sphericalCopyCoefficient_antisymm {Q r : ℕ} (hrQ : r ≤ Q)
    (D T p j k : ℕ) :
    sphericalCopyCoefficient Q D T r p k j = -sphericalCopyCoefficient Q D T r p j k := by
  by_cases h : Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k=T
  · have hs : Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ k+j ∧ p+k+j=T := by
      simpa only [Nat.add_comm k j, Nat.add_right_comm p k j] using h
    rw [sphericalCopyCoefficient, ite_eq_left hs, sphericalCopyCoefficient, ite_eq_left h,
      Nat.add_comm k j]
    have hc : coupledCoefficient Q Q r (j+k-r) k =
        -coupledCoefficient Q Q r (j+k-r) j := by
      have hv := coupledVector_antisymm hrQ h.1 (j+k-r) j k
      dsimp only [coupledVector] at hv
      rw [ite_eq_left (by omega : j+k=r+(j+k-r)),
        ite_eq_left (by omega : k+j=r+(j+k-r))] at hv
      exact hv
    rw [hc]
    ring
  · have hs : ¬ (Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ k+j ∧ p+k+j=T) := by
      simpa only [Nat.add_comm k j, Nat.add_right_comm p k j] using h
    simp only [sphericalCopyCoefficient, ite_eq_right h, ite_eq_right hs, neg_zero]

theorem sphericalCopyCoefficient_diagonal {Q r : ℕ} (hrQ : r ≤ Q)
    (D T p j : ℕ) : sphericalCopyCoefficient Q D T r p j j = 0 := by
  have h := sphericalCopyCoefficient_antisymm hrQ D T p j j
  linarith



theorem orderedFourColumn_wedgeAnnihilator (Q : ℕ) (p : Fin (2*Q-2+1)) (j k : Orbital Q) :
    wedgeAnnihilator Q 4 (wideFourWedgeMatrix Q *ᵥ orderedFourColumn Q p j k) =
      annihilator Q k * annihilator Q j * pairAnnihilator Q p.val := by
  classical
  rw [wedgeAnnihilator_mulVec]
  simp only [wideFourWedgeMatrix_annihilator_column]
  unfold orderedFourColumn
  split_ifs with h hk
  · simp [Pi.single_apply, ite_smul, apply_ite]
  · simp only [Pi.single_apply, apply_ite, star_neg, star_one, star_zero,
      ite_smul, neg_one_smul, zero_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    rw [annihilator_swap Q j k, neg_mul, neg_neg]
  · have he : j=k := le_antisymm (le_of_not_gt hk) (le_of_not_gt h)
    subst k
    simp [annihilator_square]

 

theorem composed_orderedFourColumn_inner {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hrQ : r ≤ Q) (hor : Odd r)
    (p : Fin (2*Q-2+1)) (j k : Orbital Q) :
    star (fun b => (composedCoupledVector Q r (D-r) (T-D) b : ℂ)) ⬝ᵥ
      orderedFourColumn Q p j k =
        (sphericalCopyCoefficient Q D T r p.val j.val k.val : ℂ) := by
  classical
  unfold orderedFourColumn
  split_ifs with h hk
  · rw [dotProduct_single]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, mul_one,
      composedCoupledVector_eq_sphericalCopy_all hr hD hrQ hor]
  · rw [dotProduct_single]
    change star (composedCoupledVector Q r (D-r) (T-D) (p,⟨(k,j),hk⟩) : ℂ) * (-1) = _
    rw [composedCoupledVector_eq_sphericalCopy_all hr hD hrQ hor]
    dsimp only
    rw [sphericalCopyCoefficient_antisymm hrQ D T p.val j.val k.val]
    simp
  · have he : j=k := le_antisymm (le_of_not_gt hk) (le_of_not_gt h)
    subst k
    simp [sphericalCopyCoefficient_diagonal hrQ]



theorem exteriorLift_outer_congruence {ι : Type*} [Fintype ι]
    (Q k : ℕ) (W : Matrix (SectorOccupation Q k) ι ℂ) (x y : ι → ℂ) :
    exteriorLift Q k (W * Matrix.vecMulVec x (star y) * Wᴴ) =
      (wedgeAnnihilator Q k (W *ᵥ x))ᴴ * wedgeAnnihilator Q k (W *ᵥ y) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, exteriorLift_rankOne]

 

theorem rowFourPrewedge_lift {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    exteriorLift Q 4 (wideFourWedgeMatrix Q * rowFourPrewedge Q p i j a *
      (wideFourWedgeMatrix Q)ᴴ) = rowFourBody Q (fun b => (p b).val) i j a := by
  classical
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (c • M) = c • exteriorLift Q 4 M :=
    (exteriorLiftLinear Q 4).map_smul c M
  have hn (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (-M) = -exteriorLift Q 4 M := (exteriorLiftLinear Q 4).map_neg M
  simp only [rowFourPrewedge, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hn, exteriorLift_sum, hs,
    exteriorLift_outer_congruence, orderedFourColumn_wedgeAnnihilator]
  unfold rowFourBody
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ext A B
  simp [Matrix.smul_apply, Complex.real_smul, Matrix.mul_assoc]

 

theorem outer_bilinear {ι : Type*} [Fintype ι] (u v x y : ι → ℂ) :
    star x ⬝ᵥ (Matrix.vecMulVec u (star v) *ᵥ y) =
      (star x ⬝ᵥ u) * star (star y ⬝ᵥ v) := by
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, Matrix.star_dotProduct v y]

 

theorem rowFourPrewedge_coupled_bilinear {β : Type*} [Fintype β]
    {Q D T r s : ℕ} (hr : r ≤ D) (hs : s ≤ D) (hD : D ≤ T)
    (hrQ : r ≤ Q) (hsQ : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    star (fun b => (composedCoupledVector Q r (D-r) (T-D) b : ℂ)) ⬝ᵥ
      (rowFourPrewedge Q p i j a *ᵥ
        fun b => (composedCoupledVector Q s (D-s) (T-D) b : ℂ)) =
      (-(∑ b, ∑ c, a b*a c *
        sphericalCopyCoefficient Q D T r (p b).val (j b).val (i c).val *
        sphericalCopyCoefficient Q D T s (p c).val (j c).val (i b).val) : ℝ) := by
  classical
  simp only [rowFourPrewedge, Matrix.neg_mulVec, dotProduct_neg,
    Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    outer_bilinear, composed_orderedFourColumn_inner hr hD hrQ hor,
    composed_orderedFourColumn_inner hs hD hsQ hos, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, mul_assoc]


theorem sourceRowFourKernel_lift {Q t : ℕ} (hQ : 8 ≤ Q) (a : RowEntry t → ℝ) :
    exteriorLift Q 4 (wideFourWedgeMatrix Q * sourceRowFourKernel hQ a *
      (wideFourWedgeMatrix Q)ᴴ) =
      rowFourBody Q rowP (sourceRowI hQ) (sourceRowJ hQ) a :=
  rowFourPrewedge_lift Q (sourceRowFourP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

 

theorem sphericalCopyCoefficient_level (Q D T r p j k : ℕ) (h : p+j+k ≠ T) :
    sphericalCopyCoefficient Q D T r p j k = 0 := by
  simp [sphericalCopyCoefficient, h]

 

theorem rowFour_copyWeight_sum {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (r s : CopyLabel D) (b c : RowEntry t) :
    (∑ k : Fin (4*Q-1-2*D),
      sphericalCopyCoefficient Q D (D+k.val) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (D+k.val) s.val.val (rowP c) (rowJ c) (rowI b)) =
      sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b) := by
  classical
  have hl := rowFourLevel_le b c
  by_cases hd : D ≤ rowFourLevel b c
  · let k : Fin (4*Q-1-2*D) := ⟨rowFourLevel b c-D, by omega⟩
    rw [Finset.sum_eq_single k]
    · have he : D+k.val = rowFourLevel b c := by dsimp [k]; omega
      rw [he]
    · intro k' _ hne
      have he : rowP b+rowJ b+rowI c ≠ D+k'.val := by
        intro he
        apply hne
        apply Fin.ext
        dsimp [k]
        dsimp [rowFourLevel] at *
        omega
      rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ he, zero_mul]
    · simp
  · have hz : sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val
        (rowP b) (rowJ b) (rowI c) = 0 := by
      simp [sphericalCopyCoefficient, hd]
    rw [hz, zero_mul]
    apply Finset.sum_eq_zero
    intro k _
    have he : rowP b+rowJ b+rowI c ≠ D+k.val := by
      dsimp [rowFourLevel] at hd
      omega
    rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ he, zero_mul]

 

theorem sourceRowFourKernel_copyTrace {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    (∑ k : Fin (4*Q-1-2*D),
      star (fun b => (composedCoupledVector Q r.val.val (D-r.val.val) k.val b : ℂ)) ⬝ᵥ
        (sourceRowFourKernel (by omega : 8 ≤ Q) a *ᵥ
          fun b => (composedCoupledVector Q s.val.val (D-s.val.val) k.val b : ℂ))) =
      (rowFourTrace Q D t a r s : ℂ) := by
  classical
  have hr : r.val.val ≤ D := by have := r.val.isLt; omega
  have hs : s.val.val ≤ D := by have := s.val.isLt; omega
  have he (k : Fin (4*Q-1-2*D)) := rowFourPrewedge_coupled_bilinear
    hr hs (by omega : D ≤ D+k.val) (by omega : r.val.val ≤ Q)
    (by omega : s.val.val ≤ Q) r.property s.property
    (sourceRowFourP (by omega : 8 ≤ Q))
    (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) a
  simp only [Nat.add_sub_cancel_left, sourceRowFourP, sourceRowI, sourceRowJ] at he
  simp only [sourceRowFourKernel, he]
  rw [← Complex.ofReal_sum]
  apply congrArg (fun x : ℝ => (x : ℂ))
  simp only [rowFourTrace, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [rowFour_copyWeight_sum hQ hD]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem trace_column_bilinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C D : Matrix ι κ ℂ) (M : Matrix ι ι ℂ) :
    (Cᴴ*M*D).trace = ∑ k, star (fun b => C b k) ⬝ᵥ (M *ᵥ fun b => D b k) := by
  rw [Matrix.mul_assoc]
  rfl

 

theorem fourCopy_row_trace {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    ((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace = (rowFourTrace Q D t a r s : ℂ) := by
  have hr := r.val.isLt
  have hs := s.val.isLt
  rw [trace_column_bilinear]
  erw [fourCopyColumns, ite_eq_left (by omega : D+r.val.val ≤ 2*Q),
    fourCopyColumns, ite_eq_left (by omega : D+s.val.val ≤ 2*Q)]
  have hd : fourSpinDegree Q D+1 = 4*Q-1-2*D := by
    dsimp [fourSpinDegree]
    omega
  convert sourceRowFourKernel_copyTrace hQ hD a r s using 1
  all_goals try with_reducible_and_instances rfl
  rw [hd]

 

theorem fourCopy_row_trace_above_support {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : 23 < D)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    ((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace = 0 := by
  by_cases hr : D+r.val.val ≤ 2*Q
  · by_cases hs : D+s.val.val ≤ 2*Q
    · rw [trace_column_bilinear]
      erw [fourCopyColumns, ite_eq_left hr, fourCopyColumns, ite_eq_left hs]
      apply Finset.sum_eq_zero
      intro k _
      have hrl : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
      have hsl : s.val.val ≤ D := Nat.le_of_lt_succ s.val.isLt
      have he := rowFourPrewedge_coupled_bilinear hrl hsl (by omega : D ≤ D+k.val)
        (by omega : r.val.val ≤ Q) (by omega : s.val.val ≤ Q) r.property s.property
        (sourceRowFourP (by omega : 8 ≤ Q)) (sourceRowI (by omega : 8 ≤ Q))
        (sourceRowJ (by omega : 8 ≤ Q)) a
      simp only [Nat.add_sub_cancel_left] at he
      rw [sourceRowFourKernel, he]
      have hz : (∑ b : RowEntry t, ∑ c : RowEntry t, a b*a c *
          sphericalCopyCoefficient Q D (D+k.val) r.val.val (rowP b) (rowJ b) (rowI c) *
          sphericalCopyCoefficient Q D (D+k.val) s.val.val (rowP c) (rowJ c) (rowI b)) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        apply Finset.sum_eq_zero
        intro c _
        have hl := rowFourLevel_le b c
        have hn : rowP b+rowJ b+rowI c ≠ D+k.val := by
          dsimp [rowFourLevel] at hl
          omega
        rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ hn, mul_zero, zero_mul]
      simp only [sourceRowFourP, sourceRowI, sourceRowJ, hz, neg_zero, Complex.ofReal_zero]
    · simp [fourCopyColumns, hs]
  · simp [fourCopyColumns, hr]



theorem fockAverage_rowFourBody {Q t : ℕ} (hQ : 24 ≤ Q) (a : RowEntry t → ℝ) :
    fockAverage Q (rowFourBody Q rowP (sourceRowI (by omega : 8 ≤ Q))
      (sourceRowJ (by omega : 8 ≤ Q)) a) =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        ((rowFourTrace Q D t a r s : ℂ)/(fourSpinDegree Q D+1 : ℂ)) •
          fourCopyLift Q D r s := by
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (c • M) = c • exteriorLift Q 4 M := (exteriorLiftLinear Q 4).map_smul c M
  rw [← sourceRowFourKernel_lift (by omega : 8 ≤ Q) a, fockAverage_exteriorLift,
    sectorAverage_four_kernel (by omega)]
  simp only [exteriorLift_sum, hs]
  let f (D : ℕ) := ∑ r : CopyLabel D, ∑ s : CopyLabel D,
    (((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace / (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s
  change (∑ D : Fin (2*Q), f D.val) = _
  rw [Fin.sum_univ_eq_sum_range f (2*Q)]
  calc
    _ = ∑ D ∈ Finset.Icc 1 23, f D := by
      symm
      apply Finset.sum_subset
      · intro D hD
        simp only [Finset.mem_Icc] at hD
        simp only [Finset.mem_range]
        omega
      · intro D hDr hD
        by_cases hz : D=0
        · subst D
          have he : IsEmpty (CopyLabel 0) := ⟨fun r => by have := r.val.isLt; have := r.property.pos; omega⟩
          let := he
          simp [f]
        · have hd : 23 < D := by simp only [Finset.mem_Icc] at hD; omega
          dsimp [f]
          simp only [fourCopy_row_trace_above_support hQ hd, zero_div, zero_smul, Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      dsimp [f]
      simp only [fourCopy_row_trace hQ (Finset.mem_Icc.mp hD).2]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Highest. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem exteriorLift_mixed_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Q k : ℕ)
    (C : Matrix (SectorOccupation Q k) ι ℂ) (D : Matrix (SectorOccupation Q k) κ ℂ)
    (p : ι) (q : κ) :
    exteriorLift Q k (C*Matrix.single p q (1 : ℂ)*Dᴴ) =
      (wedgeAnnihilator Q k (fun A => C A p))ᴴ *
        wedgeAnnihilator Q k (fun A => D A q) := by
  have h : C*Matrix.single p q (1 : ℂ)*Dᴴ =
      Matrix.vecMulVec (fun A => C A p) (star (fun A => D A q)) := by
    ext A B
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Matrix.vecMulVec_apply]
  rw [h, exteriorLift_rankOne]

 

theorem fockAverage_spin_mixed_column {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (p : Fin (n+1)) :
    fockAverage Q ((wedgeAnnihilator Q k (fun A => C A p))ᴴ *
      wedgeAnnihilator Q k (fun A => D A p)) =
      (1/(n+1 : ℂ)) • exteriorLift Q k (C*Dᴴ) := by
  rw [← exteriorLift_mixed_single Q k C D p p,
    fockAverage_spin_mixed_sandwich C D hC hD, Matrix.trace_single_eq_same]

 

theorem fourCopyWedge_column {Q D : ℕ} (hr : D ≤ Q) (r : CopyLabel D)
    (k : Fin (fourSpinDegree Q D+1)) :
    (fun A => fourCopyWedge Q D r A k) =
      composedFourWedgeColumn Q r.val.val (D-r.val.val) k.val := by
  have hrl := r.val.isLt
  unfold fourCopyWedge fourCopyColumns
  erw [ite_eq_left (by omega : D+r.val.val ≤ 2*Q)]
  rfl

 
theorem fockAverage_highestFour {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q)
    (r s : CopyLabel D) :
    fockAverage Q ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s) =
      (1/(fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  have h := fockAverage_spin_mixed_column (fourCopyWedge Q D r) (fourCopyWedge Q D s)
    (fourCopyWedge_intertwines hQ r) (fourCopyWedge_intertwines hQ s)
    (⟨0, by omega⟩ : Fin (fourSpinDegree Q D+1))
  rw [fourCopyWedge_column hD, fourCopyWedge_column hD,
    ← highestFourAnnihilator_eq_wedge hD r, ← highestFourAnnihilator_eq_wedge hD s] at h
  exact h

 
theorem exteriorLift_mixed_gram {ι : Type*} [Fintype ι]
    (Q k : ℕ) (C D : Matrix (SectorOccupation Q k) ι ℂ) :
    exteriorLift Q k (C*Dᴴ) = ∑ p,
      (wedgeAnnihilator Q k (fun A => C A p))ᴴ *
        wedgeAnnihilator Q k (fun A => D A p) := by
  have h : C*Dᴴ = ∑ p, Matrix.vecMulVec (fun A => C A p) (star (fun A => D A p)) := by
    ext A B
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply]
  rw [h, exteriorLift_sum]
  simp only [exteriorLift_rankOne]

 
theorem fourCopyLift_eq_weights {Q D : ℕ} (hD : D ≤ Q) (r s : CopyLabel D) :
    fourCopyLift Q D r s = ∑ k : Fin (fourSpinDegree Q D+1),
      (composedFourAnnihilator Q r.val.val (D-r.val.val) k.val)ᴴ *
        composedFourAnnihilator Q s.val.val (D-s.val.val) k.val := by
  rw [fourCopyLift, exteriorLift_mixed_gram]
  simp only [fourCopyWedge_column hD, ← composedFourAnnihilator_eq_wedge]



theorem targetCopy_sum {Q D : ℕ} (hD : 1 ≤ D) (f : CopyLabel D → CopyLabel D → FockMatrix Q) :
    (∑ r, ∑ s, targetCopy D r s • f r s) = f (firstFourCopy hD) (firstFourCopy hD) := by
  classical
  have he (r : CopyLabel D) : r.val.val=1 ↔ r=firstFourCopy hD := by
    constructor
    · intro h
      exact Subtype.ext (Fin.ext h)
    · rintro rfl
      rfl
  simp [targetCopy, he, ite_and, ite_smul]

 

theorem fourCopyLift_first {Q D : ℕ} (hQ : 1 ≤ Q) (hD : 1 ≤ D) (hd : D ≤ Q) :
    fourCopyLift Q D (firstFourCopy hD) (firstFourCopy hD) =
      ∑ k ∈ Finset.range (fourSpinDegree Q D+1),
        (fourCoupledAnnihilator Q (D-1) k)ᴴ * fourCoupledAnnihilator Q (D-1) k := by
  rw [fourCopyLift_eq_weights hd]
  simp only [firstFourCopy, composedFourAnnihilator_one hQ]
  exact Fin.sum_univ_eq_sum_range (fun k =>
    (fourCoupledAnnihilator Q (D-1) k)ᴴ * fourCoupledAnnihilator Q (D-1) k) _

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Retained. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem retainedFourTarget_copy_sum {Q : ℕ} (hQ : 24 ≤ Q) :
    exteriorLift Q 4 (retainedFourTarget Q 23) =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        targetCopy D r s • fourCopyLift Q D r s := by
  classical
  let f (z : ℕ) := ∑ k ∈ Finset.range ((2*Q-2)+(2*Q-2)-2*z+1),
    (fourCoupledAnnihilator Q z k)ᴴ * fourCoupledAnnihilator Q z k
  have h1 : exteriorLift Q 4 (retainedFourTarget Q 23) =
      ∑ z ∈ Finset.range (2*Q-2+1), if z+1 ≤ 23 then f z else 0 := by
    rw [retainedFourTarget_lift]
    change (∑ c : (z : Fin (min (2*Q-2) (2*Q-2)+1)) ×
      Fin ((2*Q-2)+(2*Q-2)-2*z.val+1), if c.1.val+1 ≤ 23 then
        (fourCoupledAnnihilator Q c.1.val c.2.val)ᴴ *
          fourCoupledAnnihilator Q c.1.val c.2.val else 0) = _
    rw [Fintype.sum_sigma, min_self]
    rw [← Fin.sum_univ_eq_sum_range (fun z => if z+1 ≤ 23 then f z else 0)]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z.val+1 ≤ 23
    · simp only [hz, ite_true, if_true]
      exact Fin.sum_univ_eq_sum_range (fun k =>
        (fourCoupledAnnihilator Q z.val k)ᴴ * fourCoupledAnnihilator Q z.val k) _
    · simp only [hz, ite_false, Finset.sum_const_zero]
  rw [h1, ← Finset.sum_filter]
  have he : (Finset.range (2*Q-2+1)).filter (fun z => z+1 ≤ 23) = Finset.range 23 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  apply Finset.sum_bij (fun z _ => z+1)
  · intro z hz
    have := Finset.mem_range.mp hz
    simp only [Finset.mem_Icc]
    omega
  · intro z hz w hw hzw
    omega
  · intro D hD
    have hD' := Finset.mem_Icc.mp hD
    refine ⟨D-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro z hz
    have hz' := Finset.mem_range.mp hz
    rw [targetCopy_sum (by omega : 1 ≤ z+1),
      fourCopyLift_first (by omega : 1 ≤ Q) (by omega : 1 ≤ z+1) (by omega : z+1 ≤ Q)]
    have hd : (2*Q-2)+(2*Q-2)-2*z+1 = fourSpinDegree Q (z+1)+1 := by
      dsimp [fourSpinDegree]
      omega
    simp only [Nat.add_sub_cancel, f, hd]

 

theorem averagedRowsFour_copy_sum {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 24 ≤ Q) :
    averagedRowsFour (by omega : 8 ≤ Q) rows =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        (((2*Q-1 : ℕ) : ℂ) *
          ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ) /
          (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  rw [averagedRowsFour, map_sum]
  simp_rw [fockAverage_rowFourBody hQ]
  simp only [Finset.smul_sum, smul_smul, ← mul_div_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_smul]
  simp only [← Finset.sum_div, ← Finset.mul_sum, ← Complex.ofReal_sum]

 
theorem fourCopyAllowance_copy_sum {Q : ℕ} (hQ : 24 ≤ Q) :
    fourCopyAllowance Q = ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
      ((((2*Q-1 : ℕ) : ℂ) * (1 : Matrix (CopyLabel D) (CopyLabel D) ℂ) r s) /
        (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  classical
  unfold fourCopyAllowance
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
  rw [map_sum, Finset.smul_sum]
  simp_rw [fockAverage_highestFour (by omega : 1 ≤ Q) hd]
  apply Finset.sum_congr rfl
  intro r _
  simp [Matrix.one_apply, ite_smul, smul_smul, div_eq_mul_inv]

 

theorem fourSpinRatio_common_dimensions {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    (fourSpinRatio Q D : ℂ) = (fourSpinDegree Q D+1 : ℂ) / ((2*Q-1 : ℕ) : ℂ) := by
  rw [fourSpinRatio_eq_dimensions hQ hD, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_natCast]
  have hd : 4*Q-1-2*D = fourSpinDegree Q D+1 := by
    dsimp [fourSpinDegree]
    omega
  rw [hd, Nat.cast_add_one]

 

theorem averagedFourComparison_eq {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) {Q : ℕ} (hQ : 24 ≤ Q) :
    averagedFourComparison rows ε Q =
      exteriorLift Q 4 (retainedFourTarget Q 23) -
        averagedRowsFour (by omega : 8 ≤ Q) rows + ε • fourCopyAllowance Q := by
  classical
  rw [retainedFourTarget_copy_sum hQ, averagedRowsFour_copy_sum rows hQ,
    fourCopyAllowance_copy_sum hQ, averagedFourComparison]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, fockAverage_highestFour (by omega : 1 ≤ Q) hd]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) ε]
  simp only [fourComparison, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, smul_smul, ← sub_smul, ← add_smul]
  rw [fourSpinRatio_common_dimensions (by omega) hd]
  congr 1
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  have hm : (fourSpinDegree Q D+1 : ℂ) ≠ 0 := by
    rw [← Nat.cast_add_one]
    exact_mod_cast (show fourSpinDegree Q D+1 ≠ 0 by omega)
  simp only [Matrix.one_apply]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  split_ifs <;> field_simp

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

 

theorem averagedRowsFour_eventual_bound_oai {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (hε : 0 ≤ ε)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Q, (hQ : 24 ≤ Q) →
        (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) +
          (1222*ε+e Q) • hamiltonian Q -
          averagedRowsFour (by omega : 8 ≤ Q) rows).PosSemidef := by
  obtain ⟨e, hepos, helim, he⟩ := averagedFourComparison_transfer rows ε hCertificate
  refine ⟨e, hepos, helim, ?_⟩
  intro Q hQ
  have h := he Q hQ
  rw [averagedFourComparison_eq rows ε hQ] at h
  have hr : (1222 : ℂ) • hamiltonian Q = (1222 : ℝ) • hamiltonian Q := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    norm_num [RCLike.ofReal_eq_complex_ofReal]
  have hallow := (fourCopyAllowance_bound hQ).smul hε
  rw [hr] at hallow
  have hdisc := discardedFourTarget_lift_posSemidef Q 23 (by omega)
  convert (h.add hallow).add hdisc using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_sub, smul_smul, add_smul, mul_comm ε (1222:ℝ)]
  abel



end LaughlinFock
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinFock.averagedRowsFour_eventual_bound_oai.{u_1} := @OAI.LaughlinFock.averagedRowsFour_eventual_bound_oai.{u_1}
