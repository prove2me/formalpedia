-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.physical_spin_square_split
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:25:10.008882+00:00
-- url     : https://prove2.me/submissions/a492ca16-c240-4179-9f5c-cbe3f51d20b8

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L035

section
-- module Solutions.OAIQ030_LG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Occupation
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.basisContraction_apply_empty _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.extendLocal_add _root_.OAI.LaughlinGap.Occupation.extendLocal_adjoint _root_.OAI.LaughlinGap.Occupation.extendLocal_mul _root_.OAI.LaughlinGap.Occupation.extendLocal_one _root_.OAI.LaughlinGap.Occupation.extendLocal_smul _root_.OAI.LaughlinGap.Occupation.extendLocal_zero _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply_label _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.slice_apply _root_.OAI.LaughlinGap.Occupation.slice_extendLocal _root_.OAI.LaughlinGap.Occupation.vacuum_norm _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation. -/

noncomputable section


namespace LaughlinGap
namespace Occupation
open scoped BigOperators InnerProduct

theorem transition_complement {n : ℕ} (j : Fin n) (ε : Bool) :
    transition j ε ∘ₗ transition j (!ε) + transition j (!ε) ∘ₗ transition j ε =
      LinearMap.id := by
  ext x A
  change transition j ε (transition j (!ε) x) A +
    transition j (!ε) (transition j ε x) A = x A
  cases ε <;> by_cases hj : j ∈ A <;> simp [transition_apply, hj, ← mul_assoc]

theorem annihilation_creation_CAR {n : ℕ} (i j : Fin n) :
    annihilation i ∘ₗ creation j + creation j ∘ₗ annihilation i =
      if i = j then LinearMap.id else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using transition_complement i false
  · rw [ite_eq_right hij, transition_anticommute_of_ne hij false true]
    exact neg_add_cancel _

theorem annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j = (if i = j then 1 else 0) - creation j * annihilation i := by
  exact eq_sub_of_add_eq (annihilation_creation_CAR i j)

theorem annihilation_creation_mul {n : ℕ} (i j : Fin n)
    (X : Module.End ℂ (Hilbert n)) :
    annihilation i * (creation j * X) =
      (if i = j then X else 0) - creation j * (annihilation i * X) := by
  rw [← mul_assoc, annihilation_creation, sub_mul]
  by_cases hij : i = j <;> simp [hij, mul_assoc]

theorem pair_normal_order {n : ℕ} (i j k l : Fin n) :
    annihilation j * annihilation i * creation k * creation l =
      (if i = k ∧ j = l then 1 else 0) -
      (if j = k ∧ i = l then 1 else 0) -
      (if i = k then creation l * annihilation j else 0) +
      (if j = k then creation l * annihilation i else 0) +
      (if i = l then creation k * annihilation j else 0) -
      (if j = l then creation k * annihilation i else 0) +
      creation k * creation l * annihilation j * annihilation i := by
  rw [mul_assoc, mul_assoc, annihilation_creation_mul]
  simp only [mul_sub]
  rw [annihilation_creation_mul]
  rw [annihilation_creation]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, annihilation_creation_mul]
  rw [annihilation_creation]
  simp only [ite_and]
  split_ifs <;> noncomm_ring

end Occupation
end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

section PairNormalization
open Polynomial

private theorem coeff_euler (P : ℝ[X]) (n : ℕ) :
    (euler P).coeff n = (n : ℝ) * P.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]

private theorem weighted_binomial_polynomial_identity (n : ℕ) :
    let F : ℝ[X] := (X + 1) ^ (n + 2)
    euler (euler F) * F + F * euler (euler F) - 2 * (euler F * euler F) =
      C (2 * (n + 2 : ℝ)) * X * (X + 1) ^ (2 * n + 2) := by
  dsimp only
  have hd : ((X + 1) ^ (n + 2) : ℝ[X]).derivative =
      C ((n : ℝ) + 2) * (X + 1) ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, derivative_pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, derivative_add, derivative_X, derivative_one,
      add_zero, mul_one]
    congr 2
    ring
  have hd' : ((X + 1) ^ (n + 1) : ℝ[X]).derivative =
      C ((n : ℝ) + 1) * (X + 1) ^ n := by
    simp [derivative_pow_succ, derivative_add]
  simp only [euler, derivative_mul, hd, derivative_X]
  simp only [derivative_C, hd', zero_mul, zero_add, mul_one]
  simp only [show 2 * n + 2 = n + n + 2 by omega, pow_add, pow_two, map_mul,
    map_add, map_ofNat, map_one]
  ring

theorem weighted_binomial_antidiagonal (Q : ℕ) (hQ : 2 ≤ Q) (p : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p + 1),
      ((ij.1 : ℝ) - ij.2) ^ 2 * (Q.choose ij.1 : ℝ) * Q.choose ij.2) =
      2 * Q * ((2 * Q - 2).choose p : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 2 := ⟨Q - 2, by omega⟩
  have heq : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p + 1),
      ((ij.1 : ℝ) - ij.2) ^ 2 * ((n + 2).choose ij.1 : ℝ) * (n + 2).choose ij.2) =
      ((euler (euler ((X + 1) ^ (n + 2) : ℝ[X]))) * (X + 1) ^ (n + 2) +
        (X + 1) ^ (n + 2) * (euler (euler ((X + 1) ^ (n + 2) : ℝ[X]))) -
        2 * (euler ((X + 1) ^ (n + 2)) * euler ((X + 1) ^ (n + 2)))).coeff (p + 1) := by
    simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_mul, coeff_euler,
      coeff_X_add_one_pow]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [heq, weighted_binomial_polynomial_identity]
  rw [mul_assoc, coeff_C_mul, coeff_X_mul, coeff_X_add_one_pow]
  congr 2
  norm_cast

theorem pairCoefficient_sq (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1)
    (x y : Fin (Q + 1)) :
    pairCoefficient Q p x y ^ 2 =
      if x.val + y.val = p + 1 then
        ((x.val : ℝ) - y.val) ^ 2 * (Q.choose x.val : ℝ) * Q.choose y.val /
          (2 * Q * ((2 * Q - 2).choose p : ℝ))
      else 0 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have hch : ((2 * Q - 2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)).ne'
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) =
      ((Q.choose x.val : ℝ) * Q.choose y.val) /
        ((Q : ℝ) * ((2 * Q - 2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs with hs
  · rw [hrad, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  · simp

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  by_cases hs : x.val + y.val = p + 1
  · simp only [hs, Nat.add_comm y.val x.val, ↓reduceIte]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring
  · simp [hs, Nat.add_comm]

private theorem sum_fin_pair_on_antidiagonal (Q n : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ x y, (Q < x ∨ Q < y) → f x y = 0) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      if x.val + y.val = n then f x.val y.val else 0) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, f ij.1 ij.2 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin (Q + 1),
    if x + y.val = n then f x y.val else 0)]
  have hs (x : ℕ) := Fin.sum_univ_eq_sum_range
    (fun y => if x + y = n then f x y else 0) (Q + 1)
  simp_rw [hs]
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro ij hij
    simpa using (Finset.mem_filter.mp hij).2
  · intro ij hij hnot
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have heq : ij.1 + ij.2 = n := by simpa using hij
    apply hf
    omega

theorem pairCoefficient_sum_sq (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p < 2 * Q - 1) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1), pairCoefficient Q p x y ^ 2) = 1 := by
  simp_rw [pairCoefficient_sq Q p hQ hp]
  have hch : ((2 * Q - 2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2 * Q - 2 by omega)).ne'
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  rw [sum_fin_pair_on_antidiagonal Q (p + 1)
    (fun x y => ((x : ℝ) - y) ^ 2 * (Q.choose x : ℝ) * Q.choose y /
      (2 * Q * ((2 * Q - 2).choose p : ℝ)))]
  · rw [← Finset.sum_div, weighted_binomial_antidiagonal Q hQ p]
    field_simp
  · intro x y hxy
    rcases hxy with hx | hy
    · simp [Nat.choose_eq_zero_of_lt hx]
    · simp [Nat.choose_eq_zero_of_lt hy]

theorem pairCoefficient_sum_mul_of_ne (Q p r : ℕ) (hpr : p ≠ r) :
    (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      pairCoefficient Q p x y * pairCoefficient Q r x y) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  unfold pairCoefficient
  split_ifs <;> simp_all

theorem pairVector_inner (Q p r : ℕ) :
    inner ℂ (pairVector Q p) (pairVector Q r) =
      ((∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
        pairCoefficient Q p x y * pairCoefficient Q r x y : ℝ) : ℂ) := by
  simp [pairVector, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

theorem pairVector_orthonormal (Q : ℕ) (hQ : 2 ≤ Q) :
    Orthonormal ℂ (fun p : Fin (2 * Q - 1) => pairVector Q p.val) := by
  rw [orthonormal_iff_ite]
  intro p r
  rw [pairVector_inner]
  split_ifs with hpr
  · subst r
    rw [show (∑ x : Fin (Q + 1), ∑ y : Fin (Q + 1),
      pairCoefficient Q p.val x y * pairCoefficient Q p.val x y) = 1 by
        simpa only [pow_two] using pairCoefficient_sum_sq Q p.val hQ p.isLt]
    rfl
  · rw [pairCoefficient_sum_mul_of_ne Q p.val r.val (fun h => hpr (Fin.ext h))]
    rfl

end PairNormalization

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEnergy
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Energy. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexOrder

section PositiveLifting
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem matrixLift_rankOne (B : ι → Module.End ℂ E) (v w : ι → ℂ) :
    matrixLift B (Matrix.vecMulVec v (star w)) =
      (contractCombination B v).adjoint * contractCombination B w := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Pi.star_apply, contractCombination, map_sum, map_smulₛₗ,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Complex.star_def, Complex.conj_conj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrixLift_columns {κ : Type*} [Fintype κ]
    (B : ι → Module.End ℂ E) (W : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) :
    matrixLift B (W * C * W.conjTranspose) =
      matrixLift (fun r => contractCombination B (fun i => W i r)) C := by
  classical
  have hm : W * C * W.conjTranspose =
      ∑ r, ∑ s, C r s • Matrix.vecMulVec (fun i => W i r) (star (fun i => W i s)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hm]
  simp only [map_sum, map_smul, matrixLift_rankOne]
  rfl

end PositiveLifting

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma annihilation_eq_zero_of_degree_zero {n : ℕ} {x : Hilbert n}
    (hx : Homogeneous 0 x) (j : Fin n) : annihilation j x = 0 := by
  ext A
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · simp only [transition_apply, hj, decide_false, ite_true,
      flip_of_not_mem hj]
    rw [hx (insert j A) (by simp), mul_zero]
    rfl

lemma word_homogeneous {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous (k + js.length) x) : Homogeneous k (word js x) := by
  induction js generalizing x with
  | nil => simpa only [word, List.length_nil, Nat.add_zero, LinearMap.id_apply] using hx
  | cons j js ih =>
    exact ih (annihilation_homogeneous (by simpa only [List.length_cons, Nat.add_assoc] using hx) j)

lemma word_eq_zero_of_degree_lt {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous k x) (hk : k < js.length) : word js x = 0 := by
  induction js generalizing k x with
  | nil => simp at hk
  | cons j js ih =>
    cases k with
    | zero => simp only [word, LinearMap.comp_apply, annihilation_eq_zero_of_degree_zero hx, map_zero]
    | succ k =>
      exact ih (annihilation_homogeneous hx j) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

lemma basisContraction_degree {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x)
    (A : BasisLabel n k) : basisContraction A x = x A.val • vacuum n := by
  have hd : Homogeneous 0 (basisContraction A x) :=
    word_homogeneous (A.val.sort (· ≤ ·)) (by simpa only [Finset.length_sort, A.property, Nat.zero_add] using hx)
  rw [degree_zero_eq_vacuum hd, basisContraction_apply_empty]

lemma basisContraction_eq_zero_of_degree_lt {n j k : ℕ} {x : Hilbert n}
    (hx : Homogeneous j x) (hjk : j < k) (A : BasisLabel n k) : basisContraction A x = 0 :=
  word_eq_zero_of_degree_lt (A.val.sort (· ≤ ·)) hx (by simpa only [Finset.length_sort, A.property] using hjk)

@[simp] lemma basisContraction_sectorInclusion {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : BasisLabel n k) : basisContraction A (sectorInclusion n k x) = x A • vacuum n := by
  rw [basisContraction_degree (sectorInclusion_homogeneous x), sectorInclusion_apply_label]

theorem exteriorLift_eq_zero_of_degree_lt {n j k : ℕ} {x : Hilbert n}
    (hx : Homogeneous j x) (hjk : j < k) (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) :
    exteriorLift M x = 0 := by
  simp only [exteriorLift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, basisContraction_eq_zero_of_degree_lt hx hjk,
    map_zero, smul_zero, Finset.sum_const_zero]

theorem exteriorLift_inner_sector {n k : ℕ}
    (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) (x y : ExteriorCoordinates n k) :
    inner ℂ (sectorInclusion n k x) (exteriorLift M (sectorInclusion n k y)) =
      inner ℂ x (M.toEuclideanLin y) := by
  classical
  simp only [exteriorLift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right, basisContraction_sectorInclusion,
    inner_smul_left]
  simp only [inner_self_eq_norm_sq_to_K, vacuum_norm, RCLike.ofReal_one,
    one_pow, mul_one]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Contraction
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct Topology ComplexOrder

lemma word_perm_scalar {n : ℕ} {js ks : List (Fin n)} (h : js.Perm ks) :
    ∃ c : ℂ, word js = c • word ks := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons j h ih =>
    obtain ⟨c,hc⟩ := ih
    exact ⟨c, by simp only [word_cons, hc, smul_mul_assoc]⟩
  | swap i j js =>
    refine ⟨-1, ?_⟩
    rw [word_cons, word_cons, word_cons, word_cons]
    rw [mul_assoc, annihilation_anticommute i j, mul_neg, ← mul_assoc]
    simp only [neg_smul, one_smul]
  | trans h h' ih ih' =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := ih'
    exact ⟨c*d, by rw [hc, hd, smul_smul]⟩

lemma word_eq_zero_of_not_nodup {n : ℕ} (js : List (Fin n)) (h : ¬ js.Nodup) :
    word js = 0 := by
  induction js with
  | nil => simp at h
  | cons j js ih =>
    by_cases hj : js.Nodup
    · have hm : j ∈ js := by simpa only [List.nodup_cons, hj, and_true, not_not] using h
      obtain ⟨c,hc⟩ := word_perm_scalar (List.perm_cons_erase hm)
      rw [word_cons, hc, word_cons, smul_mul_assoc, mul_assoc]
      have hz : annihilation j * annihilation j = 0 := transition_square j false
      rw [hz, mul_zero, smul_zero]
    · rw [word_cons, ih hj, zero_mul]

theorem word_normal_form {n : ℕ} (js : List (Fin n)) :
    ∃ c : ℂ, word js = c • word (js.toFinset.sort (· ≤ ·)) := by
  by_cases hn : js.Nodup
  · apply word_perm_scalar
    exact ((js.toFinset.sort_perm_toList (· ≤ ·)).trans (List.toFinset_toList hn)).symm
  · exact ⟨0, by rw [word_eq_zero_of_not_nodup js hn, zero_smul]⟩

theorem basisContraction_adjoint_vacuum {n k : ℕ} (A : BasisLabel n k) :
    (basisContraction A).adjoint (vacuum n) = EuclideanSpace.single A.val 1 := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, inner_vacuum_left, basisContraction_apply_empty]
  simp [EuclideanSpace.inner_single_left]

@[simp] lemma reconstruct_allBasisContraction {n : ℕ} (A : Finset (Fin n)) :
    reconstruct (allBasisContraction A) = allBasisContraction A := by
  change fullContraction ((basisContraction (⟨A,rfl⟩ : BasisLabel n A.card)).adjoint (vacuum n)) = _
  rw [basisContraction_adjoint_vacuum, fullContraction_single]
  simp

theorem reconstruct_word {n : ℕ} (js : List (Fin n)) : reconstruct (word js) = word js := by
  obtain ⟨c,hc⟩ := word_normal_form js
  rw [hc]
  change reconstruct (c • allBasisContraction js.toFinset) = c • allBasisContraction js.toFinset
  rw [map_smul, reconstruct_allBasisContraction]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma basicPair_middle {n : ℕ} (a b : PairLabel n) :
    basicPair a * (basicPair b).adjoint =
      (if a = b then 1 else 0) + oneContraction a b + (basicPair b).adjoint * basicPair a := by
  have hcross : ¬(a.val.2 = b.val.1 ∧ a.val.1 = b.val.2) := by
    rintro ⟨ha,hb⟩
    have h := a.property
    rw [ha,hb] at h
    exact lt_asymm h b.property
  have hdiag : (a.val.1 = b.val.1 ∧ a.val.2 = b.val.2) ↔ a = b := by
    constructor
    · rintro ⟨h₁,h₂⟩
      apply Subtype.ext
      exact Prod.ext h₁ h₂
    · rintro rfl; exact ⟨rfl,rfl⟩
  simp only [basicPair, adjoint_mul, annihilation_adjoint]
  rw [← mul_assoc, pair_normal_order, ite_eq_right hcross]
  simp only [hdiag]
  unfold oneContraction
  noncomm_ring

lemma annihilation_commute_basicPair {n : ℕ} (i : Fin n) (a : PairLabel n) :
    annihilation i * basicPair a = basicPair a * annihilation i := by
  unfold basicPair
  rw [← mul_assoc, annihilation_anticommute i a.val.2, neg_mul, mul_assoc,
    annihilation_anticommute i a.val.1, mul_neg, neg_neg, ← mul_assoc]

lemma basicPair_commute {n : ℕ} (a b : PairLabel n) :
    basicPair a * basicPair b = basicPair b * basicPair a := by
  change annihilation a.val.2 * annihilation a.val.1 * basicPair b = _
  rw [mul_assoc, annihilation_commute_basicPair, ← mul_assoc,
    annihilation_commute_basicPair, mul_assoc]
  rfl

lemma pairContraction_commute {n : ℕ} (v w : PairLabel n → ℂ) :
    pairContraction v * pairContraction w = pairContraction w * pairContraction v := by
  simp only [pairContraction, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [basicPair_commute, mul_comm]

theorem pairContraction_middle {n : ℕ} (v w : PairLabel n → ℂ) :
    pairContraction v * (pairContraction w).adjoint =
      (∑ a, star (v a) * w a) • 1 + pairOneContraction v w +
        (pairContraction w).adjoint * pairContraction v := by
  classical
  simp only [pairContraction, map_sum, map_smulₛₗ, Complex.star_def, Complex.conj_conj, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [basicPair_middle, smul_add, Finset.sum_add_distrib]
  have hdiag : (∑ a : PairLabel n, ∑ b : PairLabel n,
      (star (v a) * w b) • (if a = b then (1 : Module.End ℂ (Hilbert n)) else 0)) =
      (∑ a, star (v a) * w a) • 1 := by
    simp [smul_ite, ← Finset.sum_smul]
  simp only [mul_comm (w _) ((starRingEnd ℂ) (v _))]
  simp only [Complex.star_def] at hdiag
  rw [hdiag]
  congr 1
  rw [Finset.sum_comm]

theorem pairHamiltonian_square {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairHamiltonian v * pairHamiltonian v =
      pairHamiltonian v + pairThreeTerm v + pairFourTerm v := by
  classical
  have hp (p r : ι) :
      ((pairContraction (v p)).adjoint * pairContraction (v p)) *
        ((pairContraction (v r)).adjoint * pairContraction (v r)) =
      (if p = r then (pairContraction (v p)).adjoint * pairContraction (v r) else 0) +
      (pairContraction (v p)).adjoint * pairOneContraction (v p) (v r) * pairContraction (v r) +
      (pairContraction (v r) * pairContraction (v p)).adjoint *
        (pairContraction (v r) * pairContraction (v p)) := by
    rw [mul_assoc, ← mul_assoc (pairContraction (v p)), pairContraction_middle, hv]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, adjoint_mul]
    have he : (pairContraction (v p)).adjoint *
        ((pairContraction (v r)).adjoint * pairContraction (v p) * pairContraction (v r)) =
        (pairContraction (v p)).adjoint * (pairContraction (v r)).adjoint *
          (pairContraction (v r) * pairContraction (v p)) := by
      rw [mul_assoc, pairContraction_commute (v p) (v r), ← mul_assoc]
    rw [he]
    by_cases h : p = r <;> simp [h, mul_assoc]
  unfold pairHamiltonian
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, hp, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NormalOrder
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_creation _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma word_rankOne_mem_bodySpace {n k : ℕ} (js ks : List (Fin n))
    (hj : js.length = k) (hk : ks.length = k) :
    (word js).adjoint * word ks ∈ bodySpace n k := by
  classical
  by_cases hn : js.Nodup
  · by_cases hm : ks.Nodup
    · obtain ⟨c,hc⟩ := word_normal_form js
      obtain ⟨d,hd⟩ := word_normal_form ks
      let A : BasisLabel n k := ⟨js.toFinset, (List.toFinset_card_of_nodup hn).trans hj⟩
      let B : BasisLabel n k := ⟨ks.toFinset, (List.toFinset_card_of_nodup hm).trans hk⟩
      have hA : word js = c • basisContraction A := hc
      have hB : word ks = d • basisContraction B := hd
      rw [hA,hB,map_smulₛₗ,smul_mul_assoc,mul_smul_comm,smul_smul]
      exact ⟨Matrix.single A B ((starRingEnd ℂ) c * d), exteriorLift_single _ _ _⟩
    · rw [word_eq_zero_of_not_nodup ks hm, mul_zero]
      exact (bodySpace n k).zero_mem
  · rw [word_eq_zero_of_not_nodup js hn, map_zero, zero_mul]
    exact (bodySpace n k).zero_mem

lemma triple_basic_eq_word {n : ℕ} (i : Fin n) (a : PairLabel n) :
    annihilation i * basicPair a = word [a.val.1,a.val.2,i] := by
  simp only [basicPair, word_cons, word_nil, one_mul, mul_assoc]

lemma triple_rankOne_mem_bodySpace {n : ℕ} (v w : PairLabel n → ℂ) (i j : Fin n) :
    (annihilation i * pairContraction v).adjoint *
      (annihilation j * pairContraction w) ∈ bodySpace n 3 := by
  classical
  simp only [pairContraction, Finset.mul_sum, mul_smul_comm, map_sum,
    map_smulₛₗ]
  simp only [Finset.sum_mul]
  simp only [smul_mul_assoc, Finset.smul_sum, smul_smul]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  rw [triple_basic_eq_word, triple_basic_eq_word]
  exact word_rankOne_mem_bodySpace _ _ rfl rfl

lemma middle_rankOne_mem_bodySpace {n : ℕ} (v w : PairLabel n → ℂ) (i j : Fin n) :
    (pairContraction v).adjoint * (creation i * annihilation j) * pairContraction w ∈
      bodySpace n 3 := by
  convert triple_rankOne_mem_bodySpace v w i j using 1
  all_goals try with_reducible_and_instances rfl
  rw [adjoint_mul, annihilation_adjoint]
  simp only [mul_assoc]

theorem pairThreeTerm_mem_bodySpace {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : pairThreeTerm v ∈ bodySpace n 3 := by
  classical
  unfold pairThreeTerm
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  simp only [pairOneContraction, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  simp only [oneContraction, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    mul_ite, ite_mul, mul_zero, zero_mul]
  have h (i j : Fin n) := middle_rankOne_mem_bodySpace (v p) (v r) i j
  have hc (P : Prop) [Decidable P] (i j : Fin n) :
      (if P then (pairContraction (v p)).adjoint * (creation i * annihilation j) *
        pairContraction (v r) else 0) ∈ bodySpace n 3 := by
    split_ifs
    · exact h i j
    · exact (bodySpace n 3).zero_mem
  exact Submodule.sub_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (hc _ _ _))
      (hc _ _ _)) (hc _ _ _)) (hc _ _ _)

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma homogeneous_smul {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) (c : ℂ) :
    Homogeneous k (c • x) := by
  intro A hA
  simp [hx A hA]

lemma homogeneous_sum {n k : ℕ} {ι : Type*} (s : Finset ι) (x : ι → Hilbert n)
    (hx : ∀ i ∈ s, Homogeneous k (x i)) : Homogeneous k (∑ i ∈ s, x i) := by
  intro A hA
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hx i hi A hA)

lemma vacuum_homogeneous (n : ℕ) : Homogeneous 0 (vacuum n) := by
  intro A hA
  have hh : A ≠ ∅ := by intro h; apply hA; simp [h]
  simp [vacuum_apply, hh]

lemma creation_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x)
    (i : Fin n) : Homogeneous (k+1) (creation i x) := by
  intro A hA
  by_cases hi : i ∈ A
  · have hc : (A.erase i).card ≠ k := by
      have hh := Finset.card_erase_add_one hi
      omega
    simp [transition_apply, hi, hx _ hc]
  · simp [transition_apply, hi]

lemma pairContraction_adjoint_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous k x) :
    Homogeneous (k+2) ((pairContraction v).adjoint x) := by
  simp only [pairContraction, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  simpa only [basicPair, adjoint_mul, annihilation_adjoint, Module.End.mul_apply] using
    creation_homogeneous (creation_homogeneous hx a.val.2) a.val.1

lemma fullContraction_eq_exteriorContraction {n k : ℕ} {x : Hilbert n}
    (hx : Homogeneous k x) :
    fullContraction x = exteriorContraction (sectorReadout n k x) := by
  classical
  change (∑ A, star (x A) • allBasisContraction A) =
    ∑ A : BasisLabel n k, star (x A.val) • basisContraction A
  calc
    (∑ A, star (x A) • allBasisContraction A) =
        ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => A.card = k),
          star (x A) • allBasisContraction A := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      have hh : A.card ≠ k := by simpa using hA
      simp [hx A hh]
    _ = _ := Finset.sum_subtype _ (by simp) _

lemma reconstruct_pair_product {n : ℕ} (v w : PairLabel n → ℂ) :
    reconstruct (pairContraction v * pairContraction w) = pairContraction v * pairContraction w := by
  simp only [pairContraction, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have he : basicPair a * basicPair b = word [b.val.1,b.val.2,a.val.1,a.val.2] := by
    simp only [basicPair, word_cons, word_nil, one_mul, mul_assoc]
  rw [he,reconstruct_word]

lemma pairWedgeColumn_contraction {n : ℕ} (v w : PairLabel n → ℂ) :
    exteriorContraction (pairWedgeColumn v w) = pairContraction w * pairContraction v := by
  have hh : Homogeneous 4 ((pairContraction w * pairContraction v).adjoint (vacuum n)) := by
    rw [adjoint_mul, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous v
      (pairContraction_adjoint_homogeneous w (vacuum_homogeneous n))
  rw [pairWedgeColumn, ← fullContraction_eq_exteriorContraction hh]
  exact reconstruct_pair_product w v

theorem pairFourTerm_eq_lift {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    pairFourTerm v = exteriorLift (pairWedgeMatrix v * (pairWedgeMatrix v).conjTranspose) := by
  classical
  have hw := matrixLift_columns basisContraction (pairWedgeMatrix v) (1 : Matrix (ι × ι) (ι × ι) ℂ)
  simp only [Matrix.mul_one] at hw
  rw [exteriorLift, hw]
  have he (pr : ι × ι) :
      contractCombination basisContraction (fun A => pairWedgeMatrix v A pr) =
        pairContraction (v pr.2) * pairContraction (v pr.1) :=
    pairWedgeColumn_contraction (v pr.1) (v pr.2)
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, he,
    Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fintype.sum_prod_type]
  rfl

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairContraction_eq_pairAnnihilator {n : ℕ} (v : Fin n → Fin n → ℂ) :
    pairContraction (fun a => v a.val.1 a.val.2) = pairAnnihilator v := by
  classical
  simp only [pairContraction, basicPair]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
    (by simp) (fun a => star (v a.1 a.2) • (annihilation a.2 * annihilation a.1))]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, pairAnnihilator]

lemma sectorInclusion_readout {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    sectorInclusion n k (sectorReadout n k x) = x := by
  ext A
  by_cases hA : A.card = k
  · simp [sectorInclusion_apply, hA]
  · simp [sectorInclusion_apply, hA, hx A hA]

@[simp] theorem sectorExtract_exteriorLift {n k : ℕ}
    (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) :
    sectorExtract n k (exteriorLift M) = M := by
  apply Matrix.toEuclideanLin.injective
  rw [sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (sectorReadout n k (exteriorLift M (sectorInclusion n k y))) = _
  rw [← sectorInclusion_adjoint, LinearMap.adjoint_inner_right]
  exact exteriorLift_inner_sector M x y

lemma exteriorLift_sectorExtract {n k : ℕ} {T : Module.End ℂ (Hilbert n)}
    (hT : T ∈ bodySpace n k) : exteriorLift (sectorExtract n k T) = T := by
  obtain ⟨M,rfl⟩ := hT
  rw [sectorExtract_exteriorLift]

lemma sectorExtract_mul {n k : ℕ} (T S : Module.End ℂ (Hilbert n))
    (hS : ∀ x, Homogeneous k x → Homogeneous k (S x)) :
    sectorExtract n k (T * S) = sectorExtract n k T * sectorExtract n k S := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n k (T (S (sectorInclusion n k x))) =
    sectorReadout n k (T (sectorInclusion n k (sectorReadout n k (S (sectorInclusion n k x)))))
  rw [sectorInclusion_readout (hS _ (sectorInclusion_homogeneous x))]

lemma sectorExtract_eq_zero {n k : ℕ} (T : Module.End ℂ (Hilbert n))
    (hT : ∀ x, Homogeneous k x → T x = 0) : sectorExtract n k T = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [map_zero, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n k (T (sectorInclusion n k x)) = 0
  rw [hT _ (sectorInclusion_homogeneous x), map_zero]

lemma pairContraction_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous (k+2) x) : Homogeneous k (pairContraction v x) := by
  simp only [pairContraction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  exact annihilation_homogeneous (annihilation_homogeneous hx a.val.1) a.val.2

lemma pairHamiltonian_homogeneous {n k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous (k+2) x) :
    Homogeneous (k+2) (pairHamiltonian v x) := by
  simp only [pairHamiltonian, LinearMap.sum_apply, Module.End.mul_apply]
  exact homogeneous_sum _ _ (fun p _ => pairContraction_adjoint_homogeneous _
    (pairContraction_homogeneous _ hx))

lemma numberOperator_one {n : ℕ} {x : Hilbert n} (hx : Homogeneous 1 x) :
    (∑ i : Fin n, creation i (annihilation i x)) = x := by
  ext A
  rw [numberOperator_apply]
  by_cases hA : A.card = 1
  · simp [hA]
  · simp [hx A hA]

lemma pairTripleOperator_three {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous 3 x) :
    pairTripleOperator v x = pairHamiltonian v x := by
  simp only [pairTripleOperator, pairHamiltonian, LinearMap.sum_apply,
    adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [← map_sum, numberOperator_one (pairContraction_homogeneous (v p) hx)]

lemma reconstruct_triple_pair {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    reconstruct (annihilation i * pairContraction v) = annihilation i * pairContraction v := by
  simp only [pairContraction, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    triple_basic_eq_word, reconstruct_word]

lemma tripleWedgeColumn_contraction {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    exteriorContraction (tripleWedgeColumn v i) = annihilation i * pairContraction v := by
  have hh : Homogeneous 3 ((annihilation i * pairContraction v).adjoint (vacuum n)) := by
    rw [adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous v (creation_homogeneous (vacuum_homogeneous n) i)
  rw [tripleWedgeColumn, ← fullContraction_eq_exteriorContraction hh]
  exact reconstruct_triple_pair v i

lemma pairTripleOperator_eq_lift {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    pairTripleOperator v = exteriorLift (tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose) := by
  classical
  have hw := matrixLift_columns basisContraction (tripleWedgeMatrix v)
    (1 : Matrix (ι × Fin n) (ι × Fin n) ℂ)
  simp only [Matrix.mul_one] at hw
  rw [exteriorLift, hw]
  have he (pi : ι × Fin n) :
      contractCombination basisContraction (fun A => tripleWedgeMatrix v A pi) =
        annihilation pi.2 * pairContraction (v pi.1) := tripleWedgeColumn_contraction _ _
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, he,
    Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fintype.sum_prod_type]
  rfl

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairHamiltonian_sector_three {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    sectorExtract n 3 (pairHamiltonian v) = tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose := by
  rw [← sectorExtract_exteriorLift (tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose),
    ← pairTripleOperator_eq_lift]
  apply Matrix.toEuclideanLin.injective
  rw [sectorExtract_toEuclideanLin, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n 3 (pairHamiltonian v (sectorInclusion n 3 x)) =
    sectorReadout n 3 (pairTripleOperator v (sectorInclusion n 3 x))
  rw [pairTripleOperator_three v (sectorInclusion_homogeneous x)]

theorem pairThreeTerm_eq_lift {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairThreeTerm v = exteriorLift (tripleWedgeMatrix v *
      ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
      (tripleWedgeMatrix v).conjTranspose) := by
  have h4 : sectorExtract n 3 (pairFourTerm v) = 0 := by
    apply sectorExtract_eq_zero
    intro x hx
    rw [pairFourTerm_eq_lift]
    exact exteriorLift_eq_zero_of_degree_lt hx (by omega) _
  have he := congrArg (sectorExtract n 3) (pairHamiltonian_square v hv)
  rw [sectorExtract_mul _ _ (fun x hx => pairHamiltonian_homogeneous v hx),
    pairHamiltonian_sector_three v, map_add, map_add, pairHamiltonian_sector_three v,
    h4, add_zero] at he
  have h3 : sectorExtract n 3 (pairThreeTerm v) =
      tripleWedgeMatrix v * ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
        (tripleWedgeMatrix v).conjTranspose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc] at he ⊢
    exact eq_sub_of_add_eq' he.symm
  rw [← exteriorLift_sectorExtract (pairThreeTerm_mem_bodySpace v), h3]

theorem normal_ordered_square {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairHamiltonian v * pairHamiltonian v = pairHamiltonian v +
      exteriorLift (tripleWedgeMatrix v *
        ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
        (tripleWedgeMatrix v).conjTranspose) +
      exteriorLift (pairWedgeMatrix v * (pairWedgeMatrix v).conjTranspose) := by
  rw [pairHamiltonian_square v hv, pairThreeTerm_eq_lift v hv, pairFourTerm_eq_lift]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sum_increasing_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    2 * (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]
  ring

lemma sphericalExteriorPairCoefficient_eq_tensor (Q p : ℕ) (i j : Fin (Q+1)) :
    sphericalExteriorPairCoefficient Q p i.val j.val = Real.sqrt 2 * pairCoefficient Q p i j := by
  unfold sphericalExteriorPairCoefficient pairCoefficient
  split_ifs
  · have h : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  · simp

lemma physicalPair_contraction (Q : ℕ) (p : Fin (2*Q-1)) :
    pairContraction (physicalPairForms Q p) = localPair (Q+1) Q p.val := by
  exact pairContraction_eq_pairAnnihilator (fun x y : Fin (Q+1) =>
    (sphericalExteriorPairCoefficient Q p.val x.val y.val : ℂ))

theorem physicalPairForms_orthonormal {Q : ℕ} (hQ : 2 ≤ Q) :
    ∀ p r, (∑ a, star (physicalPairForms Q p a) * physicalPairForms Q r a) =
      if p = r then 1 else 0 := by
  intro p r
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hprod (a : PairLabel (Q+1)) :
      star (physicalPairForms Q p a) * physicalPairForms Q r a =
      ((2 * (pairCoefficient Q p.val a.val.1 a.val.2 *
        pairCoefficient Q r.val a.val.1 a.val.2) : ℝ) : ℂ) := by
    simp only [physicalPairForms, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    linear_combination (pairCoefficient Q p.val a.val.1 a.val.2 *
      pairCoefficient Q r.val a.val.1 a.val.2) * hs
  simp_rw [hprod]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  have hsum := sum_increasing_pairs
    (fun i j : Fin (Q+1) => pairCoefficient Q p.val i j * pairCoefficient Q r.val i j)
    (by intro i j; rw [pairCoefficient_swap Q p.val j i, pairCoefficient_swap Q r.val j i]; ring)
    (by intro i; simp [pairCoefficient])
  rw [hsum, ← pairVector_inner]
  exact (orthonormal_iff_ite.mp (pairVector_orthonormal Q hQ)) p r

theorem physical_normal_ordered_square {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalOccupationHamiltonian Q * physicalOccupationHamiltonian Q =
      physicalOccupationHamiltonian Q +
      exteriorLift (tripleWedgeMatrix (physicalPairForms Q) *
        ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
          tripleWedgeMatrix (physicalPairForms Q) - 1) *
        (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose) +
      exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
        (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) :=
  normal_ordered_square _ (physicalPairForms_orthonormal hQ)

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Creation
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma sum_symmetric_triangle {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
  classical
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  conv_lhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma orderedPair_contraction (Q p : ℕ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) •
      (annihilation j * annihilation i)) =
    (Real.sqrt 2 : ℂ) • localPair (Q+1) Q p := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  let T : Module.End ℂ (Hilbert (Q+1)) := ∑ i, ∑ j, if i < j then
    (pairCoefficient Q p i j : ℂ) • (annihilation j * annihilation i) else 0
  have he : localPair (Q+1) Q p = (Real.sqrt 2 : ℂ) • T := by
    simp only [localPair, pairAnnihilator, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, mul_smul, T,
      Finset.smul_sum, smul_ite, smul_zero]
  rw [sum_symmetric_triangle, he, smul_smul, hs]
  · change T + T = (2:ℂ) • T
    module
  · intro i j
    rw [pairCoefficient_swap Q p i j, annihilation_anticommute i j]
    simp
  · intro i
    simp [pairCoefficient]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complexify_injective : Function.Injective (complexify (ι := ι)) := by
  intro A B h
  apply_fun Matrix.toEuclideanLin.symm at h
  simp only [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearEquiv.symm_apply_apply] at h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma complexify_combination [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (a : ι → ℝ) :
    complexify (combination B a) = ∑ i, (a i : ℂ) • complexify (B i) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact_mod_cast (rfl : a i • complexify (B i) = a i • complexify (B i))

omit [DecidableEq ι] in
lemma complexify_lift [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (A : Matrix ι ι ℝ) :
    complexify (lift B A) = matrixLift (fun i => complexify (B i)) (A.map (algebraMap ℝ ℂ)) := by
  simp only [lift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    map_mul, complexify_transpose, Matrix.map_apply]
  rfl

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwiningSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.nestedBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

namespace LadderMap
variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable {S : LadderSystem ι} {T : LadderSystem κ} {U : LadderSystem σ}

lemma weight (A : LadderMap S T) (x : ι → ℝ) :
    T.weight (A.toLinearMap x) = A.toLinearMap (S.weight x) := by
  rw [T.weight_eq, A.raise, A.lower, S.weight_eq, map_sub, A.lower, A.raise]

lemma casimir (A : LadderMap S T) (x : ι → ℝ) :
    T.casimir (A.toLinearMap x) = A.toLinearMap (S.casimir x) := by
  simp only [LadderSystem.casimir_apply, A.weight, A.lower, A.raise, map_add, map_smul]

lemma raw (A : LadderMap S T) (x : ι → ℝ) (l : ℕ) :
    T.raw (A.toLinearMap x) l = A.toLinearMap (S.raw x l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [LadderSystem.raw_succ, LadderSystem.raw_succ, ih, A.lower]

lemma normalized (A : LadderMap S T) (x : ι → ℝ) (d l : ℕ) :
    T.normalized (A.toLinearMap x) d l = A.toLinearMap (S.normalized x d l) := by
  simp only [LadderSystem.normalized, map_smul, A.raw]

end LadderMap

theorem coupledTensor_expansion (n m : ℕ)
    (y : (Fin (n+1) × Fin (m+1)) → ℝ) :
    (∑ i : CoupledIndex n m,
      dotProduct (coupledTensor n m i.1.val i.2.val) y •
        coupledTensor n m i.1.val i.2.val) = y := by
  funext pq
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) => x pq)
    ((coupledBasis n m).sum_repr (WithLp.toLp 2 y))
  simpa only [OrthonormalBasis.repr_apply_apply, coupledBasis_apply, coupledFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

lemma spinCasimir_injective :
    Function.Injective (fun d : ℕ => (d : ℝ)*(d+2)) := by
  intro d e h
  have hd : (0 : ℝ) ≤ d := by positivity
  have he : (0 : ℝ) ≤ e := by positivity
  have hs : 0 < (d : ℝ)+e+2 := by positivity
  have hh : ((d : ℝ)-e)*((d : ℝ)+e+2) = 0 := by nlinarith
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hs.ne')
  exact_mod_cast heq

theorem coupledHighest_eigenline {n m z : ℕ} (hz : z ≤ min n m)
    {y : (Fin (n+1) × Fin (m+1)) → ℝ}
    (hyH : (tensorSpin n m).weight y = ((n+m-2*z : ℕ) : ℝ) • y)
    (hyC : (tensorSpin n m).casimir y =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • y) :
    y = dotProduct (highestTensor n m z) y • highestTensor n m z := by
  classical
  let iz : CoupledIndex n m := ⟨⟨z,by omega⟩,0⟩
  calc
    y = ∑ i : CoupledIndex n m,
        dotProduct (coupledTensor n m i.1.val i.2.val) y •
          coupledTensor n m i.1.val i.2.val := (coupledTensor_expansion n m y).symm
    _ = dotProduct (highestTensor n m z) y • highestTensor n m z := by
      apply Finset.sum_eq_single iz
      · intro i _ hne
        obtain ⟨w,k⟩ := i
        have hw : w.val ≤ min n m := Nat.le_of_lt_succ w.isLt
        have hk : k.val ≤ n+m-2*w.val := Nat.le_of_lt_succ k.isLt
        have horth : dotProduct (coupledTensor n m w.val k.val) y = 0 := by
          by_cases hwz : w.val=z
          · have hk0 : k.val ≠ 0 := by
              intro hk0
              apply hne
              apply Sigma.ext
              · exact Fin.ext hwz
              · apply (Fin.heq_ext_iff (by dsimp [iz]; omega)).mpr
                exact hk0
            apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
              (coupledTensor_weight hw hk) hyH
            simp only [hwz]
            intro hh
            apply hk0
            have : (k.val : ℝ) = 0 := by linarith
            exact_mod_cast this
          · apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
              (coupledTensor_casimir hw hk) hyC
            intro hh
            have HD := spinCasimir_injective hh
            have := le_min_iff.mp hw
            have := le_min_iff.mp hz
            omega
        rw [horth, zero_smul]
      · simp

lemma LadderSystem.raw_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (l : ℕ) : S.raw (c • x) l = c • S.raw x l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [S.raw_succ, ih, map_smul, S.raw_succ]

lemma LadderSystem.normalized_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (d l : ℕ) :
    S.normalized (c • x) d l = c • S.normalized x d l := by
  simp only [LadderSystem.normalized, S.raw_smul, smul_comm c]

theorem tensorSpin_schur {n m z l : ℕ} (hz : z ≤ min n m) (hl : l ≤ n+m-2*z)
    (A : LadderMap (tensorSpin n m) (tensorSpin n m)) :
    A.toLinearMap (coupledTensor n m z l) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        coupledTensor n m z l := by
  have hh : A.toLinearMap (highestTensor n m z) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        highestTensor n m z := by
    apply coupledHighest_eigenline hz
    · rw [A.weight, highestTensor_weight hz, map_smul]
    · rw [A.casimir]
      have hc := coupledTensor_casimir hz (by omega : 0 ≤ n+m-2*z)
      rw [coupledTensor_zero] at hc
      rw [hc, map_smul]
  rw [coupledTensor_eq_normalized hz hl, ← A.normalized]
  conv_lhs => rw [hh, LadderSystem.normalized_smul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinAveraging
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

lemma toMatrix_transposeMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    LinearMap.toMatrix' (transposeMap A) = (LinearMap.toMatrix' A).transpose := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, transposeMap, Matrix.transpose_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  change dotProduct (A _) (Pi.single j 1) = _
  rw [dotProduct_single_one]
  apply congrArg (fun x : ι → ℝ => A x j)
  funext k
  by_cases hk : i=k <;> simp [hk, eq_comm]

lemma coupledEmbedding_entry {n m z : ℕ} (hz : z ≤ min n m)
    (a : Fin (n+1) × Fin (m+1)) (l : Fin (n+m-2*z+1)) :
    LinearMap.toMatrix' (coupledEmbedding hz).toLinearMap a l = coupledTensor n m z l.val a := by
  rw [LinearMap.toMatrix'_apply, coupledEmbedding_apply]
  simp [Pi.single_apply, ite_apply]

lemma tensorProjection_eq {n m z : ℕ} (hz : z ≤ min n m) :
    tensorProjection hz = ∑ l : Fin (n+m-2*z+1),
      Matrix.vecMulVec (coupledTensor n m z l.val) (coupledTensor n m z l.val) := by
  simp only [tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coupledEmbedding_entry,
    Matrix.sum_apply, Matrix.vecMulVec_apply]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

theorem pairCoefficient_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1)
    (i j : Fin (Q+1)) :
    pairCoefficient Q p i j = if i.val+j.val=p+1 then
      ((i.val : ℝ)-j.val)*Real.sqrt (Q.choose i.val : ℝ)*Real.sqrt (Q.choose j.val : ℝ) /
        Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)) else 0 := by
  have hch : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2*Q-2 by omega)).ne'
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial i.val : ℝ)*(Q.descFactorial j.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*
          (i.val.factorial : ℝ)*(j.val.factorial : ℝ))) =
      ((Q.choose i.val : ℝ)*Q.choose j.val) / ((Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs
  · rw [hrad, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity :
        0 ≤ (Q.choose i.val : ℝ)),
      show (2 : ℝ)*Q*((2*Q-2).choose p : ℝ) =
        2*(Q*((2*Q-2).choose p : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rfl

lemma sqrt_choose_lowering {Q k : ℕ} (hk : k < Q) :
    Real.sqrt (((k : ℝ)+1)*((Q : ℝ)-k))*Real.sqrt (Q.choose k : ℝ) =
      ((k : ℝ)+1)*Real.sqrt (Q.choose (k+1) : ℝ) := by
  have hq : (k : ℝ) ≤ Q := by exact_mod_cast hk.le
  have hc : (Q.choose (k+1) : ℝ)*((k : ℝ)+1) =
      (Q.choose k : ℝ)*((Q : ℝ)-k) := by
    have H := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq Q k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using H
  rw [← Real.sqrt_mul (by positivity : 0 ≤ ((k : ℝ)+1)*((Q : ℝ)-k))]
  rw [show (((k : ℝ)+1)*((Q : ℝ)-k))*(Q.choose k : ℝ) =
      (((k : ℝ)+1)^2)*(Q.choose (k+1) : ℝ) by nlinarith [hc]]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

lemma binomialPairTensor_swap (Q p : ℕ) (i j : Fin (Q+1)) :
    binomialPairTensor Q p (j,i) = -binomialPairTensor Q p (i,j) := by
  unfold binomialPairTensor
  by_cases h : i.val+j.val=p+1
  · simp only [h, Nat.add_comm j.val i.val, ite_true]
    ring
  · simp [h, Nat.add_comm j.val i.val]

lemma binomialPairTensor_lower_first (Q p : ℕ) (i j : Fin (Q+1)) :
    lowering Q (fun a => binomialPairTensor Q p (a,j)) i =
      if i.val+j.val=p+2 then
        (i.val : ℝ)*((i.val : ℝ)-1-j.val)*Real.sqrt (Q.choose i.val : ℝ)*
          Real.sqrt (Q.choose j.val : ℝ) else 0 := by
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    rw [lowering_succ]
    simp only [binomialPairTensor, Fin.val_castSucc, Fin.val_succ]
    by_cases h : i.val+j.val=p+1
    · rw [ite_eq_left h, ite_eq_left (by omega : i.val+1+j.val=p+2)]
      simp only [Nat.cast_add, Nat.cast_one, ladderStep]
      have hc := sqrt_choose_lowering i.isLt
      calc
        _ = (((i.val : ℝ)-j.val)*Real.sqrt (Q.choose j.val : ℝ)) *
            (Real.sqrt (((i.val : ℝ)+1)*((Q : ℝ)-i.val))*Real.sqrt (Q.choose i.val : ℝ)) := by ring
        _ = _ := by rw [hc]; ring
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬i.val+1+j.val=p+2), mul_zero]

theorem binomialPairTensor_lower (Q p : ℕ) :
    (tensorSpin Q Q).lower (binomialPairTensor Q p) =
      ((p : ℝ)+1) • binomialPairTensor Q (p+1) := by
  funext ⟨i,j⟩
  rw [tensorSpin_lower, binomialPairTensor_lower_first]
  have hswap : (fun a => binomialPairTensor Q p (i,a)) =
      -(fun a => binomialPairTensor Q p (a,i)) := by
    funext a
    exact binomialPairTensor_swap Q p a i
  rw [hswap, map_neg]
  simp only [Pi.neg_apply]
  rw [binomialPairTensor_lower_first]
  simp only [binomialPairTensor, Pi.smul_apply, smul_eq_mul]
  by_cases h : i.val+j.val=p+2
  · simp only [ite_eq_left h, ite_eq_left (by omega : j.val+i.val=p+2)]
    have hc : (i.val : ℝ)+j.val=(p : ℝ)+2 := by exact_mod_cast h
    rw [show (p : ℝ)+1=(i.val : ℝ)+j.val-1 by linarith]
    ring
  · simp only [ite_eq_right h, ite_eq_right (by omega : ¬j.val+i.val=p+2), neg_zero, zero_add, mul_zero]

lemma physicalPairTensor_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1) :
    physicalPairTensor Q p =
      (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ))) • binomialPairTensor Q p := by
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ hp, binomialPairTensor,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma pairNormalization_step {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)))*((p : ℝ)+1) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p))*
        (1/Real.sqrt (2*Q*((2*Q-2).choose (p+1) : ℝ))) := by
  have hc := sqrt_choose_lowering hp
  have hs0 : Real.sqrt (((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp.le
  have hs1 : Real.sqrt (((2*Q-2).choose (p+1) : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp
  simp only [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*Q)]
  field_simp
  nlinarith [congrArg (fun a => a*Real.sqrt (2*(Q : ℝ))) hc]

theorem physicalPairTensor_lower {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (tensorSpin Q Q).lower (physicalPairTensor Q p) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) • physicalPairTensor Q (p+1) := by
  rw [physicalPairTensor_binomial hQ (by omega), map_smul, binomialPairTensor_lower,
    physicalPairTensor_binomial hQ (by omega), smul_smul, smul_smul,
    pairNormalization_step hQ hp]

lemma highestWeight_first_one {Q : ℕ} (hQ : 0 < Q) :
    highestWeight Q Q 1 1 = 1 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  simp only [highestWeight, Nat.choose_self, Nat.cast_one, Finset.prod_range_one,
    one_mul, highestFactor, Nat.cast_zero, sub_zero]
  rw [show (Q : ℝ)-1+0+1 = Q by ring, div_self hQr]

lemma highestNormalization_first {Q : ℕ} (hQ : 0 < Q) :
    highestNormalization Q Q 1 = 2 := by
  norm_num [highestNormalization, Finset.sum_range_succ, highestWeight_first_one hQ]

lemma sqrt_Q_over_sqrt_twoQ {Q : ℕ} (hQ : 0 < Q) :
    Real.sqrt (Q : ℝ)/Real.sqrt (2*Q : ℝ) = 1/Real.sqrt 2 := by
  have hQr : Real.sqrt (Q : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

theorem physicalPairTensor_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalPairTensor Q 0 = highestTensor Q Q 1 := by
  have hQ0 : 0 < Q := by omega
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ (by omega : 0 < 2*Q-1),
    highestTensor]
  by_cases h : i.val+j.val=1
  · rw [ite_eq_left h, ite_eq_left h]
    rcases (show i.val=0 ∧ j.val=1 ∨ i.val=1 ∧ j.val=0 by omega) with hij | hij
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, zero_sub,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, highestCoefficient,
        highestWeight_zero, highestNormalization_first hQ0]
      simp only [Nat.sub_zero, pow_one, Real.sqrt_one, one_mul, neg_mul, neg_div]
      exact congrArg Neg.neg (sqrt_Q_over_sqrt_twoQ hQ0)
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, sub_zero,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, one_mul, highestCoefficient,
        highestWeight_first_one hQ0, highestNormalization_first hQ0,
        Nat.sub_self, pow_zero, Real.sqrt_one]
      exact sqrt_Q_over_sqrt_twoQ hQ0
  · simp only [ite_eq_right h]

theorem physicalPairTensor_eq_coupled {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    physicalPairTensor Q p = coupledTensor Q Q 1 p := by
  have hz : 1 ≤ min Q Q := by omega
  have hd : Q+Q-2*1=2*Q-2 := by omega
  rw [coupledTensor_eq_normalized hz (by omega), hd]
  induction p with
  | zero => rw [LadderSystem.normalized_zero, physicalPairTensor_zero hQ]
  | succ p ih =>
    have hl : p < 2*Q-2 := by omega
    have ha : Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'
      have hpr : (p : ℝ) < (2*Q-2 : ℕ) := by exact_mod_cast hl
      exact mul_pos (by positivity) (by linarith)
    rw [LadderSystem.normalized_succ _ _ hl, ← ih (by omega), physicalPairTensor_lower hQ hl,
      smul_smul, one_div_mul_cancel ha, one_smul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairInclusion_apply {Q : ℕ} (hQ : 2 ≤ Q) (a : Fin (2*Q-2+1) → ℝ) :
    (pairInclusion hQ).toLinearMap a =
      ∑ p : Fin (2*Q-2+1), a p • physicalPairTensor Q p.val := by
  simp only [pairInclusion, LadderSystem.embeddingMap, LadderSystem.embedding_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ p.isLt),
    coupledTensor_eq_normalized (by omega : 1 ≤ min Q Q) (by omega : p.val ≤ Q+Q-2*1)]
  congr 2
  omega

lemma pairSpectatorInclusion_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (i j k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).toLinearMap a ((i,j),k) =
      ∑ p : Fin (2*Q-2+1), pairCoefficient Q p.val i j * a (p,k) := by
  change (pairInclusion hQ).toLinearMap (fun p => a (p,k)) (i,j) = _
  rw [pairInclusion_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, physicalPairTensor, mul_comm]

theorem compressedSwap_eigenvector {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    (compressedSwap hQ).toLinearMap (coupledTensor (2*Q-2) Q z l) =
      swapScalar Q z hQ • coupledTensor (2*Q-2) Q z l := by
  exact tensorSpin_schur (by omega : z ≤ min (2*Q-2) Q) hl (compressedSwap hQ)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

@[simp] lemma complexify_physicalPair (Q p : ℕ) :
    complexify (physicalPair Q p) = Occupation.localPair (Q+1) Q p := by
  rw [physicalPair, map_smul, complexify_combination]
  simp only [productFamily, map_mul, complexify_annihilation, Fintype.sum_prod_type,
    physicalPairTensor, Occupation.orderedPair_contraction]
  have he : (1/Real.sqrt 2 : ℝ) • ((Real.sqrt 2 : ℂ) • Occupation.localPair (Q+1) Q p) =
      ((1/Real.sqrt 2)*Real.sqrt 2 : ℝ) • Occupation.localPair (Q+1) Q p := by
    rw [mul_smul]; rfl
  rw [he, one_div_mul_cancel (by positivity : Real.sqrt 2 ≠ 0), one_smul]

@[simp] lemma complexify_physicalHamiltonian (Q : ℕ) :
    complexify (physicalHamiltonian Q) = Occupation.physicalOccupationHamiltonian Q := by
  simp only [physicalHamiltonian, map_sum, map_mul, complexify_transpose,
    complexify_physicalPair, Occupation.physicalOccupationHamiltonian, Occupation.pairHamiltonian,
    Occupation.physicalPair_contraction]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_HighestRatios
attribute [-simp] _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest Ratios. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma highest_numerator_product {m z : ℕ} (hz : z ≤ m) (p : ℕ) :
    (∏ k ∈ Finset.range p, ((m : ℝ)-z+k+1)) =
      ((m-z+p).descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih]
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
    push_cast
    rw [Nat.cast_sub hz]
    ring

lemma highest_denominator_product {n p : ℕ} (hp : p ≤ n) :
    (∏ k ∈ Finset.range p, ((n : ℝ)-k)) = (n.descFactorial p : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.cast_sub ((Finset.mem_range.mp hk).le.trans hp)]

theorem highestWeight_factorial {n m z p : ℕ} (hz : z ≤ min n m) (hp : p ≤ z) :
    highestWeight n m z p = (z.choose p : ℝ) *
      ((m-z+p).descFactorial p : ℝ) / (n.descFactorial p : ℝ) := by
  simp only [highestWeight, highestFactor, Finset.prod_div_distrib,
    highest_numerator_product (le_min_iff.mp hz).2 p,
    highest_denominator_product (hp.trans (le_min_iff.mp hz).1), mul_div_assoc]

lemma highestCoefficient_zero_ne {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z 0 ≠ 0 := by
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Real.sqrt_pos.mpr (highestNormalization_pos hz)).ne'

theorem highestCoefficient_ratio {n m z p : ℕ} (_hz : z ≤ min n m) (hp : p ≤ z) :
    highestCoefficient n m z p = highestCoefficient n m z 0 *
      ((-1 : ℝ)^p * Real.sqrt (highestWeight n m z p)) := by
  have he : (-1 : ℝ)^(z-p) = (-1 : ℝ)^z * (-1 : ℝ)^p := by
    have hzz : z=(z-p)+p := by omega
    conv_rhs => rw [hzz, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  rw [he]
  ring

lemma highestCoefficient_last {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z z = highestCoefficient n m z 0 *
      ((-1 : ℝ)^z * Real.sqrt ((m.descFactorial z : ℝ)/(n.descFactorial z : ℝ))) := by
  rw [highestCoefficient_ratio hz (le_refl z), highestWeight_factorial hz (le_refl z),
    Nat.sub_add_cancel (le_min_iff.mp hz).2, Nat.choose_self, Nat.cast_one, one_mul]

lemma highestCoefficient_penultimate {n m z : ℕ} (hz : z ≤ min n m) (hpos : 0<z) :
    highestCoefficient n m z (z-1) = highestCoefficient n m z 0 *
      ((-1 : ℝ)^(z-1) * Real.sqrt ((z : ℝ)*((m-1).descFactorial (z-1) : ℝ) /
        (n.descFactorial (z-1) : ℝ))) := by
  rw [highestCoefficient_ratio hz (by omega), highestWeight_factorial hz (by omega)]
  rw [show m-z+(z-1) = m-1 by omega,
    show z.choose (z-1) = z by simpa using Nat.choose_symm (by omega : 1 ≤ z)]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwinerAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwiner Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[simp] lemma LadderMap.transpose_matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : A.transpose.matrix = A.matrix.transpose := toMatrix_transposeMap _

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma sum_fin_extend {M : Type*} [AddCommMonoid M] {T K : ℕ} (h : T ≤ K) (f : ℕ → M) :
    (∑ z : Fin (T+1), f z.val) = ∑ z : Fin (K+1), if z.val ≤ T then f z.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range f,
    Fin.sum_univ_eq_sum_range (fun z => if z ≤ T then f z else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_range,Finset.mem_filter]
  omega

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Endpoints. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairCoefficient_one {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairCoefficient Q z ⟨1,by omega⟩ ⟨z,by omega⟩ =
      (1-(z : ℝ))*Real.sqrt (fallingRatio Q z)/Real.sqrt 2 := by
  have hn : 0 < ((2*Q-2).descFactorial z : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : z ≤ 2*Q-2)
  have hf : (0 : ℝ) < z.factorial := by exact_mod_cast z.factorial_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  unfold pairCoefficient
  rw [ite_eq_left (by simp [Nat.add_comm] : 1+z=z+1)]
  simp only [Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, mul_one]
  congr 2
  congr 1
  unfold fallingRatio
  field_simp

lemma pairCoefficient_zero_succ {Q a : ℕ} (hQ : 2 ≤ Q) (hz : a+1 ≤ Q) :
    pairCoefficient Q a 0 ⟨a+1,by omega⟩ =
      -Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ)/
        ((2*Q-2).descFactorial a : ℝ))/Real.sqrt 2 := by
  have hn : 0 < ((2*Q-2).descFactorial a : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : a ≤ 2*Q-2)
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have ha : (0 : ℝ) < (a : ℝ)+1 := by positivity
  have hdesc : Q.descFactorial (a+1) = Q*(Q-1).descFactorial a := by
    have h := Nat.succ_descFactorial_succ (Q-1) a
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Q)] using h
  simp only [pairCoefficient, Fin.val_zero, Nat.zero_add, ite_true,
    Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_sub, Nat.descFactorial_zero,
    Nat.factorial_zero, hdesc, Nat.factorial_succ, Nat.cast_mul, one_mul, mul_one]
  congr 1
  rw [neg_mul, neg_inj]
  rw [show Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ)/
      ((2*Q-2).descFactorial a : ℝ)) =
      ((a : ℝ)+1)*Real.sqrt (((Q : ℝ)*((Q-1).descFactorial a : ℝ)*(a.factorial : ℝ))/
        ((Q : ℝ)*((2*Q-2).descFactorial a : ℝ)*(((a : ℝ)+1)*(a.factorial : ℝ)))) by
    rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [Real.sqrt_sq ha.le]
    field_simp]

lemma pairCoefficient_zero_formula {Q : ℕ} (hQ : 2 ≤ Q) (i j : Fin (Q+1)) :
    pairCoefficient Q 0 i j =
      if i=⟨1,by omega⟩ ∧ j=0 then 1/Real.sqrt 2
      else if i=0 ∧ j=⟨1,by omega⟩ then -1/Real.sqrt 2 else 0 := by
  have h0 : fallingRatio Q 0 = 1 := by simp [fallingRatio]
  by_cases hi1 : i=⟨1,by omega⟩ ∧ j=0
  · rcases hi1 with ⟨rfl,rfl⟩
    rw [ite_eq_left ⟨rfl,rfl⟩]
    simpa only [Fin.mk_zero, h0, Nat.cast_zero, sub_zero, Real.sqrt_one, mul_one] using
      pairCoefficient_one hQ (Nat.zero_le Q)
  · rw [ite_eq_right hi1]
    by_cases hi0 : i=0 ∧ j=⟨1,by omega⟩
    · rcases hi0 with ⟨rfl,rfl⟩
      rw [ite_eq_left ⟨rfl,rfl⟩]
      simpa only [Nat.cast_zero, zero_add, Nat.descFactorial_zero, Nat.cast_one,
        mul_one, div_one, Real.sqrt_one] using
        pairCoefficient_zero_succ hQ (by omega : 0+1 ≤ Q)
    · rw [ite_eq_right hi0, pairCoefficient, ite_eq_right]
      intro h
      rcases (show i.val=1 ∧ j.val=0 ∨ i.val=0 ∧ j.val=1 by omega) with hh | hh
      · exact hi1 ⟨Fin.ext hh.1,Fin.ext hh.2⟩
      · exact hi0 ⟨Fin.ext hh.1,Fin.ext hh.2⟩

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpectrum
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.LadderMap.transpose_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairSpectatorInclusion_transpose_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (x : ((Fin (Q+1) × Fin (Q+1)) × Fin (Q+1)) → ℝ)
    (p : Fin (2*Q-2+1)) (k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).transpose.toLinearMap x (p,k) =
      ∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q p.val i j * x ((i,j),k) := by
  classical
  change transposeMap (pairSpectatorInclusion hQ).toLinearMap x (p,k) = _
  simp only [transposeMap, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type]
  simp_rw [pairSpectatorInclusion_apply]
  simp only [Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  simp

lemma compressedSwap_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ)
    (p : Fin (2*Q-2+1)) (k : Fin (Q+1)) :
    (compressedSwap hQ).toLinearMap a (p,k) =
      ∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q p.val i j *
        (∑ b : Fin (2*Q-2+1), pairCoefficient Q b.val i k * a (b,j)) := by
  change (pairSpectatorInclusion hQ).transpose.toLinearMap
    ((swap23 Q).toLinearMap ((pairSpectatorInclusion hQ).toLinearMap a)) (p,k) = _
  rw [pairSpectatorInclusion_transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact pairSpectatorInclusion_apply hQ a i k j

lemma pairCoefficient_zero_contract {Q : ℕ} (hQ : 2 ≤ Q)
    (f : Fin (Q+1) → Fin (Q+1) → ℝ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q 0 i j * f i j) =
      (f ⟨1,by omega⟩ 0 - f 0 ⟨1,by omega⟩)/Real.sqrt 2 := by
  have hneq : (⟨1,by omega⟩ : Fin (Q+1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hc (i j : Fin (Q+1)) : pairCoefficient Q 0 i j =
      (if i=⟨1,by omega⟩ ∧ j=0 then 1/Real.sqrt 2 else 0) +
        (if i=0 ∧ j=⟨1,by omega⟩ then -1/Real.sqrt 2 else 0) := by
    rw [pairCoefficient_zero_formula hQ]
    by_cases h1 : i=⟨1,by omega⟩ ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h1
      simp [hneq]
    · simp [h1]
  simp_rw [hc, add_mul, Finset.sum_add_distrib, ite_and, ite_mul, zero_mul,
    Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma pairSpectatorInclusion_highest {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (i j k : Fin (Q+1)) (hk : k.val ≤ z) :
    (pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z) ((i,j),k) =
      pairCoefficient Q (z-k.val) i j * highestCoefficient (2*Q-2) Q z (z-k.val) := by
  classical
  let p : Fin (2*Q-2+1) := ⟨z-k.val,by omega⟩
  rw [pairSpectatorInclusion_apply]
  calc
    _ = pairCoefficient Q p.val i j * highestTensor (2*Q-2) Q z (p,k) := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        have hne : q.val+k.val ≠ z := by
          intro hs
          apply hqp
          apply Fin.ext
          dsimp [p]
          omega
        simp [highestTensor, hne]
      · simp
    _ = _ := by simp [p, highestTensor, Nat.sub_add_cancel hk]

theorem swapScalar_coordinate {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestCoefficient (2*Q-2) Q z 0 * swapScalar Q z hQ =
      (((pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z)
        ((⟨1,by omega⟩,⟨z,by omega⟩),0)) -
       ((pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z)
        ((0,⟨z,by omega⟩),⟨1,by omega⟩)))/Real.sqrt 2 := by
  have h := congrFun (compressedSwap_eigenvector hQ hz (by omega : 0 ≤ (2*Q-2)+Q-2*z))
    ((0 : Fin (2*Q-2+1)), (⟨z,by omega⟩ : Fin (Q+1)))
  rw [coupledTensor_zero, compressedSwap_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul, highestTensor, Fin.val_zero,
    Nat.zero_add, ite_true] at h
  rw [mul_comm]
  rw [← h, pairCoefficient_zero_contract hQ]
  simp only [pairSpectatorInclusion_apply, highestTensor]

lemma fallingRatio_penultimate {Q a : ℕ} (hQ : 2 ≤ Q) (ha : a+1 ≤ Q) :
    (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) / ((2*Q-2).descFactorial a : ℝ)) =
      fallingRatio Q (a+1) * ((a : ℝ)+1) * (2*(Q : ℝ)-2-a)/(Q : ℝ) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hd : 0 < ((2*Q-2).descFactorial a : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : a ≤ 2*Q-2)
  have hf : 0 < 2*(Q : ℝ)-2-a := by
    have hqa : (a : ℝ)+1 ≤ Q := by exact_mod_cast ha
    have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  unfold fallingRatio
  rw [show Q.descFactorial (a+1) = Q * (Q-1).descFactorial a by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Q)] using
      Nat.succ_descFactorial_succ (Q-1) a]
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (by omega : a ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  rw [mul_div_cancel_right₀ _ (by linarith : 2*((Q : ℝ)-1)-a ≠ 0)]

lemma swapScalar_succ {Q a : ℕ} (hQ : 2 ≤ Q) (ha : a+1 ≤ Q) :
    swapScalar Q (a+1) hQ = -(threeBodyGramCoefficient Q (a+1))/2 := by
  have hz : a+1 ≤ min (2*Q-2) Q := by omega
  have hs0 := highestCoefficient_zero_ne hz
  have hf : 0 ≤ fallingRatio Q (a+1) := by unfold fallingRatio; positivity
  have hg : 0 ≤ ((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
      ((2*Q-2).descFactorial a : ℝ) := by positivity
  have ht : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs := swapScalar_coordinate hQ ha
  rw [pairSpectatorInclusion_highest hQ ha _ _ _ (by simp),
    pairSpectatorInclusion_highest hQ ha _ _ _ (by simp)] at hs
  simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel] at hs
  rw [pairCoefficient_one hQ ha, pairCoefficient_zero_succ hQ ha,
    highestCoefficient_last hz] at hs
  have hp := highestCoefficient_penultimate hz (by omega : 0 < a+1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hp
  rw [hp, ← fallingRatio] at hs
  simp only [Nat.cast_add, Nat.cast_one] at hs
  have hsqf := Real.sq_sqrt hf
  have hsqg := Real.sq_sqrt hg
  have hsq2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have he : highestCoefficient (2*Q-2) Q (a+1) 0 * swapScalar Q (a+1) hQ =
      highestCoefficient (2*Q-2) Q (a+1) 0 *
        (((-1 : ℝ)^(a+1)* (1-((a : ℝ)+1))*fallingRatio Q (a+1) +
          (-1 : ℝ)^a * (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
            ((2*Q-2).descFactorial a : ℝ)))/2) := by
    rw [hs]
    calc
      _ = highestCoefficient (2*Q-2) Q (a+1) 0 *
          (((-1 : ℝ)^(a+1)* (1-((a : ℝ)+1))*(Real.sqrt (fallingRatio Q (a+1)))^2 +
            (-1 : ℝ)^a * (Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
              ((2*Q-2).descFactorial a : ℝ)))^2)/(Real.sqrt 2)^2) := by ring
      _ = _ := by rw [hsqf, hsqg, hsq2]
  apply (mul_left_cancel₀ hs0) at he
  rw [he, fallingRatio_penultimate hQ ha, threeBodyGramCoefficient]
  push_cast
  rw [pow_succ]
  have hq : (Q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pairSpectatorInclusion_highest_eq_zero {Q z : ℕ} (hQ : 2 ≤ Q)
    (i j k : Fin (Q+1)) (hk : z < k.val) :
    (pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z) ((i,j),k) = 0 := by
  rw [pairSpectatorInclusion_apply]
  apply Finset.sum_eq_zero
  intro p hp
  simp [highestTensor, show p.val+k.val ≠ z by omega]

lemma swapScalar_zero {Q : ℕ} (hQ : 2 ≤ Q) : swapScalar Q 0 hQ = 1/2 := by
  have h := swapScalar_coordinate hQ (Nat.zero_le Q)
  rw [pairSpectatorInclusion_highest hQ (Nat.zero_le Q) _ _ _ (by simp),
    pairSpectatorInclusion_highest_eq_zero hQ _ _ _ (by simp)] at h
  simp only [Fin.val_zero, Nat.sub_zero, highestCoefficient_zero_zero, mul_one, one_mul,
    Fin.mk_zero, sub_zero] at h
  have hc := pairCoefficient_one hQ (Nat.zero_le Q)
  simp only [Fin.mk_zero] at hc
  rw [hc] at h
  simp only [fallingRatio, Nat.descFactorial_zero, Nat.cast_one, Nat.cast_zero,
    div_one, Real.sqrt_one, sub_zero, mul_one] at h
  rw [h, div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem swapScalar_eq {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    swapScalar Q z hQ = -(threeBodyGramCoefficient Q z)/2 := by
  cases z with
  | zero =>
    rw [swapScalar_zero hQ]
    norm_num [threeBodyGramCoefficient, fallingRatio]
  | succ a => exact swapScalar_succ hQ hz

theorem compressedSwap_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    (compressedSwap hQ).toLinearMap (coupledTensor (2*Q-2) Q z l) =
      (-(threeBodyGramCoefficient Q z)/2) • coupledTensor (2*Q-2) Q z l := by
  rw [compressedSwap_eigenvector hQ hz hl, swapScalar_eq hQ hz]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeGram
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.LadderMap.transpose_matrix _root_.OAI.LaughlinGap.Spin.nestedBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Gram. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma cycleMap_dot {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cycleMap ι x) (cycleMap ι y) = dotProduct x y := by
  exact (cycleIndex ι).sum_comp (fun t => x t * y t)

lemma cycleMap_adjoint {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cycleMap ι x) y = dotProduct x (cycleMap ι (cycleMap ι y)) := by
  simpa only [cycleMap_cube] using cycleMap_dot x (cycleMap ι (cycleMap ι y))

lemma cyclicSum_dot {ι : Type*} [Fintype ι] (x y : ThreeIndex ι → ℝ) :
    dotProduct (cyclicSum ι x) (cyclicSum ι y) =
      3 * (dotProduct x y + dotProduct x (cycleMap ι y) +
        dotProduct x (cycleMap ι (cycleMap ι y))) := by
  simp only [cyclicSum_apply, add_dotProduct, dotProduct_add,
    cycleMap_adjoint, cycleMap_cube]
  ring

lemma pairSpectatorInclusion_antisymmetric {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (i j k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).toLinearMap a ((j,i),k) =
      -(pairSpectatorInclusion hQ).toLinearMap a ((i,j),k) := by
  simp only [pairSpectatorInclusion_apply, pairCoefficient_swap Q _ j i,
    neg_mul, Finset.sum_neg_distrib, neg_neg]

lemma pairSpectatorInclusion_isometry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      ((pairSpectatorInclusion hQ).toLinearMap b) = dotProduct a b := by
  have hab (p r : Fin (2*Q-2+1)) :
      (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        pairCoefficient Q p.val i j * pairCoefficient Q r.val i j) =
        if p=r then 1 else 0 := by
    split_ifs with hh
    · subst r
      simpa only [← sq] using pairCoefficient_sum_sq Q p.val hQ (by omega)
    · exact pairCoefficient_sum_mul_of_ne Q p.val r.val (fun he => hh (Fin.ext he))
  classical
  have hfixed (aa bb : Fin (2*Q-2+1) → ℝ) :
      (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        (∑ p, pairCoefficient Q p.val i j * aa p) *
          (∑ r, pairCoefficient Q r.val i j * bb r)) = ∑ p, aa p * bb p := by
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    let f := fun (i j : Fin (Q+1)) (p r : Fin (2*Q-2+1)) =>
      pairCoefficient Q p.val i j * aa p * (pairCoefficient Q r.val i j * bb r)
    change (∑ i, ∑ j, ∑ p, ∑ r, f i j p r) = _
    calc
      _ = ∑ i, ∑ p, ∑ j, ∑ r, f i j p r := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ p, ∑ i, ∑ j, ∑ r, f i j p r := Finset.sum_comm
      _ = ∑ p, ∑ i, ∑ r, ∑ j, f i j p r := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ p, ∑ r, ∑ i, ∑ j, f i j p r := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_comm
      _ = ∑ p, ∑ r, (∑ i, ∑ j,
          pairCoefficient Q p.val i j * pairCoefficient Q r.val i j) * (aa p * bb r) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [f]
        ring
      _ = _ := by simp [hab]
  simp only [dotProduct, Fintype.sum_prod_type, pairSpectatorInclusion_apply]
  let f := fun (i j k : Fin (Q+1)) =>
    (∑ p : Fin (2*Q-2+1), pairCoefficient Q p.val i j * a (p,k)) *
      (∑ r : Fin (2*Q-2+1), pairCoefficient Q r.val i j * b (r,k))
  change (∑ i, ∑ j, ∑ k, f i j k) = _
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ p, a (p,k)*b (p,k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hfixed (fun p => a (p,k)) (fun p => b (p,k))
    _ = _ := Finset.sum_comm

lemma swap23Linear_adjoint (Q : ℕ)
    (x y : ThreeIndex (Fin (Q+1)) → ℝ) :
    dotProduct (swap23Linear Q x) y = dotProduct x (swap23Linear Q y) := by
  let e : ThreeIndex (Fin (Q+1)) ≃ ThreeIndex (Fin (Q+1)) := {
    toFun := fun t => ((t.1.1,t.2),t.1.2)
    invFun := fun t => ((t.1.1,t.2),t.1.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact e.sum_comp (fun t => x t * swap23Linear Q y t)

lemma cycleSquare_pairSpectatorInclusion {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    cycleMap (Fin (Q+1)) (cycleMap (Fin (Q+1))
      ((pairSpectatorInclusion hQ).toLinearMap a)) =
      -(swap23Linear Q ((pairSpectatorInclusion hQ).toLinearMap a)) := by
  funext ⟨⟨i,j⟩,k⟩
  exact pairSpectatorInclusion_antisymmetric hQ a i k j

lemma cyclicSum_pair_dot {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct (cyclicSum (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap a))
      (cyclicSum (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap b)) =
      3 * (dotProduct a b - 2 * dotProduct a ((compressedSwap hQ).toLinearMap b)) := by
  have hab : dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      (swap23Linear Q ((pairSpectatorInclusion hQ).toLinearMap b)) =
      dotProduct a ((compressedSwap hQ).toLinearMap b) :=
    transposeMap_adjoint (pairSpectatorInclusion hQ).toLinearMap a _
  have hc : dotProduct ((pairSpectatorInclusion hQ).toLinearMap a)
      (cycleMap (Fin (Q+1)) ((pairSpectatorInclusion hQ).toLinearMap b)) =
      - dotProduct a ((compressedSwap hQ).toLinearMap b) := by
    rw [dotProduct_comm, cycleMap_adjoint,
      cycleSquare_pairSpectatorInclusion, dotProduct_neg, dotProduct_comm,
      swap23Linear_adjoint, hab]
  rw [cyclicSum_dot, pairSpectatorInclusion_isometry, hc,
    cycleSquare_pairSpectatorInclusion, dotProduct_neg, hab]
  ring

theorem orderedThreeWedge_dot {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    dotProduct (orderedThreeWedge hQ a) (orderedThreeWedge hQ b) =
      dotProduct a b - 2 * dotProduct a ((compressedSwap hQ).toLinearMap b) := by
  simp only [orderedThreeWedge, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, cyclicSum_pair_dot]
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hs]

theorem orderedThreeGram_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    orderedThreeGram hQ a = a - (2 : ℝ) • (compressedSwap hQ).toLinearMap a := by
  apply eq_of_dotProduct_eq
  intro b
  change dotProduct b (transposeMap (orderedThreeWedge hQ) (orderedThreeWedge hQ a)) = _
  rw [← transposeMap_adjoint, orderedThreeWedge_dot,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem orderedThreeGram_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    orderedThreeGram hQ (coupledTensor (2*Q-2) Q z l) =
      (1+threeBodyGramCoefficient Q z) • coupledTensor (2*Q-2) Q z l := by
  rw [orderedThreeGram_apply, compressedSwap_eigenvalue hQ hz hl]
  funext pq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem orderedThreeGram_defect_expansion {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    orderedThreeGram hQ a - a =
      ∑ i : CoupledIndex (2*Q-2) Q,
        (threeBodyGramCoefficient Q i.1.val *
          dotProduct (coupledTensor (2*Q-2) Q i.1.val i.2.val) a) •
            coupledTensor (2*Q-2) Q i.1.val i.2.val := by
  let D := orderedThreeGram hQ - LinearMap.id
  change D a = _
  conv_lhs => rw [← coupledTensor_expansion (2*Q-2) Q a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  dsimp [D]
  rw [orderedThreeGram_eigenvalue hQ (by have := i.1.isLt; omega)
    (Nat.le_of_lt_succ i.2.isLt)]
  funext pq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_WedgeIdentification
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_creation _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.LadderMap.transpose_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Identification. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

@[simp] lemma annihilation_vacuum {n : ℕ} (i : Fin n) :
    annihilation i (vacuum n) = 0 := by
  have h := word_eq_zero_of_degree_lt [i] (vacuum_homogeneous n) (by simp)
  simpa only [word_cons, word_nil, one_mul] using h

lemma annihilation_creation_apply {n : ℕ} (i j : Fin n) (x : Hilbert n) :
    annihilation i (creation j x) = (if i=j then x else 0) - creation j (annihilation i x) := by
  have h := congrArg (fun A : Module.End ℂ (Hilbert n) => A x)
    (annihilation_creation_CAR i j)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at h
  convert eq_sub_of_add_eq h using 2
  all_goals try with_reducible_and_instances rfl
  split_ifs <;> simp only [LinearMap.id_apply, LinearMap.zero_apply]

lemma annihilation_creation_vacuum {n : ℕ} (i j : Fin n) :
    annihilation i (creation j (vacuum n)) = if i=j then vacuum n else 0 := by
  rw [annihilation_creation_apply, annihilation_vacuum, map_zero, sub_zero]

lemma double_creation_vacuum {n : ℕ} (i x y : Fin n) :
    annihilation i (creation x (creation y (vacuum n))) =
      (if i=x then creation y (vacuum n) else 0) -
      (if i=y then creation x (vacuum n) else 0) := by
  rw [annihilation_creation_apply, annihilation_creation_vacuum]
  congr 1
  split_ifs <;> simp

lemma triple_creation_vacuum {n : ℕ} (i x y z : Fin n) :
    annihilation i (creation x (creation y (creation z (vacuum n)))) =
      (if i=x then creation y (creation z (vacuum n)) else 0) -
      (if i=y then creation x (creation z (vacuum n)) else 0) +
      (if i=z then creation x (creation y (vacuum n)) else 0) := by
  rw [annihilation_creation_apply, double_creation_vacuum, map_sub]
  have h₁ : creation x (if i=y then creation z (vacuum n) else 0) =
      if i=y then creation x (creation z (vacuum n)) else 0 := by
    split_ifs <;> simp
  have h₂ : creation x (if i=z then creation y (vacuum n) else 0) =
      if i=z then creation x (creation y (vacuum n)) else 0 := by
    split_ifs <;> simp
  rw [h₁,h₂]
  abel

lemma orbitalDelta_smul {n : ℕ} (i j : Fin n) (x : Hilbert n) :
    orbitalDelta i j • x = if i=j then x else 0 := by
  simp [orbitalDelta, ite_smul]

lemma annihilation_creation_vacuum_delta {n : ℕ} (i j : Fin n) :
    annihilation i (creation j (vacuum n)) = orbitalDelta i j • vacuum n := by
  rw [orbitalDelta_smul, annihilation_creation_vacuum]

lemma double_creation_vacuum_delta {n : ℕ} (i x y : Fin n) :
    annihilation i (creation x (creation y (vacuum n))) =
      orbitalDelta i x • creation y (vacuum n) -
      orbitalDelta i y • creation x (vacuum n) := by
  simp only [orbitalDelta_smul, double_creation_vacuum]

lemma triple_creation_vacuum_delta {n : ℕ} (i x y z : Fin n) :
    annihilation i (creation x (creation y (creation z (vacuum n)))) =
      orbitalDelta i x • creation y (creation z (vacuum n)) -
      orbitalDelta i y • creation x (creation z (vacuum n)) +
      orbitalDelta i z • creation x (creation y (vacuum n)) := by
  simp only [orbitalDelta_smul, triple_creation_vacuum]

lemma word_three_creation_vacuum {n : ℕ} (i j k x y z : Fin n) :
    word [i,j,k] (creation x (creation y (creation z (vacuum n)))) ∅ =
      orbitalDelta i x * (orbitalDelta j y * orbitalDelta k z -
        orbitalDelta j z * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k z -
        orbitalDelta j z * orbitalDelta k x) +
      orbitalDelta i z * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x) := by
  simp only [word_cons, word_nil, one_mul, Module.End.mul_apply,
    triple_creation_vacuum_delta, map_add, map_sub, map_smul,
    double_creation_vacuum_delta, annihilation_creation_vacuum_delta,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, vacuum_apply,
    ite_true, mul_one]

lemma sum_increasing_pairs_add {n : ℕ} {M : Type*} [AddCommGroup M]
    (f : Fin n → Fin n → M) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ a : PairLabel n, f a.val.1 a.val.2) +
      (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma pairContraction_adjoint_apply {n : ℕ} (v : PairLabel n → ℂ) (x : Hilbert n) :
    (pairContraction v).adjoint x =
      ∑ a : PairLabel n, v a • creation a.val.1 (creation a.val.2 x) := by
  simp only [pairContraction, map_sum, map_smulₛₗ, basicPair,
    adjoint_mul, annihilation_adjoint, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, Complex.star_def, Complex.conj_conj]

lemma pairContraction_ordered_adjoint {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (x : Hilbert n) :
    (pairContraction (fun a : PairLabel n =>
      ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint x =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        ∑ i, ∑ j, (c i j : ℂ) • creation i (creation j x) := by
  have hsum := sum_increasing_pairs_add
    (fun i j : Fin n => (c i j : ℂ) • creation i (creation j x)) (by
      intro i j
      have he := congrArg (fun A : Module.End ℂ (Hilbert n) => A x)
        (creation_anticommute j i)
      simp only [Module.End.mul_apply, LinearMap.neg_apply] at he
      rw [hc i j, Complex.ofReal_neg, he, neg_smul, smul_neg, neg_neg]) (by
      intro i
      have h : c i i = 0 := by have hh := hc i i; linarith
      simp [h])
  rw [← hsum, ← two_smul ℂ (∑ a : PairLabel n,
    (c a.val.1 a.val.2 : ℂ) • creation a.val.1 (creation a.val.2 x)), smul_smul]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * 2 = (Real.sqrt 2 : ℂ) := by
    have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hr : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      field_simp
      nlinarith
    exact_mod_cast hr
  rw [hs, pairContraction_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [smul_smul, Complex.ofReal_mul]

lemma sum_orbitalDelta_mul {n : ℕ} (i : Fin n) (f : Fin n → ℂ) :
    (∑ j, orbitalDelta i j * f j) = f i := by
  simp [orbitalDelta, ite_mul]

lemma sum_mul_orbitalDelta {n : ℕ} (i : Fin n) (f : Fin n → ℂ) :
    (∑ j, f j * orbitalDelta i j) = f i := by
  simp [orbitalDelta, mul_ite]

lemma pair_times_three_determinant {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    (∑ x, ∑ y, (c x y : ℂ) *
      (orbitalDelta i x * (orbitalDelta j y * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k x) +
      orbitalDelta i l * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x))) =
    2 * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  have he (x y : Fin n) : (c x y : ℂ) *
      (orbitalDelta i x * (orbitalDelta j y * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k x) +
      orbitalDelta i l * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x)) =
      orbitalDelta i x * ((c x y : ℂ) * orbitalDelta j y) * orbitalDelta k l -
      orbitalDelta i x * ((c x y : ℂ) * orbitalDelta k y) * orbitalDelta j l -
      orbitalDelta j x * ((c x y : ℂ) * orbitalDelta i y) * orbitalDelta k l +
      orbitalDelta k x * ((c x y : ℂ) * orbitalDelta i y) * orbitalDelta j l +
      orbitalDelta j x * ((c x y : ℂ) * orbitalDelta k y) * orbitalDelta i l -
      orbitalDelta k x * ((c x y : ℂ) * orbitalDelta j y) * orbitalDelta i l := by ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_mul_orbitalDelta,
    sum_orbitalDelta_mul]
  rw [hc i j, hc k i, hc j k]
  push_cast
  ring

lemma rawReadout_three_pair {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    rawReadout n 3
      ((annihilation l * pairContraction (fun a : PairLabel n =>
        ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint (vacuum n)) ![i,j,k] =
    (Real.sqrt 2 : ℂ) * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  rw [rawReadout_apply]
  simp only [List.ofFn_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.ofFn_zero, adjoint_mul, annihilation_adjoint, Module.End.mul_apply,
    pairContraction_ordered_adjoint c hc, map_smul, map_sum, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, word_three_creation_vacuum]
  rw [pair_times_three_determinant c hc i j k l]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * 2 = (Real.sqrt 2 : ℂ) := by
    have hr : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      field_simp
      nlinarith
    exact_mod_cast hr
  rw [← mul_assoc, hs]

lemma normalizedReadout_three_pair {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    normalizedReadout n 3
      ((annihilation l * pairContraction (fun a : PairLabel n =>
        ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint (vacuum n)) ![i,j,k] =
    ((Real.sqrt 3)⁻¹ : ℂ) * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  change ((Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ : ℂ) * rawReadout n 3 _ ![i,j,k] = _
  rw [rawReadout_three_pair c hc i j k l, ← mul_assoc]
  have hs : (Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ * Real.sqrt 2 = (Real.sqrt 3)⁻¹ := by
    norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one]
    rw [show (6:ℝ)=3*2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  have hs' : ((Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ : ℂ) * (Real.sqrt 2 : ℂ) =
      ((Real.sqrt 3)⁻¹ : ℂ) := by exact_mod_cast hs
  rw [hs']

lemma normalizedReadout_inner_sector {n N : ℕ} (x y : ExteriorCoordinates n N) :
    inner ℂ (normalizedReadout n N (sectorInclusion n N x))
      (normalizedReadout n N (sectorInclusion n N y)) = inner ℂ x y := by
  let f := (normalizedReadout n N).comp (sectorInclusion n N)
  apply (LinearMap.norm_map_iff_inner_map_map f).mp _ x y
  intro a
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (normalizedReadout_norm_sq (sectorInclusion_homogeneous a)).trans
    (sectorInclusion_norm_sq a)

end LaughlinGap.Occupation

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation

lemma normalizedReadout_spin_three_column {Q : ℕ} (hQ : 2 ≤ Q)
    (p : Fin (2*Q-2+1)) (l i j k : Fin (Q+1)) :
    normalizedReadout (Q+1) 3
      (sectorInclusion (Q+1) 3 (tripleWedgeColumn (spinPairForms Q p) l)) ![i,j,k] =
    ((orderedThreeWedge hQ (Pi.single (p,l) 1) ((i,j),k) : ℝ) : ℂ) := by
  have hh : Homogeneous 3
      ((annihilation l * pairContraction (spinPairForms Q p)).adjoint (vacuum (Q+1))) := by
    rw [adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous _ (creation_homogeneous (vacuum_homogeneous _) _)
  rw [tripleWedgeColumn, sectorInclusion_readout hh]
  have hv : spinPairForms Q p = fun a : PairLabel (Q+1) =>
      ((Real.sqrt 2 * pairCoefficient Q p.val a.val.1 a.val.2 : ℝ) : ℂ) := by
    funext a
    exact congrArg Complex.ofReal (sphericalExteriorPairCoefficient_eq_tensor _ _ _ _)
  rw [hv, normalizedReadout_three_pair _ (fun i j => pairCoefficient_swap Q p.val i j)]
  simp only [orderedThreeWedge, LinearMap.smul_apply, LinearMap.comp_apply,
    Pi.smul_apply, smul_eq_mul, cyclicSum_apply, Pi.add_apply, cycleMap_apply,
    pairSpectatorInclusion_apply]
  simp [Pi.single_apply, mul_ite, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_inv, orbitalDelta, ite_and]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero]

lemma spinTripleGram_entry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : Fin (2*Q-2+1) × Fin (Q+1)) :
    ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)) a b =
    ((orderedThreeGram hQ (Pi.single b 1) a : ℝ) : ℂ) := by
  have he : ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)) a b =
      inner ℂ (tripleWedgeColumn (spinPairForms Q a.1) a.2)
        (tripleWedgeColumn (spinPairForms Q b.1) b.2) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tripleWedgeMatrix,
      PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he, ← normalizedReadout_inner_sector, PiLp.inner_apply]
  rw [← (tupleThreeEquiv (Fin (Q+1))).sum_comp]
  change (∑ t : ThreeIndex (Fin (Q+1)),
    inner ℂ
      (normalizedReadout (Q+1) 3 (sectorInclusion (Q+1) 3
        (tripleWedgeColumn (spinPairForms Q a.1) a.2)) ![t.1.1,t.1.2,t.2])
      (normalizedReadout (Q+1) 3 (sectorInclusion (Q+1) 3
        (tripleWedgeColumn (spinPairForms Q b.1) b.2)) ![t.1.1,t.1.2,t.2])) = _
  simp only [normalizedReadout_spin_three_column hQ, RCLike.inner_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  change dotProduct (orderedThreeWedge hQ (Pi.single b 1))
    (orderedThreeWedge hQ (Pi.single a 1)) = _
  rw [dotProduct_comm, transposeMap_adjoint, dotProduct_comm, dotProduct_single_one]
  rfl

end LaughlinGap.Spin

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

lemma physicalTripleGram_entry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : Fin (2*Q-1) × Fin (Q+1)) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)) a b =
    ((orderedThreeGram hQ (Pi.single (physicalThreeIndexEquiv hQ b) 1)
      (physicalThreeIndexEquiv hQ a) : ℝ) : ℂ) := by
  exact spinTripleGram_entry hQ (physicalThreeIndexEquiv hQ a)
    (physicalThreeIndexEquiv hQ b)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalSpinSpectrum
attribute [-simp] _root_.OAI.LaughlinGap.Spin.nestedBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Spin Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

theorem physicalTripleGram_spectral {Q : ℕ} (hQ : 2 ≤ Q) :
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q) - 1 =
    ∑ i : CoupledIndex (2*Q-2) Q,
      (threeBodyGramCoefficient Q i.1.val : ℂ) •
        physicalThreeRankOne hQ i.1.val i.2.val := by
  classical
  ext a b
  have he := congrFun (orderedThreeGram_defect_expansion hQ
    (Pi.single (physicalThreeIndexEquiv hQ b) 1)) (physicalThreeIndexEquiv hQ a)
  have hid : (Pi.single (physicalThreeIndexEquiv hQ b) (1 : ℝ) :
      (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (physicalThreeIndexEquiv hQ a) = if a=b then 1 else 0 := by
    simp [Pi.single_apply]
  simp only [Pi.sub_apply, hid, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_single_one] at he
  rw [Matrix.sub_apply, physicalTripleGram_entry hQ, Matrix.one_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, physicalThreeRankOne,
    Matrix.vecMulVec_apply, Pi.star_apply, physicalThreeVector,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  have hcast : (if a=b then (1 : ℂ) else 0) = ↑(if a=b then (1:ℝ) else 0) := by
    split_ifs <;> rfl
  rw [hcast, ← Complex.ofReal_sub, he]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem physicalTripleGram_spin_blocks {Q : ℕ} (hQ : 2 ≤ Q) :
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q) - 1 =
    ∑ z : Fin (min (2*Q-2) Q+1),
      (threeBodyGramCoefficient Q z.val : ℂ) • physicalThreeProjection hQ z.val := by
  rw [physicalTripleGram_spectral hQ, Fintype.sum_sigma]
  simp only [physicalThreeProjection, Finset.smul_sum]

end LaughlinGap.Spin

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder
open Spin

theorem physical_spin_square {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalOccupationHamiltonian Q * physicalOccupationHamiltonian Q =
      physicalOccupationHamiltonian Q +
      (∑ z : Fin (min (2*Q-2) Q+1),
        (threeBodyGramCoefficient Q z.val : ℂ) • physicalSpinThreeLift hQ z.val) +
      exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
        (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [physical_normal_ordered_square hQ, physicalTripleGram_spin_blocks hQ]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    map_sum, map_smul, physicalSpinThreeLift]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealSpinSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Spin Square. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators
lemma matrixLift_reindex {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : ι ≃ κ) (B : κ → Module.End ℂ E) (A : Matrix κ κ ℂ) :
    matrixLift (fun i => B (e i)) (fun i j => A (e i) (e j)) = matrixLift B A := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk]
  have hh (i : κ) : (∑ j : ι, A i (e j) • ((B i).adjoint * B (e j))) =
      ∑ j : κ, A i j • ((B i).adjoint * B j) := e.sum_comp (fun j : κ => A i j • ((B i).adjoint * B j))
  simp only [hh]
  exact e.sum_comp (fun i : κ => ∑ j : κ, A i j • ((B i).adjoint * B j))
end LaughlinGap

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Occupation

@[simp] lemma complexify_physicalTriple (Q : ℕ) (a : Fin (2*Q-2+1) × Fin (Q+1)) :
    complexify (physicalTriple Q a) = Occupation.annihilation a.2 * Occupation.localPair (Q+1) Q a.1.val := by
  simp [physicalTriple, productFamily]

lemma complexify_three_lift {Q : ℕ} (hQ : 2 ≤ Q)
    (A : Matrix (Fin (2*Q-2+1) × Fin (Q+1)) (Fin (2*Q-2+1) × Fin (Q+1)) ℝ) :
    complexify (lift (physicalTriple Q) A) =
      exteriorLift (tripleWedgeMatrix (physicalPairForms Q) *
        (Matrix.of (fun i j => (A (physicalThreeIndexEquiv hQ i) (physicalThreeIndexEquiv hQ j) : ℂ)) :
          Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ) *
        (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [complexify_lift, exteriorLift, matrixLift_columns]
  have he (i : Fin (2*Q-1) × Fin (Q+1)) :
      contractCombination basisContraction (fun a => tripleWedgeMatrix (physicalPairForms Q) a i) =
      complexify (physicalTriple Q (physicalThreeIndexEquiv hQ i)) := by
    rw [show (fun a => tripleWedgeMatrix (physicalPairForms Q) a i) =
      (tripleWedgeColumn (physicalPairForms Q i.1) i.2 : BasisLabel (Q+1) 3 → ℂ) from rfl]
    change exteriorContraction (tripleWedgeColumn (physicalPairForms Q i.1) i.2) = _
    rw [tripleWedgeColumn_contraction, physicalPair_contraction, complexify_physicalTriple]
    rfl
  simp only [he]
  exact (matrixLift_reindex (physicalThreeIndexEquiv hQ)
    (fun a => complexify (physicalTriple Q a)) (A.map (algebraMap ℝ ℂ))).symm

lemma physicalThreeProjection_real {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (Matrix.of (fun i j => ((tensorProjection (show z ≤ min (2*Q-2) Q by omega))
      (physicalThreeIndexEquiv hQ i) (physicalThreeIndexEquiv hQ j) : ℂ))) =
      physicalThreeProjection hQ z := by
  ext i j
  simp [tensorProjection_eq, physicalThreeProjection, physicalThreeRankOne,
    physicalThreeVector, Matrix.vecMulVec_apply, Matrix.sum_apply]

@[simp] lemma complexify_threeSpinLift {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    complexify (threeSpinLift hQ hz) = physicalSpinThreeLift hQ z := by
  rw [threeSpinLift, complexify_three_lift hQ, physicalThreeProjection_real hQ hz]
  rfl

@[simp] lemma complexify_fourTarget (Q : ℕ) :
    complexify (fourTarget Q) = exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
      (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [← pairFourTerm_eq_lift]
  simp [fourTarget, pairFourTerm, physicalPair_contraction, adjoint_mul]

theorem physical_spin_square_real {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
      (∑ z : Fin (Q+1), (threeBodyGramCoefficient Q z.val) •
        threeSpinLift hQ (Nat.le_of_lt_succ z.isLt)) + fourTarget Q := by
  apply complexify_injective
  simp only [map_mul, map_add, map_sum, map_smul, complexify_physicalHamiltonian,
    complexify_threeSpinLift, complexify_fourTarget]
  rw [physical_spin_square hQ]
  congr 2
  let e : Fin (min (2*Q-2) Q+1) ≃ Fin (Q+1) := finCongr (by omega)
  have he := e.sum_comp (fun z : Fin (Q+1) =>
    (threeBodyGramCoefficient Q z.val : ℂ) • physicalSpinThreeLift hQ z.val)
  exact he

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_GlobalBoundCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

lemma spin_sum_split {Q : ℕ} (hQ : 15 ≤ Q) :
    (∑ z : Fin (Q+1), threeBodyGramCoefficient Q z.val •
      threeSpinLift (by omega : 2 ≤ Q) (Nat.le_of_lt_succ z.isLt)) =
      threeRetained hQ + threeTailLift (by omega : 2 ≤ Q) := by
  classical
  let f : ℕ → FockMatrix (Q+1) := fun z => if hz : z ≤ Q then
    threeBodyGramCoefficient Q z • threeSpinLift (by omega) hz else 0
  have hret : threeRetained hQ = ∑ z : Fin (Q+1), if z.val ≤ 15 then f z.val else 0 := by
    rw [← sum_fin_extend hQ]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [f,threeRetained]
    rw [dite_eq_left (by omega)]
  have htail : threeTailLift (by omega : 2 ≤ Q) =
      ∑ z : Fin (Q+1), if 16 ≤ z.val then f z.val else 0 := by
    unfold threeTailLift
    apply Finset.sum_congr rfl
    intro z hz
    simp only [f,dite_eq_left (Nat.le_of_lt_succ z.isLt)]
  rw [hret,htail,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : z.val ≤ 15 <;> simp [h,show (16 ≤ z.val) ↔ ¬ z.val ≤ 15 by omega,f,Nat.le_of_lt_succ z.isLt]

lemma physical_spin_square_split_oai {Q : ℕ} (hQ : 15 ≤ Q) :
    physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
      (threeRetained hQ + threeTailLift (by omega : 2 ≤ Q)) + fourTarget Q := by
  rw [physical_spin_square_real (by omega : 2 ≤ Q),spin_sum_split hQ]

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.physical_spin_square_split_oai := @OAI.LaughlinGap.RealOccupation.physical_spin_square_split_oai
