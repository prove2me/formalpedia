-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.three_comparison_of_strict_traces
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:26:15.159139+00:00
-- url     : https://prove2.me/submissions/5147bc75-a8af-4fb4-ba15-1a9a49ebbcf8

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L035

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/

noncomputable section


namespace LaughlinGap.Averaging
open scoped BigOperators InnerProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma coordinates_inner (A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates A) (coordinates B) = (A.transpose * B).trace := by
  change inner ℝ (WithLp.toLp 2 (fun ij : ι × ι => A ij.1 ij.2))
    (WithLp.toLp 2 (fun ij : ι × ι => B ij.1 ij.2)) = _
  simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma average_mem (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A ∈ S := by
  have hm := (invariantSpace S).starProjection_apply_mem (coordinates A)
  obtain ⟨B, hB, he⟩ := hm
  have hab : average S A = B := by
    change coordinates.symm ((invariantSpace S).starProjection (coordinates A)) = B
    rw [← he]
    exact coordinates.symm_apply_apply B
  exact hab ▸ hB

lemma average_orthogonal (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    ((A - average S A).transpose * B).trace = 0 := by
  rw [← coordinates_inner, map_sub]
  have hB' : coordinates B ∈ invariantSpace S := ⟨B, hB, rfl⟩
  have he := (invariantSpace S).starProjection_inner_eq_zero (coordinates A) (coordinates B) hB'
  simpa [average] using he

lemma average_unique (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A B : Matrix ι ι ℝ) (hB : B ∈ S)
    (h : ∀ C ∈ S, ((A-B).transpose * C).trace = 0) :
    average S A = B := by
  apply coordinates.injective
  change (invariantSpace S).starProjection (coordinates A) = coordinates B
  apply (invariantSpace S).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨B, hB, rfl⟩
  · rintro _ ⟨C,hC,rfl⟩
    rw [← map_sub]
    change inner ℝ (coordinates (A-B)) (coordinates C) = 0
    rw [coordinates_inner]
    exact h C hC

lemma average_transpose (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A.transpose = (average S A).transpose := by
  apply average_unique S A.transpose (average S A).transpose
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (star_mem (average_mem S A) : star (average S A) ∈ S)
  · intro C hC
    have ht : C.transpose ∈ S := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using (star_mem hC : star C ∈ S)
    have h := average_orthogonal S A ht
    rw [← Matrix.transpose_sub, Matrix.transpose_transpose]
    rw [← Matrix.trace_transpose, Matrix.transpose_mul] at h
    rw [Matrix.transpose_transpose, Matrix.trace_mul_comm] at h
    exact h

lemma trace_mul_average (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    (A * B).trace = (average S A * B).trace := by
  have h := average_orthogonal S A.transpose hB
  rw [average_transpose, ← Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.trace_sub] at h
  exact sub_eq_zero.mp h

lemma average_trace (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    (average S A).trace = A.trace := by
  have h := trace_mul_average S A (one_mem S)
  simpa using h.symm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma adjointMap_inner (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    inner ℝ (coordinates (F A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (adjointMap F B)) := by
  let F' := coordinates.toLinearMap.comp (F.comp coordinates.symm.toLinearMap)
  exact (LinearMap.adjoint_inner_right F' (coordinates A) (coordinates B)).symm

theorem average_natural (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (T : StarSubalgebra ℝ (Matrix κ κ ℝ)) (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A ∈ S, F A ∈ T) (hF' : ∀ B ∈ T, adjointMap F B ∈ S)
    (A : Matrix ι ι ℝ) : average T (F A) = F (average S A) := by
  apply average_unique T (F A) (F (average S A)) (hF _ (average_mem S A))
  intro B hB
  rw [← map_sub, ← coordinates_inner, adjointMap_inner, coordinates_inner]
  exact average_orthogonal S A (hF' B hB)

lemma commutator_adjoint (L A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates (commutator L A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (commutator L.transpose B)) := by
  simp only [coordinates_inner, commutator, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.transpose_sub, Matrix.transpose_mul, sub_mul, mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle' A.transpose B L.transpose]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma coordinates_eq_zero_of_inner {B : Matrix ι ι ℝ}
    (h : ∀ A, inner ℝ (coordinates A) (coordinates B) = 0) : B = 0 := by
  have he := inner_self_eq_zero.mp (h B)
  apply coordinates.injective
  simpa using he

lemma commutator_intertwines_adjoint {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (B : Matrix κ κ ℝ) :
    commutator L (adjointMap F B) = adjointMap F (commutator M B) := by
  apply sub_eq_zero.mp
  apply coordinates_eq_zero_of_inner
  intro A
  rw [map_sub, inner_sub_right]
  apply sub_eq_zero.mpr
  rw [← adjointMap_inner]
  have hM := commutator_adjoint M.transpose (F A) B
  simp only [Matrix.transpose_transpose] at hM
  rw [← hM, ← hF, adjointMap_inner]
  have he := commutator_adjoint L.transpose A (adjointMap F B)
  simpa only [Matrix.transpose_transpose] using he.symm

lemma map_rotationCommutant {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    {A : Matrix ι ι ℝ} (hA : A ∈ rotationCommutant L) :
    F A ∈ rotationCommutant M := by
  rw [rotationCommutant_mem] at hA ⊢
  constructor
  · rw [← hF, hA.1, map_zero]
  · rw [← hF', hA.2, map_zero]

theorem rotation_average_natural {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (A : Matrix ι ι ℝ) :
    average (rotationCommutant M) (F A) = F (average (rotationCommutant L) A) := by
  apply average_natural
  · intro B hB
    exact map_rotationCommutant F hF hF' hB
  · intro B hB
    rw [rotationCommutant_mem] at hB ⊢
    constructor
    · rw [commutator_intertwines_adjoint F hF', hB.1, map_zero]
    · have hh : ∀ A, F (commutator L.transpose.transpose A) =
          commutator M.transpose.transpose (F A) := by simpa using hF
      rw [commutator_intertwines_adjoint F hh, hB.2, map_zero]

end LaughlinGap.Averaging

end

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

end PairNormalization

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators Topology
open Filter

lemma fallingRatio_eq_prod (Q z : ℕ) :
    fallingRatio Q z = ∏ k ∈ Finset.range z,
      ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ) := by
  simp [fallingRatio, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma fallingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (1 - (k : ℝ) / Q) / (2 - ((k : ℝ) + 2) / Q))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) + 2)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k + 3)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ Q), Nat.cast_sub (by omega : k ≤ 2 * Q - 2),
    Nat.cast_sub (by omega : 2 ≤ 2 * Q)]
  push_cast
  field_simp [hQ0]
  ring_nf

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1 / 2 : ℝ) ^ z)) := by
  simpa only [fallingRatio_eq_prod, Finset.prod_const, Finset.card_range] using
    (tendsto_finsetProd (Finset.range z) (fun k _ => fallingFactor_tendsto k))

theorem threeBodyGramCoefficient_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyGramCoefficient Q z)
      atTop (𝓝 ((3 * (z : ℝ) - 1) * (-1 / 2 : ℝ) ^ z)) := by
  have h := ((tendsto_const_nhds (x := (-1 : ℝ) ^ z)).mul (fallingRatio_tendsto z)).mul
    ((tendsto_const_nhds (x := 3 * (z : ℝ) - 1)).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z : ℝ) * ((z : ℝ) + 1))))
  convert h using 1
  · rfl
  · 
    rw [sub_zero, div_pow, div_pow]
    ring_nf

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyDimensionRatio Q z) atTop (𝓝 (3 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (3 - (1 + 2 * (z : ℝ)) / Q) / (2 - (1 : ℝ) / Q))
      atTop (𝓝 (3 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (3 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 + 2 * (z : ℝ)))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold threeBodyDimensionRatio
  field_simp [hQ0]
  ring_nf

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEnergy
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation
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

lemma word_eq_zero_of_degree_lt {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous k x) (hk : k < js.length) : word js x = 0 := by
  induction js generalizing k x with
  | nil => simp at hk
  | cons j js ih =>
    cases k with
    | zero => simp only [word, LinearMap.comp_apply, annihilation_eq_zero_of_degree_zero hx, map_zero]
    | succ k =>
      exact ih (annihilation_homogeneous hx j) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Contraction
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
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

lemma triple_basic_eq_word {n : ℕ} (i : Fin n) (a : PairLabel n) :
    annihilation i * basicPair a = word [a.val.1,a.val.2,i] := by
  simp only [basicPair, word_cons, word_nil, one_mul, mul_assoc]

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

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

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

lemma annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i = if i=j then 1 else 0 := by
  apply complexify_injective
  simp only [map_add, map_mul, complexify_annihilation, complexify_creation, apply_ite,
    map_one, map_zero]
  by_cases h : i=j <;> simpa [h, Module.End.one_eq_id, Module.End.mul_eq_comp] using
    Occupation.annihilation_creation_CAR i j

lemma annihilation_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j = -(annihilation j * annihilation i) := by
  apply complexify_injective
  simp only [map_mul, map_neg, complexify_annihilation]
  exact Occupation.annihilation_anticommute i j

lemma secondQuantization_transpose {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    (secondQuantization L).transpose = secondQuantization L.transpose := by
  simp only [secondQuantization, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, creation, Matrix.transpose_apply, Matrix.transpose_transpose]
  rw [Finset.sum_comm]

lemma elementary_commutator_annihilation {n : ℕ} (i j k : Fin n) :
    (creation i * annihilation j) * annihilation k -
      annihilation k * (creation i * annihilation j) =
        -(if k=i then annihilation j else 0) := by
  have h := annihilation_creation k i
  have h' := annihilation_anticommute j k
  have hm := congrArg (fun B : FockMatrix n => B * annihilation j) h
  simp only [add_mul] at hm
  rw [← mul_assoc] 
  rw [mul_assoc (creation i), h', mul_neg, ← mul_assoc]
  rw [sub_eq_add_neg, ← neg_add, add_comm, hm]
  split_ifs <;> simp

lemma commutator_annihilation {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Averaging.commutator (secondQuantization L) (annihilation k) =
      -∑ j, L k j • annihilation j := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk,
    secondQuantization, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub,
    elementary_commutator_annihilation, smul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_ite, smul_zero]
  simp

lemma commutator_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L A B : Matrix ι ι ℝ) :
    Averaging.commutator L (A*B) = Averaging.commutator L A * B + A * Averaging.commutator L B := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk]
  noncomm_ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
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
lemma lift_rankOne [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (x y : ι → ℝ) :
    lift B (Matrix.vecMulVec x y) = (combination B x).transpose * combination B y := by
  simp only [lift, combination, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma lift_positive (B : ι → Matrix κ κ ℝ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (lift B A).PosSemidef := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have he : star C * C = ∑ k, Matrix.vecMulVec (fun i => C k i) (fun i => C k i) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [he, map_sum]
  apply Matrix.posSemidef_sum
  intro k hk
  rw [lift_rankOne]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (combination B (fun i => C k i))

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

lemma commutator_transpose (L A : Matrix κ κ ℝ) :
    commutator L A.transpose = -(commutator L.transpose A).transpose := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  abel

omit [DecidableEq ι] in
lemma Covariant.transpose [DecidableEq ι] {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) :
    Covariant L.transpose D.transpose B where
  lower i := h.raise i
  raise i := by simpa using h.lower i

lemma Covariant.commutator_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    commutator L (lift B A) = lift B (commutator D A) := by
  have ht (i : ι) : commutator L (B i).transpose = ∑ k, D k i • (B k).transpose := by
    rw [commutator_transpose, h.raise, Matrix.transpose_neg, neg_neg]
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sum, map_smul, commutator_mul, ht, h.lower, Matrix.sum_mul,
    Matrix.mul_neg, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← sub_eq_add_neg, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply,
    Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  · conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_comm

theorem Covariant.average_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    average (rotationCommutant L) (lift B A) = lift B (average (rotationCommutant D) A) := by
  apply rotation_average_natural
  · exact fun A => (h.commutator_lift A).symm
  · exact fun A => (h.transpose.commutator_lift A).symm

theorem annihilation_covariant {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Covariant (secondQuantization L) L annihilation where
  lower i := commutator_annihilation L i
  raise i := by rw [secondQuantization_transpose]; exact commutator_annihilation L.transpose i

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

theorem highestFactor_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z k : ℕ) :
    Tendsto (fun q => highestFactor (n q) (m q) z k) atTop (𝓝 r) := by
  have hquot : Tendsto
      (fun q => ((m q : ℝ) / n q + (-(z : ℝ) + k + 1) / n q) /
        (1 - (k : ℝ) / n q)) atTop (𝓝 r) := by
    simpa only [add_zero, sub_zero, div_one, Pi.div_def] using
      (hmn.add (hn.const_div_atTop (-(z : ℝ) + k + 1))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hn.const_div_atTop (k : ℝ)))
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  apply hquot.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (k : ℝ))] with q hq
  have hN : (n q : ℝ) ≠ 0 := by
    have hk : (0 : ℝ) ≤ k := by positivity
    linarith
  have hNk : (n q : ℝ) - k ≠ 0 := by linarith
  dsimp [highestFactor]
  field_simp
  ring

theorem highestWeight_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestWeight (n q) (m q) z p) atTop
      (𝓝 ((z.choose p : ℝ) * r ^ p)) := by
  have h := (tendsto_const_nhds (x := (z.choose p : ℝ))).mul
    (tendsto_finsetProd (Finset.range p) (fun k _ => highestFactor_tendsto hn hmn z k))
  simpa only [Finset.prod_const, Finset.card_range, highestWeight] using h

theorem highestNormalization_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z : ℕ) :
    Tendsto (fun q => highestNormalization (n q) (m q) z) atTop (𝓝 ((r+1)^z)) := by
  have hsum : (∑ p ∈ Finset.range (z+1), (z.choose p : ℝ) * r^p) = (r+1)^z := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro p hp
    simp [mul_comm]
  simpa only [highestNormalization, hsum] using
    tendsto_finsetSum (Finset.range (z+1)) (fun p _ => highestWeight_tendsto hn hmn z p)

theorem highestCoefficient_tendsto_ratio {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
        Real.sqrt ((r+1)^z))) := by
  have hpos : 0 < (r+1)^z := pow_pos (by linarith) z
  exact ((tendsto_const_nhds.mul (highestWeight_tendsto hn hmn z p).sqrt).div
    (highestNormalization_tendsto hn hmn z).sqrt (Real.sqrt_pos.mpr hpos).ne')

lemma sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ k hk => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), hk, pow_succ]

lemma highest_ratio_eq {r : ℝ} (hr : 0 ≤ r) (z p : ℕ) :
    (-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
      Real.sqrt ((r+1)^z) =
    limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
      (1 / Real.sqrt (r+1)) z p := by
  by_cases hp : p ≤ z
  · have he : z = p + (z-p) := (Nat.add_sub_of_le hp).symm
    have hpos : Real.sqrt (r+1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    rw [Real.sqrt_mul (by positivity), sqrt_nat_pow hr,
      sqrt_nat_pow (by linarith : 0 ≤ r+1)]
    unfold limitingHighestCoefficient
    rw [div_pow, div_pow, one_pow]
    rw [show Real.sqrt (r+1)^z = Real.sqrt (r+1)^p * Real.sqrt (r+1)^(z-p) by
      rw [← pow_add, Nat.add_sub_of_le hp]]
    ring
  · simp [Nat.choose_eq_zero_of_lt (by omega : z < p), limitingHighestCoefficient]

theorem highestCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 (limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
        (1 / Real.sqrt (r+1)) z p)) := by
  simpa only [highest_ratio_eq hr] using highestCoefficient_tendsto_ratio hr hn hmn z p

lemma firstAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((n q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (1 / (1+r))) := by
  have h : Tendsto (fun q => (1 + a / (n q : ℝ)) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (1 / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((n q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma secondAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((m q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (r / (1+r))) := by
  have h : Tendsto (fun q => ((m q : ℝ) / n q + a / n q) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (r / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      (hmn.add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((m q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma firstSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((n q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop (𝓝 (1 / Real.sqrt (1+r))) := by
  have h := (firstAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

lemma secondSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((m q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop
      (𝓝 (Real.sqrt r / Real.sqrt (1+r))) := by
  have h := (secondAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div hr] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

lemma firstLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => firstLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r))) := by
  have h := (firstSqrtRatio_tendsto hr hn hmn (1-(p : ℝ)) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : firstLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((n q : ℝ)+(1-(p : ℝ))) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [firstLoweringCoefficient, Real.sqrt_mul (Nat.cast_nonneg p),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf, mul_one_div] using h

lemma secondLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ)
    (hp : p ≤ z+l+1) :
    Tendsto (fun q => secondLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt r / Real.sqrt (1+r)))) := by
  have hp' : (0 : ℝ) ≤ (z : ℝ)+l-p+1 := by
    have h : (p : ℝ) ≤ (z : ℝ)+l+1 := by exact_mod_cast hp
    linarith
  have h := (secondSqrtRatio_tendsto hr hn hmn (-(z : ℝ)-l+p) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : secondLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((m q : ℝ)+(-(z : ℝ)-l+p)) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [secondLoweringCoefficient, Real.sqrt_mul hp',
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf] using h

lemma coupledCoefficient_eq_zero {n m z l p : ℕ} (hp : z+l < p) :
    coupledCoefficient n m z l p = 0 := by
  induction l generalizing p with
  | zero => exact highestCoefficient_eq_zero (by omega)
  | succ l ih =>
    simp [coupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

lemma limitingCoupledCoefficient_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    limitingCoupledCoefficient u v z l p = 0 := by
  induction l generalizing p with
  | zero => simp [limitingCoupledCoefficient, limitingHighestCoefficient,
      Nat.choose_eq_zero_of_lt (show z < p by omega)]
  | succ l ih =>
    simp [limitingCoupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

theorem coupledCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
        (1 / Real.sqrt (1+r)) z l p)) := by
  induction l generalizing p with
  | zero => simpa only [coupledCoefficient, limitingCoupledCoefficient, add_comm 1 r] using
      highestCoefficient_tendsto hr hn hmn z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have h₁ : Tendsto (fun q => if p = 0 then (0 : ℝ) else
          firstLoweringCoefficient (n q) (m q) z l p * coupledCoefficient (n q) (m q) z l (p-1))
        atTop (𝓝 (if p = 0 then 0 else
          Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r) *
            limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
              (1 / Real.sqrt (1+r)) z l (p-1))) := by
        split_ifs with hp0
        · exact tendsto_const_nhds
        · exact (firstLoweringCoefficient_tendsto hr hn hmn z l p).mul (ih (p-1))
      have h₂ := (secondLoweringCoefficient_tendsto hr hn hmn z l p hp).mul (ih p)
      convert h₁.add h₂ using 1
      · rfl
      · congr 1
        simp only [limitingCoupledCoefficient]
        split_ifs <;> ring
    · simpa only [coupledCoefficient_eq_zero (show z+(l+1) < p by omega),
        limitingCoupledCoefficient_eq_zero (show z+(l+1) < p by omega)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

open Polynomial

lemma binomial_linear_coeff (u v : ℝ) (z p : ℕ) :
    ((C u * X - C v)^z).coeff p = (z.choose p : ℝ) * u^p * (-v)^(z-p) := by
  have h := comp_C_mul_X_coeff (p := (X + C (-v))^z) (r := u) (n := p)
  simp only [pow_comp, add_comp, X_comp, C_comp, coeff_X_add_C_pow] at h
  rw [map_neg] at h
  rw [sub_eq_add_neg]
  rw [h]
  ring

lemma monomialWeight_choose {z p : ℕ} (hp : p ≤ z) :
    monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ) =
      Real.sqrt (z.choose p : ℝ) := by
  have hc : (z.choose p : ℝ) * (p.factorial : ℝ) * ((z-p).factorial : ℝ) =
      (z.factorial : ℝ) := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hp)
  have hs : Real.sqrt (z.choose p : ℝ) * monomialWeight z p =
      Real.sqrt (z.factorial : ℝ) := by
    rw [monomialWeight, ← Real.sqrt_mul (by positivity)]
    congr 1
    simpa only [mul_assoc] using hc
  apply (div_eq_iff (Real.sqrt_pos.mpr (by exact_mod_cast z.factorial_pos)).ne').mpr
  rw [← hs]
  have he : Real.sqrt (z.choose p : ℝ) ^ 2 = (z.choose p : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    _ = monomialWeight z p * Real.sqrt (z.choose p : ℝ) ^ 2 := by rw [he]
    _ = _ := by ring

lemma highestCoefficient_eq_polynomial (u v : ℝ) (z p : ℕ) :
    limitingHighestCoefficient u v z p =
      monomialWeight z p * (couplingPolynomial u v z 0).coeff p := by
  simp only [couplingPolynomial, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one,
    mul_one, pow_zero, coeff_C_mul, binomial_linear_coeff]
  by_cases hp : p ≤ z
  · rw [show (-v)^(z-p) = (-1 : ℝ)^(z-p)*v^(z-p) by rw [← mul_pow]; congr 1; ring]
    calc
      limitingHighestCoefficient u v z p =
          (monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ)) *
            (-1 : ℝ)^(z-p)*u^p*v^(z-p) := by
        rw [monomialWeight_choose hp]
        unfold limitingHighestCoefficient
        ring
      _ = _ := by ring
  · simp [limitingHighestCoefficient, Nat.choose_eq_zero_of_lt (show z < p by omega)]

lemma couplingPolynomial_step (u v : ℝ) (z l : ℕ) :
    couplingPolynomial u v z (l+1) =
      C (1 / Real.sqrt ((l : ℝ)+1)) *
        ((C v * X + C u) * couplingPolynomial u v z l) := by
  have hf : Real.sqrt ((l+1).factorial : ℝ) =
      Real.sqrt ((l : ℝ)+1) * Real.sqrt (l.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.sqrt_mul (by positivity)]
  have hn : 1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt ((l+1).factorial : ℝ)) =
      (1 / Real.sqrt ((l : ℝ)+1)) *
        (1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt (l.factorial : ℝ))) := by
    rw [hf]
    ring
  unfold couplingPolynomial
  rw [hn, map_mul, pow_succ]
  ring

lemma couplingPolynomial_natDegree_le (u v : ℝ) (z l : ℕ) :
    (couplingPolynomial u v z l).natDegree ≤ z+l := by
  have ha : (C u * X - C v : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  have hb : (C v * X + C u : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  unfold couplingPolynomial
  apply natDegree_mul_le.trans
  apply add_le_add
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by nlinarith))
  · exact natDegree_pow_le.trans (by nlinarith)

lemma couplingPolynomial_coeff_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    (couplingPolynomial u v z l).coeff p = 0 :=
  coeff_eq_zero_of_natDegree_lt ((couplingPolynomial_natDegree_le u v z l).trans_lt hp)

lemma monomialWeight_first {T p : ℕ} (hp : 0 < p) (hpT : p ≤ T+1) :
    monomialWeight (T+1) p = Real.sqrt (p : ℝ) * monomialWeight T (p-1) := by
  have hpp : (p-1)+1 = p := by omega
  have hfac : p.factorial = p * (p-1).factorial := by
    simpa only [hpp] using Nat.factorial_succ (p-1)
  have hTp : (T+1)-p = T-(p-1) := by omega
  simp only [monomialWeight, hfac, Nat.cast_mul, hTp]
  rw [← Real.sqrt_mul (Nat.cast_nonneg p)]
  congr 1
  ring

lemma monomialWeight_second {T p : ℕ} (hp : p ≤ T) :
    monomialWeight (T+1) p =
      Real.sqrt ((T : ℝ)-p+1) * monomialWeight T p := by
  have hTp : (T+1)-p = (T-p)+1 := by omega
  simp only [monomialWeight, hTp, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hp]
  rw [← Real.sqrt_mul (by
    have h : (p : ℝ) ≤ T := by exact_mod_cast hp
    linarith : (0 : ℝ) ≤ (T : ℝ)-p+1)]
  congr 1
  ring

lemma couplingPolynomial_step_coeff (u v : ℝ) (z l p : ℕ) :
    (couplingPolynomial u v z (l+1)).coeff p =
      ((if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) +
        u * (couplingPolynomial u v z l).coeff p) / Real.sqrt ((l : ℝ)+1) := by
  rw [couplingPolynomial_step, coeff_C_mul, add_mul, mul_assoc (C v), coeff_add]
  simp only [coeff_C_mul]
  cases p with
  | zero => simp [div_eq_mul_inv, mul_comm]
  | succ p => simp [coeff_X_mul, mul_add, mul_comm, div_eq_mul_inv, mul_left_comm]

theorem limitingCoupledCoefficient_eq_polynomial (u v : ℝ) (z l p : ℕ) :
    limitingCoupledCoefficient u v z l p =
      monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p := by
  induction l generalizing p with
  | zero => simpa only [Nat.add_zero, limitingCoupledCoefficient] using
      highestCoefficient_eq_polynomial u v z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have hfirst : monomialWeight (z+l+1) p *
          (if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) =
        (if p = 0 then 0 else Real.sqrt (p : ℝ) * v *
          (monomialWeight (z+l) (p-1) * (couplingPolynomial u v z l).coeff (p-1))) := by
        split_ifs with hp0
        · simp
        · rw [monomialWeight_first (by omega : 0 < p) hp]
          ring
      have hsecond : monomialWeight (z+l+1) p *
          (u * (couplingPolynomial u v z l).coeff p) =
        Real.sqrt ((z : ℝ)+l-p+1) * u *
          (monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p) := by
        by_cases hpT : p ≤ z+l
        · rw [monomialWeight_second hpT, Nat.cast_add]
          ring
        · rw [couplingPolynomial_coeff_eq_zero (by omega : z+l < p)]
          ring
      simp only [limitingCoupledCoefficient, ih, couplingPolynomial_step_coeff,
        ← Nat.add_assoc]
      rw [← mul_div_assoc, mul_add, hfirst, hsecond]
    · rw [limitingCoupledCoefficient_eq_zero (by omega : z+(l+1) < p),
        couplingPolynomial_coeff_eq_zero (by omega : z+(l+1) < p), mul_zero]

theorem coupledCoefficient_tendsto_polynomial {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (monomialWeight (z+l) p *
        (couplingPolynomial (Real.sqrt r / Real.sqrt (1+r))
          (1 / Real.sqrt (1+r)) z l).coeff p)) := by
  simpa only [limitingCoupledCoefficient_eq_polynomial] using
    coupledCoefficient_tendsto hr hn hmn z l p

end LaughlinGap.Spin

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

lemma trace_mul_rankOne {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    (A * Matrix.vecMulVec x y).trace = dotProduct y (A.mulVec x) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantFamily
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Family. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

omit [DecidableEq ι] in
lemma Covariant.combination_lower [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L (combination B x) = -combination B (D.transpose.mulVec x) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    h.lower, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

lemma Covariant.combination_raise {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L.transpose (combination B x) = -combination B (D.mulVec x) := by
  simpa using h.transpose.combination_lower x

omit [DecidableEq κ] [Fintype σ] [DecidableEq σ] in
lemma combination_embeddingFamily [DecidableEq κ] [Fintype σ] [DecidableEq σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (B : κ → Matrix σ σ ℝ) (x : ι → ℝ) :
    combination (embeddingFamily A B) x = combination B (A.toLinearMap x) := by
  rw [A.toLinearMap.pi_apply_eq_sum_univ x, map_sum]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, embeddingFamily, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (Pi.single i 1 : ι → ℝ) = (fun j => if i=j then 1 else 0) := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs]

lemma Covariant.embedding {L : Matrix σ σ ℝ} {S : LadderSystem ι}
    {T : LadderSystem κ} {B : κ → Matrix σ σ ℝ}
    (h : Covariant L (loweringMatrix T) B) (A : LadderMap S T) :
    Covariant L (loweringMatrix S) (embeddingFamily A B) where
  lower i := by
    change commutator L (combination B _) = _
    rw [h.combination_lower, loweringMatrix_transpose, LinearMap.toMatrix'_mulVec]
    change -combination B (T.raise (A.toLinearMap (Pi.single i 1))) = _
    rw [A.raise, ← combination_embeddingFamily]
    congr 1
    simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have he := congrArg (fun M : Matrix ι ι ℝ => M j i) (loweringMatrix_transpose S)
    simpa only [Matrix.transpose_apply, loweringMatrix, LinearMap.toMatrix'_apply] using he.symm
  raise i := by
    change commutator L.transpose (combination B _) = _
    rw [h.combination_raise, loweringMatrix, LinearMap.toMatrix'_mulVec]
    change -combination B (T.lower (A.toLinearMap (Pi.single i 1))) = _
    rw [A.lower, ← combination_embeddingFamily]
    rfl

lemma loweringMatrix_tensor (S : LadderSystem ι) (T : LadderSystem κ)
    (i j : ι × κ) :
    loweringMatrix (S.tensor T) i j =
      (if i.2=j.2 then loweringMatrix S i.1 j.1 else 0) +
      (if i.1=j.1 then loweringMatrix T i.2 j.2 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [loweringMatrix, LinearMap.toMatrix'_apply, LadderSystem.tensor,
    LinearMap.add_apply, onFirstEnd_apply, onSecondEnd_apply, Pi.add_apply]
  have hf : (fun a : ι => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) =
      if i₂=j₂ then Pi.single j₁ 1 else 0 := by
    funext a
    by_cases he : i₂=j₂ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  have hs : (fun a : κ => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) =
      if i₁=j₁ then Pi.single j₂ 1 else 0 := by
    funext a
    by_cases he : i₁=j₁ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  change S.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) i₁ +
    T.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) i₂ = _
  rw [hf, hs]
  split_ifs <;> simp_all

lemma product_commutator {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ} {E : Matrix κ κ ℝ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : ∀ i, commutator L (B i) = -∑ j, D i j • B j)
    (hC : ∀ i, commutator L (C i) = -∑ j, E i j • C j) (i : ι × κ) :
    commutator L (productFamily B C i) =
      -∑ j : ι × κ, ((if i.2=j.2 then D i.1 j.1 else 0) +
        (if i.1=j.1 then E i.2 j.2 else 0)) • productFamily B C j := by
  simp only [productFamily, commutator_mul, hB, hC, neg_mul, Matrix.mul_neg,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    Fintype.sum_prod_type, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const_zero, Finset.sum_ite_eq]
  abel

lemma Covariant.product {L : Matrix σ σ ℝ} {S : LadderSystem ι} {T : LadderSystem κ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : Covariant L (loweringMatrix S) B) (hC : Covariant L (loweringMatrix T) C) :
    Covariant L (loweringMatrix (S.tensor T)) (productFamily B C) where
  lower i := by simpa only [loweringMatrix_tensor] using product_commutator hB.lower hC.lower i
  raise i := by
    simpa only [Matrix.transpose_apply, loweringMatrix_tensor, eq_comm] using
      product_commutator hB.transpose.lower hC.transpose.lower i

omit [DecidableEq ι] in
lemma Covariant.smul [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (r : ℝ) :
    Covariant L D (fun i => r • B i) where
  lower i := by simp only [map_smul, h.lower, smul_neg, Finset.smul_sum, smul_comm r]
  raise i := by simp only [map_smul, h.raise, smul_neg, Finset.smul_sum, smul_comm r]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IrrepAveraging
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irrep Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

lemma standardLadderSystem_casimir (n : ℕ) (x : Fin (n+1) → ℝ) :
    (standardLadderSystem n).casimir x = ((n : ℝ)*(n+2)) • x := by
  funext p
  simp only [LadderSystem.casimir_apply, standardLadderSystem, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, weight_apply, lowering_raising_apply]
  ring

theorem standardLadderMap_eq_zero {n m : ℕ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem m)) :
    A.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  have h := A.casimir x
  rw [standardLadderSystem_casimir, standardLadderSystem_casimir, map_smul] at h
  have hne : (m : ℝ)*(m+2) ≠ (n : ℝ)*(n+2) := by
    intro he
    exact hnm (spinCasimir_injective he).symm
  funext j
  have he := congrFun h j
  change (m : ℝ)*(m+2)*A.toLinearMap x j = (n : ℝ)*(n+2)*A.toLinearMap x j at he
  exact (mul_left_cancel₀ (sub_ne_zero.mpr hne) (by nlinarith :
    ((m : ℝ)*(m+2)-(n : ℝ)*(n+2)) * A.toLinearMap x j =
      ((m : ℝ)*(m+2)-(n : ℝ)*(n+2))*0))

lemma ladderStep_pos (n : ℕ) (p : Fin n) : 0 < ladderStep n p := by
  apply Real.sqrt_pos.mpr
  have hp : (p.val : ℝ) < n := by exact_mod_cast p.isLt
  exact mul_pos (by positivity) (by linarith)

lemma weight_single (n : ℕ) (i : Fin (n+1)) :
    weight n (Pi.single i 1) = ((n : ℝ)-2*i.val) • Pi.single i 1 := by
  funext j
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

lemma lowering_single (n : ℕ) (p : Fin n) :
    lowering n (Pi.single p.castSucc 1) = ladderStep n p • Pi.single p.succ 1 := by
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
    by_cases h : j=p
    · subst j; simp
    · have hn : p.val ≠ j.val := by intro hp; apply h; exact (Fin.ext hp).symm
      simp [Fin.ext_iff, hn, eq_comm]

theorem standardLadderMap_schur {n : ℕ}
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem n)) (x : Fin (n+1) → ℝ) :
    A.toLinearMap x = A.toLinearMap (Pi.single 0 1) 0 • x := by
  let c : Fin (n+1) → ℝ := fun i => A.toLinearMap (Pi.single i 1) i
  have hd (i : Fin (n+1)) : A.toLinearMap (Pi.single i 1) = c i • Pi.single i 1 := by
    have hw := A.weight (Pi.single i 1)
    change weight n (A.toLinearMap (Pi.single i 1)) = A.toLinearMap (weight n _) at hw
    rw [weight_single, map_smul] at hw
    funext j
    by_cases h : i=j
    · subst j; simp [c]
    · have hv : i.val ≠ j.val := by exact fun he => h (Fin.ext he)
      have he := congrFun hw j
      simp only [weight_apply, Pi.smul_apply, smul_eq_mul] at he
      have hne : ((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val) ≠ 0 := by
        intro he
        apply hv
        exact_mod_cast (by linarith : (i.val : ℝ)=j.val)
      have hz : A.toLinearMap (Pi.single i 1) j = 0 := by
        apply (mul_eq_zero.mp (show (((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val)) *
          A.toLinearMap (Pi.single i 1) j = 0 by nlinarith)).resolve_left hne
      simp [hz, h, eq_comm]
  have hc : ∀ i, c i = c 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have he := A.lower (Pi.single i.castSucc 1)
      change lowering n (A.toLinearMap (Pi.single i.castSucc 1)) = A.toLinearMap (lowering n _) at he
      rw [hd, map_smul, lowering_single, map_smul, hd] at he
      have hh := congrFun he i.succ
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hh
      have hci : c i.succ = c i.castSucc := by
        nlinarith [ladderStep_pos n i]
      exact hci.trans ih
  rw [A.toLinearMap.pi_apply_eq_sum_univ x]
  have hs (i : Fin (n+1)) : (fun j => if i=j then (1:ℝ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  simp only [hs, hd, hc, smul_smul]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Pi.smul_apply, c, mul_comm]

theorem standardSpin_average (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix (standardLadderSystem n))) A =
      (A.trace / (n+1 : ℕ)) • 1 := by
  let S := rotationCommutant (loweringMatrix (standardLadderSystem n))
  let Y := average S A
  let L := commutantLadderMap (standardLadderSystem n) (average_mem S A)
  let c := L.toLinearMap (Pi.single 0 1) 0
  have he : Y = c • 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hv := standardLadderMap_schur L x
    change Matrix.toLin' Y x = c • x at hv
    rwa [Matrix.toLin'_apply] at hv
  have hc : c = A.trace / (n+1 : ℕ) := by
    have ht := average_trace S A
    change Y.trace = A.trace at ht
    rw [he, Matrix.trace_smul, Matrix.trace_one] at ht
    apply (eq_div_iff (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0)).mpr
    simpa using ht
  exact he.trans (congrArg (fun t : ℝ => t • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) hc)

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

lemma physicalPair_embedding {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-2+1)) :
    physicalPair Q p.val = (1/Real.sqrt 2) •
      embeddingFamily (pairInclusion hQ) (productFamily annihilation annihilation) p := by
  simp only [embeddingFamily, pairInclusion_apply, Pi.single_apply,
    ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem physicalPair_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (standardLadderSystem (2*Q-2)))
      (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) := by
  have ha := annihilation_covariant (loweringMatrix (standardLadderSystem Q))
  have hp := (ha.product ha).embedding (pairInclusion hQ)
  have he : (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) =
      (fun p => (1/Real.sqrt 2) • embeddingFamily (pairInclusion hQ)
        (productFamily annihilation annihilation) p) := funext (physicalPair_embedding hQ)
  rw [he]
  exact hp.smul (1/Real.sqrt 2)

@[simp] lemma complexify_physicalHamiltonian (Q : ℕ) :
    complexify (physicalHamiltonian Q) = Occupation.physicalOccupationHamiltonian Q := by
  simp only [physicalHamiltonian, map_sum, map_mul, complexify_transpose,
    complexify_physicalPair, Occupation.physicalOccupationHamiltonian, Occupation.pairHamiltonian,
    Occupation.physicalPair_contraction]

theorem physicalTriple_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (tensorSpin (2*Q-2) Q)) (physicalTriple Q) :=
  (physicalPair_covariant hQ).product (annihilation_covariant _)

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
-- module Solutions.OAIQ030_LG.LaughlinGap_FourSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

lemma affine_twice_spin_tendsto (r : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono (fun Q => show Q-r ≤ 2*Q-2*r by omega)
  exact tendsto_sub_atTop_nat r

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

lemma LadderMap.matrix_lower {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : loweringMatrix T * A.matrix = A.matrix * loweringMatrix S := by
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, loweringMatrix, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.lower

lemma LadderMap.matrix_raise {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : (loweringMatrix T).transpose * A.matrix =
      A.matrix * (loweringMatrix S).transpose := by
  simp only [loweringMatrix_transpose]
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, LadderMap.matrix, Matrix.toLin'_toMatrix']
  exact LinearMap.ext A.raise

@[simp] lemma LadderMap.transpose_matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : A.transpose.matrix = A.matrix.transpose := toMatrix_transposeMap _

lemma copyLift_commutator {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S) X) =
      commutator (loweringMatrix T) (copyLift A B X) := by
  have ht := B.transpose.matrix_lower
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S), ← A.matrix_lower,
    Matrix.mul_assoc (loweringMatrix T), Matrix.mul_assoc (loweringMatrix T),
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

lemma copyLift_commutator_transpose {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (X : Matrix ι ι ℝ) :
    copyLift A B (commutator (loweringMatrix S).transpose X) =
      commutator (loweringMatrix T).transpose (copyLift A B X) := by
  have ht := B.transpose.matrix_raise
  rw [LadderMap.transpose_matrix] at ht
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Averaging.commutator,
    Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A.matrix (loweringMatrix S).transpose, ← A.matrix_raise,
    Matrix.mul_assoc (loweringMatrix T).transpose, Matrix.mul_assoc (loweringMatrix T).transpose,
    Matrix.mul_assoc A.matrix X]
  simp only [Matrix.mul_assoc, ht]

theorem copyLift_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix T)) (copyLift A B X) =
      (X.trace / (n+1 : ℕ)) • (A.matrix * B.matrix.transpose) := by
  rw [rotation_average_natural (copyLift A B) (copyLift_commutator A B)
    (copyLift_commutator_transpose A B), standardSpin_average]
  simp [copyLift]

omit [DecidableEq κ] in
lemma copyLift_rankOne {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) (x y : ι → ℝ) :
    copyLift A B (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y) := by
  simp only [copyLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, LadderMap.matrix_mulVec, Matrix.vecMul_transpose]

lemma trace_rankOne_mul {σ : Type*} [Fintype σ] (x y : σ → ℝ) (C : Matrix σ σ ℝ) :
    (Matrix.vecMulVec x y * C).trace = dotProduct y (C.mulVec x) := by
  rw [Matrix.trace_mul_comm, trace_mul_rankOne]

theorem distinct_copy_average {n m : ℕ} {T : LadderSystem κ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) T)
    (B : LadderMap (standardLadderSystem m) T)
    (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap x) (B.toLinearMap y)) = 0 := by
  apply average_unique _ _ _ (zero_mem _)
  intro C hC
  simp only [sub_zero, Matrix.transpose_vecMulVec, trace_rankOne_mul]
  let L := A.transpose.comp ((commutantLadderMap T hC).comp B)
  have he : L.toLinearMap = 0 := standardLadderMap_eq_zero hnm.symm L
  rw [transposeMap_adjoint]
  have hv := LinearMap.congr_fun he y
  change transposeMap A.toLinearMap (Matrix.toLin' C (B.toLinearMap y)) = 0 at hv
  rw [Matrix.toLin'_apply] at hv
  rw [hv, dotProduct_zero]

theorem equal_copy_average {n : ℕ} {T : LadderSystem κ}
    (A B : LadderMap (standardLadderSystem n) T) (i j : Fin (n+1)) :
    average (rotationCommutant (loweringMatrix T))
      (Matrix.vecMulVec (A.toLinearMap (Pi.single i 1))
        (B.toLinearMap (Pi.single j 1))) =
      (if i=j then (1 : ℝ)/(n+1 : ℕ) else 0) • (A.matrix * B.matrix.transpose) := by
  rw [← copyLift_rankOne, copyLift_average, Matrix.trace_vecMulVec]
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma Covariant.equal_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n : ℕ}
    (A C : LadderMap (standardLadderSystem n) S) (i j : Fin (n+1)) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap (Pi.single i 1))).transpose *
        combination B (C.toLinearMap (Pi.single j 1))) =
      if i=j then average (rotationCommutant L)
        ((combination B (A.toLinearMap (Pi.single (0 : Fin (n+1)) 1))).transpose *
          combination B (C.toLinearMap (Pi.single (0 : Fin (n+1)) 1))) else 0 := by
  simp only [← lift_rankOne, h.average_lift, equal_copy_average, map_smul]
  split_ifs <;> simp

lemma Covariant.distinct_descendant_average {L : Matrix κ κ ℝ} {S : LadderSystem ι}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L (loweringMatrix S) B) {n m : ℕ}
    (hnm : n ≠ m) (A : LadderMap (standardLadderSystem n) S)
    (C : LadderMap (standardLadderSystem m) S) (x : Fin (n+1) → ℝ) (y : Fin (m+1) → ℝ) :
    average (rotationCommutant L)
      ((combination B (A.toLinearMap x)).transpose * combination B (C.toLinearMap y)) = 0 := by
  rw [← lift_rankOne, h.average_lift, distinct_copy_average hnm, map_zero]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeBounds
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Bounds. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma threeSpinLift_positive {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeSpinLift hQ hz).PosSemidef := by
  apply lift_positive
  rw [tensorProjection_eq]
  apply Matrix.posSemidef_sum
  intro l hl
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (coupledTensor (2*Q-2) Q z l.val)

lemma threeSpinLift_average_highest {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    average (rotationCommutant (fockLowering Q))
      ((combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)).transpose *
        combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)) =
      (1/((2*Q-2)+Q-2*z+1 : ℕ) : ℝ) • threeSpinLift hQ hz := by
  let hz' : z ≤ min (2*Q-2) Q := by omega
  have he : (coupledEmbedding hz').toLinearMap (Pi.single (0 : Fin ((2*Q-2)+Q-2*z+1)) 1) =
      highestTensor (2*Q-2) Q z := by
    rw [coupledEmbedding_apply]
    simp [Pi.single_apply, ite_smul]
  rw [← lift_rankOne, (physicalTriple_covariant hQ).average_lift, ← he,
    equal_copy_average]
  simp only [ite_true, map_smul]
  simp only [threeSpinLift, tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap, LadderMap.matrix]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma coupledTensor_low_expansion {n m T : ℕ} (hT : T ≤ min n m)
    (a : Fin (n+1) × Fin (m+1)) (ha : a.1.val+a.2.val=T) :
    (∑ z : Fin (T+1), coupledTensor n m z.val (T-z.val) a •
      coupledTensor n m z.val (T-z.val)) = Pi.single a 1 := by
  classical
  have hex := coupledTensor_expansion n m (Pi.single a 1)
  simp only [dotProduct_single_one] at hex
  rw [← hex]
  apply Finset.sum_bij_ne_zero (fun z _ _ => lowCoupledInclusion hT z)
  · simp
  · intro z hz hz0 w hw hw0 he
    exact Fin.ext (congrArg (fun i : CoupledIndex n m => i.1.val) he)
  · intro b hb hb0
    have hw : b.1.val+b.2.val=T := by
      by_contra hn
      exact hb0 (by simp [coupledTensor, show a.1.val+a.2.val ≠ b.1.val+b.2.val by omega])
    let z : Fin (T+1) := ⟨b.1.val,by omega⟩
    have hz : lowCoupledInclusion hT z = b := by
      rcases b with ⟨r,l⟩
      have hr : (lowCoupledInclusion hT z).1 = r := Fin.ext rfl
      apply Sigma.ext hr
      apply (Fin.heq_ext_iff (by rfl)).mpr
      dsimp [lowCoupledInclusion,z]
      dsimp at hw
      omega
    refine ⟨z,Finset.mem_univ _,?_,hz⟩
    change coupledTensor n m (lowCoupledInclusion hT z).1.val
      (lowCoupledInclusion hT z).2.val a • coupledTensor n m
      (lowCoupledInclusion hT z).1.val (lowCoupledInclusion hT z).2.val ≠ 0
    rwa [hz]
  · intros
    rfl

lemma coupledEmbedding_single {n m z : ℕ} (hz : z ≤ min n m)
    (l : Fin (n+m-2*z+1)) :
    (coupledEmbedding hz).toLinearMap (Pi.single l 1) = coupledTensor n m z l.val := by
  rw [coupledEmbedding_apply]
  simp [Pi.single_apply, ite_smul]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Covariant.coupled_average {n m z w T U : ℕ}
    (hT : T ≤ min n m) (hU : U ≤ min n m) (hz : z ≤ T) (hw : w ≤ U)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B) :
    average (rotationCommutant L)
      ((combination B (coupledTensor n m z (T-z))).transpose *
        combination B (coupledTensor n m w (U-w))) =
      if z=w ∧ T=U then
        average (rotationCommutant L)
          ((combination B (highestTensor n m z)).transpose *
            combination B (highestTensor n m z)) else 0 := by
  let hz' : z ≤ min n m := hz.trans hT
  let hw' : w ≤ min n m := hw.trans hU
  rw [← coupledEmbedding_single hz' (⟨T-z,by omega⟩ : Fin (n+m-2*z+1)),
    ← coupledEmbedding_single hw' (⟨U-w,by omega⟩ : Fin (n+m-2*w+1))]
  by_cases hzw : z=w
  · subst w
    rw [h.equal_descendant_average]
    simp only [coupledEmbedding_single, Fin.val_zero, coupledTensor_zero, true_and,
      Fin.mk.injEq]
    congr 1
    apply propext
    omega
  · rw [ite_eq_right (by tauto)]
    exact h.distinct_descendant_average (by omega) _ _ _ _

lemma Covariant.rawTensor_cross_average {n m T : ℕ} (hT : T ≤ min n m)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B)
    (a b : Fin (n+1) × Fin (m+1))
    (ha : a.1.val+a.2.val=T) (hb : b.1.val+b.2.val=T) :
    average (rotationCommutant L) ((B a).transpose * B b) =
      ∑ z : Fin (T+1),
        (coupledCoefficient n m z.val (T-z.val) a.1.val *
          coupledCoefficient n m z.val (T-z.val) b.1.val) •
        average (rotationCommutant L)
          ((combination B (highestTensor n m z.val)).transpose *
            combination B (highestTensor n m z.val)) := by
  classical
  have hex (c : Fin (n+1) × Fin (m+1)) (hc : c.1.val+c.2.val=T) :=
    congrArg (combination B) (coupledTensor_low_expansion hT c hc)
  have hea := hex a ha
  have heb := hex b hb
  simp only [map_sum, map_smul, combination_single] at hea heb
  rw [← hea, ← heb]
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_sum, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hh (w : Fin (T+1)) := h.coupled_average hT hT
    (Nat.le_of_lt_succ z.isLt) (Nat.le_of_lt_succ w.isLt)
  simp only [hh, and_true, Fin.val_inj]
  rw [Finset.sum_eq_single z]
  · simp only [ite_true, coupledTensor, show a.1.val+a.2.val=z.val+(T-z.val) by omega,
      show b.1.val+b.2.val=z.val+(T-z.val) by omega]
    rw [mul_comm]
  · intro w hw hwz
    rw [ite_eq_right (Ne.symm hwz), smul_zero]
  · simp

end LaughlinGap.RealOccupation

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

lemma RowEntry.balance {t : Fin 8} (a : RowEntry t) :
    t.val+a.output.val = a.val.1.val+a.val.2.val := by
  dsimp [RowEntry.output]; have := a.property; omega

lemma sum_fin_extend {M : Type*} [AddCommMonoid M] {T K : ℕ} (h : T ≤ K) (f : ℕ → M) :
    (∑ z : Fin (T+1), f z.val) = ∑ z : Fin (K+1), if z.val ≤ T then f z.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range f,
    Fin.sum_univ_eq_sum_range (fun z => if z ≤ T then f z else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_range,Finset.mem_filter]
  omega

lemma rowTriple_cross_average {Q T : ℕ} (hQ : 15 ≤ Q)
    (a b : Fin 8 × Fin 9) (ha : a.1.val+a.2.val=T) (hb : b.1.val+b.2.val=T) :
    average (rotationCommutant (fockLowering Q))
      ((rowTriple (by omega) a).transpose * rowTriple (by omega) b) =
      ∑ z : Fin 16,
        (threeWeightCoefficient Q z.val T a.1.val * threeWeightCoefficient Q z.val T b.1.val) •
          threeHighestAverage Q z.val := by
  have ht : T ≤ 15 := by have := a.1.isLt; have := a.2.isLt; omega
  let a' : Fin (2*Q-2+1) × Fin (Q+1) := (⟨a.1.val,by omega⟩,⟨a.2.val,by omega⟩)
  let b' : Fin (2*Q-2+1) × Fin (Q+1) := (⟨b.1.val,by omega⟩,⟨b.2.val,by omega⟩)
  change average _ ((physicalTriple Q a').transpose * physicalTriple Q b') = _
  rw [(physicalTriple_covariant (by omega : 2 ≤ Q)).rawTensor_cross_average (by omega) a' b' ha hb]
  change (∑ z : Fin (T+1),
    (coupledCoefficient (2*Q-2) Q z.val (T-z.val) a.1.val * coupledCoefficient (2*Q-2) Q z.val (T-z.val) b.1.val) •
      threeHighestAverage Q z.val) = _
  rw [sum_fin_extend ht (fun z =>
    (coupledCoefficient (2*Q-2) Q z (T-z) a.1.val *
      coupledCoefficient (2*Q-2) Q z (T-z) b.1.val) • threeHighestAverage Q z)]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp [a',b']
  by_cases hzt : z.val ≤ T <;> simp [threeWeightCoefficient,hzt,threeHighestAverage]

lemma rowThree_average {Q : ℕ} (hQ : 15 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowThree (by omega) r) =
      ∑ z : Fin 16, rowThreeTrace Q z.val r • threeHighestAverage Q z.val := by
  classical
  have ha (a : RowEntry r.t) := rowTriple_cross_average hQ (r.t,a.output) a.val rfl a.balance.symm
  have hb (a : RowEntry r.t) := rowTriple_cross_average hQ a.val (r.t,a.output) a.balance.symm rfl
  have hc (a b : RowEntry r.t) :
      average (rotationCommutant (fockLowering Q))
        (if a.output=b.output then (rowTriple (by omega) a.val).transpose * rowTriple (by omega) b.val else 0) =
      ∑ z : Fin 16, (if a.output=b.output then
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) a.val.1.val *
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) b.val.1.val else 0) •
          threeHighestAverage Q z.val := by
    by_cases hab : a.output=b.output
    · rw [ite_eq_left hab,rowTriple_cross_average hQ a.val b.val a.balance.symm (by rw [hab];exact b.balance.symm)]
      simp only [hab,ite_true]
    · simp [hab]
  have hd (a : RowEntry r.t) :
      average (rotationCommutant (fockLowering Q))
        ((rowTriple (by omega) (r.t,a.output)).transpose * rowTriple (by omega) a.val +
          (rowTriple (by omega) a.val).transpose * rowTriple (by omega) (r.t,a.output)) =
      ∑ z : Fin 16, (2 * threeWeightCoefficient Q z.val (r.t.val+a.output.val) r.t.val *
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) a.val.1.val) •
          threeHighestAverage Q z.val := by
    rw [map_add,ha,hb,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rw [← add_smul]
    congr 1
    ring
  rw [rowThree,map_add]
  simp only [map_sum,map_smul,hd,hc,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm (f := fun (a : RowEntry r.t) (z : Fin 16) => _)]
  conv_lhs =>
    arg 2; arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun (a : RowEntry r.t) (z : Fin 16) => _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [← Finset.sum_smul, ← add_smul, rowThreeTrace, rowTrace]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> ring

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
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.LadderMap.transpose_matrix
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

lemma threeBodyGramCoefficient_zero (Q : ℕ) : threeBodyGramCoefficient Q 0 = -1 := by
  norm_num [threeBodyGramCoefficient, fallingRatio]

lemma threeBodyGramCoefficient_one {Q : ℕ} (hQ : 2 ≤ Q) :
    threeBodyGramCoefficient Q 1 = -1 := by
  have hq : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (Q : ℝ) ≠ 0 := by linarith
  have hd : (Q : ℝ)-1 ≠ 0 := by linarith
  simp only [threeBodyGramCoefficient, fallingRatio, Nat.descFactorial_one,
    Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring

lemma threeBodyGramCoefficient_three {Q : ℕ} (hQ : 3 ≤ Q) :
    threeBodyGramCoefficient Q 3 = -1 := by
  have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : (Q : ℝ)-1 ≠ 0 := by linarith
  have h2 : (Q : ℝ)-1-1 ≠ 0 := by linarith
  have h3 : ((Q : ℝ)-1)*2-1 ≠ 0 := by linarith
  rw [threeBodyGramCoefficient, fallingRatio_eq_prod]
  norm_num [Finset.prod_range_succ, Nat.cast_sub (by omega : 2 ≤ Q),
    Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_sub (by omega : 2 ≤ 2*Q),
    Nat.cast_sub (by omega : 1 ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q-2)]
  field_simp
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

lemma linearMap_apply_coordinates {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (x : ι → ℝ) (k : κ) :
    (∑ i, A (Pi.single i 1) k * x i) = A x k := by
  conv_rhs => rw [A.pi_apply_eq_sum_univ x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  have he : Pi.single i (1:ℝ) = (fun j : ι => if i=j then (1:ℝ) else 0) := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [he]

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

theorem physicalTripleGram_mulVec_real {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)).mulVec
        (fun i => (a (physicalThreeIndexEquiv hQ i) : ℂ)) =
      fun i => ((orderedThreeGram hQ a (physicalThreeIndexEquiv hQ i) : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, physicalTripleGram_entry hQ,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [(physicalThreeIndexEquiv hQ).sum_comp (fun j =>
    orderedThreeGram hQ (Pi.single j 1) (physicalThreeIndexEquiv hQ i) * a j)]
  rw [linearMap_apply_coordinates]

theorem physicalTripleGram_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)).mulVec (physicalThreeVector hQ z l) =
    (1+(threeBodyGramCoefficient Q z : ℂ)) • physicalThreeVector hQ z l := by
  unfold physicalThreeVector
  rw [physicalTripleGram_mulVec_real hQ, orderedThreeGram_eigenvalue hQ hz hl]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one]

theorem physicalTripleWedge_null {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) (hn : z=0 ∨ z=1 ∨ z=3) :
    (tripleWedgeMatrix (physicalPairForms Q)).mulVec (physicalThreeVector hQ z l) = 0 := by
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp
  have hq : threeBodyGramCoefficient Q z = -1 := by
    rcases hn with rfl | rfl | rfl
    · exact threeBodyGramCoefficient_zero Q
    · exact threeBodyGramCoefficient_one hQ
    · exact threeBodyGramCoefficient_three hz
  rw [physicalTripleGram_eigenvalue hQ hz hl, hq]
  simp

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalSpinSpectrum
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

theorem physicalThreeProjection_wedge_null {Q z : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hn : z=0 ∨ z=1 ∨ z=3) :
    tripleWedgeMatrix (physicalPairForms Q) * physicalThreeProjection hQ z = 0 := by
  simp only [physicalThreeProjection, physicalThreeRankOne, Matrix.mul_sum,
    Matrix.mul_vecMulVec]
  apply Finset.sum_eq_zero
  intro l hl
  rw [physicalTripleWedge_null hQ hz (by omega : l.val ≤ (2*Q-2)+Q-2*z) hn]
  simp

end LaughlinGap.Spin

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

lemma threeSpinLift_null {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (hn : z=0 ∨ z=1 ∨ z=3) :
    threeSpinLift hQ hz = 0 := by
  apply complexify_injective
  rw [map_zero, complexify_threeSpinLift, physicalSpinThreeLift,
    physicalThreeProjection_wedge_null hQ hz hn, Matrix.zero_mul, map_zero]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma threeWeightCoefficient_tendsto (z T p : ℕ) :
    Tendsto (fun Q => threeWeightCoefficient Q z T p) atTop
      (𝓝 (threeWeightCoefficientStar z T p)) := by
  by_cases hz : z ≤ T
  · have hr : Tendsto (fun Q : ℕ => (Q:ℝ) / (2*Q-2:ℕ)) atTop (𝓝 (1/2:ℝ)) := by
      simpa [Nat.sub_zero] using fallingFactor_tendsto 0
    have hu : Real.sqrt (1/2:ℝ) / Real.sqrt (1+(1/2:ℝ)) = 1/Real.sqrt 3 := by
      rw [show (1:ℝ)+1/2=3/2 by norm_num, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),
        Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_one]
      field_simp
    have hv : 1 / Real.sqrt (1+(1/2:ℝ)) = Real.sqrt 2 / Real.sqrt 3 := by
      rw [show (1:ℝ)+1/2=3/2 by norm_num, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
      field_simp
    have h := coupledCoefficient_tendsto_polynomial (by norm_num : (0:ℝ) ≤ 1/2)
      (affine_twice_spin_tendsto 1) hr z (T-z) p
    simpa only [threeWeightCoefficient,threeWeightCoefficientStar,ite_eq_left hz,
      Nat.add_sub_of_le hz,hu,hv,mul_one] using h
  · simp only [threeWeightCoefficient,threeWeightCoefficientStar,ite_eq_right hz]
    exact tendsto_const_nhds

lemma rowTrace_tendsto {s : ℕ → ℕ → ℕ → ℕ → ℝ} {s₀ : ℕ → ℕ → ℕ → ℝ}
    (hs : ∀ z T p, Tendsto (fun Q => s Q z T p) atTop (𝓝 (s₀ z T p)))
    (r : RowData) (z : ℕ) :
    Tendsto (fun Q => rowTrace (s Q) z r) atTop (𝓝 (rowTrace s₀ z r)) := by
  unfold rowTrace
  apply Tendsto.add
  · apply tendsto_finsetSum
    intro a ha
    exact ((hs _ _ _).const_mul _).mul (hs _ _ _)
  · apply tendsto_finsetSum
    intro a ha
    apply tendsto_finsetSum
    intro b hb
    by_cases he : a.output=b.output
    · simp only [ite_eq_left he]
      exact ((hs _ _ _).const_mul _).mul (hs _ _ _)
    · simp only [ite_eq_right he]
      exact tendsto_const_nhds

lemma rowThreeTrace_tendsto (r : RowData) (z : ℕ) :
    Tendsto (fun Q => rowThreeTrace Q z r) atTop
      (𝓝 (rowTrace threeWeightCoefficientStar z r)) :=
  rowTrace_tendsto threeWeightCoefficient_tendsto r z

lemma threeHighestAverage_eq {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeHighestAverage Q z =
      (1/((2*Q-2)+Q-2*z+1 : ℕ):ℝ) • threeSpinLift hQ hz :=
  threeSpinLift_average_highest hQ hz

lemma three_dimension_identity {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((2*Q-2+Q-2*z+1:ℕ):ℝ) / ((2*Q-1:ℕ):ℝ) = threeBodyDimensionRatio Q z := by
  rw [threeBodyDimensionRatio, Nat.cast_add, Nat.cast_sub (by omega : 2*z ≤ 2*Q-2+Q),
      Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2*Q), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
  push_cast
  ring

theorem three_comparison_of_strict_traces_oai {ι : Type*} [Fintype ι]
    (rows : ι → RowData)
    (hc : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val)) :
    ∀ᶠ Q in atTop, ∀ hQ : 15 ≤ Q,
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowThree (by omega) (rows r)) ≤
      ∑ z : Fin 16, threeBodyGramCoefficient Q z.val •
        threeSpinLift (by omega : 2 ≤ Q) (show z.val ≤ Q by omega) := by
  have hseq (z : Fin 16) : ∀ᶠ Q in atTop,
      z.val=0 ∨ z.val=1 ∨ z.val=3 ∨
        (∑ r, rowThreeTrace Q z.val (rows r)) ≤
          threeBodyDimensionRatio Q z.val * threeBodyGramCoefficient Q z.val := by
    by_cases hn : z.val=0 ∨ z.val=1 ∨ z.val=3
    · exact Eventually.of_forall (fun _ => by tauto)
    · have hlim := tendsto_finsetSum Finset.univ (fun r _ => rowThreeTrace_tendsto (rows r) z.val)
      have htarget := (threeBodyDimensionRatio_tendsto z.val).mul
        (threeBodyGramCoefficient_tendsto z.val)
      filter_upwards [hlim.eventually_lt htarget (hc z (by tauto) (by tauto) (by tauto))] with Q hQ
      exact Or.inr (Or.inr (Or.inr hQ.le))
  filter_upwards [eventually_all.mpr hseq] with Q hs
  intro hQ
  simp only [map_sum,rowThree_average hQ,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z hz
  rw [← Finset.sum_smul, threeHighestAverage_eq (by omega) (by omega),smul_smul]
  rcases hs z with hn | hn | hn | he
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inl hn)]
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inr (Or.inl hn))]
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inr (Or.inr hn))]
  · apply smul_le_smul_of_nonneg_right _ (threeSpinLift_positive (by omega : 2 ≤ Q) (by omega : z.val ≤ Q)).nonneg
    have hd : (0:ℝ) < ((2*Q-2)+Q-2*z.val+1:ℕ) := by positivity
    have hd₂ : (0:ℝ) < (2*Q-1:ℕ) := by exact_mod_cast (show 0 < 2*Q-1 by omega)
    rw [← three_dimension_identity (by omega : 2 ≤ Q) (by omega : z.val ≤ Q)] at he
    rw [← Finset.mul_sum]
    rw [div_mul_eq_mul_div] at he
    have hh := (le_div_iff₀ hd₂).mp he
    rw [mul_comm _ ((2*Q-1:ℕ):ℝ)] at hh
    rw [mul_comm (↑(2 * Q - 2 + Q - 2 * ↑z + 1) : ℝ)] at hh
    simpa only [div_eq_mul_inv, one_div, one_mul] using (div_le_iff₀ hd).mpr hh

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinGap.RealOccupation.three_comparison_of_strict_traces_oai.{u_1} := @OAI.LaughlinGap.RealOccupation.three_comparison_of_strict_traces_oai.{u_1}
