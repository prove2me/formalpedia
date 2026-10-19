-- Prove2me | solution 1 for OAI.Erdos3.exists_prepared_polynomial_layer_exp_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:16:04.767415+00:00
-- url     : https://prove2.me/submissions/a97957b4-fed6-447c-8335-28f02f5b218a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B230

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {I J : Type*} [Fintype J]

theorem samplingRankCut_decomposition (a : J → ℤ) (e : J → ℝ)
    (p : VectorPolynomial I ℝ (J → ℝ)) :
    p = map (samplingRankProjection a e) p + integerRowPolynomial a p ⊗ₜ[ℝ] e := by
  apply coefficients.injective
  ext α j
  simp only [map_add, coefficients_map, coefficients_tmul, Finsupp.add_apply,
    samplingRankProjection_apply, integerRowPolynomial_coeff, integerRowLinear_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem samplingRankCut_finrank_lt (a : J → ℤ) (e : J → ℝ)
    (W : Submodule ℝ (J → ℝ)) (he : e ∈ W) (hae : integerRowLinear a e = 1) :
    Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro h
  have hem : e ∈ W ⊓ LinearMap.ker (integerRowLinear a) := by rw [h]; exact he
  have hz : integerRowLinear a e = 0 := hem.2
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped Matrix BigOperators

theorem exists_bounded_rational_unit_preimage {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (i : ι) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hconsistent : ∃ x : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x = Pi.single i 1) :
    ∃ x : κ → ℚ, A *ᵥ x = Pi.single i 1 ∧
      ∀ j, RationalHeightLE (x j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  have hSr := real_matrix_image_section A S hS
  obtain ⟨y, hy⟩ := hconsistent
  have hinv : Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr]
  refine ⟨fun j => S j i, ?_, fun j => hSH j i⟩
  ext k
  rw [Matrix.mulVec_single_one] at hinv
  have hk := congrFun hinv k
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.of_apply,
    Pi.single_apply] at hk ⊢
  split_ifs at hk ⊢ <;> exact_mod_cast hk

theorem exists_bounded_joint_rational_section {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℚ)
    {H R : ℕ} (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (ha : ∀ i, RationalHeightLE (a i) R)
    (hconsistent : ∃ y : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) = 0 ∧
      ∑ i, (a i : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i ≠ 0) :
    let hSystem := (Fintype.card ι + 1) * (R * H) ^ Fintype.card ι
    let hSection := rationalKernelHeight (Fintype.card ρ + 1) hSystem
    ∃ z : κ → ℚ, A *ᵥ (B *ᵥ z) = 0 ∧
      (∑ i, a i * (B *ᵥ z) i) = 1 ∧
      (∀ j, RationalHeightLE (z j) hSection) ∧
      ∀ i, RationalHeightLE ((B *ᵥ z) i)
        ((Fintype.card κ + 1) * (H * hSection) ^ Fintype.card κ) := by
  classical
  intro hSystem hSection
  let C : Matrix (Option ρ) ι ℚ := Matrix.of (fun r i => r.elim (a i) (fun r => A r i))
  let M : Matrix (Option ρ) κ ℚ := C * B
  have hC : ∀ i j, RationalHeightLE (C i j) R := by
    intro i j
    cases i with
    | none => exact ha j
    | some i => exact hA i j
  have hM : ∀ i j, RationalHeightLE (M i j) hSystem :=
    rationalHeightLE_matrix_mul C B hC hB
  have hSystem1 : 1 ≤ hSystem := by
    dsimp [hSystem]
    exact Nat.mul_pos (Nat.succ_pos _) (pow_pos (Nat.mul_pos hR hH) _)
  have hMr : Matrix.of (fun i j => (M i j : ℝ)) =
      Matrix.of (fun i j => (C i j : ℝ)) * Matrix.of (fun i j => (B i j : ℝ)) := by
    ext i j
    simp [M, Matrix.mul_apply]
  have hunit : ∃ x : κ → ℝ, Matrix.of (fun i j => (M i j : ℝ)) *ᵥ x =
      Pi.single none 1 := by
    obtain ⟨y, hy, hay⟩ := hconsistent
    let t : ℝ := ∑ i, (a i : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i
    refine ⟨t⁻¹ • y, ?_⟩
    rw [Matrix.mulVec_smul, hMr, ← Matrix.mulVec_mulVec]
    ext i
    cases i with
    | none =>
      change t⁻¹ * t = 1
      exact inv_mul_cancel₀ hay
    | some i =>
      have hi := congrFun hy i
      change t⁻¹ * (Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y)) i = 0
      simp only [hi, Pi.zero_apply, mul_zero]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_rational_unit_preimage M none hSystem1 hM hunit
  have hcz : C *ᵥ (B *ᵥ z) = Pi.single none 1 := by
    rw [Matrix.mulVec_mulVec]
    exact hz
  refine ⟨z, ?_, congrFun hcz none, ?_, ?_⟩
  · ext i
    exact congrFun hcz (some i)
  · simpa only [hSection, Fintype.card_option] using hzH
  · intro i
    exact rationalHeightLE_sum (fun j => B i j * z j)
      (fun j => (hB i j).mul (by simpa only [hSection, Fintype.card_option] using hzH j))

namespace VectorPolynomial

theorem exists_bounded_joint_rational_direction {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℤ)
    {H R : ℕ} (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (ha : ∀ i, |(a i : ℝ)| ≤ R)
    (hrow : ∃ w : jointRationalSpace B A, integerRowLinear a w.val ≠ 0) :
    let hSystem := (Fintype.card ι + 1) * (R * H) ^ Fintype.card ι
    let hSection := rationalKernelHeight (Fintype.card ρ + 1) hSystem
    ∃ e : ι → ℚ, (fun i => (e i : ℝ)) ∈ jointRationalSpace B A ∧
      integerRowLinear a (fun i => (e i : ℝ)) = 1 ∧
      ∀ i, RationalHeightLE (e i)
        ((Fintype.card κ + 1) * (H * hSection) ^ Fintype.card κ) := by
  classical
  intro hSystem hSection
  have haQ : ∀ i, RationalHeightLE (a i : ℚ) R := by
    intro i
    have habs : (a i).natAbs ≤ R := by
      exact_mod_cast (show ((a i).natAbs : ℝ) ≤ R by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using ha i)
    exact ⟨by simpa only [Rat.num_intCast] using habs, by simpa only [Rat.den_intCast] using hR⟩
  have hconsistent : ∃ y : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) = 0 ∧
      ∑ i, ((a i : ℚ) : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i ≠ 0 := by
    obtain ⟨w, hw⟩ := hrow
    obtain ⟨⟨y, hy⟩, hAw⟩ := w.property
    change Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y = w.val at hy
    refine ⟨y, ?_, ?_⟩
    · rw [hy]
      exact hAw
    · simpa only [Rat.cast_intCast, ← integerRowLinear_apply, hy] using hw
  obtain ⟨z, hAz, haz, hzH, heH⟩ :=
    exists_bounded_joint_rational_section B A (fun i => (a i : ℚ)) hH hR hB hA haQ hconsistent
  let e := B *ᵥ z
  have heq : (fun i => (e i : ℝ)) =
      Matrix.of (fun i j => (B i j : ℝ)) *ᵥ (fun j => (z j : ℝ)) := by
    ext i
    simp [e, Matrix.mulVec, dotProduct]
  refine ⟨e, ⟨?_, ?_⟩, ?_, heH⟩
  · exact ⟨fun j => (z j : ℝ), heq.symm⟩
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ (fun i => (e i : ℝ)) = 0
    ext i
    have hi := congrArg (fun v : ρ → ℚ => (v i : ℝ)) hAz
    simpa [e, Matrix.mulVec, dotProduct] using hi
  · have hi := congrArg (fun q : ℚ => (q : ℝ)) haz
    simpa [e, integerRowLinear_apply, Matrix.mulVec, dotProduct] using hi

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem PolynomialRationalApproximation.homogeneous_decomposition
    {I : Type*} {T : I → ℝ} {R : ℝ} {h : ℕ} {P : MvPolynomial I ℝ}
    (happrox : PolynomialRationalApproximation T R P) (hP : P.IsHomogeneous h)
    (hT : ∀ i, 0 < T i) (hR : 0 ≤ R) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧
      ∃ (Q : MvPolynomial I ℤ) (E : MvPolynomial I ℝ),
        Q.IsHomogeneous h ∧ E.IsHomogeneous h ∧
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ R / monomialScale T α := by
  classical
  obtain ⟨D, hD, hDR, Q, hQ⟩ := happrox
  let Qtop := MvPolynomial.homogeneousComponent h Q
  let E := P - MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Qtop
  have hQtop : Qtop.IsHomogeneous h := MvPolynomial.homogeneousComponent_isHomogeneous _ _
  refine ⟨D, hD, hDR, Qtop, E, hQtop, hP.sub ((hQtop.map _).C_mul _),
    (sub_add_cancel P _).symm, ?_⟩
  intro α
  dsimp only [E]
  rw [MvPolynomial.coeff_sub, integerPolynomialQuotient_coeff]
  by_cases hα : α.degree = h
  · simpa only [Qtop, MvPolynomial.coeff_homogeneousComponent, if_pos hα] using hQ α
  · rw [hP.coeff_eq_zero hα]
    simp only [Qtop, MvPolynomial.coeff_homogeneousComponent, if_neg hα,
      Int.cast_zero, zero_div, sub_zero, abs_zero]
    exact div_nonneg hR (monomialScale_pos T hT α).le

namespace VectorPolynomial

open scoped TensorProduct

theorem samplingRankCut_homogeneous_split {I J : Type*} [Fintype J]
    (a : J → ℤ) (e : J → ℝ) (p : VectorPolynomial I ℝ (J → ℝ))
    {h : ℕ} {T : I → ℝ} {R : ℝ}
    (hp : DegreeLE (fun _ => 1) (h + 1) p) (hT : ∀ i, 0 < T i) (hR : 0 ≤ R)
    (happrox : PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent (h + 1) (integerRowPolynomial a p))) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧
      ∃ (Q : MvPolynomial I ℤ) (E l : MvPolynomial I ℝ),
        Q.IsHomogeneous (h + 1) ∧ E.IsHomogeneous (h + 1) ∧ l.totalDegree ≤ h ∧
        (∀ α, |E.coeff α| ≤ R / monomialScale T α) ∧
        p = map (samplingRankProjection a e) p + E ⊗ₜ[ℝ] e +
          (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q) ⊗ₜ[ℝ] e +
          l ⊗ₜ[ℝ] e := by
  classical
  obtain ⟨D, hD, hDR, Q, E, hQ, hE, htop, hcoeff⟩ :=
    happrox.homogeneous_decomposition (MvPolynomial.homogeneousComponent_isHomogeneous _ _) hT hR
  let l := integerRowPolynomial a (p - homogeneousPart (h + 1) p)
  have hl : l.totalDegree ≤ h :=
    integerRowPolynomial_totalDegree_le a (sub_homogeneousPart_degreeLE hp)
  have hrow : integerRowPolynomial a p =
      MvPolynomial.homogeneousComponent (h + 1) (integerRowPolynomial a p) + l := by
    ext α
    simp only [l, integerRowPolynomial, MvPolynomial.coeff_add,
      MvPolynomial.coeff_homogeneousComponent, coeff_coordinate, map_sub,
      Finsupp.sub_apply, coefficients_homogeneousPart]
    split_ifs <;> simp
  refine ⟨D, hD, hDR, Q, E, l, hQ, hE, hl, hcoeff, ?_⟩
  calc
    p = map (samplingRankProjection a e) p + integerRowPolynomial a p ⊗ₜ[ℝ] e :=
      samplingRankCut_decomposition a e p
    _ = _ := by
      rw [hrow, htop]
      simp only [TensorProduct.add_tmul]
      abel

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

theorem coefficients_substitute_mem {I K V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (f : I → MvPolynomial K ℝ) (p : VectorPolynomial I ℝ V)
    (hp : ∀ α, coefficients p α ∈ W) :
    ∀ α, coefficients (substitute f p) α ∈ W := by
  intro α
  rw [coefficients_substitute]
  exact W.sum_mem (fun β _ => W.smul_mem _ (hp β))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineRemainder
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem exists_integer_affine_remainder {I : Type*}
    (P : MvPolynomial I ℤ) (r : I → ℤ) (a : ℤ) :
    ∃ Q : MvPolynomial I ℤ,
      aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp⟩
  | add P S hP hS =>
    obtain ⟨Q, hQ⟩ := hP
    obtain ⟨T, hT⟩ := hS
    refine ⟨Q + T, ?_⟩
    simp only [map_add, hQ, hT]
    ring
  | mul_X P i hP =>
    obtain ⟨Q, hQ⟩ := hP
    refine ⟨Q * (C (r i) + C a * X i) + C (eval r P) * X i, ?_⟩
    simp only [map_mul, aeval_X, eval_X, hQ]
    ring

theorem exists_integer_affine_remainder_degree {I : Type*}
    (P : MvPolynomial I ℤ) (r : I → ℤ) {a : ℤ} (ha : a ≠ 0) :
    ∃ Q : MvPolynomial I ℤ,
      aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q ∧
      Q.totalDegree ≤ P.totalDegree := by
  obtain ⟨Q, hQ⟩ := exists_integer_affine_remainder P r a
  refine ⟨Q, hQ, ?_⟩
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hCa : (C a : MvPolynomial I ℤ) ≠ 0 := by simpa using ha
  have hprod : C a * Q = aeval (fun i => C (r i) + C a * X i) P - C (eval r P) := by
    rw [hQ]
    ring
  have hdeg : (aeval (fun i => C (r i) + C a * X i) P).totalDegree ≤ P.totalDegree := by
    have hf (i : I) : (C (r i) + C a * X i).totalDegree ≤ 1 := by
      apply (totalDegree_add _ _).trans
      simp only [max_le_iff, totalDegree_C]
      refine ⟨by omega, ?_⟩
      simpa only [totalDegree_C, totalDegree_X, zero_add] using totalDegree_mul (C a) (X i)
    simpa only [Nat.mul_one] using aeval_polynomial_totalDegree_le P _ le_rfl hf
  have hbound := (totalDegree_sub_C_le (aeval (fun i => C (r i) + C a * X i) P)
    (eval r P)).trans hdeg
  rwa [← hprod, totalDegree_mul_of_isDomain hCa hQ0, totalDegree_C, zero_add] at hbound

theorem integer_affine_remainder_eval {I : Type*}
    (P Q : MvPolynomial I ℤ) (r : I → ℤ) (a : ℤ)
    (hQ : aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q)
    (x : I → ℤ) : eval (fun i => r i + a * x i) P = eval r P + a * eval x Q := by
  have he := congrArg (aeval (R := ℤ) x) hQ
  rw [comp_aeval_apply] at he
  simpa only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply, aeval_eq_eval] using he

theorem exists_rational_affine_integer_remainder {I J : Type*} [Fintype J]
    (P : MvPolynomial I ℤ) (e : J → ℚ) {H : ℕ}
    (he : ∀ i, RationalHeightLE (e i) H) :
    ∃ d : ℕ, 0 < d ∧ d ≤ H ^ Fintype.card J ∧
      ∀ D : ℕ, 0 < D → ∀ r : I → ℤ, ∃ Q : J → MvPolynomial I ℤ,
        (∀ i, (Q i).totalDegree ≤ P.totalDegree) ∧
        ∀ (x : I → ℤ) (i : J),
          (eval (fun j => r j + (D * d : ℕ) * x j) P : ℝ) / D * (e i : ℝ) =
            (eval r P : ℝ) / D * (e i : ℝ) + (eval x (Q i) : ℝ) := by
  classical
  obtain ⟨d, hd, hdH, z, hz, _⟩ := exists_bounded_integer_array e he
  refine ⟨d, hd, hdH, ?_⟩
  intro D hD r
  have ha : ((D * d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD hd).ne'
  obtain ⟨Q, hQ, hdegree⟩ := exists_integer_affine_remainder_degree P r ha
  refine ⟨fun i => C (z i) * Q, ?_, ?_⟩
  · intro i
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hdegree)
  · intro x i
    have hvalue := integer_affine_remainder_eval P Q r ((D * d : ℕ) : ℤ) hQ x
    have hvalueR : (eval (fun j => r j + (D * d : ℕ) * x j) P : ℝ) =
        (eval r P : ℝ) + (D : ℝ) * d * (eval x Q : ℝ) := by exact_mod_cast hvalue
    have hzi : (z i : ℝ) = (d : ℝ) * (e i : ℝ) := by
      exact_mod_cast hz i
    rw [hvalueR, map_mul, eval_C, Int.cast_mul, hzi]
    have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralSlowSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_integral_slow_slice {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (N : I → ℕ) (P : MvPolynomial I ℤ) (E : MvPolynomial I ℝ) (e : J → ℚ)
    {s H D : ℕ} {R δ : ℝ} (hD : 0 < D) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hP : P.totalDegree ≤ s) (hE : E.totalDegree ≤ s)
    (he : ∀ i, RationalHeightLE (e i) H)
    (hcoeff : ∀ α, |E.coeff α| ≤ R / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let K := ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * R * Fintype.card I * s * H
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((D * H ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (q : ℕ) (A : ResidueBoxSlice N q) (Q : J → MvPolynomial I ℤ) (c : J → ℝ),
      0 < q ∧ q ≤ D * H ^ Fintype.card J ∧
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      (∀ i, (Q i).totalDegree ≤ s) ∧
      ∀ (j : ∀ i, Fin (A.length i)) (i : J),
        |(MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E -
            MvPolynomial.eval (fun v => (A.start v : ℝ)) E) * (e i : ℝ)| ≤ δ ∧
        MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E * (e i : ℝ) +
          (MvPolynomial.eval (fun v => ((A.point j v).val : ℤ)) P : ℝ) / D * (e i : ℝ) =
          c i + (MvPolynomial.eval (fun v => ((j v).val : ℤ)) (Q i) : ℝ) +
            (MvPolynomial.eval (fun v => ((A.point j v).val : ℝ)) E -
              MvPolynomial.eval (fun v => (A.start v : ℝ)) E) * (e i : ℝ) := by
  intro K ρ hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hKρ : K * ρ ≤ δ := by
    have hquot : ρ ≤ δ / (K + 1) := min_le_right _ _
    have hm := (le_div_iff₀ (by linarith : 0 < K + 1)).mp hquot
    nlinarith
  obtain ⟨d, hd, hdH, hrem⟩ := exists_rational_affine_integer_remainder P e he
  let q := D * d
  have hq : 0 < q := Nat.mul_pos hD hd
  have hqB : q ≤ D * H ^ Fintype.card J := Nat.mul_le_mul_left D hdH
  have hlargeq (i : I) : 4 * (q : ℝ) ≤ ρ * N i :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqB) (by norm_num)).trans (hlarge i)
  obtain ⟨A, hA, hscore, hslow⟩ :=
    exists_slowPolynomial_residueSlice N hq hρ hρ1 hR hlargeq E hE hcoeff f
  obtain ⟨Q, hQ, hQeval⟩ := hrem D hD (fun v => (A.start v : ℤ))
  let c : J → ℝ := fun i => MvPolynomial.eval (fun v => (A.start v : ℝ)) E * (e i : ℝ) +
    (MvPolynomial.eval (fun v => (A.start v : ℤ)) P : ℝ) / D * (e i : ℝ)
  refine ⟨q, A, Q, c, hq, hqB, hA, hscore, fun i => (hQ i).trans hP, ?_⟩
  intro j i
  constructor
  · rw [abs_mul]
    have hm := mul_le_mul (hslow j) (he i).abs_real_le (abs_nonneg _) (by positivity)
    apply (hm.trans_eq ?_).trans hKρ
    dsimp [K]
    ring
  · have hr := hQeval (fun v => ((j v).val : ℤ)) i
    have hpoint : (fun v => (A.start v : ℤ) + (D * d : ℕ) * ((j v).val : ℤ)) =
        (fun v => ((A.point j v).val : ℤ)) := by
      funext v
      simp only [ResidueBoxSlice.point, Nat.cast_add, Nat.cast_mul, q]
    rw [hpoint] at hr
    dsimp [c]
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem copiedLayerSpace_finrank {J K : Type*} [Fintype J] [Fintype K]
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    Module.finrank ℝ (copiedLayerSpace W V) = Module.finrank ℝ W + Module.finrank ℝ V := by
  rw [(copiedLayerSpaceEquiv W V).finrank_eq, Module.finrank_prod]

theorem copiedLayerSpace_line_finrank {J K : Type*} [Fintype J] [Fintype K]
    (W : Submodule ℝ (J → ℝ)) (e : K → ℝ) (he : e ≠ 0) :
    Module.finrank ℝ (copiedLayerSpace W (Submodule.span ℝ {e})) = Module.finrank ℝ W + 1 := by
  rw [copiedLayerSpace_finrank, finrank_span_singleton he]

theorem eval_copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) (x : I → ℝ) :
    eval x (copiedLayerPolynomial p q) = Sum.elim (eval x p) (eval x q) := by
  ext j
  cases j <;> simp [copiedLayerPolynomial, copyLeft, copyRight]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateCopySum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coordinateCopySum_sum {C D J R : Type*} [Fintype C] [Fintype D]
    [DecidableEq J] [CommRing R] (a : C → J) (b : D → J) (x : C → R) (y : D → R) :
    coordinateCopySum (Sum.elim a b) (Sum.elim x y) =
      coordinateCopySum a x + coordinateCopySum b y := by
  ext j
  simp only [coordinateCopySum_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply]
  rfl

theorem coordinateCopySum_abs_le {C J : Type*} [Fintype C] [DecidableEq J]
    (label : C → J) {x : C → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ c, |x c| ≤ δ) (j : J) :
    |coordinateCopySum label x j| ≤ Fintype.card C * δ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ c, |if label c = j then x c else 0|) ≤ ∑ _c : C, δ := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> simp_all
    _ = _ := by simp

theorem coordinateCopySum_map {C J R S : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] [CommRing S] (label : C → J) (f : R →+* S) (x : C → R) (j : J) :
    f (coordinateCopySum label x j) = coordinateCopySum label (fun c => f (x c)) j := by
  simp only [coordinateCopySum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem coordinateCopySum_polynomial_degree {C J I R : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] (label : C → J) (p : C → MvPolynomial I R) {d : ℕ}
    (hp : ∀ c, (p c).totalDegree ≤ d) (j : J) :
    (coordinateCopySum label p j).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro c _
  split_ifs
  · exact hp c
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem layerRankPotential_add {s : ℕ} (d e : Fin s → ℕ) :
    layerRankPotential (d + e) = layerRankPotential d + layerRankPotential e := by
  simp only [layerRankPotential, Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]

theorem layerRankPotential_mono {s : ℕ} {d e : Fin s → ℕ}
    (h : ∀ i, d i ≤ e i) : layerRankPotential d ≤ layerRankPotential e :=
  Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h i))

theorem layerRankPotential_single {s : ℕ} (i : Fin s) (n : ℕ) :
    layerRankPotential (Pi.single i n) = (i.val + 1) * n := by
  classical
  simp [layerRankPotential, Pi.single_apply]

theorem sum_ranks_le_potential {s : ℕ} (d : Fin s → ℕ) :
    ∑ i, d i ≤ layerRankPotential d := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem layerRankPotential_transfer {s : ℕ} (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1) {d e : Fin s → ℕ}
    (hstep : ∀ i, (e + Pi.single upper 1 : Fin s → ℕ) i ≤ (d + Pi.single lower 1 : Fin s → ℕ) i) :
    layerRankPotential e + 1 ≤ layerRankPotential d := by
  have h := layerRankPotential_mono hstep
  rw [layerRankPotential_add, layerRankPotential_add,
    layerRankPotential_single, layerRankPotential_single, Nat.mul_one, Nat.mul_one] at h
  omega

theorem layerRankPotential_absorb_constant {s : ℕ} (lowest : Fin s) (hlowest : lowest.val = 0)
    {d e : Fin s → ℕ} (hstep : ∀ i, (e + Pi.single lowest 1 : Fin s → ℕ) i ≤ d i) :
    layerRankPotential e + 1 ≤ layerRankPotential d := by
  have h := layerRankPotential_mono hstep
  simpa only [layerRankPotential_add, layerRankPotential_single, hlowest] using h

theorem layerRankPotential_initial {s : ℕ} (D : ℕ) :
    layerRankPotential (Pi.single (Fin.last s) D) = (s + 1) * D :=
  layerRankPotential_single (Fin.last s) D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationSizes
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem integerPolynomialQuotient_eval {I : Type*} (D : ℕ) (Q : MvPolynomial I ℤ)
    (x : I → ℤ) :
    MvPolynomial.eval (fun i => (x i : ℝ))
      (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q) =
      (MvPolynomial.eval x Q : ℝ) / D := by
  have he : (MvPolynomial.eval x Q : ℝ) =
      MvPolynomial.eval (fun i => (x i : ℝ)) (MvPolynomial.map (Int.castRingHom ℝ) Q) :=
    MvPolynomial.map_eval (Int.castRingHom ℝ) x Q
  rw [map_mul, MvPolynomial.eval_C, ← he]
  simp only [div_eq_mul_inv]
  ring

theorem exists_rankPreparationStep {I J C V : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) (p : VectorPolynomial I ℝ (J → ℝ))
    (N : I → ℕ) {H R h : ℕ} {δ : ℝ}
    (hH : 1 ≤ H) (hR : 1 ≤ R) (hδ : 0 < δ) (hN : ∀ i, 0 < N i)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (hp : DegreeLE (fun _ => 1) (h + 1) p)
    (hmem : ∀ α, coefficients p α ∈ jointRationalSpace B A)
    (hfail : ¬ HasLayerSamplingRank (h + 1) (fun i => (N i : ℝ)) R (jointRationalSpace B A) p)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let W := jointRationalSpace B A
    let He := rankCutDirectionHeight (Fintype.card J) (Fintype.card C) (Fintype.card V) H R
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (h + 1) *
      R * Fintype.card I * ((h + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : J → ℤ) (e : J → ℚ) (q : ℕ) (S : ResidueBoxSlice N q)
      (cut : VectorPolynomial I ℝ (J → ℝ)) (l E : MvPolynomial I ℝ)
      (integerPart : J → MvPolynomial I ℤ) (c : J → ℝ),
      cut = map (samplingRankProjection a (fun i => (e i : ℝ))) p ∧
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      (fun i => (e i : ℝ)) ∈ W ∧ integerRowLinear a (fun i => (e i : ℝ)) = 1 ∧
      (∀ α, coefficients cut α ∈ W ⊓ LinearMap.ker (integerRowLinear a)) ∧
      DegreeLE (fun _ => 1) (h + 1) cut ∧ l.totalDegree ≤ h ∧ E.totalDegree ≤ h + 1 ∧
      Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card J ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (S.length i)), f (S.point j)) ∧
      (∀ i, (integerPart i).totalDegree ≤ h + 1) ∧
      ∀ (j : ∀ i, Fin (S.length i)) (i : J),
        |(MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) E -
            MvPolynomial.eval (fun v => (S.start v : ℝ)) E) * (e i : ℝ)| ≤ δ ∧
        eval (fun v => ((S.point j v).val : ℝ)) p i =
          eval (fun v => ((S.point j v).val : ℝ)) cut i +
            MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) l * (e i : ℝ) +
            (MvPolynomial.eval (fun v => ((j v).val : ℤ)) (integerPart i) : ℝ) + c i +
            (MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) E -
              MvPolynomial.eval (fun v => (S.start v : ℝ)) E) * (e i : ℝ) := by
  classical
  intro W He K ρ hlarge
  simp only [HasLayerSamplingRank, not_forall, not_not] at hfail
  obtain ⟨a, ha, hrow, happrox⟩ := hfail
  obtain ⟨e, heW, hae, heH⟩ := exists_bounded_joint_rational_direction B A a hH hR hB hA ha
    (by simpa only [integerRowLinear_apply] using hrow)
  obtain ⟨D, hD, hDR, Q, E, l, hQ, hE, hl, hcoeff, hsplit⟩ :=
    samplingRankCut_homogeneous_split a (fun i => (e i : ℝ)) p hp
      (fun i => by exact_mod_cast hN i) (Nat.cast_nonneg R) happrox
  have hDRnat : D ≤ R := by exact_mod_cast hDR
  have hlargeD (i : I) : 4 * ((D * He ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.mul_le_mul_right _ hDRnat))
      (by norm_num)).trans (hlarge i)
  obtain ⟨q, S, integerPart, c, hq, hqbound, hlength, hscore, hdegree, hparts⟩ :=
    exists_integral_slow_slice N Q E e hD (Nat.cast_nonneg R) hδ hQ.totalDegree_le
      hE.totalDegree_le heH hcoeff f hlargeD
  let cut := map (samplingRankProjection a (fun i => (e i : ℝ))) p
  refine ⟨a, e, q, S, cut, l, E, integerPart, c, rfl, ha, heH, heW, hae, ?_, hp.map _, hl,
    hE.totalDegree_le, samplingRankCut_finrank_lt a _ W heW hae, hq,
    hqbound.trans (Nat.mul_le_mul_right _ hDRnat), hlength, hscore, hdegree, ?_⟩
  · intro α
    rw [coefficients_map]
    exact samplingRankProjection_mem a _ W heW hae (hmem α)
  · intro j i
    obtain ⟨herror, hparts⟩ := hparts j i
    refine ⟨herror, ?_⟩
    have hv := congrArg (fun t : VectorPolynomial I ℝ (J → ℝ) =>
      eval (fun v => ((S.point j v).val : ℝ)) t i) hsplit
    simp only [map_add, eval_tmul, MvPolynomial.aeval_eq_eval, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hv
    have hr := integerPolynomialQuotient_eval D Q (fun v => ((S.point j v).val : ℤ))
    simp only [Int.cast_natCast] at hr
    rw [hr] at hv
    change eval (fun v => ((S.point j v).val : ℝ)) p i = _ at hv
    dsimp only [cut]
    linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Matrix
open VectorPolynomial

attribute [instance] RankPreparationLayer.coordFinite RankPreparationLayer.columnFinite
  RankPreparationLayer.rowFinite

namespace RankPreparationLayer

variable {I J : Type}

theorem Valid.reindex {L : RankPreparationLayer I J} {d H R : ℕ}
    (hL : L.Valid d H R) (f : I → MvPolynomial I ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (L.reindex f).Valid d H R :=
  ⟨degreeLE_substitute_affine f hf L.poly hL.1,
    coefficients_substitute_mem L.space f L.poly hL.2.1, hL.2.2⟩

theorem reindex_value [DecidableEq J] (L : RankPreparationLayer I J)
    (f : I → MvPolynomial I ℝ) (x : I → ℝ) :
    (L.reindex f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) := by
  exact congrArg (coordinateCopySum L.label) (eval_substitute f x L.poly)

theorem cut_rank_lt (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ)
    (he : e ∈ L.space) (hae : integerRowLinear a e = 1) :
    (L.cut a e).rank < L.rank := by
  unfold rank
  rw [cut_space]
  exact samplingRankCut_finrank_lt a e L.space he hae

theorem appendLine_rank (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) (he : (fun i => (e i : ℝ)) ≠ 0) :
    (L.appendLine label e l).rank = L.rank + 1 := by
  unfold rank
  rw [appendLine_space]
  exact copiedLayerSpace_line_finrank L.space _ he

theorem appendLine_value [DecidableEq J] (L : RankPreparationLayer I J)
    {C : Type} [Fintype C] (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) (x : I → ℝ) :
    (L.appendLine label e l).value x =
      L.value x + coordinateCopySum label (MvPolynomial.aeval (R := ℝ) x l • fun i => (e i : ℝ)) := by
  unfold value
  change coordinateCopySum (Sum.elim L.label label)
    (eval x (copiedLayerPolynomial L.poly (l ⊗ₜ[ℝ] (fun i => (e i : ℝ))))) = _
  rw [eval_copiedLayerPolynomial, eval_tmul, coordinateCopySum_sum]

theorem initial_space [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).space = ⊤ := by
  change jointRationalSpace (1 : Matrix J J ℚ) (0 : Matrix PEmpty J ℚ) = ⊤
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) *ᵥ x = x
      have hcast : Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) = 1 := by
        ext i j
        simp only [Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hcast, Matrix.one_mulVec]
    · ext i
      exact i.elim

theorem initial_valid [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) {d H R : ℕ} (hH : 1 ≤ H)
    (hp : DegreeLE (fun _ => 1) d p) : (initial p).Valid d H R := by
  refine ⟨hp, ?_, ?_, ?_⟩
  · intro α
    rw [initial_space]
    trivial
  · change ∀ i j : J, RationalHeightLE ((1 : Matrix J J ℚ) i j) H
    intro i j
    change RationalHeightLE (if i = j then (1 : ℚ) else 0) H
    split_ifs
    · exact rationalHeightLE_one hH
    · exact rationalHeightLE_zero hH
  · intro i
    exact i.elim

@[simp] theorem initial_rank [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).rank = Fintype.card J := by
  unfold rank
  rw [initial_space]
  change Module.finrank ℝ (⊤ : Submodule ℝ (J → ℝ)) = Fintype.card J
  simp

end RankPreparationLayer
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem rankCutDirectionHeight_le_exp (ambient columns rows H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hr : (rows : ℝ) + 1 ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    (rankCutDirectionHeight ambient columns rows H R : ℝ) ≤ Real.exp ((p + 2) ^ 38) := by
  let Hsys := (ambient + 1) * (R * H) ^ ambient
  have hfront : (ambient : ℝ) + 1 ≤ Real.exp p :=
    (by linarith : (ambient : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hprod : (R : ℝ) * H ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using mul_le_mul hR hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hsys : (Hsys : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg H)) hprod ambient
    rw [← Real.exp_nat_mul] at hpow
    have htotal : (Hsys : ℝ) ≤ Real.exp (p + ambient * (2 * p)) := by
      dsimp only [Hsys]
      push_cast
      rw [Real.exp_add]
      exact mul_le_mul hfront hpow (by positivity) (Real.exp_nonneg _)
    apply htotal.trans (Real.exp_le_exp.mpr ?_)
    have hm := mul_le_mul_of_nonneg_right ha (show 0 ≤ 2 * p by positivity)
    nlinarith [show 0 ≤ p ^ 3 by positivity]
  have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by decide)
  have hker : (rationalKernelHeight (rows + 1) Hsys : ℝ) ≤ Real.exp ((p + 2) ^ 35) := by
    have h := rationalKernelHeight_le_budget (rows + 1) Hsys (by positivity : 0 ≤ (p + 2) ^ 3)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hr.trans hp3) hsys
    exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 3 7))
  have hp35 : p ≤ (p + 2) ^ 35 := le_power_budget hp (by decide)
  have hbase : (H : ℝ) * rationalKernelHeight (rows + 1) Hsys ≤ Real.exp ((p + 2) ^ 36) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + 2) ^ 35) :=
        mul_le_mul hH hker (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + (p + 2) ^ 35) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          p + (p + 2) ^ 35 ≤ 2 * (p + 2) ^ 35 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 35 := by gcongr; linarith
          _ = _ := by ring)
  have hpow : (((H * rationalKernelHeight (rows + 1) Hsys) ^ columns : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 37) := by
    push_cast
    apply (pow_le_pow_left₀ (by positivity) hbase columns).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (columns : ℝ) * (p + 2) ^ 36 ≤ (p + 2) * (p + 2) ^ 36 := by gcongr; linarith
      _ = _ := by ring
  have hcol : (columns : ℝ) + 1 ≤ Real.exp p :=
    (by linarith : (columns : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hp37 : p ≤ (p + 2) ^ 37 := le_power_budget hp (by decide)
  unfold rankCutDirectionHeight
  change (((columns + 1) * (H * rationalKernelHeight (rows + 1) Hsys) ^ columns : ℕ) : ℝ) ≤ _
  push_cast
  simp only [Nat.cast_pow, Nat.cast_mul] at hpow
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 37) := mul_le_mul hcol hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ 37) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      calc
        p + (p + 2) ^ 37 ≤ 2 * (p + 2) ^ 37 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 37 := by gcongr; linarith
        _ = _ := by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ}

theorem reindex_value [DecidableEq J] (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial I ℝ) (x : I → ℝ) :
    (L.reindex f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (L i).reindex_value f x

theorem descend_potential (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ)
    (he : (fun i => (e i : ℝ)) ∈ (L upper).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    (L.descend upper lower a e l).potential + 1 ≤ L.potential := by
  have hne : upper ≠ lower := by intro h; rw [h] at hlevel; omega
  have he0 : (fun i => (e i : ℝ)) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hae
    norm_num at hae
  apply layerRankPotential_transfer upper lower hlevel
  intro i
  by_cases hiu : i = upper
  · subst i
    have hd := (L upper).cut_rank_lt a (fun i => (e i : ℝ)) he hae
    simpa [descend, Pi.single_apply, hne] using hd
  · by_cases hil : i = lower
    · subst i
      simp [descend, Ne.symm hne,
        RankPreparationLayer.appendLine_rank _ _ _ _ he0]
    · simp [descend, hiu, hil]

theorem descend_valid (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hne : upper ≠ lower) (H : Fin s → ℕ) {R He : ℕ}
    (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R)
    (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) (heH : ∀ i, RationalHeightLE (e i) He)
    (he : (fun i => (e i : ℝ)) ∈ (L upper).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1)
    (hl : l.totalDegree ≤ lower.val + 1) :
    ∀ i, (L.descend upper lower a e l i).Valid (i.val + 1)
      (if i = lower then max (H i) He else H i) R := by
  intro i
  by_cases hiu : i = upper
  · subst i
    simpa [descend, hne] using
      (hL upper).cut hR a (fun i => (e i : ℝ)) ha he hae
  · by_cases hil : i = lower
    · subst i
      simpa [descend, Ne.symm hne] using
        (hL lower).appendLine (hH lower) hR (L upper).label e l heH hl
    · simpa [descend, hiu, hil] using hL i

theorem sum_replace_two {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V]
    (f : A → V) (u v : A) (hne : u ≠ v) (a b : V) :
    (∑ i, if i = u then a else if i = v then b else f i) =
      (∑ i, f i) + (a - f u) + (b - f v) := by
  calc
    _ = ∑ i, (f i + (if i = u then a - f u else 0) + (if i = v then b - f v else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiu : i = u
      · subst i
        simp [hne]
      · by_cases hiv : i = v
        · subst i
          simp [Ne.symm hne]
        · simp [hiu, hiv]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem descend_value [DecidableEq J] (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hne : upper ≠ lower) (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ)
    (l : MvPolynomial I ℝ) (x : I → ℝ) :
    (L.descend upper lower a e l).value x = L.value x +
      ((L upper).cut a (fun i => (e i : ℝ))).value x - (L upper).value x +
      coordinateCopySum (L upper).label
        (MvPolynomial.aeval (R := ℝ) x l • fun i => (e i : ℝ)) := by
  have ht := sum_replace_two (fun i => (L i).value x) upper lower hne
    (((L upper).cut a (fun i => (e i : ℝ))).value x)
    (((L lower).appendLine (L upper).label e l).value x)
  have hsum : (L.descend upper lower a e l).value x =
      ∑ i, if i = upper then ((L upper).cut a (fun i => (e i : ℝ))).value x
        else if i = lower then ((L lower).appendLine (L upper).label e l).value x
        else (L i).value x := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [descend]
    split_ifs <;> rfl
  rw [hsum, ht, RankPreparationLayer.appendLine_value]
  unfold value
  abel

theorem absorb_potential (L : RankPreparationFamily I J s) (lowest : Fin s)
    (hlowest : lowest.val = 0) (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
    (he : (fun i => (e i : ℝ)) ∈ (L lowest).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    (L.absorb lowest a e).potential + 1 ≤ L.potential := by
  apply layerRankPotential_absorb_constant lowest hlowest
  intro i
  by_cases hi : i = lowest
  · subst i
    have hd := (L lowest).cut_rank_lt a (fun i => (e i : ℝ)) he hae
    simpa [absorb, Pi.single_apply] using hd
  · simp [absorb, hi]

theorem absorb_valid (L : RankPreparationFamily I J s) (lowest : Fin s)
    (H : Fin s → ℕ) {R : ℕ} (hR : 1 ≤ R)
    (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R)
    (he : (fun i => (e i : ℝ)) ∈ (L lowest).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    ∀ i, (L.absorb lowest a e i).Valid (i.val + 1) (H i) R := by
  intro i
  by_cases hi : i = lowest
  · subst i
    simpa [absorb] using (hL lowest).cut hR a (fun i => (e i : ℝ)) ha he hae
  · simpa [absorb, hi] using hL i

theorem sum_replace_one {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V]
    (f : A → V) (u : A) (a : V) :
    (∑ i, if i = u then a else f i) = (∑ i, f i) + (a - f u) := by
  calc
    _ = ∑ i, (f i + if i = u then a - f u else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = u
      · subst i; simp
      · simp [hi]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem absorb_value [DecidableEq J] (L : RankPreparationFamily I J s) (lowest : Fin s)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) (x : I → ℝ) :
    (L.absorb lowest a e).value x = L.value x +
      ((L lowest).cut a (fun i => (e i : ℝ))).value x - (L lowest).value x := by
  have ht := sum_replace_one (fun i => (L i).value x) lowest
    (((L lowest).cut a (fun i => (e i : ℝ))).value x)
  have hsum : (L.absorb lowest a e).value x =
      ∑ i, if i = lowest then ((L lowest).cut a (fun i => (e i : ℝ))).value x else (L i).value x := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [absorb]
    split_ifs <;> rfl
  rw [hsum, ht]
  unfold value
  abel

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_descend_slice_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s : ℕ} (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1) (N : I → ℕ) (H : Fin s → ℕ)
    {R : ℕ} {δ : ℝ} (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (hfail : ¬ HasLayerSamplingRank (upper.val + 1) (fun i => (N i : ℝ)) R
      (L upper).space (L upper).poly) (f : (∀ i, Fin (N i)) → ℝ) :
    let He := rankCutDirectionHeight (Fintype.card (L upper).Coord)
      (Fintype.card (L upper).Column) (Fintype.card (L upper).Row) (H upper) R
    let K := (((upper.val + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (upper.val + 1) *
      R * Fintype.card I * ((upper.val + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card (L upper).Coord : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ)
      (q : ℕ) (S : ResidueBoxSlice N q) (l : MvPolynomial I ℝ)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      let L' := (L.descend upper lower a e l).reindex S.polynomial
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      L'.potential + 1 ≤ L.potential ∧
      (∀ i, (L' i).Valid (i.val + 1) (if i = lower then max (H i) He else H i) R) ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card (L upper).Coord ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ upper.val + 1) ∧
      (∀ x j, |err x j| ≤ Fintype.card (L upper).Coord * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro He K ρ hlarge
  have hne : upper ≠ lower := by intro h; rw [h] at hlevel; omega
  obtain ⟨a, e, q, S, cut, l, E, ip, c, hcut, ha, heH, heW, hae, hmem, hdeg, hl, hE,
    hrank, hq, hqbound, hlength, hscore, hip, hparts⟩ :=
    exists_rankPreparationStep (L upper).basis (L upper).rows (L upper).poly N
      (hH upper) hR hδ hN (hL upper).2.2.1 (hL upper).2.2.2
      (hL upper).1 (hL upper).2.1 hfail f hlarge
  let V := L.descend upper lower a e l
  let L' := V.reindex S.polynomial
  let ip' : J → MvPolynomial I ℤ := coordinateCopySum (L upper).label ip
  let c' : J → ℝ := coordinateCopySum (L upper).label c
  let er (x : ∀ i, Fin (S.length i)) (j : (L upper).Coord) : ℝ :=
    (MvPolynomial.eval (fun i => ((S.point x i).val : ℝ)) E -
      MvPolynomial.eval (fun i => (S.start i : ℝ)) E) * (e j : ℝ)
  let er' (x : ∀ i, Fin (S.length i)) : J → ℝ := coordinateCopySum (L upper).label (er x)
  refine ⟨a, e, q, S, l, ip', c', er', ha, heH, ?_, ?_, hq, hqbound, hlength, hscore, ?_, ?_, ?_⟩
  · exact L.descend_potential upper lower hlevel a e l heW hae
  · intro i
    exact (L.descend_valid upper lower hne H hH hR hL a e l ha heH heW hae
      (by omega) i).reindex S.polynomial S.polynomial_degree
  · exact coordinateCopySum_polynomial_degree (L upper).label ip hip
  · intro x j
    exact coordinateCopySum_abs_le (L upper).label hδ.le (fun i => (hparts x i).1) j
  · intro x j
    let y : I → ℝ := fun i => ((S.point x i).val : ℝ)
    have hv : eval y (L upper).poly = eval y cut +
        MvPolynomial.eval y l • (fun i => (e i : ℝ)) +
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) + c + er x := by
      ext i
      exact (hparts x i).2
    have hcopy := congrArg (coordinateCopySum (L upper).label) hv
    simp only [map_add] at hcopy
    have hint : (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) =
        coordinateCopySum (L upper).label
          (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j :=
      coordinateCopySum_map (L upper).label
        ((Int.castRingHom ℝ).comp (MvPolynomial.eval (fun v => ((x v).val : ℤ)))) ip j
    have hnew : L'.value (fun i => ((x i).val : ℝ)) = V.value y := by
      exact (reindex_value V S.polynomial _).trans (by simp only [ResidueBoxSlice.polynomial_eval]; rfl)
    have hdesc := L.descend_value upper lower hne a e l y
    rw [hcut] at hcopy
    have hcopyj := congrFun hcopy j
    have hdescj := congrFun hdesc j
    change L.value y j = L'.value (fun i => ((x i).val : ℝ)) j + _ + _ + _
    rw [hnew, hint]
    change (L upper).value y j =
      ((L upper).cut a (fun i => (e i : ℝ))).value y j +
      coordinateCopySum (L upper).label (MvPolynomial.eval y l • fun i => (e i : ℝ)) j +
      coordinateCopySum (L upper).label
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j + c' j + er' x j at hcopyj
    simp only [Pi.add_apply, Pi.sub_apply, MvPolynomial.aeval_eq_eval] at hdescj
    dsimp only [V] at *
    linarith

theorem exists_absorb_slice_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s : ℕ} (L : RankPreparationFamily I J s) (lowest : Fin s)
    (hlowest : lowest.val = 0) (N : I → ℕ) (H : Fin s → ℕ)
    {R : ℕ} {δ : ℝ} (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (hfail : ¬ HasLayerSamplingRank (lowest.val + 1) (fun i => (N i : ℝ)) R
      (L lowest).space (L lowest).poly) (f : (∀ i, Fin (N i)) → ℝ) :
    let He := rankCutDirectionHeight (Fintype.card (L lowest).Coord)
      (Fintype.card (L lowest).Column) (Fintype.card (L lowest).Row) (H lowest) R
    let K := (((lowest.val + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (lowest.val + 1) *
      R * Fintype.card I * ((lowest.val + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card (L lowest).Coord : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
      (q : ℕ) (S : ResidueBoxSlice N q)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      let L' := (L.absorb lowest a e).reindex S.polynomial
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      L'.potential + 1 ≤ L.potential ∧
      (∀ i, (L' i).Valid (i.val + 1) (H i) R) ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card (L lowest).Coord ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ lowest.val + 1) ∧
      (∀ x j, |err x j| ≤ Fintype.card (L lowest).Coord * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro He K ρ hlarge
  obtain ⟨a, e, q, S, cut, l, E, ip, c, hcut, ha, heH, heW, hae, hmem, hdeg, hl, hE,
    hrank, hq, hqbound, hlength, hscore, hip, hparts⟩ :=
    exists_rankPreparationStep (L lowest).basis (L lowest).rows (L lowest).poly N
      (hH lowest) hR hδ hN (hL lowest).2.2.1 (hL lowest).2.2.2
      (hL lowest).1 (hL lowest).2.1 hfail f hlarge
  have hconst : l = MvPolynomial.C (l.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega)
  let V := L.absorb lowest a e
  let L' := V.reindex S.polynomial
  let ip' : J → MvPolynomial I ℤ := coordinateCopySum (L lowest).label ip
  let c' : J → ℝ := coordinateCopySum (L lowest).label ((l.coeff 0) • (fun i => (e i : ℝ)) + c)
  let er (x : ∀ i, Fin (S.length i)) (j : (L lowest).Coord) : ℝ :=
    (MvPolynomial.eval (fun i => ((S.point x i).val : ℝ)) E -
      MvPolynomial.eval (fun i => (S.start i : ℝ)) E) * (e j : ℝ)
  let er' (x : ∀ i, Fin (S.length i)) : J → ℝ := coordinateCopySum (L lowest).label (er x)
  refine ⟨a, e, q, S, ip', c', er', ha, heH, ?_, ?_, hq, hqbound, hlength, hscore, ?_, ?_, ?_⟩
  · exact L.absorb_potential lowest hlowest a e heW hae
  · intro i
    exact (L.absorb_valid lowest H hR hL a e ha heW hae i).reindex S.polynomial S.polynomial_degree
  · exact coordinateCopySum_polynomial_degree (L lowest).label ip hip
  · intro x j
    exact coordinateCopySum_abs_le (L lowest).label hδ.le (fun i => (hparts x i).1) j
  · intro x j
    let y : I → ℝ := fun i => ((S.point x i).val : ℝ)
    have hv : eval y (L lowest).poly = eval y cut +
        MvPolynomial.eval y l • (fun i => (e i : ℝ)) +
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) + c + er x := by
      ext i
      exact (hparts x i).2
    have hel : MvPolynomial.eval y l = l.coeff 0 := by
      conv_lhs => rw [hconst]
      rw [MvPolynomial.eval_C]
    rw [hel] at hv
    have hcopy := congrArg (coordinateCopySum (L lowest).label) hv
    simp only [map_add] at hcopy
    have hint : (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) =
        coordinateCopySum (L lowest).label
          (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j :=
      coordinateCopySum_map (L lowest).label
        ((Int.castRingHom ℝ).comp (MvPolynomial.eval (fun v => ((x v).val : ℤ)))) ip j
    have hnew : L'.value (fun i => ((x i).val : ℝ)) = V.value y := by
      exact (reindex_value V S.polynomial _).trans (by simp only [ResidueBoxSlice.polynomial_eval]; rfl)
    have habs := L.absorb_value lowest a e y
    rw [hcut] at hcopy
    have hcopyj := congrFun hcopy j
    have habsj := congrFun habs j
    change L.value y j = L'.value (fun i => ((x i).val : ℝ)) j + _ + _ + _
    rw [hnew, hint]
    change (L lowest).value y j =
      ((L lowest).cut a (fun i => (e i : ℝ))).value y j +
      coordinateCopySum (L lowest).label ((l.coeff 0) • fun i => (e i : ℝ)) j +
      coordinateCopySum (L lowest).label
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j +
      coordinateCopySum (L lowest).label c j + er' x j at hcopyj
    simp only [Pi.add_apply, Pi.sub_apply] at habsj
    dsimp only [V, c'] at *
    simp only [map_add, Pi.add_apply]
    linarith

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

variable {I J : Type} {s : ℕ}

theorem Sized.reindex {L : RankPreparationFamily I J s} {D t : ℕ}
    (h : L.Sized D t) (f : I → MvPolynomial I ℝ) : (L.reindex f).Sized D t := h

theorem copy_power_step (a d : ℕ) : a ^ (d + 1) + a ^ d ≤ (a + 1) ^ (d + 1) := by
  calc
    a ^ (d + 1) + a ^ d = a ^ d * (a + 1) := by rw [pow_succ]; ring
    _ ≤ (a + 1) ^ d * (a + 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := (pow_succ _ _).symm

theorem Sized.descend {L : RankPreparationFamily I J s} {D t : ℕ} (h : L.Sized D t)
    (upper lower : Fin s) (hlevel : upper.val = lower.val + 1)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ) :
    (L.descend upper lower a e l).Sized D (t + 1) := by
  have hne : upper ≠ lower := by intro heq; rw [heq] at hlevel; omega
  have hmono := h.mono (Nat.le_succ t)
  intro i
  by_cases hiu : i = upper
  · subst i
    simp only [RankPreparationFamily.descend, ↓reduceIte]
    change Fintype.card (L upper).Coord ≤ _ ∧ Fintype.card (L upper).Column ≤ _ ∧
      Fintype.card (Option (L upper).Row) ≤ _
    exact ⟨(hmono upper).1, (hmono upper).2.1, by simpa using Nat.add_le_add_right (h upper).2.2 1⟩
  · by_cases hil : i = lower
    · subst i
      simp only [RankPreparationFamily.descend, hiu, ↓reduceIte]
      change Fintype.card ((L lower).Coord ⊕ (L upper).Coord) ≤ _ ∧
        Fintype.card (Option (L lower).Column) ≤ _ ∧ Fintype.card (L lower).Row ≤ _
      have hd : s - 1 - lower.val = (s - 1 - upper.val) + 1 := by omega
      refine ⟨?_, ?_, (hmono lower).2.2⟩
      · rw [Fintype.card_sum]
        calc
          _ ≤ D * (t + 1) ^ (s - 1 - lower.val) + D * (t + 1) ^ (s - 1 - upper.val) :=
            Nat.add_le_add (h lower).1 (h upper).1
          _ = D * ((t + 1) ^ ((s - 1 - upper.val) + 1) + (t + 1) ^ (s - 1 - upper.val)) := by
            rw [hd, Nat.mul_add]
          _ ≤ D * (t + 1 + 1) ^ ((s - 1 - upper.val) + 1) :=
            Nat.mul_le_mul_left D (copy_power_step _ _)
          _ = _ := by rw [hd]
      · rw [Fintype.card_option]
        have hb := (h lower).2.1
        omega
    · simpa only [RankPreparationFamily.descend, hiu, hil, ↓reduceIte] using hmono i

theorem Sized.absorb {L : RankPreparationFamily I J s} {D t : ℕ} (h : L.Sized D t)
    (lowest : Fin s) (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) :
    (L.absorb lowest a e).Sized D (t + 1) := by
  have hmono := h.mono (Nat.le_succ t)
  intro i
  by_cases hi : i = lowest
  · subst i
    simp only [RankPreparationFamily.absorb, ↓reduceIte]
    change Fintype.card (L lowest).Coord ≤ _ ∧ Fintype.card (L lowest).Column ≤ _ ∧
      Fintype.card (Option (L lowest).Row) ≤ _
    exact ⟨(hmono lowest).1, (hmono lowest).2.1, by simpa using Nat.add_le_add_right (h lowest).2.2 1⟩
  · simpa only [RankPreparationFamily.absorb, hi, ↓reduceIte] using hmono i

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem rankCutDirectionHeight_le_preparationHeight (ambient columns rows H R depth : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hr : (rows : ℝ) + 1 ≤ p) (hH : H ≤ preparationHeight p depth)
    (hR : (R : ℝ) ≤ Real.exp p) :
    rankCutDirectionHeight ambient columns rows H R ≤ preparationHeight p (depth + 1) := by
  have hpq := le_power_budget hp (preparationExponent_pos depth)
  have hHp : (H : ℝ) ≤ Real.exp ((p + 2) ^ budgetDepthExponent 38 depth) :=
    (Nat.cast_le.mpr hH).trans (preparationHeight_le_exp p depth)
  have hbound := rankCutDirectionHeight_le_exp ambient columns rows H R
    (by positivity : 0 ≤ (p + 2) ^ budgetDepthExponent 38 depth)
    (ha.trans hpq) (hc.trans hpq) (hr.trans hpq) hHp
    (hR.trans (Real.exp_le_exp.mpr hpq))
  apply Nat.le_floor
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  exact shifted_power_budget_le hp (budgetDepthExponent 38 depth) 38

end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

theorem initial_potential (p : VectorPolynomial I ℝ (J → ℝ)) :
    (initial (j := j) p).potential = (j + 1) * Fintype.card J := by
  have hr : (fun i => (initial (j := j) p i).rank) = Pi.single (Fin.last j) (Fintype.card J) := by
    funext i
    by_cases hi : i = Fin.last j
    · subst i; simp [initial]
    · simp [initial, hi]
  unfold potential
  rw [hr, layerRankPotential_initial]

theorem initial_value (p : VectorPolynomial I ℝ (J → ℝ)) (x : I → ℝ) :
    (initial (j := j) p).value x = eval x p := by
  have hv (i : Fin (j + 1)) : (initial p i).value x = if i = Fin.last j then eval x p else 0 := by
    by_cases hi : i = Fin.last j <;> simp [initial, hi]
  unfold value
  simp only [hv, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem initial_sized (p : VectorPolynomial I ℝ (J → ℝ)) :
    (initial (j := j) p).Sized (Fintype.card J) 0 := by
  intro i
  by_cases hi : i = Fin.last j
  · simp only [initial, hi, ite_true]
    change Fintype.card J ≤ _ ∧ Fintype.card J ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp
  · simp only [initial, hi, ite_false]
    change Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp

theorem initial_heights (p : VectorPolynomial I ℝ (J → ℝ))
    {budget : ℝ} {R : ℕ} (hbudget : 0 ≤ budget) (hp : DegreeLE (fun _ => 1) (j + 1) p) :
    (initial (j := j) p).PreparedHeights budget R := by
  intro i
  by_cases hi : i = Fin.last j
  · subst i
    simpa only [initial, ite_true, Fin.val_last] using
      RankPreparationLayer.initial_valid p (preparationHeight_pos hbudget _) hp
  · simpa only [initial, hi, ite_false] using
      (RankPreparationLayer.empty_valid (I := I) (J := J) (i.val + 1)
        (preparationHeight budget (j + 1 - 1 - i.val)) R)

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationShrink_one_le (s n M : ℕ) {R : ℕ} {p δ : ℝ}
    (hR : 1 ≤ R) (hp : 0 ≤ p) (hδ : 0 < δ) :
    1 ≤ preparationShrink s n M R p δ := by
  have hheight := preparationHeight_pos hp s
  have hQ : 1 ≤ preparationModulusCap s M R p := by
    exact Nat.mul_pos hR (pow_pos hheight M)
  have hρ : 0 < min 1 (δ / (preparationOscillationCap s n R p + 1)) := by positivity
  apply (le_div_iff₀ hρ).mpr
  have hQreal : (1 : ℝ) ≤ preparationModulusCap s M R p := by exact_mod_cast hQ
  have hρle := min_le_left (1 : ℝ) (δ / (preparationOscillationCap s n R p + 1))
  nlinarith

theorem preparation_section_bound {I J : Type} {s M R : ℕ} {p : ℝ}
    (L : RankPreparationFamily I J s) (i : Fin s) (hp : 0 ≤ p)
    (hM : (M : ℝ) ≤ p) (hR : (R : ℝ) ≤ Real.exp p)
    (hcoords : Fintype.card (L i).Coord ≤ M)
    (hcols : Fintype.card (L i).Column ≤ M) (hrows : Fintype.card (L i).Row + 1 ≤ M) :
    let He := rankCutDirectionHeight (Fintype.card (L i).Coord)
      (Fintype.card (L i).Column) (Fintype.card (L i).Row)
      (preparationHeight p (s - 1 - i.val)) R
    He ≤ preparationHeight p ((s - 1 - i.val) + 1) ∧ He ≤ preparationHeight p s := by
  intro He
  have he : He ≤ preparationHeight p ((s - 1 - i.val) + 1) :=
    rankCutDirectionHeight_le_preparationHeight _ _ _ _ _ _ hp
      ((Nat.cast_le.mpr hcoords).trans hM) ((Nat.cast_le.mpr hcols).trans hM)
      (by exact_mod_cast (Nat.cast_le.mpr hrows).trans hM) le_rfl hR
  exact ⟨he, he.trans (preparationHeight_mono hp (by omega))⟩

theorem preparation_step_caps (s n M R h He c : ℕ) {p δ : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M) :
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) * R * n * ((h + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    let ρ₀ := min 1 (δ / (preparationOscillationCap s n R p + 1))
    R * He ^ c ≤ preparationModulusCap s M R p ∧ 0 < ρ₀ ∧ ρ₀ ≤ ρ := by
  intro K ρ ρ₀
  have hheight := preparationHeight_pos hp s
  have hq : He ^ c ≤ preparationHeight p s ^ M :=
    (Nat.pow_le_pow_left he c).trans (Nat.pow_le_pow_right hheight hc)
  have hKnat : (h + 1 + 1) * (n + 1) ^ (h + 1) * R * n * (h + 1) * He ≤
      preparationOscillationCap s n R p := by
    unfold preparationOscillationCap
    gcongr <;> omega
  have hK : K ≤ preparationOscillationCap s n R p := by
    dsimp only [K]
    exact_mod_cast hKnat
  refine ⟨Nat.mul_le_mul_left R hq, by dsimp [ρ₀]; positivity, ?_⟩
  apply min_le_min_left 1
  exact div_le_div_of_nonneg_left hδ.le (by dsimp [K]; positivity) (by linarith)

theorem preparation_large_side {s n M R h He c : ℕ} {p δ N : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M)
    (hN : preparationShrink s n M R p δ ≤ N) :
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) * R * n * ((h + 1 : ℕ) : ℝ) * He
    4 * ((R * He ^ c : ℕ) : ℝ) ≤ min 1 (δ / (K + 1)) * N := by
  intro K
  obtain ⟨hq, hρ, hρle⟩ := preparation_step_caps s n M R h He c hp hδ hh he hc
  have hQ0 : 0 ≤ (4 : ℝ) * preparationModulusCap s M R p := by positivity
  have hN0 : 0 ≤ N := (div_nonneg hQ0 hρ.le).trans hN
  have hl := (div_le_iff₀ hρ).mp hN
  have hqr : ((R * He ^ c : ℕ) : ℝ) ≤ preparationModulusCap s M R p := Nat.cast_le.mpr hq
  have hm := mul_le_mul_of_nonneg_right hρle hN0
  nlinarith

theorem preparation_side_loss {s n M R h He c q len : ℕ} {p δ N : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M) (hq : q ≤ R * He ^ c)
    (hN : 0 ≤ N)
    (hlen : min 1 (δ / ((((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) *
      R * n * ((h + 1 : ℕ) : ℝ) * He + 1)) * N ≤ 4 * q * len) :
    N ≤ preparationShrink s n M R p δ * len := by
  obtain ⟨hQ, hρ, hρle⟩ := preparation_step_caps s n M R h He c hp hδ hh he hc
  have hm := mul_le_mul_of_nonneg_right hρle hN
  have hqr : (q : ℝ) ≤ preparationModulusCap s M R p := Nat.cast_le.mpr (hq.trans hQ)
  have hlen0 : (0 : ℝ) ≤ len := Nat.cast_nonneg _
  have hb : min 1 (δ / (preparationOscillationCap s n R p + 1)) * N ≤
      (4 * preparationModulusCap s M R p) * len := by nlinarith
  dsimp only [preparationShrink]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hρ).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparationSliceComposition
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

theorem integerPolynomial_degree (S : ResidueBoxSlice N q) (i : I) :
    (S.integerPolynomial i).totalDegree ≤ 1 := by
  dsimp only [integerPolynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

theorem reindexInteger_degree (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ) {d : ℕ}
    (hP : P.totalDegree ≤ d) : (S.reindexInteger P).totalDegree ≤ d := by
  exact (aeval_polynomial_totalDegree_le P S.integerPolynomial hP S.integerPolynomial_degree).trans_eq
    (Nat.mul_one d)

end ResidueBoxSlice

namespace RankPreparationFamily

theorem compose_slice_identity {I J : Type} [Fintype I] [DecidableEq J] {s : ℕ}
    {L L' L'' : RankPreparationFamily I J s} {N : I → ℕ} {q r : ℕ}
    (S : ResidueBoxSlice N q) (T : ResidueBoxSlice S.length r)
    (ip ip' : J → MvPolynomial I ℤ) (c c' : J → ℝ)
    (err : (∀ i, Fin (S.length i)) → J → ℝ) (err' : (∀ i, Fin (T.length i)) → J → ℝ)
    (hS : ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
      L'.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j)
    (hT : ∀ x j, L'.value (fun i => ((T.point x i).val : ℝ)) j =
      L''.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) + c' j + err' x j) :
    ∀ x j, L.value (fun i => (((S.comp T).point x i).val : ℝ)) j =
      L''.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (T.reindexInteger (ip j) + ip' j) : ℝ) +
      (c j + c' j) + (err (T.point x) j + err' x j) := by
  intro x j
  change (∀ i, Fin (T.length i)) at x
  rw [ResidueBoxSlice.comp_point, hS, hT, map_add, Int.cast_add, ResidueBoxSlice.reindexInteger_eval]
  ring

end RankPreparationFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationIteration
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_uniform_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s D t T R : ℕ} {p δ : ℝ} (L : RankPreparationFamily I J s) (N : I → ℕ)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (ht : t ≤ T) (hsize : L.Sized D t) (hheight : L.PreparedHeights p R)
    (hM : (preparationCoordinateCap s D T : ℝ) ≤ p)
    (hbad : ¬ ∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (N i : ℝ)) R (L u).space (L u).poly)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let M := preparationCoordinateCap s D T
    let Q := preparationModulusCap s M R p
    let C := preparationShrink s (Fintype.card I) M R p δ
    (∀ i, C ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L' : RankPreparationFamily I J s)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      L'.potential + 1 ≤ L.potential ∧ L'.Sized D (t + 1) ∧ L'.PreparedHeights p R ∧
      0 < q ∧ q ≤ Q ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ s) ∧ (∀ x j, |err x j| ≤ M * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro M Q C hlarge
  have hC := preparationShrink_one_le s (Fintype.card I) M hR hp hδ
  have hN (i : I) : 0 < N i := by
    have h := hC.trans (hlarge i)
    exact_mod_cast h
  push Not at hbad
  obtain ⟨u, hfail⟩ := hbad
  obtain ⟨hcoord, hcol, hrow⟩ := preparationCoordinateCap_bounds hsize ht u
  let He := rankCutDirectionHeight (Fintype.card (L u).Coord) (Fintype.card (L u).Column)
    (Fintype.card (L u).Row) (preparationHeight p (s - 1 - u.val)) R
  obtain ⟨heNext, heGlobal⟩ := preparation_section_bound L u hp hM hRp hcoord hcol hrow
  have hlargeStep (i : I) := preparation_large_side hp hδ (Nat.succ_le_of_lt u.isLt)
    heGlobal hcoord (hlarge i)
  have hcaps := preparation_step_caps s (Fintype.card I) M R u.val He
    (Fintype.card (L u).Coord) hp hδ (Nat.succ_le_of_lt u.isLt) heGlobal hcoord
  by_cases hu : u.val = 0
  · obtain ⟨a, e, q, S, ip, c, err, ha, heH, hpotential, hvalid, hq, hqbound, hlength,
      hscore, hip, herr, hid⟩ := exists_absorb_slice_step L u hu N
        (fun i => preparationHeight p (s - 1 - i.val)) (fun _ => preparationHeight_pos hp _)
        hR hδ hN hheight hfail f hlargeStep
    let L' := (L.absorb u a e).reindex S.polynomial
    refine ⟨q, S, L', ip, c, err, hpotential, (hsize.absorb u a e).reindex S.polynomial,
      hvalid, hq, hqbound.trans hcaps.1, ?_, hscore, ?_, ?_, hid⟩
    · intro i
      exact ⟨(hlength i).1, preparation_side_loss hp hδ (Nat.succ_le_of_lt u.isLt)
        heGlobal hcoord hqbound (Nat.cast_nonneg _) (hlength i).2⟩
    · intro j
      exact (hip j).trans (Nat.succ_le_of_lt u.isLt)
    · intro x j
      exact (herr x j).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcoord) hδ.le)
  · let v : Fin s := ⟨u.val - 1, by omega⟩
    have hlevel : u.val = v.val + 1 := by dsimp [v]; omega
    obtain ⟨a, e, q, S, l, ip, c, err, ha, heH, hpotential, hvalid, hq, hqbound, hlength,
      hscore, hip, herr, hid⟩ := exists_descend_slice_step L u v hlevel N
        (fun i => preparationHeight p (s - 1 - i.val)) (fun _ => preparationHeight_pos hp _)
        hR hδ hN hheight hfail f hlargeStep
    let L' := (L.descend u v a e l).reindex S.polynomial
    refine ⟨q, S, L', ip, c, err, hpotential,
      (hsize.descend u v hlevel a e l).reindex S.polynomial, ?_, hq,
      hqbound.trans hcaps.1, ?_, hscore, ?_, ?_, hid⟩
    · intro i
      apply (hvalid i).mono_height
      split_ifs with hi
      · subst i
        apply max_le le_rfl
        have hd : s - 1 - v.val = (s - 1 - u.val) + 1 := by omega
        rwa [hd]
      · exact le_rfl
    · intro i
      exact ⟨(hlength i).1, preparation_side_loss hp hδ (Nat.succ_le_of_lt u.isLt)
        heGlobal hcoord hqbound (Nat.cast_nonneg _) (hlength i).2⟩
    · intro j
      exact (hip j).trans (Nat.succ_le_of_lt u.isLt)
    · intro x j
      exact (herr x j).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcoord) hδ.le)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_family {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s D t T R : ℕ} {p δ : ℝ} (r : ℕ) (L : RankPreparationFamily I J s) (N : I → ℕ)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (hpot : L.potential ≤ r) (ht : t + r ≤ T)
    (hsize : L.Sized D t) (hheight : L.PreparedHeights p R)
    (hM : (preparationCoordinateCap s D T : ℝ) ≤ p)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let M := preparationCoordinateCap s D T
    let Q := preparationModulusCap s M R p
    let C := preparationShrink s (Fintype.card I) M R p δ
    (∀ i, C ^ (r + 1) ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L' : RankPreparationFamily I J s)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      L'.potential ≤ L.potential ∧ L'.Sized D (t + r) ∧ L'.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L' u).space (L' u).poly) ∧
      0 < q ∧ q ≤ Q ^ r ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C ^ r * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ s) ∧ (∀ x j, |err x j| ≤ r * M * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro M Q C hlarge
  induction r using Nat.strong_induction_on generalizing t L N with
  | h r ih =>
    have hC : 1 ≤ C := preparationShrink_one_le s (Fintype.card I) M hR hp hδ
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hQ : 1 ≤ Q := Nat.mul_pos hR (pow_pos (preparationHeight_pos hp s) M)
    have hN (i : I) : 0 < N i := by
      have hn : (1 : ℝ) ≤ N i := (one_le_pow₀ hC).trans (hlarge i)
      exact_mod_cast hn
    by_cases hgood : ∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (N i : ℝ)) R (L u).space (L u).poly
    · refine ⟨1, ResidueBoxSlice.identity N, L, fun _ => 0, fun _ => 0, fun _ _ => 0,
        le_rfl, hsize.mono (Nat.le_add_right t r), hheight, hgood, by omega,
        one_le_pow₀ hQ, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine ⟨hN i, ?_⟩
        exact le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_pow₀ hC)
      · change (𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (N i)), f ((ResidueBoxSlice.identity N).point x)
        simp only [ResidueBoxSlice.identity_point, le_refl]
      · intro j
        simp
      · intro x j
        simp only [abs_zero]
        positivity
      · intro x j
        change (∀ i, Fin (N i)) at x
        simp only [ResidueBoxSlice.identity_point, map_zero, Int.cast_zero, add_zero]
    · have hside (i : I) : C ≤ N i := by
        have hpow : C ≤ C ^ (r + 1) := by
          simpa only [pow_one] using pow_le_pow_right₀ hC (Nat.le_add_left 1 r)
        exact hpow.trans (hlarge i)
      obtain ⟨q₁, S₁, L₁, ip₁, c₁, e₁, hdrop, hsize₁, hheight₁, hq₁, hq₁bound,
        hlength₁, hscore₁, hip₁, he₁, hid₁⟩ :=
        exists_uniform_step L N hp hR hRp hδ (by omega) hsize hheight hM hgood f hside
      have hr : 0 < r := by omega
      obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
      subst r
      have hnext (i : I) : C ^ (r' + 1) ≤ S₁.length i := by
        apply le_of_mul_le_mul_left (a := C) _ hCpos
        calc
          C * C ^ (r' + 1) = C ^ (r' + 1 + 1) := by rw [pow_succ]; ring
          _ ≤ N i := hlarge i
          _ ≤ C * S₁.length i := (hlength₁ i).2
      obtain ⟨q₂, S₂, L₂, ip₂, c₂, e₂, hpot₂, hsize₂, hheight₂, hgood₂, hq₂,
        hq₂bound, hlength₂, hscore₂, hip₂, he₂, hid₂⟩ :=
        ih r' (Nat.lt_succ_self r') L₁ S₁.length (by omega) (by omega) hsize₁ hheight₁
          (fun x => f (S₁.point x)) hnext
      refine ⟨q₁ * q₂, S₁.comp S₂, L₂,
        fun j => S₂.reindexInteger (ip₁ j) + ip₂ j, fun j => c₁ j + c₂ j,
        fun x j => e₁ (S₂.point x) j + e₂ x j,
        hpot₂.trans (by omega), ?_, hheight₂, hgood₂, Nat.mul_pos hq₁ hq₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · convert hsize₂ using 1; omega
      · calc
          q₁ * q₂ ≤ Q * Q ^ r' := Nat.mul_le_mul hq₁bound hq₂bound
          _ = Q ^ (r' + 1) := by rw [pow_succ]; ring
      · intro i
        refine ⟨(hlength₂ i).1, ?_⟩
        calc
          (N i : ℝ) ≤ C * S₁.length i := (hlength₁ i).2
          _ ≤ C * (C ^ r' * S₂.length i) := mul_le_mul_of_nonneg_left (hlength₂ i).2 hCpos.le
          _ = C ^ (r' + 1) * (S₁.comp S₂).length i := by
            change C * (C ^ r' * (S₂.length i : ℝ)) = C ^ (r' + 1) * S₂.length i
            rw [pow_succ]
            ring
      · change (𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S₂.length i)), f ((S₁.comp S₂).point x)
        simpa only [ResidueBoxSlice.comp_point] using hscore₁.trans hscore₂
      · intro j
        exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le (S₂.reindexInteger_degree _ (hip₁ j)) (hip₂ j))
      · intro x j
        calc
          |e₁ (S₂.point x) j + e₂ x j| ≤ |e₁ (S₂.point x) j| + |e₂ x j| := abs_add_le _ _
          _ ≤ M * δ + r' * M * δ := add_le_add (he₁ _ _) (he₂ _ _)
          _ = (r' + 1 : ℕ) * M * δ := by push_cast; ring
      · exact compose_slice_identity S₁ S₂ ip₁ ip₂ c₁ c₂ e₁ e₂ hid₁ hid₂

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialLayer
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_polynomial_layer {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let Q := preparationModulusCap (j + 1) M R p
    let C := preparationShrink (j + 1) (Fintype.card I) M R p share
    (M : ℝ) ≤ p → (∀ i, C ^ (T + 1) ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ q ≤ Q ^ T ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C ^ T * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ (∀ x k, |err x k| ≤ δ) ∧
      ∀ x k, eval (fun i => ((S.point x i).val : ℝ)) P k =
        L.value (fun i => ((x i).val : ℝ)) k +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip k) : ℝ) + c k + err x k := by
  classical
  intro D T M share Q C hM hlarge
  have hshare : 0 < share := by dsimp [share]; positivity
  let L₀ := RankPreparationFamily.initial (j := j) P
  have hpot : L₀.potential = T := RankPreparationFamily.initial_potential P
  obtain ⟨q, S, L, ip, c, err, hpotL, hsize, hheight, hgood, hq, hqbound, hlength,
    hscore, hip, herr, hid⟩ :=
    RankPreparationFamily.exists_prepared_family (t := 0) (T := T) T L₀ N hp hR hRp hshare
      hpot.le (by omega) (RankPreparationFamily.initial_sized P)
      (RankPreparationFamily.initial_heights P hp hP) hM f hlarge
  refine ⟨q, S, L, ip, c, err, ?_, ?_, hheight, hgood, hq, hqbound, hlength,
    hscore, hip, ?_, ?_⟩
  · exact (sum_ranks_le_potential (fun u => (L u).rank)).trans (hpotL.trans hpot.le)
  · simpa only [Nat.zero_add] using hsize
  · intro x k
    apply (herr x k).trans
    have hden : 0 < (T : ℝ) * M + 1 := by positivity
    change (T : ℝ) * M * (δ / ((T : ℝ) * M + 1)) ≤ δ
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · intro x k
    have h := hid x k
    rw [RankPreparationFamily.initial_value] at h
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparationLogCost
namespace OAI

section

namespace Erdos3

theorem preparationModulusCap_le_exp {s M R : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ p) (hR : (R : ℝ) ≤ Real.exp p) :
    (preparationModulusCap s M R p : ℝ) ≤
      Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 2)) := by
  let e := budgetDepthExponent 38 s
  let X := (p + 2) ^ e
  have hX : 1 ≤ X := one_le_pow₀ (by linarith)
  have hheight := preparationHeight_le_exp p s
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (preparationHeight p s)) hheight M
  rw [← Real.exp_nat_mul] at hpow
  have hb : (M : ℝ) * X + p ≤ (p + 2) ^ (e + 2) := by
    calc
      (M : ℝ) * X + p ≤ p * X + p * X := by gcongr; nlinarith
      _ = (2 * p) * X := by ring
      _ ≤ (p + 2) ^ 2 * X := by gcongr; nlinarith
      _ = (p + 2) ^ (e + 2) := by dsimp [X]; rw [pow_add]; ring
  unfold preparationModulusCap
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp (M * X) := mul_le_mul hR hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (M * X + p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hb

theorem preparationShrink_le_exp {s n M R : ℕ} {p δ : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hM : (M : ℝ) ≤ p)
    (hR : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    preparationShrink s n M R p δ ≤ Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 6)) := by
  let e := budgetDepthExponent 38 s
  let U := (p + 2) ^ (e + 2)
  have hbase : 1 ≤ p + 2 := by linarith
  have hU : 1 ≤ U := one_le_pow₀ hbase
  have hpU : p ≤ U := le_power_budget hp (by omega)
  have hnp : (n : ℝ) + 1 ≤ Real.exp p := (by linarith : (n : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hsp : (s : ℝ) + 1 ≤ Real.exp p := (by linarith : (s : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hep : Real.exp p ≤ Real.exp U := Real.exp_le_exp.mpr hpU
  have hnU : (n : ℝ) ≤ Real.exp U := (by linarith : (n : ℝ) ≤ (n : ℝ) + 1).trans (hnp.trans hep)
  have hsU : (s : ℝ) ≤ Real.exp U := (by linarith : (s : ℝ) ≤ (s : ℝ) + 1).trans (hsp.trans hep)
  have hp2 : p ^ 2 ≤ U :=
    (pow_le_pow_left₀ hp (by linarith : p ≤ p + 2) 2).trans (pow_le_pow_right₀ hbase (by omega))
  have hnPower : ((n : ℝ) + 1) ^ s ≤ Real.exp U := by
    apply (pow_le_pow_left₀ (by positivity) hnp s).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hs hp).trans (by nlinarith [hp2]))
  have hheight : (preparationHeight p s : ℝ) ≤ Real.exp U :=
    (preparationHeight_le_exp p s).trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by omega)))
  have hK : (preparationOscillationCap s n R p : ℝ) ≤ Real.exp (6 * U) := by
    have hb : (preparationOscillationCap s n R p : ℝ) ≤
        Real.exp U * Real.exp U * Real.exp U * Real.exp U * Real.exp U * Real.exp U := by
      unfold preparationOscillationCap
      push_cast
      gcongr
      · exact hsp.trans hep
      · exact hR.trans hep
    apply hb.trans_eq
    repeat rw [← Real.exp_add]
    congr 1
    ring
  have htwo : (2 : ℝ) ≤ Real.exp U := by linarith [Real.add_one_le_exp U]
  have hK1 : (preparationOscillationCap s n R p : ℝ) + 1 ≤ Real.exp (7 * U) := by
    have he1 : 1 ≤ Real.exp (6 * U) := Real.one_le_exp (by positivity)
    calc
      _ ≤ 2 * Real.exp (6 * U) := by linarith
      _ ≤ Real.exp U * Real.exp (6 * U) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hδlower : Real.exp (-U) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos U) hδ).mpr (hδinv.trans hep)
  let ρ := min 1 (δ / (preparationOscillationCap s n R p + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρlower : Real.exp (-8 * U) ≤ ρ := by
    apply le_min
    · exact Real.exp_le_one_iff.mpr (by linarith)
    · apply (le_div_iff₀ (by positivity : 0 < (preparationOscillationCap s n R p : ℝ) + 1)).mpr
      calc
        _ ≤ Real.exp (-8 * U) * Real.exp (7 * U) := mul_le_mul_of_nonneg_left hK1 (Real.exp_nonneg _)
        _ = Real.exp (-U) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ δ := hδlower
  have hfour : (4 : ℝ) ≤ Real.exp (2 * U) := by
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp U * Real.exp U := mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hC : preparationShrink s n M R p δ ≤ Real.exp (11 * U) := by
    apply (div_le_iff₀ hρ).mpr
    calc
      _ ≤ Real.exp (2 * U) * Real.exp U :=
        mul_le_mul hfour (preparationModulusCap_le_exp hp hM hR) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (11 * U) * Real.exp (-8 * U) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (11 * U) * ρ := mul_le_mul_of_nonneg_left hρlower (Real.exp_nonneg _)
  apply hC.trans (Real.exp_le_exp.mpr ?_)
  have hb4 : (11 : ℝ) ≤ (p + 2) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 ≤ p + 2) 4
    norm_num at h
    linarith
  calc
    11 * U ≤ (p + 2) ^ 4 * U := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = (p + 2) ^ (e + 6) := by dsimp [U]; rw [← pow_add]; congr 1; omega

theorem preparation_total_cost_le_exp {s n M R T : ℕ} {p δ : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hM : (M : ℝ) ≤ p)
    (hT : (T : ℝ) + 1 ≤ p) (hR : (R : ℝ) ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    ((preparationModulusCap s M R p ^ T : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 7)) ∧
      preparationShrink s n M R p δ ^ (T + 1) ≤
        Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 7)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hQ := preparationModulusCap_le_exp (s := s) hp hM hR
  have hC := preparationShrink_le_exp hp hs hn hM hR hδ hδinv
  constructor
  · push_cast
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ T).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (T : ℝ) * (p + 2) ^ (budgetDepthExponent 38 s + 2) ≤
          (p + 2) * (p + 2) ^ (budgetDepthExponent 38 s + 2) := by gcongr; linarith
      _ = (p + 2) ^ (budgetDepthExponent 38 s + 3) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
  · have hC0 : 0 ≤ preparationShrink s n M R p δ := by
      unfold preparationShrink
      positivity
    apply (pow_le_pow_left₀ hC0 hC (T + 1)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      ((T + 1 : ℕ) : ℝ) * (p + 2) ^ (budgetDepthExponent 38 s + 6) ≤
          (p + 2) * (p + 2) ^ (budgetDepthExponent 38 s + 6) := by
            gcongr
            push_cast
            linarith
      _ = _ := by rw [pow_succ]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_polynomial_layer_exp_s2_oai {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    (M : ℝ) ≤ p → ((j + 1 : ℕ) : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ p →
    (T : ℝ) + 1 ≤ p → share⁻¹ ≤ Real.exp p → (∀ i, Real.exp budget ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ (∀ x k, |err x k| ≤ δ) ∧
      ∀ x k, eval (fun i => ((S.point x i).val : ℝ)) P k =
        L.value (fun i => ((x i).val : ℝ)) k +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip k) : ℝ) + c k + err x k := by
  classical
  intro D T M share budget hM hs hn hT hshareinv hN
  have hshare : 0 < share := by dsimp [share]; positivity
  obtain ⟨hQ, hC⟩ := preparation_total_cost_le_exp hp hs hn hM hT hRp hshare hshareinv
  obtain ⟨q, S, L, ip, c, err, hrank, hsize, hheight, hgood, hq, hqbound,
    hlength, hscore, hip, herr, hid⟩ :=
    exists_prepared_polynomial_layer P hP hp hR hRp hδ N f hM (fun i => hC.trans (hN i))
  refine ⟨q, S, L, ip, c, err, hrank, hsize, hheight, hgood, hq,
    (Nat.cast_le.mpr hqbound).trans hQ, ?_, hscore, hip, herr, hid⟩
  intro i
  refine ⟨(hlength i).1, (hlength i).2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (pow_le_pow_right₀ (preparationShrink_one_le (j + 1) (Fintype.card I) M hR hp hshare)
    (Nat.le_succ T)).trans hC

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_prepared_polynomial_layer_exp_s2_oai := @OAI.Erdos3.exists_prepared_polynomial_layer_exp_s2_oai
