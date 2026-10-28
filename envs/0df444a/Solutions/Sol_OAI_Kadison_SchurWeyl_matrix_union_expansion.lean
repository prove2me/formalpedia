-- Prove2me | solution 1 for OAI.Kadison.SchurWeyl.matrix_union_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:33:49.279009+00:00
-- url     : https://prove2.me/submissions/b24f90d5-22e9-40aa-9cce-5fb5a4f6e6ed

import Mathlib
import Definitions.Def_OAIQ039C016
import Definitions.Def_OAIQ039C029
import Theorems.Thm_OAI_Kadison_SchurWeyl_cycleTrace_map

section
-- module Solutions.OAIQ039_CM.Commutator_SchurWeylDevelopment
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [DecidableEq J] in
lemma tensorPower_diagonal (d : I → 𝕜) :
    tensorPower (J := J) (Matrix.diagonal d) =
      Matrix.diagonal (fun a : J → I => ∏ j, d (a j)) := by
  classical
  ext a b
  by_cases h : a = b
  · subst b; simp
  · have hex : ∃ j, a j ≠ b j := Function.ne_iff.mp h
    obtain ⟨j, hj⟩ := hex
    rw [Matrix.diagonal_apply_ne _ h]
    change (∏ j, Matrix.diagonal d (a j) (b j)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

omit [Fintype I] [DecidableEq J] in
@[simp] lemma tensorPower_one : tensorPower (J := J) (1 : Matrix I I 𝕜) = 1 := by
  rw [← Matrix.diagonal_one, tensorPower_diagonal]
  simp

omit [DecidableEq I] in
lemma tensorPower_mul (A B : Matrix I I 𝕜) :
    tensorPower (J := J) (A * B) = tensorPower A * tensorPower B := by
  classical
  ext a b
  simp only [tensorPower_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

lemma tensorPower_commute_permutation (A : Matrix I I 𝕜) (σ : Equiv.Perm J) :
    tensorPower A * permutationMatrix σ = permutationMatrix σ * tensorPower A := by
  classical
  ext a b
  simp only [Matrix.mul_apply, permutationMatrix, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (b ∘ σ.symm)]
  · rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (a ∘ σ)]
    · have ha : a = (a ∘ σ) ∘ σ.symm := by ext j; simp
      rw [ite_eq_left ha, one_mul]
      dsimp [tensorPower]
      simpa using (Equiv.prod_comp σ.symm fun j => A (a (σ j)) (b j))
    · intro c _ hc
      have hn : a ≠ c ∘ σ.symm := by
        intro he
        apply hc
        ext j
        simpa using congrFun he (σ j) |>.symm
      simp [hn]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

omit [Fintype I] [DecidableEq J] in
lemma assignmentMatrix_column (b c : J → I) (hb : Function.Injective b) (r : I) (j : J) :
    assignmentMatrix (𝕜 := 𝕜) b c r (b j) = if r = c j then 1 else 0 := by
  classical
  unfold assignmentMatrix
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hn : b j ≠ b k := fun h => hk (hb h).symm
    simp [hn]
  · simp

omit [Fintype I] [DecidableEq J] in
lemma tensorPower_assignment (b c : J → I) (hb : Function.Injective b) (a : J → I) :
    tensorPower (assignmentMatrix (𝕜 := 𝕜) b c) a b = if a = c then 1 else 0 := by
  classical
  simp only [tensorPower_apply, assignmentMatrix_column b c hb]
  by_cases h : a = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma eq_zero_of_commute_of_column_zero (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ A : Matrix I I 𝕜, S * tensorPower A = tensorPower A * S)
    (hzero : ∀ a, S a b = 0) : S = 0 := by
  classical
  ext a c
  have he := congrArg (fun X : Matrix (J → I) (J → I) 𝕜 => X a b)
    (hS (assignmentMatrix b c))
  simp only [Matrix.mul_apply, tensorPower_assignment b c hb, hzero, mul_zero,
    Finset.sum_const_zero, mul_ite, mul_one] at he
  simpa using he

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma exists_permutation_of_range (a b : J → I) (hb : Function.Injective b)
    (h : ∀ j, ∃ k, a k = b j) :
    ∃ σ : Equiv.Perm J, a = b ∘ σ.symm := by
  classical
  choose g hg using h
  have hgi : Function.Injective g := by
    intro j k he
    apply hb
    rw [← hg j, ← hg k, he]
  let σ : Equiv.Perm J := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hgi, rfl⟩)
  refine ⟨σ, funext fun j => ?_⟩
  have he := hg (σ.symm j)
  change a (σ (σ.symm j)) = b (σ.symm j) at he
  simpa using he

lemma column_support_permutations [Nontrivial 𝕜]
    (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ d : I → 𝕜, S * tensorPower (Matrix.diagonal d) =
      tensorPower (Matrix.diagonal d) * S)
    (a : J → I) (ha : S a b ≠ 0) :
    ∃ σ : Equiv.Perm J, a = b ∘ σ.symm := by
  classical
  apply exists_permutation_of_range a b hb
  intro j
  by_contra hn
  push Not at hn
  let d : I → 𝕜 := fun r => if r = b j then 0 else 1
  have hd₁ : (∏ k, d (a k)) = 1 := by simp [d, hn]
  have hd₀ : (∏ k, d (b k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [d])
  have he := congrArg (fun X : Matrix (J → I) (J → I) 𝕜 => X a b) (hS d)
  rw [tensorPower_diagonal] at he
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hd₀, hd₁, mul_zero, one_mul] at he
  exact ha he.symm

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma permutation_label_injective (b : J → I) (hb : Function.Injective b) :
    Function.Injective (fun σ : Equiv.Perm J => b ∘ σ.symm) := by
  intro σ ρ he
  have hs : σ.symm = ρ.symm := by
    ext j
    exact hb (congrFun he j)
  exact congrArg Equiv.symm hs

theorem commutant_tensorPower [Nontrivial 𝕜]
    (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) 𝕜)
    (hS : ∀ A : Matrix I I 𝕜, S * tensorPower A = tensorPower A * S) :
    S = ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ := by
  classical
  let Q : Matrix (J → I) (J → I) 𝕜 := ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ
  have hQ : ∀ A : Matrix I I 𝕜, Q * tensorPower A = tensorPower A * Q := by
    intro A
    dsimp [Q]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul,
      tensorPower_commute_permutation]
  have hcol : ∀ a, S a b = Q a b := by
    intro a
    by_cases ha : S a b = 0
    · dsimp [Q]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, permutationMatrix]
      rw [ha]
      symm
      apply Finset.sum_eq_zero
      intro σ _
      split_ifs with h
      · rw [← h, ha, zero_mul]
      · exact mul_zero _
    · obtain ⟨σ, rfl⟩ := column_support_permutations b hb S (fun d => hS _) a ha
      dsimp [Q]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, permutationMatrix]
      rw [Finset.sum_eq_single σ]
      · simp
      · intro ρ _ hρ
        have hn : b ∘ σ.symm ≠ b ∘ ρ.symm := fun he =>
          hρ ((permutation_label_injective b hb he).symm)
        simp [hn]
      · simp
  have hz : S - Q = 0 := eq_zero_of_commute_of_column_zero b hb _
    (fun A => by rw [Matrix.sub_mul, Matrix.mul_sub, hS A, hQ A])
    (fun a => by simp [hcol a])
  exact sub_eq_zero.mp hz

lemma complex_unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hi : Set.InjOn (fun x : ℝ => (Circle.exp x : ℂ)) (Set.Icc 0 1) :=
    Circle.coe_injective.comp_injOn (Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three]))
  exact ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image hi).mono
    (by rintro _ ⟨x, _, rfl⟩; exact Circle.norm_coe _)

lemma diagonal_unitary (d : I → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ unitary (Matrix I I ℂ) := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  simp [Pi.star_apply, RCLike.star_def, Complex.mul_conj', hd]

lemma commute_diagonal_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) (d : I → ℂ) :
    S * tensorPower (Matrix.diagonal d) = tensorPower (Matrix.diagonal d) * S := by
  classical
  rw [tensorPower_diagonal]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  let p : MvPolynomial I ℂ := MvPolynomial.C (S a b) * ∏ j, MvPolynomial.X (b j)
  let q : MvPolynomial I ℂ := (∏ j, MvPolynomial.X (a j)) * MvPolynomial.C (S a b)
  have hpq : p = q := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1})
      (fun _ => complex_unit_circle_infinite)
    intro z hz
    have he := congrArg (fun X : Matrix (J → I) (J → I) ℂ => X a b)
      (hS ⟨Matrix.diagonal z, diagonal_unitary z (fun i => hz i (Set.mem_univ _))⟩)
    rw [tensorPower_diagonal] at he
    simpa [p, q] using he
  have he := congrArg (MvPolynomial.eval d) hpq
  simpa [p, q] using he

lemma commute_hermitian_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S)
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    S * tensorPower A = tensorPower A * S := by
  have hU : Commute S (tensorPower (hA.eigenvectorUnitary : Matrix I I ℂ)) :=
    hS hA.eigenvectorUnitary
  have hD : Commute S (tensorPower (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))) :=
    commute_diagonal_of_unitary S hS _
  have hUs : Commute S (tensorPower ((star hA.eigenvectorUnitary : unitary (Matrix I I ℂ)) : Matrix I I ℂ)) :=
    hS (star hA.eigenvectorUnitary)
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simpa only [tensorPower_mul, Unitary.coe_star] using ((hU.mul_right hD).mul_right hUs).eq

omit [DecidableEq I] in
lemma commute_complexification
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ A : Matrix I I ℂ, A.IsHermitian → S * tensorPower A = tensorPower A * S)
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) :
    S * tensorPower (A + z • B) = tensorPower (A + z • B) * S := by
  classical
  ext a b
  let P (r s : I) : MvPolynomial Unit ℂ := MvPolynomial.C (A r s) +
    MvPolynomial.X () * MvPolynomial.C (B r s)
  let p : MvPolynomial Unit ℂ := ∑ c : J → I,
    MvPolynomial.C (S a c) * ∏ j, P (c j) (b j)
  let q : MvPolynomial Unit ℂ := ∑ c : J → I,
    (∏ j, P (a j) (c j)) * MvPolynomial.C (S c b)
  have hpq : p = q := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro x hx
    obtain ⟨t, ht⟩ := hx () (Set.mem_univ _)
    have hs : (A + (t : ℂ) • B).IsHermitian := by
      exact hA.add (hB.smul (by change star (t : ℂ) = (t : ℂ); simp))
    have he := congrArg (fun X : Matrix (J → I) (J → I) ℂ => X a b) (hS _ hs)
    simpa [p, q, P, Matrix.mul_apply, tensorPower, ← ht] using he
  have he := congrArg (MvPolynomial.eval (fun _ => z)) hpq
  simpa [p, q, P, Matrix.mul_apply, tensorPower] using he

lemma commute_all_of_unitary
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) (A : Matrix I I ℂ) :
    S * tensorPower A = tensorPower A * S := by
  have hre : (realPart A : Matrix I I ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (realPart A).property
  have him : (imaginaryPart A : Matrix I I ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (imaginaryPart A).property
  simpa only [realPart_add_I_smul_imaginaryPart] using
    commute_complexification S (commute_hermitian_of_unitary S hS)
      (realPart A) (imaginaryPart A) hre him Complex.I

theorem commutant_unitary_tensorPower (b : J → I) (hb : Function.Injective b)
    (S : Matrix (J → I) (J → I) ℂ)
    (hS : ∀ U : unitary (Matrix I I ℂ), S * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * S) :
    S = ∑ σ : Equiv.Perm J, S (b ∘ σ.symm) b • permutationMatrix σ :=
  commutant_tensorPower b hb S (commute_all_of_unitary S hS)

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantForms
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
lemma tensorMatrices_mul (A B : J → Matrix I I 𝕜) :
    tensorMatrices (fun j => A j * B j) = tensorMatrices A * tensorMatrices B := by
  classical
  ext a b
  simp only [tensorMatrices, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

omit [Fintype I] [DecidableEq J] in
lemma tensorMatrices_single (a b : J → I) :
    tensorMatrices (fun j => Matrix.single (a j) (b j) (1 : 𝕜)) = Matrix.single a b 1 := by
  classical
  ext c d
  simp only [tensorMatrices, Matrix.single_apply]
  by_cases h : c = a ∧ d = b
  · rcases h with ⟨rfl, rfl⟩; simp
  · rw [ite_eq_right (by simpa [eq_comm] using h)]
    have he : ∃ j, ¬ (a j = c j ∧ b j = d j) := by
      by_contra! hn
      exact h ⟨funext fun j => (hn j).1.symm, funext fun j => (hn j).2.symm⟩
    obtain ⟨j, hj⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

omit [DecidableEq I] in
lemma traceForm_apply (T : Matrix (J → I) (J → I) 𝕜) (A : J → Matrix I I 𝕜) :
    traceForm T A = Matrix.trace (T * tensorMatrices A) := by
  simp [traceForm, Matrix.trace, Matrix.mul_apply, tensorMatrices,
    _root_.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, smul_eq_mul]

lemma traceForm_single (T : Matrix (J → I) (J → I) 𝕜) (a b : J → I) :
    traceForm T (fun j => Matrix.single (a j) (b j) 1) = T b a := by
  rw [traceForm_apply, tensorMatrices_single, Matrix.trace_mul_single]
  simp

lemma traceForm_coefficientMatrix (F : MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜) :
    traceForm (coefficientMatrix F) = F := by
  apply Module.Basis.ext_multilinear (fun _ => Matrix.stdBasis 𝕜 I I)
  intro v
  have hb (p : I × I) : Matrix.stdBasis 𝕜 I I p = Matrix.single p.1 p.2 1 := by
    rcases p with ⟨i, j⟩
    exact Matrix.stdBasis_eq_single 𝕜 i j
  simp only [hb, traceForm_single, coefficientMatrix]

lemma coefficientMatrix_traceForm (T : Matrix (J → I) (J → I) 𝕜) :
    coefficientMatrix (traceForm T) = T := by
  ext a b
  exact traceForm_single T b a

lemma traceForm_injective : Function.Injective (traceForm (I := I) (J := J) (𝕜 := 𝕜)) := by
  intro T S h
  simpa only [coefficientMatrix_traceForm] using congrArg coefficientMatrix h

omit [DecidableEq I] in
lemma traceForm_conjugate (T : Matrix (J → I) (J → I) 𝕜)
    (U V : Matrix I I 𝕜) (A : J → Matrix I I 𝕜) :
    traceForm T (fun j => U * A j * V) =
      traceForm (tensorPower V * T * tensorPower U) A := by
  simp only [traceForm_apply, tensorMatrices_mul]
  change Matrix.trace (T * (tensorPower U * tensorMatrices A * tensorPower V)) = _
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

lemma coefficientMatrix_commute_unitary
    (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A)
    (U : unitary (Matrix I I ℂ)) :
    coefficientMatrix F * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * coefficientMatrix F := by
  have hconj : tensorPower (star (U : Matrix I I ℂ)) * coefficientMatrix F *
      tensorPower (U : Matrix I I ℂ) = coefficientMatrix F := by
    apply traceForm_injective
    apply MultilinearMap.ext
    intro A
    rw [← traceForm_conjugate, traceForm_coefficientMatrix, hF]
  have hu : tensorPower (U : Matrix I I ℂ) * tensorPower (star (U : Matrix I I ℂ)) =
      (1 : Matrix (J → I) (J → I) ℂ) := by
    rw [← tensorPower_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, tensorPower_one]
  have hh := congrArg (fun T => tensorPower (U : Matrix I I ℂ) * T) hconj
  simpa only [← Matrix.mul_assoc, hu, Matrix.one_mul] using hh

theorem invariant_multilinear_form (b : J → I) (hb : Function.Injective b)
    (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A) :
    ∃ c : Equiv.Perm J → ℂ, ∀ A : J → Matrix I I ℂ,
      F A = ∑ σ, c σ * Matrix.trace (permutationMatrix σ * tensorMatrices A) := by
  let T := coefficientMatrix F
  have he : T = ∑ σ : Equiv.Perm J, T (b ∘ σ.symm) b • permutationMatrix σ :=
    commutant_unitary_tensorPower b hb T (coefficientMatrix_commute_unitary F hF)
  refine ⟨fun σ => T (b ∘ σ.symm) b, fun A => ?_⟩
  have ht : F A = Matrix.trace (T * tensorMatrices A) := by
    rw [← traceForm_apply, traceForm_coefficientMatrix]
  calc
    F A = Matrix.trace (T * tensorMatrices A) := ht
    _ = Matrix.trace ((∑ σ : Equiv.Perm J, T (b ∘ σ.symm) b • permutationMatrix σ) *
        tensorMatrices A) := congrArg (fun V => Matrix.trace (V * tensorMatrices A)) he
    _ = _ := by simp [Matrix.sum_mul, Matrix.trace_smul, smul_eq_mul]

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma rawCycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    rawCycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) (1 : 𝕜)) =
      if σ = τ then 1 else 0 := by
  classical
  unfold rawCycleTrace
  rw [tensorMatrices_single, Matrix.trace_mul_single]
  simp only [MulOpposite.op_one, one_smul, permutationMatrix]
  have he : b = (fun j => b (τ j)) ∘ σ.symm ↔ σ = τ := by
    constructor
    · intro h
      apply Equiv.ext
      intro j
      apply hb
      simpa using congrFun h (σ j)
    · rintro rfl
      ext j
      simp
  by_cases h : σ = τ
  · subst τ
    simp [Function.comp_def]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (he.mp hh))]

lemma cycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    cycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) 1) =
      if σ = τ then (Fintype.card I : ℂ)⁻¹ ^ cycleCount τ else 0 := by
  rw [cycleTrace, rawCycleTrace_single b hb]
  split_ifs with h
  · subst τ; rw [mul_one]
  · rw [mul_zero]

lemma cycleTrace_coefficients_unique [Nonempty I] (b : J → I)
    (hb : Function.Injective b) (c d : Equiv.Perm J → ℂ)
    (h : ∀ A : J → Matrix I I ℂ, ∑ σ, c σ * cycleTrace σ A =
      ∑ σ, d σ * cycleTrace σ A) : c = d := by
  classical
  funext τ
  have he := h (fun j => Matrix.single (b (τ j)) (b j) 1)
  simp only [cycleTrace_single b hb, mul_ite, mul_zero] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  apply mul_right_cancel₀ _ he
  exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))

theorem invariant_multilinear_form_normalized [Nonempty I] (b : J → I)
    (hb : Function.Injective b) (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A) :
    ∃! c : Equiv.Perm J → ℂ, ∀ A : J → Matrix I I ℂ,
      F A = ∑ σ, c σ * cycleTrace σ A := by
  classical
  obtain ⟨c, hc⟩ := invariant_multilinear_form b hb F hF
  let d : Equiv.Perm J → ℂ := fun σ => c σ * (Fintype.card I : ℂ) ^ cycleCount σ
  have hi : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd (A : J → Matrix I I ℂ) : F A = ∑ σ, d σ * cycleTrace σ A := by
    rw [hc]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [d, cycleTrace, rawCycleTrace]
    rw [mul_assoc, ← mul_assoc ((Fintype.card I : ℂ) ^ cycleCount σ),
      ← mul_pow, mul_inv_cancel₀ hi, one_pow, one_mul]
  refine ⟨d, hd, ?_⟩
  intro e he
  exact cycleTrace_coefficients_unique b hb e d (fun A => (he A).symm.trans (hd A))

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleEmbeddings
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {I K J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype K] [DecidableEq K] [Nonempty K] [Fintype J] [DecidableEq J]

theorem stable_cycle_coefficients_map
    (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
    (b : J → I) (hb : Function.Injective b) (c d : Equiv.Perm J → ℂ)
    (h : ∀ A : J → Matrix I I ℂ,
      ∑ σ, c σ * cycleTrace σ A = ∑ σ, d σ * cycleTrace σ (fun j => φ (A j))) :
    c = d := by
  apply cycleTrace_coefficients_unique b hb c d
  intro A
  simpa only [cycleTrace_map] using h A

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleEmbeddings2
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem matrix_union_expansion_oai (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (F : ∀ n, MultilinearMap ℂ (fun _ : J => Matrix (I n) (I n) ℂ) ℂ)
    (hinv : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)) (A : J → Matrix (I n) (I n) ℂ),
      F n (fun j => (u : Matrix (I n) (I n) ℂ) * A j * star (u : Matrix (I n) (I n) ℂ)) = F n A)
    (hcomp : ∀ n m (h : n ≤ m) (A : J → Matrix (I n) (I n) ℂ),
      F m (fun j => φ h (A j)) = F n A) :
    ∃ c : Equiv.Perm J → ℂ, ∀ n (A : J → Matrix (I n) (I n) ℂ),
      F n A = ∑ σ, c σ * cycleTrace σ A := by
  classical
  obtain ⟨n₀, _, hn₀⟩ := hsize 0 (Fintype.card J)
  let b : J ↪ I n₀ := Classical.choice (Function.Embedding.nonempty_of_card_le hn₀)
  obtain ⟨c, hc, _⟩ := invariant_multilinear_form_normalized b b.injective (F n₀) (hinv n₀)
  refine ⟨c, ?_⟩
  intro n A
  obtain ⟨m, hnm, hm⟩ := hsize (max n n₀) (Fintype.card J)
  have hn : n ≤ m := (le_max_left n n₀).trans hnm
  have hn₀m : n₀ ≤ m := (le_max_right n n₀).trans hnm
  let b' : J ↪ I m := Classical.choice (Function.Embedding.nonempty_of_card_le hm)
  obtain ⟨d, hd, _⟩ := invariant_multilinear_form_normalized b' b'.injective (F m) (hinv m)
  have hcd : c = d := by
    apply stable_cycle_coefficients_map (φ hn₀m) b b.injective
    intro B
    rw [← hc, ← hd, hcomp]
  rw [← hcomp n m hn A, hd]
  simp only [← hcd, cycleTrace_map]

end Kadison.SchurWeyl
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.SchurWeyl.matrix_union_expansion_oai.{u_1, u_2} := @OAI.Kadison.SchurWeyl.matrix_union_expansion_oai.{u_1, u_2}
