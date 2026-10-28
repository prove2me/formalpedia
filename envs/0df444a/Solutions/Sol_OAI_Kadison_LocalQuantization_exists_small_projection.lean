-- Prove2me | solution 1 for OAI.Kadison.LocalQuantization.exists_small_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:27:55.428252+00:00
-- url     : https://prove2.me/submissions/31a6aee1-c6c7-4f62-8f16-3ef201a04ca6

import Mathlib
import Definitions.Def_OAIQ039C028
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C036

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section Signs

variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
lemma character_sq (s : Finset I) (σ : I → Bool) : character s σ * character s σ = 1 := by
  rw [character, ← Finset.prod_mul_distrib]
  simp

lemma character_flip (s : Finset I) (i : I) (σ : I → Bool) :
    character s (flip i σ) = (if i ∈ s then -1 else 1) * character s σ := by
  have hfun : (fun j => sign (flip i σ j)) = Function.update (fun j => sign (σ j)) i (-sign (σ i)) := by
    funext j
    by_cases h : j = i
    · subst j; simp [flip]
    · simp [flip, h]
  rw [character, hfun]
  by_cases hi : i ∈ s
  · rw [Finset.prod_update_of_mem hi]
    rw [ite_eq_left hi]
    have hprod := Finset.mul_prod_erase s (fun j => sign (σ j)) hi
    simp only [Finset.sdiff_singleton_eq_erase]
    simpa only [character, neg_mul, neg_one_mul, one_mul] using congrArg Neg.neg hprod
  · rw [Finset.prod_update_of_notMem hi, ite_eq_right hi, one_mul]
    rfl

variable [Fintype I]

lemma different_character_sum (s t : Finset I) (hst : s ≠ t) :
    ∑ σ : I → Bool, character s σ * character t σ = 0 := by
  have hex : ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∉ s ∧ i ∈ t) := by
    by_contra! h
    apply hst
    ext i
    specialize h i
    tauto
  obtain ⟨i, hi⟩ := hex
  have h := (flipEquiv i).sum_comp (fun σ => character s σ * character t σ)
  simp only [flipEquiv, Function.Involutive.coe_toPerm, character_flip] at h
  rcases hi with hi | hi
  · simp only [ite_eq_left hi.1, ite_eq_right hi.2, one_mul, neg_mul,
      Finset.sum_neg_distrib] at h
    linarith
  · simp only [ite_eq_right hi.1, ite_eq_left hi.2, neg_one_mul, one_mul, mul_neg,
      Finset.sum_neg_distrib] at h
    linarith

lemma character_gram (s t : Finset I) :
    ∑ σ : I → Bool, character s σ * character t σ =
      if s = t then (Fintype.card (I → Bool) : ℝ) else 0 := by
  by_cases h : s = t
  · subst t
    simp [character_sq]
  · rw [ite_eq_right h]
    exact different_character_sum s t h

end Signs

section Hilbert

variable {I J H : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma sign_parseval (f : J → Finset I) (hf : Function.Injective f) (x : J → H) :
    (∑ σ : I → Bool, ‖∑ j, character (f j) σ • x j‖ ^ 2) =
      (Fintype.card (I → Bool) : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
  classical
  have he (σ : I → Bool) : ‖∑ j, character (f j) σ • x j‖ ^ 2 =
      ∑ j, ∑ k, (character (f j) σ * character (f k) σ) * inner ℝ (x j) (x k) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    simp only [mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [real_inner_comm (x k) (x j)]
  simp_rw [he]
  calc
    (∑ σ : I → Bool, ∑ j, ∑ k,
        (character (f j) σ * character (f k) σ) * inner ℝ (x j) (x k)) =
        ∑ j, ∑ k, (∑ σ : I → Bool, character (f j) σ * character (f k) σ) *
          inner ℝ (x j) (x k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp [character_gram, hf.eq_iff, Finset.mul_sum]

end Hilbert

section UpperTriangle

variable {I : Type*} [Fintype I] [LinearOrder I]

omit [Fintype I] in
lemma label_injective : Function.Injective (label (I := I)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hb : b.val.1 ∈ label (some b) := by simp [label]
      rw [← hab] at hb
      simp [label] at hb
  | some a =>
    cases b with
    | none =>
      have ha : a.val.1 ∈ label (some a) := by simp [label]
      rw [hab] at ha
      simp [label] at ha
    | some b =>
      have h₁ : a.val.1 = b.val.1 ∨ a.val.1 = b.val.2 := by
        have ha : a.val.1 ∈ label (some a) := by simp [label]
        rw [hab] at ha
        simpa [label] using ha
      have h₂ : b.val.1 = a.val.1 ∨ b.val.1 = a.val.2 := by
        have hb : b.val.1 ∈ label (some b) := by simp [label]
        rw [← hab] at hb
        simpa [label] using hb
      have he₁ : a.val.1 = b.val.1 := by
        rcases h₁ with h₁ | h₁
        · exact h₁
        rcases h₂ with h₂ | h₂
        · exact h₂.symm
        · have ha := a.property
          have hb := b.property
          rw [h₁, ← h₂] at ha
          exact (lt_asymm ha hb).elim
      have he₂ : a.val.2 = b.val.2 := by
        have ha : a.val.2 ∈ label (some a) := by simp [label]
        rw [hab] at ha
        have hh : a.val.2 = b.val.1 ∨ a.val.2 = b.val.2 := by simpa [label] using ha
        rcases hh with hh | hh
        · exact ((ne_of_gt a.property) (hh.trans he₁.symm)).elim
        · exact hh
      congr 1
      exact Subtype.ext (Prod.ext he₁ he₂)

variable {V : Type*} [AddCommMonoid V]

lemma sum_upper (f : I × I → V) :
    (∑ p : Upper (I := I), f p.val) = ∑ i, ∑ j, if i < j then f (i,j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : I × I => p.1 < p.2))
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]

lemma sum_matrix_split (x : I → I → V) :
    (∑ i, ∑ j, x i j) = (∑ i, x i i) +
      ∑ p : Upper (I := I), (x p.val.1 p.val.2 + x p.val.2 p.val.1) := by
  have he (i j : I) : x i j = (if i = j then x i j else 0) +
      (if i < j then x i j else 0) + (if j < i then x i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  calc
    (∑ i, ∑ j, x i j) = (∑ i, x i i) +
        (∑ i, ∑ j, if i < j then x i j else 0) +
        (∑ i, ∑ j, if j < i then x i j else 0) := by
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
      simp only [Finset.sum_add_distrib]
      simp
    _ = _ := by
      rw [sum_upper (fun p : I × I => x p.1 p.2 + x p.2 p.1)]
      rw [Finset.sum_comm (f := fun i j => if j < i then x i j else 0)]
      have hh (i j : I) : (if i < j then x i j + x j i else 0) =
          (if i < j then x i j else 0) + (if i < j then x j i else 0) := by
        split_ifs <;> simp
      simp_rw [hh]
      simp only [Finset.sum_add_distrib, add_assoc]

end UpperTriangle

section MatrixSigns

variable {I H : Type*} [Fintype I] [LinearOrder I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma matrixSignSum_eq (x : I → I → H) (σ : I → Bool) :
    matrixSignSum x σ =
      ∑ p : Option (Upper (I := I)), character (label p) σ • matrixCoefficient x p := by
  rw [Fintype.sum_option, matrixSignSum, sum_matrix_split]
  simp only [label, character_empty, matrixCoefficient, one_smul, sign_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hne : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  simp [character, hne, smul_add, mul_comm]

omit [InnerProductSpace ℝ H] in
lemma norm_add_sq_bound (a b : H) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a+b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖-‖b‖)]

omit [InnerProductSpace ℝ H] in
lemma upper_norm_sum_bound (x : I → I → H) :
    (∑ p : Upper (I := I), ‖x p.val.1 p.val.2 + x p.val.2 p.val.1‖^2) ≤
      2 * ∑ i, ∑ j, ‖x i j‖^2 := by
  calc
    _ ≤ ∑ p : Upper (I := I), 2*(‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
      Finset.sum_le_sum (fun _ _ => norm_add_sq_bound _ _)
    _ = 2 * ∑ p : Upper (I := I), (‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := by
      rw [sum_matrix_split (fun i j => ‖x i j‖^2)]
      have h : 0 ≤ ∑ i, ‖x i i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith

theorem exists_matrix_sign_bound (x : I → I → H) :
    ∃ σ : I → Bool, ‖matrixSignSum x σ‖^2 ≤
      ‖∑ i, x i i‖^2 + 2 * ∑ i, ∑ j, ‖x i j‖^2 := by
  let B := ‖∑ i, x i i‖^2 + 2 * ∑ i, ∑ j, ‖x i j‖^2
  have he := sign_parseval (label (I := I)) label_injective (matrixCoefficient x)
  simp_rw [← matrixSignSum_eq] at he
  rw [Fintype.sum_option] at he
  simp only [matrixCoefficient] at he
  have hle : (∑ σ : I → Bool, ‖matrixSignSum x σ‖^2) ≤ ∑ _σ : I → Bool, B := by
    rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (upper_norm_sum_bound x)) (Nat.cast_nonneg _)
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact ⟨σ, hσ⟩

end MatrixSigns

section MatrixAlgebra

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma star_column (i₀ : I) (σ : I → Bool) :
    star (column φ i₀ σ) = ∑ i, sign (σ i) • unit φ i₀ i := by
  simp only [column, star_sum, star_smul, star_trivial, unit_star]

lemma column_right (i₀ : I) (σ : I → Bool) :
    column φ i₀ σ * unit φ i₀ i₀ = column φ i₀ σ := by
  simp [column, Finset.sum_mul]

lemma column_inner (i₀ : I) (σ : I → Bool) :
    star (column φ i₀ σ) * column φ i₀ σ = (Fintype.card I : ℝ) • unit φ i₀ i₀ := by
  rw [star_column, column, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, unit_mul]
  have hs (i : I) :
      (∑ j, sign (σ j) • sign (σ i) • (if i = j then unit φ i₀ i₀ else 0)) =
      unit φ i₀ i₀ := by
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, smul_smul, sign_sq, one_smul]
    · intro j hj hji
      simp [Ne.symm hji]
    · simp
  simp only [hs, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℝ ..).symm

lemma column_sandwich (i₀ : I) (σ : I → Bool) (x : A) :
    star (column φ i₀ σ) * x * column φ i₀ σ =
      ∑ i, ∑ j, (sign (σ i) * sign (σ j)) • (unit φ i₀ i * x * unit φ j i₀) := by
  rw [star_column, column]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  rw [mul_comm]

lemma traceSquare_smul (τ : A →ₗ[ℝ] ℝ) (r : ℝ) (x : A) :
    traceSquare τ (r • x) = r^2 * traceSquare τ x := by
  simp [traceSquare, star_smul, smul_smul, pow_two,
    mul_assoc]

variable (τ : A →ₗ[ℝ] ℝ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a))

include hτ in
lemma trace_rotate (a b c : A) : τ (a*b*c) = τ (b*c*a) := by
  rw [mul_assoc, hτ]

include hτ in
lemma unit_trace_eq (i j : I) : τ (unit φ i i) = τ (unit φ j j) := by
  simpa only [unit_mul, ite_true] using hτ (unit φ i j) (unit φ j i)

include hτ in
lemma unit_trace (h1 : τ 1 = 1) (i : I) : τ (unit φ i i) = (Fintype.card I : ℝ)⁻¹ := by
  have : Nonempty I := ⟨i⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card I : ℝ) * τ (unit φ i i) = 1 := by
    calc
      _ = ∑ j, τ (unit φ j j) := by
        simp only [← unit_trace_eq φ τ hτ i, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ = τ 1 := by rw [← map_sum, unit_sum]
      _ = 1 := h1
  apply mul_left_cancel₀ hc
  rw [he, mul_inv_cancel₀ hc]

lemma signProjection_star (i₀ : I) (σ : I → Bool) :
    star (signProjection φ i₀ σ) = signProjection φ i₀ σ := by
  simp [signProjection]

lemma signProjection_idem (i₀ : I) (σ : I → Bool) :
    signProjection φ i₀ σ * signProjection φ i₀ σ = signProjection φ i₀ σ := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (column φ i₀ σ * star (column φ i₀ σ)) *
      (column φ i₀ σ * star (column φ i₀ σ)) =
      (Fintype.card I : ℝ) • (column φ i₀ σ * star (column φ i₀ σ)) := by
    rw [mul_assoc, ← mul_assoc (star _), column_inner, smul_mul_assoc,
      mul_smul_comm, ← mul_assoc, column_right]
  simp only [signProjection, smul_mul_assoc, mul_smul_comm, he, smul_smul]
  congr 1
  field_simp

lemma isStarProjection_signProjection (i₀ : I) (σ : I → Bool) :
    IsStarProjection (signProjection φ i₀ σ) :=
  ⟨signProjection_idem φ i₀ σ, signProjection_star φ i₀ σ⟩

include hτ in
lemma signProjection_trace (h1 : τ 1 = 1) (i₀ : I) (σ : I → Bool) :
    τ (signProjection φ i₀ σ) = (Fintype.card I : ℝ)⁻¹ := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [signProjection, map_smul, smul_eq_mul, hτ, column_inner, map_smul,
    smul_eq_mul, unit_trace φ τ hτ h1]
  field_simp

include hτ in
lemma block_traceSquare (i₀ i j : I) (x : A) :
    traceSquare τ (unit φ i₀ i * x * unit φ j i₀) =
      τ (star x * unit φ i i * x * unit φ j j) := by
  have he : star (unit φ i₀ i * x * unit φ j i₀) *
      (unit φ i₀ i * x * unit φ j i₀) =
      unit φ i₀ j * (star x * unit φ i i * x * unit φ j i₀) := by
    simp only [star_mul, unit_star, mul_assoc]
    rw [← mul_assoc (unit φ i i₀), unit_mul, ite_eq_left rfl]
  rw [traceSquare, he, hτ, mul_assoc (star x * unit φ i i * x), unit_mul, ite_eq_left rfl]

include hτ in
lemma sum_block_traceSquare (i₀ : I) (x : A) :
    (∑ i, ∑ j, traceSquare τ (unit φ i₀ i * x * unit φ j i₀)) = traceSquare τ x := by
  simp_rw [block_traceSquare φ τ hτ]
  simp only [← map_sum, ← Finset.mul_sum, unit_sum, mul_one]
  rw [← Finset.sum_mul, ← Finset.mul_sum, unit_sum, mul_one]
  rfl

lemma column_left_star (i₀ : I) (σ : I → Bool) :
    unit φ i₀ i₀ * star (column φ i₀ σ) = star (column φ i₀ σ) := by
  simpa only [star_mul, unit_star] using congrArg star (column_right φ i₀ σ)

lemma column_compression_left (i₀ : I) (σ : I → Bool) (x : A) :
    unit φ i₀ i₀ * (star (column φ i₀ σ) * x * column φ i₀ σ) =
      star (column φ i₀ σ) * x * column φ i₀ σ := by
  rw [← mul_assoc, ← mul_assoc, column_left_star]

lemma column_compression_right (i₀ : I) (σ : I → Bool) (x : A) :
    (star (column φ i₀ σ) * x * column φ i₀ σ) * unit φ i₀ i₀ =
      star (column φ i₀ σ) * x * column φ i₀ σ := by
  rw [mul_assoc _ (column _ _ _), column_right]

include hτ in
lemma column_outer_traceSquare (i₀ : I) (σ : I → Bool) (z : A)
    (hzl : unit φ i₀ i₀ * z = z) (hzr : z * unit φ i₀ i₀ = z) :
    traceSquare τ (column φ i₀ σ * z * star (column φ i₀ σ)) =
      (Fintype.card I : ℝ)^2 * traceSquare τ z := by
  have he : star (column φ i₀ σ * z * star (column φ i₀ σ)) *
      (column φ i₀ σ * z * star (column φ i₀ σ)) =
      (Fintype.card I : ℝ) •
        (column φ i₀ σ * (star z * z) * star (column φ i₀ σ)) := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star (column φ i₀ σ)), column_inner, smul_mul_assoc,
      ← mul_assoc (unit φ i₀ i₀), hzl, mul_smul_comm, mul_smul_comm]
  rw [traceSquare, he, map_smul, smul_eq_mul,
    trace_rotate τ hτ, mul_assoc, column_inner, mul_smul_comm, map_smul,
    smul_eq_mul, mul_assoc (star z), hzr, traceSquare, pow_two]
  ring

include hτ in
lemma signProjection_compression_traceSquare (i₀ : I) (σ : I → Bool) (x : A) :
    traceSquare τ (signProjection φ i₀ σ * x * signProjection φ i₀ σ) =
      (Fintype.card I : ℝ)⁻¹^2 *
        traceSquare τ (star (column φ i₀ σ) * x * column φ i₀ σ) := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : signProjection φ i₀ σ * x * signProjection φ i₀ σ =
      (Fintype.card I : ℝ)⁻¹^2 •
        (column φ i₀ σ * (star (column φ i₀ σ) * x * column φ i₀ σ) *
          star (column φ i₀ σ)) := by
    simp only [signProjection, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_two, mul_assoc]
  rw [he, traceSquare_smul, column_outer_traceSquare φ τ hτ _ _ _
    (column_compression_left φ i₀ σ x) (column_compression_right φ i₀ σ x)]
  field_simp

lemma expectation_left (x : A) (k l : I) :
    unit φ k l * expectation φ x =
      (Fintype.card I : ℝ)⁻¹ • ∑ j, unit φ k j * x * unit φ j l := by
  rw [expectation, mul_smul_comm, Finset.mul_sum]
  simp only [Finset.mul_sum, ← mul_assoc, unit_mul]
  rw [Finset.sum_eq_single l]
  · simp only [ite_true]
  · intro i hi hil
    simp [Ne.symm hil]
  · simp

lemma expectation_right (x : A) (k l : I) :
    expectation φ x * unit φ k l =
      (Fintype.card I : ℝ)⁻¹ • ∑ j, unit φ k j * x * unit φ j l := by
  rw [expectation, smul_mul_assoc, Finset.sum_mul]
  simp only [Finset.sum_mul, mul_assoc, unit_mul]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true, ← mul_assoc]
  · intro i hi hik
    simp [hik]
  · simp

lemma expectation_commutes (x : A) (k l : I) :
    unit φ k l * expectation φ x = expectation φ x * unit φ k l := by
  rw [expectation_left, expectation_right]

lemma expectation_star (x : A) : star (expectation φ x) = expectation φ (star x) := by
  simp only [expectation, star_smul, star_trivial,
    star_sum, star_mul, unit_star, mul_assoc]

include hτ in
lemma unit_mul_trace (w : A) (hw : ∀ i j, unit φ i j * w = w * unit φ i j) (i₀ : I) :
    τ (unit φ i₀ i₀ * w) = (Fintype.card I : ℝ)⁻¹ * τ w := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (i j : I) : τ (unit φ i i * w) = τ (unit φ j j * w) := by
    have h := hτ (unit φ i j) (unit φ j i * w)
    rw [← mul_assoc, unit_mul, ite_eq_left rfl, mul_assoc, ← hw,
      ← mul_assoc, unit_mul, ite_eq_left rfl] at h
    exact h
  have hs : (Fintype.card I : ℝ) * τ (unit φ i₀ i₀ * w) = τ w := by
    calc
      _ = ∑ i, τ (unit φ i i * w) := by
        simp only [← he i₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = τ ((∑ i, unit φ i i) * w) := by rw [Finset.sum_mul, map_sum]
      _ = τ w := by rw [unit_sum, one_mul]
  apply mul_left_cancel₀ hc
  rw [hs, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

lemma expectation_star_commutes (x : A) (i j : I) :
    unit φ i j * star (expectation φ x) = star (expectation φ x) * unit φ i j := by
  rw [expectation_star]
  exact expectation_commutes φ (star x) i j

include hτ in
lemma diagonal_traceSquare (i₀ : I) (x : A) :
    traceSquare τ (∑ i, unit φ i₀ i * x * unit φ i i₀) =
      (Fintype.card I : ℝ) * traceSquare τ (expectation φ x) := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ i, unit φ i₀ i * x * unit φ i i₀) =
      (Fintype.card I : ℝ) • (unit φ i₀ i₀ * expectation φ x) := by
    rw [expectation_left, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hw : ∀ i j, unit φ i j * (star (expectation φ x) * expectation φ x) =
      (star (expectation φ x) * expectation φ x) * unit φ i j := by
    intro i j
    rw [← mul_assoc, expectation_star_commutes, mul_assoc, expectation_commutes,
      ← mul_assoc]
  have ht : traceSquare τ (unit φ i₀ i₀ * expectation φ x) =
      (Fintype.card I : ℝ)⁻¹ * traceSquare τ (expectation φ x) := by
    rw [traceSquare, star_mul, unit_star, mul_assoc,
      ← mul_assoc (unit φ i₀ i₀), unit_mul, ite_eq_left rfl,
      ← mul_assoc, ← expectation_star_commutes, mul_assoc, unit_mul_trace φ τ hτ _ hw]
    rfl
  rw [he, traceSquare_smul, ht]
  field_simp

end MatrixAlgebra

section CompressionBound

open Matrix

variable {A I H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H) (hv : ∀ a, ‖v a‖^2 = traceSquare τ a)

lemma matrixSignSum_vector (i₀ : I) (x : A) (σ : I → Bool) :
    matrixSignSum (fun i j => v (unit φ i₀ i * x * unit φ j i₀)) σ =
      v (star (column φ i₀ σ) * x * column φ i₀ σ) := by
  rw [column_sandwich]
  simp only [matrixSignSum, map_sum, map_smul]

include hτ hv in
theorem exists_signProjection_bound (i₀ : I) (x : A) :
    ∃ σ : I → Bool,
      traceSquare τ (signProjection φ i₀ σ * x * signProjection φ i₀ σ) ≤
        (Fintype.card I : ℝ)⁻¹ * traceSquare τ (expectation φ x) +
        2 * (Fintype.card I : ℝ)⁻¹^2 * traceSquare τ x := by
  have : Nonempty I := ⟨i₀⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨σ, hσ⟩ := exists_matrix_sign_bound
    (fun i j => v (unit φ i₀ i * x * unit φ j i₀))
  rw [matrixSignSum_vector, ← map_sum, hv, hv, diagonal_traceSquare φ τ hτ] at hσ
  simp_rw [hv] at hσ
  rw [sum_block_traceSquare φ τ hτ] at hσ
  refine ⟨σ, ?_⟩
  rw [signProjection_compression_traceSquare φ τ hτ]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹^2 *
        ((Fintype.card I : ℝ) * traceSquare τ (expectation φ x) + 2 * traceSquare τ x) :=
      mul_le_mul_of_nonneg_left hσ (sq_nonneg _)
    _ = _ := by field_simp

end CompressionBound

section FiniteFamily

open Matrix

variable {A I J H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H) (hv : ∀ a, ‖v a‖^2 = traceSquare τ a)

include hτ in
lemma familyTrace_tracial (x y : J → A) :
    familyTrace τ (x*y) = familyTrace τ (y*x) := by
  simp only [familyTrace_apply, Pi.mul_apply, hτ]

include hv in
lemma familyVector_norm_sq (x : J → A) :
    ‖familyVector v x‖^2 = traceSquare (familyTrace τ) x := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [familyVector_apply, hv, traceSquare, familyTrace_apply,
    Pi.mul_apply, Pi.star_apply]

include hτ hv in
theorem exists_signProjection_family_bound (i₀ : I) (x : J → A) :
    ∃ σ : I → Bool,
      (∑ j, traceSquare τ (signProjection φ i₀ σ * x j * signProjection φ i₀ σ)) ≤
        (Fintype.card I : ℝ)⁻¹ * (∑ j, traceSquare τ (expectation φ (x j))) +
        2 * (Fintype.card I : ℝ)⁻¹^2 * ∑ j, traceSquare τ (x j) := by
  obtain ⟨σ, hσ⟩ := exists_signProjection_bound (familyHom (J := J) φ) (familyTrace τ)
    (familyTrace_tracial τ hτ) (familyVector v) (familyVector_norm_sq τ v hv) i₀ x
  refine ⟨σ, ?_⟩
  simpa only [traceSquare, familyTrace_apply, Pi.mul_apply, Pi.star_apply,
    signProjection_family, expectation_family] using hσ

end FiniteFamily

section ActualGNS

open scoped ComplexOrder

open UniformSpace

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [LinearOrder I] [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ)

lemma vector_norm_sq (a : A) : ‖vector τ a‖^2 = traceSquare (realTrace τ) a := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [vector_apply, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, traceSquare, realTrace_apply]
  rfl

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma real_smul_mem_range (r : ℝ) {a : A} (ha : a ∈ φ.range) : r • a ∈ φ.range := by
  obtain ⟨b, rfl⟩ := ha
  exact ⟨r • b, φ.toLinearMap.map_smul_of_tower r b⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma signProjection_mem_range (i₀ : I) (σ : I → Bool) :
    signProjection φ i₀ σ ∈ φ.range := by
  have hu (i j : I) : unit φ i j ∈ φ.range := ⟨_, rfl⟩
  have hc : column φ i₀ σ ∈ φ.range :=
    Subalgebra.sum_mem _ (fun i _ => real_smul_mem_range φ _ (hu i i₀))
  have hcs : star (column φ i₀ σ) ∈ φ.range := φ.range.star_mem' hc
  exact real_smul_mem_range φ _ (φ.range.mul_mem hc hcs)

theorem exists_rankOne_finite_test (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
    (hone : τ 1 = 1) (i₀ : I) (x : J → A) :
    ∃ q : A, q ∈ φ.range ∧ IsStarProjection q ∧
      (τ q).re = (Fintype.card I : ℝ)⁻¹ ∧
      (∑ j, ‖vector τ (q * x j * q)‖^2) ≤
        (Fintype.card I : ℝ)⁻¹ * (∑ j, ‖vector τ (expectation φ (x j))‖^2) +
        2 * (Fintype.card I : ℝ)⁻¹^2 * (∑ j, ‖vector τ (x j)‖^2) := by
  let : InnerProductSpace ℝ τ.GNS := InnerProductSpace.complexToReal
  have hr : ∀ a b : A, realTrace τ (a*b) = realTrace τ (b*a) :=
    fun a b => congrArg Complex.re (hτ a b)
  obtain ⟨σ, hσ⟩ := exists_signProjection_family_bound φ (realTrace τ) hr
    (vector τ) (vector_norm_sq τ) i₀ x
  refine ⟨signProjection φ i₀ σ, signProjection_mem_range φ i₀ σ,
    isStarProjection_signProjection φ i₀ σ, ?_, ?_⟩
  · exact signProjection_trace φ (realTrace τ) hr (by simp [hone]) i₀ σ
  · simpa only [vector_norm_sq] using hσ

end ActualGNS

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_LocalQuantization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

open Filter

namespace Kadison.LocalQuantization

open TracialGNS

section Bridge

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma expectation_eq (x : A) :
    FiniteTest.expectation φ x=MatrixExpectation.expectation φ x := by
  rw [FiniteTest.expectation,MatrixExpectation.expectation_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [FiniteTest.unit]
  congr 1
  change Complex.ofReal ((Fintype.card I : ℝ)⁻¹)=(Fintype.card I : ℂ)⁻¹
  simp

variable [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ)

lemma vector_eq (a : A) : FiniteTest.vector τ a=algebraVector τ a := rfl

end Bridge

section FiniteTests

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hone : τ 1=1)

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] A)

include hτ hone in
theorem exists_small_projection_oai
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (x : J → A)
    (hx : ∀ j, Tendsto (fun n => algebraVector τ (MatrixExpectation.expectation (stage n) (x j)))
      atTop (𝓝 0))
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ (n : ℕ) (q : A), q∈(stage n).range ∧ IsStarProjection q ∧
      0<(τ q).re ∧ (τ q).re<η ∧
      (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re := by
  have hinv : Tendsto (fun n => (Fintype.card (ι n):ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hgrow
  have hsum : Tendsto
      (fun n => ∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2)
      atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by omega : 2≠0),Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => (hx j).norm.pow 2)
  have herr : Tendsto
      (fun n => (∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2) +
        2*(Fintype.card (ι n):ℝ)⁻¹*(∑ j, ‖algebraVector τ (x j)‖^2)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,add_zero] using
      hsum.add ((tendsto_const_nhds.mul hinv).mul_const (∑ j, ‖algebraVector τ (x j)‖^2))
  have hev := (hinv.eventually (gt_mem_nhds hη)).and
    (herr.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  obtain ⟨n,hn,herrn⟩ := hev.exists
  obtain ⟨q,hq,hproj,htrace,hbound⟩ :=
    FiniteTest.exists_rankOne_finite_test τ (stage n) hτ hone (Classical.arbitrary (ι n)) x
  simp only [vector_eq,expectation_eq] at hbound
  have hp : 0<(Fintype.card (ι n):ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  refine ⟨n,q,hq,hproj,htrace ▸ hp,htrace ▸ hn,?_⟩
  rw [htrace]
  calc
    _ ≤ (Fintype.card (ι n):ℝ)⁻¹ *
        ((∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2) +
          2*(Fintype.card (ι n):ℝ)⁻¹*(∑ j, ‖algebraVector τ (x j)‖^2)) := by
      nlinarith [hbound]
    _ < (Fintype.card (ι n):ℝ)⁻¹*ε^2 := mul_lt_mul_of_pos_left herrn hp
    _ = _ := mul_comm _ _

end FiniteTests

end Kadison.LocalQuantization

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.LocalQuantization.exists_small_projection_oai.{u_1, u_2, u_3} := @OAI.Kadison.LocalQuantization.exists_small_projection_oai.{u_1, u_2, u_3}
