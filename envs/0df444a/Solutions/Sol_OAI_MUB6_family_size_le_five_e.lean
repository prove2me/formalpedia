-- Prove2me | solution 1 for OAI.MUB6.family_size_le_five_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:42:39.353659+00:00
-- url     : https://prove2.me/submissions/46fc2239-a284-4be9-ae5c-b6bb7d7d1c35

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E078
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E132
import Definitions.Def_OAIQ106E134
import Definitions.Def_OAIQ106E135
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E154
import Definitions.Def_OAIQ106E167
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_false_of_gram_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_allRowsSound_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_allKeyMoments_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_originalNodeEval88_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_originalReductionEval_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_allRowsSound_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_expandedIdentity1_e
import Theorems.Thm_OAI_MUB6_complete_family_square_not_hadamard_e
import Theorems.Thm_OAI_MUB6_pair_cross_certificate_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem unit_norm {z : ℂ} (hz : Complex.normSq z = 1) : ‖z‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

theorem character_norm (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : ‖character x a‖ = 1 := by
  simp [character, unit_norm (hx _)]

theorem g_norm_le_one {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    ‖g H a‖ ≤ 1 := by
  have hb : ‖∑ k, character (fun i => H i k) a‖ ≤ (6 : ℝ) := by
    calc
      _ ≤ ∑ k, ‖character (fun i => H i k) a‖ := norm_sum_le _ _
      _ = 6 := by simp [character_norm _ (fun i => hH.1 i _) a]
  have hi : ‖(6 : ℂ)⁻¹‖ = (6 : ℝ)⁻¹ := by
    have h := map_inv₀ Complex.isAbsoluteValueNorm.abvHom (6 : ℂ)
    change ‖(6 : ℂ)⁻¹‖ = ‖(6 : ℂ)‖⁻¹ at h
    simpa only [Complex.norm_ofNat] using h
  simpa [g, Complex.norm_mul, hi] using
    mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 6⁻¹)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite trace-preserving Kraus maps

The proof establishes the fixed-point commutation step needed in Weiner's completion
argument. It replaces the appeal to two-positivity and the multiplicative domain
with the squared Hilbert--Schmidt norm of each commutator.
-/

namespace MUB6.Weiner

open scoped BigOperators ComplexOrder
open Matrix

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma kraus_conjTranspose (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    kraus A Xᴴ = (kraus A X)ᴴ := by
  simp [kraus, conjTranspose_sum, conjTranspose_mul, mul_assoc]

omit [DecidableEq n] in
lemma trace_kraus (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (kraus A X).trace = ((∑ i, A i * (A i)ᴴ) * X).trace := by
  simp only [kraus, Matrix.trace_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- A trace-preserving Kraus sum satisfies the second normalization identity. -/
theorem right_unital_of_trace_preserving (A : ι → Matrix n n ℂ)
    (htrace : ∀ X : Matrix n n ℂ, (kraus A X).trace = X.trace) :
    ∑ i, A i * (A i)ᴴ = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← trace_kraus, htrace, Matrix.one_mul]

omit [DecidableEq n] in
/-- The trace of the sum of commutator squares. -/
lemma commutator_trace_identity (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    ∑ i, (((X * A i - A i * X)ᴴ * (X * A i - A i * X)).trace) =
      (Xᴴ * X * (∑ i, A i * (A i)ᴴ)).trace
      + (Xᴴ * (∑ i, (A i)ᴴ * A i) * X).trace
      - (kraus A Xᴴ * X).trace - (Xᴴ * kraus A X).trace := by
  simp only [conjTranspose_sub, conjTranspose_mul]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, Finset.sum_sub_distrib,
    kraus, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  have h₁ : ∀ i, (((A i)ᴴ * Xᴴ) * (X * A i)).trace =
      ((Xᴴ * X) * (A i * (A i)ᴴ)).trace := by
    intro i
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at h₁ ⊢
  simp only [h₁]
  ring

/-- Fixed points of a unital trace-preserving finite Kraus sum commute with its
Kraus operators. The result needs no positivity axioms or external solver. -/
theorem commute_of_kraus_fixed (A : ι → Matrix n n ℂ)
    (hleft : ∑ i, (A i)ᴴ * A i = 1)
    (hright : ∑ i, A i * (A i)ᴴ = 1)
    (X : Matrix n n ℂ) (hX : kraus A X = X) (i : ι) :
    Commute X (A i) := by
  have hstar : kraus A Xᴴ = Xᴴ := by rw [kraus_conjTranspose, hX]
  have hsum : ∑ j, (((X * A j - A j * X)ᴴ * (X * A j - A j * X)).trace) = 0 := by
    rw [commutator_trace_identity, hleft, hright, hX, hstar]
    simp
  have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (((X * A j - A j * X)ᴴ * (X * A j - A j * X)).trace) := by
    intro j _
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hi)

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Superoperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realignment of a self-adjoint projection

The complement operator in Weiner's argument is an orthogonal projection whose
matrix is invariant under realignment. Its columns therefore form a finite
Kraus family; choosing an orthonormal basis of its range is unnecessary.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma applySuper_add (C : Matrix (n × n) (n × n) ℂ) (X Y : Matrix n n ℂ) :
    applySuper C (X + Y) = applySuper C X + applySuper C Y := by
  ext i j
  simp [applySuper, mul_add, Finset.sum_add_distrib]

omit [DecidableEq n] in
lemma applySuper_sub (C : Matrix (n × n) (n × n) ℂ) (X Y : Matrix n n ℂ) :
    applySuper C (X - Y) = applySuper C X - applySuper C Y := by
  ext i j
  simp [applySuper, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq n] in
lemma applySuper_smul (C : Matrix (n × n) (n × n) ℂ) (a : ℂ) (X : Matrix n n ℂ) :
    applySuper C (a • X) = a • applySuper C X := by
  ext i j
  simp [applySuper, Finset.mul_sum, mul_left_comm]

omit [DecidableEq n] in
lemma applySuper_real_smul (C : Matrix (n × n) (n × n) ℂ) (a : ℝ) (X : Matrix n n ℂ) :
    applySuper C (a • X) = a • applySuper C X := by
  simpa only [← Complex.coe_smul] using applySuper_smul C (a : ℂ) X

lemma applySuper_one (X : Matrix n n ℂ) : applySuper 1 X = X := by
  ext i j
  simp [applySuper, Matrix.one_apply]

omit [DecidableEq n] in
lemma applySuper_add_left (C D : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (C + D) X = applySuper C X + applySuper D X := by
  ext i j
  simp [applySuper, add_mul, Finset.sum_add_distrib]

omit [DecidableEq n] in
lemma applySuper_sub_left (C D : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (C - D) X = applySuper C X - applySuper D X := by
  ext i j
  simp [applySuper, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
lemma applySuper_sum_left {κ : Type*} [Fintype κ]
    (C : κ → Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (∑ r, C r) X = ∑ r, applySuper (C r) X := by
  ext i j
  simp only [applySuper, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
lemma superColumn_fixed (C : Matrix (n × n) (n × n) ℂ) (hC : C * C = C)
    (p : n × n) : applySuper C (superColumn C p) = superColumn C p := by
  ext i j
  exact congrArg (fun A : Matrix (n × n) (n × n) ℂ => A (i, j) p) hC

lemma applySuper_one_entry (C : Matrix (n × n) (n × n) ℂ) (i j : n) :
    applySuper C 1 i j = ∑ k, C (i, j) (k, k) := by
  simp [applySuper, Fintype.sum_prod_type, Matrix.one_apply]

/-- A self-adjoint unital superoperator preserves the ordinary matrix trace. -/
theorem applySuper_trace (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hunital : applySuper C 1 = 1) (X : Matrix n n ℂ) :
    (applySuper C X).trace = X.trace := by
  have hentry (u v : n × n) : C u v = star (C v u) := by
    exact (congrArg (fun A : Matrix (n × n) (n × n) ℂ => A u v) hherm).symm
  have hdiag (i j : n) : (∑ k, C (k, k) (i, j)) = if i = j then 1 else 0 := by
    calc
      _ = star (∑ k, C (i, j) (k, k)) := by
        rw [star_sum]
        exact Finset.sum_congr rfl (fun k _ => hentry (k, k) (i, j))
      _ = star (applySuper C 1 i j) := by rw [applySuper_one_entry]
      _ = _ := by rw [hunital]; simp [Matrix.one_apply]
  calc
    (applySuper C X).trace = ∑ i, ∑ p, C (i, i) p * X p.1 p.2 := rfl
    _ = ∑ p, (∑ i, C (i, i) p) * X p.1 p.2 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = X.trace := by simp [hdiag, Fintype.sum_prod_type, Matrix.trace]

omit [DecidableEq n] in
/-- A Hermitian idempotent invariant under realignment is a Kraus sum of its
reshaped columns. -/
theorem applySuper_eq_kraus_columns (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (X : Matrix n n ℂ) : applySuper C X = kraus (superColumn C) X := by
  have hgram (u v : n × n) : ∑ a, star (C v a) * C u a = C u v := by
    have h := congrArg (fun A : Matrix (n × n) (n × n) ℂ => A u v)
      (show C * Cᴴ = C by rw [hherm, hidem])
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h
  have hmul (a b c : ℂ) : a * b * c = b * (a * c) := by ring
  ext i j
  symm
  calc
    kraus (superColumn C) X i j =
        ∑ l, ∑ k, X k l * (∑ a, star (C (k, i) a) * C (l, j) a) := by
      simp only [kraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, superColumn]
      simp_rw [Finset.sum_mul, hmul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ l, ∑ k, C (i, j) (k, l) * X k l := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      rw [hgram, ← hreal i j k l, mul_comm]
    _ = applySuper C X i j := by
      rw [Finset.sum_comm]
      simp only [applySuper, Fintype.sum_prod_type]

omit [DecidableEq n] in
lemma applySuper_conjTranspose (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (X : Matrix n n ℂ) : applySuper C Xᴴ = (applySuper C X)ᴴ := by
  simp only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus_conjTranspose]

omit [DecidableEq n] in
lemma applySuper_eq_sum_smul_columns (C : Matrix (n × n) (n × n) ℂ)
    (X : Matrix n n ℂ) : applySuper C X = ∑ p, X p.1 p.2 • superColumn C p := by
  ext i j
  simp only [applySuper, Matrix.sum_apply, Matrix.smul_apply, superColumn, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Every fixed point of a unital realigned orthogonal projection commutes with
every reshaped column of that projection. -/
theorem commute_of_super_fixed (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1)
    (X : Matrix n n ℂ) (hX : applySuper C X = X) (p : n × n) :
    Commute X (superColumn C p) := by
  have hleft : ∑ q, (superColumn C q)ᴴ * superColumn C q = 1 := by
    simpa only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus, Matrix.mul_one]
      using hunital
  have hright : ∑ q, superColumn C q * (superColumn C q)ᴴ = 1 := by
    apply right_unital_of_trace_preserving
    intro Y
    rw [← applySuper_eq_kraus_columns C hherm hidem hreal]
    exact applySuper_trace C hherm hunital Y
  apply commute_of_kraus_fixed (superColumn C) hleft hright X _ p
  rwa [← applySuper_eq_kraus_columns C hherm hidem hreal]

/-- The entire fixed space is commutative. Its elements are linear combinations
of the reshaped columns, which all commute with every fixed point. -/
theorem super_fixedPoints_commute (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1) (X Y : Matrix n n ℂ)
    (hX : applySuper C X = X) (hY : applySuper C Y = Y) : Commute X Y := by
  rw [← hY, applySuper_eq_sum_smul_columns]
  apply Commute.sum_right
  intro p _
  exact (commute_of_super_fixed C hherm hidem hreal hunital X hX p).smul_right _

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Complement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete complement supermatrix

The Hermitian and realignment symmetries are algebraic identities for arbitrary
complex vectors. Orthonormality and mutual unbiasedness are needed for the
separate unitality and idempotence identities.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

omit [Fintype n] in
lemma traceMatrix_hermitian : (traceMatrix : Matrix (n × n) (n × n) ℂ)ᴴ = traceMatrix := by
  ext p q
  simp [traceMatrix, Matrix.conjTranspose_apply, and_comm]

omit [Fintype n] [DecidableEq n] in
lemma pinchingMatrix_hermitian (v : κ → n → ℂ) : (pinchingMatrix v)ᴴ = pinchingMatrix v := by
  ext p q
  simp only [Matrix.conjTranspose_apply, pinchingMatrix, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype n] in
lemma complementMatrix_hermitian (v : ι → κ → n → ℂ) :
    (complementMatrix v)ᴴ = complementMatrix v := by
  simp [complementMatrix, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_sum, traceMatrix_hermitian, pinchingMatrix_hermitian]

omit [Fintype n] [DecidableEq n] in
lemma pinchingMatrix_realigned (v : κ → n → ℂ) : IsRealigned (pinchingMatrix v) := by
  intro i j k l
  apply Finset.sum_congr rfl
  intro a _
  dsimp [pinchingMatrix]
  ring

omit [Fintype n] in
/-- The identity and trace supermatrices interchange under realignment. -/
lemma one_trace_realignment (i j k l : n) :
    (1 : Matrix (n × n) (n × n) ℂ) (i, j) (k, l) = traceMatrix (l, j) (k, i) := by
  simp [Matrix.one_apply, traceMatrix, Prod.mk.injEq, and_comm, eq_comm]

omit [Fintype n] in
lemma complementMatrix_realigned (v : ι → κ → n → ℂ) : IsRealigned (complementMatrix v) := by
  intro i j k l
  have hsum : (∑ r, pinchingMatrix (v r) (i, j) (k, l)) =
      ∑ r, pinchingMatrix (v r) (l, j) (k, i) := by
    apply Finset.sum_congr rfl
    intro r _
    exact pinchingMatrix_realigned (v r) i j k l
  have h₂ : traceMatrix (i, j) (k, l) = (1 : Matrix (n × n) (n × n) ℂ) (l, j) (k, i) :=
    (one_trace_realignment l j k i).symm
  simp only [complementMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply]
  rw [hsum, one_trace_realignment i j k l, h₂]
  ring

lemma applySuper_traceMatrix (X : Matrix n n ℂ) :
    applySuper traceMatrix X = X.trace • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [applySuper, traceMatrix, Fintype.sum_prod_type, Matrix.trace]
  · simp [applySuper, traceMatrix, hij]

lemma traceMatrix_square : (traceMatrix : Matrix (n × n) (n × n) ℂ) * traceMatrix =
    (Fintype.card n : ℂ) • traceMatrix := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, hp, hq]

/-- Composing a unital map with the trace map leaves the trace map unchanged. -/
lemma mul_traceMatrix_of_unital (C : Matrix (n × n) (n × n) ℂ)
    (hC : applySuper C 1 = 1) : C * traceMatrix = traceMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hkl : k = l
  · subst l
    have h := congrArg (fun X : Matrix n n ℂ => X i j) hC
    rw [applySuper_one_entry] at h
    simpa [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, Matrix.one_apply] using h
  · simp [Matrix.mul_apply, traceMatrix, hkl]

/-- Self-adjoint unital maps also leave the trace map unchanged on the other side. -/
lemma traceMatrix_mul_of_hermitian_unital (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hC : applySuper C 1 = 1) : traceMatrix * C = traceMatrix := by
  have h := congrArg Matrix.conjTranspose (mul_traceMatrix_of_unital C hC)
  simpa only [Matrix.conjTranspose_mul, traceMatrix_hermitian, hherm] using h

/-- A pinching supermatrix is unital when its vectors are unit and complete. -/
lemma pinchingMatrix_unital (v : κ → n → ℂ)
    (hnorm : ∀ a, ∑ i, star (v a i) * v a i = 1)
    (hcomplete : ∀ i j, ∑ a, v a i * star (v a j) = if i = j then 1 else 0) :
    applySuper (pinchingMatrix v) 1 = 1 := by
  ext i j
  rw [applySuper_one_entry]
  change (∑ k, ∑ a, v a i * star (v a j) * star (v a k) * v a k) = _
  rw [Finset.sum_comm]
  have hinner (a : κ) :
      (∑ k, v a i * star (v a j) * star (v a k) * v a k) = v a i * star (v a j) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hnorm]
    simp
  simp only [hinner]
  simpa [Matrix.one_apply] using hcomplete i j

/-- Six pinching maps in dimension six leave the identity fixed. -/
lemma complementMatrix_unital (v : Fin 6 → κ → Fin 6 → ℂ)
    (hnorm : ∀ r a, ∑ i, star (v r a i) * v r a i = 1)
    (hcomplete : ∀ r i j, ∑ a, v r a i * star (v r a j) = if i = j then 1 else 0) :
    applySuper (complementMatrix v) 1 = 1 := by
  rw [complementMatrix, applySuper_sub_left, applySuper_add_left,
    applySuper_one, applySuper_traceMatrix, applySuper_sum_left]
  simp only [pinchingMatrix_unital _ (hnorm _) (hcomplete _)]
  norm_num [ofNat_smul_eq_nsmul, nsmul_eq_mul]

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Frame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one frame identities used to calculate the complement projection. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {I κ η n : Type*} [Fintype I] [Fintype κ] [Fintype η] [Fintype n]

lemma frameOperator_idempotent [DecidableEq κ] (v : κ → I → ℂ)
    (hv : ∀ a b, star (v a) ⬝ᵥ v b = if a = b then 1 else 0) :
    frameOperator v * frameOperator v = frameOperator v := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hv]
  simp [apply_ite]

lemma frameOperator_mul (v : κ → I → ℂ) (w : η → I → ℂ) (c : ℂ)
    (hvw : ∀ a b, star (v a) ⬝ᵥ w b = c) :
    frameOperator v * frameOperator w = c • Matrix.vecMulVec (∑ a, v a) (star (∑ b, w b)) := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hvw, Matrix.vecMulVec_smul]
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_mul, Finset.mul_sum]

lemma frameOperator_mulVec (v : κ → n → ℂ) (w : n → ℂ) :
    frameOperator v *ᵥ w = ∑ a, (star (v a) ⬝ᵥ w) • v a := by
  simp [frameOperator, Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]

lemma frameOperator_mulVec_of_inner (v : κ → n → ℂ) (w : n → ℂ) (c : ℂ)
    (h : ∀ a, star (v a) ⬝ᵥ w = c) :
    frameOperator v *ᵥ w = c • ∑ a, v a := by
  simp only [frameOperator_mulVec, h, Finset.smul_sum]

lemma frameOperator_mulVec_self [DecidableEq κ] (v : κ → n → ℂ)
    (h : ∀ a b, star (v a) ⬝ᵥ v b = if a = b then 1 else 0) (b : κ) :
    frameOperator v *ᵥ v b = v b := by
  rw [frameOperator_mulVec]
  simp [h]

/-- Transfer a Hermitian matrix across the complex dot product. -/
lemma dotProduct_mulVec_of_hermitian [DecidableEq n] (C : Matrix n n ℂ)
    (hC : Cᴴ = C) (u v : n → ℂ) :
    star u ⬝ᵥ (C *ᵥ v) = star (C *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hC]

lemma dotProduct_fixed_of_image [DecidableEq n] (C : Matrix n n ℂ)
    (hC : Cᴴ = C) (u v w : n → ℂ) (a : ℂ)
    (hu : C *ᵥ u = a • w) (hv : C *ᵥ v = v) :
    star u ⬝ᵥ v = star a * (star w ⬝ᵥ v) := by
  calc
    star u ⬝ᵥ v = star u ⬝ᵥ (C *ᵥ v) := by rw [hv]
    _ = star (C *ᵥ u) ⬝ᵥ v := dotProduct_mulVec_of_hermitian C hC u v
    _ = star a * (star w ⬝ᵥ v) := by
      rw [hu]
      simp [dotProduct, Finset.mul_sum, mul_assoc]

lemma projectorVector_inner (v w : n → ℂ) :
    star (projectorVector v) ⬝ᵥ projectorVector w =
      (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) := by
  simp only [dotProduct, projectorVector, Pi.star_apply, star_sum, star_mul, star_star,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] in
lemma pinchingMatrix_eq_frameOperator [DecidableEq n] (v : κ → n → ℂ) :
    pinchingMatrix v = frameOperator (fun a => projectorVector (v a)) := by
  ext p q
  simp only [pinchingMatrix, frameOperator, Matrix.sum_apply, Matrix.vecMulVec_apply,
    projectorVector, Pi.star_apply, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_ComplementAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of the missing-basis projection

The six diagonal expectation operators and the trace operator satisfy a small
multiplication table. The proof shows that the resulting complement operator
is idempotent, using ring algebra rather than numerical approximation.
-/

namespace MUB6.Weiner

variable {R : Type*} [Ring R]

open scoped BigOperators

/-- A finite family of idempotents whose off-diagonal products are one common
operator has an explicit square for its sum. -/
theorem sum_pairwise_projection_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → R) (P : R)
    (h : ∀ i j, D i * D j = if i = j then D i else P) :
    (∑ i, D i) * (∑ i, D i) = (∑ i, D i) +
      ((Fintype.card ι : R) ^ 2 - (Fintype.card ι : R)) * P := by
  have h' (i j : ι) : D i * D j = (if i = j then D i - P else 0) + P := by
    rw [h]
    split_ifs <;> simp
  simp_rw [Finset.sum_mul, Finset.mul_sum, h', Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  noncomm_ring

/-- The multiplication table for six unbiased expectation projections makes
`1 + W - S` idempotent, where `W` is the unnormalized trace operator and `S`
is the sum of the six expectations. -/
theorem complement_idempotent (S W : R)
    (hSS : S * S = S + 5 * W)
    (hSW : S * W = 6 * W) (hWS : W * S = 6 * W)
    (hWW : W * W = 6 * W) :
    (1 + W - S) * (1 + W - S) = 1 + W - S := by
  noncomm_ring [hSS, hSW, hWS, hWW]

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_OrthogonalPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplication tables for six and seven unbiased pinching operators. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma six_projection_sum_square (D : Fin 6 → SuperSix)
    (hpair : ∀ r s, D r * D s = if r = s then D r else (1 / 6 : ℂ) • traceMatrix) :
    (∑ r, D r) * (∑ r, D r) = (∑ r, D r) + 5 * traceMatrix := by
  have h := sum_pairwise_projection_square D ((1 / 6 : ℂ) • traceMatrix) hpair
  norm_num at h
  have hcoeff : (1 / 6 : ℂ) • ((30 : SuperSix) * traceMatrix) = 5 * traceMatrix := by
    ext p q
    norm_num [Matrix.mul_apply, Matrix.ofNat_apply, ite_mul]
    ring
  rwa [hcoeff] at h

lemma projection_sum_mul_traceMatrix {m : ℕ} (D : Fin m → SuperSix)
    (hunital : ∀ r, applySuper (D r) 1 = 1) :
    (∑ r, D r) * traceMatrix = (m : SuperSix) * traceMatrix := by
  simp only [Matrix.sum_mul, mul_traceMatrix_of_unital _ (hunital _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma traceMatrix_mul_projection_sum {m : ℕ} (D : Fin m → SuperSix)
    (hherm : ∀ r, (D r)ᴴ = D r) (hunital : ∀ r, applySuper (D r) 1 = 1) :
    traceMatrix * (∑ r, D r) = (m : SuperSix) * traceMatrix := by
  simp only [Matrix.mul_sum, traceMatrix_mul_of_hermitian_unital _ (hherm _) (hunital _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma traceMatrix_six_square : (traceMatrix : SuperSix) * traceMatrix = 6 * traceMatrix := by
  calc
    (traceMatrix : SuperSix) * traceMatrix = (6 : ℂ) • traceMatrix := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using (traceMatrix_square (n := Fin 6))
    _ = 6 * traceMatrix := by
      ext p q
      norm_num [Matrix.mul_apply, Matrix.ofNat_apply, ite_mul]

/-- Six mutually unbiased unital pinching maps give an idempotent complement. -/
theorem six_complement_idempotent (D : Fin 6 → SuperSix)
    (hpair : ∀ r s, D r * D s = if r = s then D r else (1 / 6 : ℂ) • traceMatrix)
    (hherm : ∀ r, (D r)ᴴ = D r) (hunital : ∀ r, applySuper (D r) 1 = 1) :
    (1 + traceMatrix - ∑ r, D r) * (1 + traceMatrix - ∑ r, D r) =
      1 + traceMatrix - ∑ r, D r :=
  complement_idempotent _ _ (six_projection_sum_square D hpair)
    (projection_sum_mul_traceMatrix D hunital)
    (traceMatrix_mul_projection_sum D hherm hunital) traceMatrix_six_square

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_BasisFrame
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rank-one frames associated with actual orthonormal and unbiased bases. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma basisCoordinates_unit (b : MUB6.Basis) (a : Coord) :
    ∑ i, star (basisCoordinates b a i) * basisCoordinates b a i = 1 := by
  simpa only [basisCoordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, mul_comm]
    using b.inner_eq_one a

lemma basisCoordinates_complete (b : MUB6.Basis) (i j : Coord) :
    ∑ a, basisCoordinates b a i * star (basisCoordinates b a j) =
      if i = j then 1 else 0 := by
  have h := (EuclideanSpace.basisFun Coord ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hij := congrArg (fun A : CMatrix => A i j) h
  simpa [basisCoordinates, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, Matrix.one_apply] using hij

lemma basis_projectorVector_sum (b : MUB6.Basis) :
    (∑ a, projectorVector (basisCoordinates b a)) = traceVector := by
  funext p
  simpa only [Finset.sum_apply, projectorVector, traceVector] using
    basisCoordinates_complete b p.1 p.2

lemma traceVector_outer : Matrix.vecMulVec traceVector (star traceVector) =
    (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.vecMulVec_apply, traceVector, traceMatrix, hp, hq]

lemma basis_projector_inner (b c : MUB6.Basis) (a d : Coord) :
    star (projectorVector (basisCoordinates b a)) ⬝ᵥ
      projectorVector (basisCoordinates c d) =
        inner ℂ (b a) (c d) * star (inner ℂ (b a) (c d)) := by
  rw [projectorVector_inner]
  have h : star (basisCoordinates b a) ⬝ᵥ basisCoordinates c d = inner ℂ (b a) (c d) := by
    change star (b a).ofLp ⬝ᵥ (c d).ofLp = inner ℂ (b a) (c d)
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct (b a) (c d)).symm
  rw [h]

lemma basis_pinching_idempotent (b : MUB6.Basis) :
    pinchingMatrix (basisCoordinates b) * pinchingMatrix (basisCoordinates b) =
      pinchingMatrix (basisCoordinates b) := by
  simp only [pinchingMatrix_eq_frameOperator]
  apply frameOperator_idempotent
  intro a c
  rw [basis_projector_inner]
  rw [b.inner_eq_ite]
  split_ifs <;> simp

lemma mub_pinching_mul {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      (1 / 6 : ℂ) • (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  rw [pinchingMatrix_eq_frameOperator, pinchingMatrix_eq_frameOperator]
  have hov : ∀ a b, star (projectorVector (basisCoordinates (B r) a)) ⬝ᵥ
      projectorVector (basisCoordinates (B s) b) = (1 / 6 : ℂ) := by
    intro a b
    rw [basis_projector_inner]
    rw [Complex.star_def, Complex.mul_conj, hB r s hrs a b]
    norm_num
  have h := frameOperator_mul
    (fun a => projectorVector (basisCoordinates (B r) a))
    (fun b => projectorVector (basisCoordinates (B s) b)) (1 / 6 : ℂ) hov
  rwa [basis_projectorVector_sum, basis_projectorVector_sum, traceVector_outer] at h

lemma basis_pinching_unital (b : MUB6.Basis) :
    applySuper (pinchingMatrix (basisCoordinates b)) 1 = 1 :=
  pinchingMatrix_unital (basisCoordinates b) (basisCoordinates_unit b) (basisCoordinates_complete b)

lemma basis_complement_unital (B : Fin 6 → MUB6.Basis) :
    applySuper (complementMatrix (fun r => basisCoordinates (B r))) 1 = 1 :=
  complementMatrix_unital _ (fun r => basisCoordinates_unit (B r))
    (fun r => basisCoordinates_complete (B r))

lemma basis_pinching_pair {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      if r = s then pinchingMatrix (basisCoordinates (B r))
      else (1 / 6 : ℂ) • traceMatrix := by
  split_ifs with h
  · subst s
    exact basis_pinching_idempotent (B r)
  · exact mub_pinching_mul B hB r s h

lemma basis_complement_idempotent (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    complementMatrix (fun r => basisCoordinates (B r)) *
        complementMatrix (fun r => basisCoordinates (B r)) =
      complementMatrix (fun r => basisCoordinates (B r)) :=
  six_complement_idempotent _ (basis_pinching_pair B hB)
    (fun r => pinchingMatrix_hermitian (basisCoordinates (B r)))
    (fun r => basis_pinching_unital (B r))

lemma basis_projectorVector_orthonormal (b : MUB6.Basis) (a d : Coord) :
    star (projectorVector (basisCoordinates b a)) ⬝ᵥ
      projectorVector (basisCoordinates b d) = if a = d then 1 else 0 := by
  rw [basis_projector_inner, b.inner_eq_ite]
  split_ifs <;> simp

lemma basis_pinching_projectorVector (b : MUB6.Basis) (a : Coord) :
    pinchingMatrix (basisCoordinates b) *ᵥ projectorVector (basisCoordinates b a) =
      projectorVector (basisCoordinates b a) := by
  rw [pinchingMatrix_eq_frameOperator]
  exact frameOperator_mulVec_self _ (basis_projectorVector_orthonormal b) a

lemma mub_pinching_projectorVector {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) (a : Coord) :
    pinchingMatrix (basisCoordinates (B r)) *ᵥ projectorVector (basisCoordinates (B s) a) =
      (1 / 6 : ℂ) • traceVector := by
  rw [pinchingMatrix_eq_frameOperator]
  have hov : ∀ d, star (projectorVector (basisCoordinates (B r) d)) ⬝ᵥ
      projectorVector (basisCoordinates (B s) a) = (1 / 6 : ℂ) := by
    intro d
    rw [basis_projector_inner, Complex.star_def, Complex.mul_conj, hB r s hrs d a]
    norm_num
  rw [frameOperator_mulVec_of_inner _ _ _ hov, basis_projectorVector_sum]

lemma traceVector_dot_projectorVector (b : MUB6.Basis) (a : Coord) :
    star traceVector ⬝ᵥ projectorVector (basisCoordinates b a) = 1 := by
  simpa [dotProduct, traceVector, projectorVector, Fintype.sum_prod_type, mul_comm] using
    basisCoordinates_unit b a

lemma traceMatrix_projectorVector (b : MUB6.Basis) (a : Coord) :
    traceMatrix *ᵥ projectorVector (basisCoordinates b a) = traceVector := by
  rw [← traceVector_outer, Matrix.vecMulVec_mulVec, traceVector_dot_projectorVector]
  simp

lemma basis_complement_projectorVector (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B)
    (r : Fin 6) (a : Coord) :
    complementMatrix (fun s => basisCoordinates (B s)) *ᵥ
        projectorVector (basisCoordinates (B r) a) = (1 / 6 : ℂ) • traceVector := by
  let v := projectorVector (basisCoordinates (B r) a)
  let w := (1 / 6 : ℂ) • traceVector
  have hterm (s : Fin 6) : pinchingMatrix (basisCoordinates (B s)) *ᵥ v =
      (if s = r then v - w else 0) + w := by
    by_cases hsr : s = r
    · subst s
      simp [v, basis_pinching_projectorVector]
    · simp only [hsr, ite_false, if_false, zero_add]
      exact mub_pinching_projectorVector B hB s r hsr a
  change (1 + traceMatrix - ∑ s, pinchingMatrix (basisCoordinates (B s))) *ᵥ v = w
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show traceMatrix *ᵥ v = traceVector from traceMatrix_projectorVector (B r) a]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, w, smul_eq_mul]
  norm_num
  ring

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

theorem character_permutation (x : Coord → ℂ) (π : Equiv.Perm Coord) (a : Charge) :
    character (x ∘ π) a = character x (permuteCharge π.symm a) := by
  unfold character permuteCharge
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun i => x i ^ a (π.symm i))

theorem g_row_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H (π i) j) a = g H (permuteCharge π.symm a) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact character_permutation (fun i => H i k) π a

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Square
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem isHadamard_of_row_gram (H : CMatrix)
    (hu : ∀ i j, Complex.normSq (H i j) = 1)
    (hr : H * H.conjTranspose = (6 : ℂ) • (1 : CMatrix)) : IsHadamard H := by
  refine ⟨hu, ?_⟩
  have hi : H * ((6 : ℂ)⁻¹ • H.conjTranspose) = (1 : CMatrix) := by
    rw [Matrix.mul_smul, hr, smul_smul]
    norm_num
  have hc := mul_eq_one_comm.mp hi
  rw [Matrix.smul_mul] at hc
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hc
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem character_doubleDifference (x : Coord → ℂ)
    (hx : ∀ k, Complex.normSq (x k) = 1) (i j : Coord) :
    character x (doubleDifference i j) = x i ^ 2 * conj (x j ^ 2) := by
  rw [doubleDifference, character_add x (fun k => unit_ne_zero (hx k)),
    character_difference x hx, map_pow]
  ring

theorem g_doubleDifference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (doubleDifference i j) =
      (6 : ℂ)⁻¹ * ∑ k, H i k ^ 2 * conj (H j k ^ 2) := by
  simp only [g, character_doubleDifference _ (fun k => hH.1 k _) i j]

theorem square_isHadamard_of_doubleDifference_zero {H : CMatrix} (hH : IsHadamard H)
    (hz : ∀ i j, i ≠ j → g H (doubleDifference i j) = 0) :
    IsHadamard (fun i j => H i j ^ 2) := by
  have hu : ∀ i j, Complex.normSq (H i j ^ 2) = 1 := by
    intro i j
    simp [map_pow, hH.1]
  apply isHadamard_of_row_gram _ hu
  ext i j
  change (∑ k, H i k ^ 2 * conj (H j k ^ 2)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  by_cases hij : i = j
  · subst j
    simp only [Complex.mul_conj, hu, Complex.ofReal_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, ite_true, if_true]
  · have h := hz i j hij
    rw [g_doubleDifference hH] at h
    have hs : (∑ k, H i k ^ 2 * conj (H j k ^ 2)) = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    simpa only [hij, ite_false, if_false, mul_zero] using hs

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
attribute [-simp] _root_.OAI.MUB6.average_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (h : ∀ i, 0 ≤ f i) : average f = 0 ↔ ∀ i, f i = 0 := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  simp only [average, mul_eq_zero, inv_eq_zero, hc, false_or]
  simpa using Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => h i)

theorem average_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, 0 ≤ f i) : 0 ≤ average f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => h i))

theorem average_le_one {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, f i ≤ 1) : average f ≤ 1 := by
  classical
  by_cases hc : Fintype.card ι = 0
  · simp [average, hc]
  · have hs : ∑ i, f i ≤ (Fintype.card ι : ℝ) := by
      calc
        _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h i)
        _ = _ := by simp
    have hp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hc
    calc
      average f ≤ (Fintype.card ι : ℝ)⁻¹ * Fintype.card ι :=
        mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.mpr hp))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hp)

theorem abs_average_le_one {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∀ i, |f i| ≤ 1) : |average f| ≤ 1 := by
  calc
    |average f| ≤ average (fun i => |f i|) := by
      simp only [average, abs_mul, abs_inv]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card ι)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (by positivity)
    _ ≤ 1 := average_le_one _ h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_const [Nonempty ι] (c : ℝ) : average (fun _ : ι => c) = c := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Moments
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem exponentMonomial_norm {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1) (A : Matrix (Fin p) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    ‖exponentMonomial H A ρ κ‖ = 1 := by
  simp [exponentMonomial, unit_norm (hH _ _)]

theorem injectiveMoment_abs_le_one {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : |injectiveMoment H A| ≤ 1 := by
  apply abs_average_le_one
  intro s
  have h₁ : |(exponentMonomial H A s.1 s.2).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (exponentMonomial_norm H hH.1 A s.1 s.2)
  have h₂ : |(exponentMonomial H.transpose A s.1 s.2).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq
      (exponentMonomial_norm H.transpose (fun i j => hH.1 j i) A s.1 s.2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_add_le (exponentMonomial H A s.1 s.2).re
    (exponentMonomial H.transpose A s.1 s.2).re
  linarith

theorem pairAverage_nonneg (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) : 0 ≤ pairAverage H F := by
  apply average_nonneg
  intro π
  exact div_nonneg (add_nonneg (hF _) (hF _)) (by norm_num)

theorem pairAverage_zero_terms (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) (hzero : pairAverage H F = 0) (π : Equiv.Perm Coord) :
    F (fun i j => H (π i) j) = 0 ∧ F (fun i j => H j (π i)) = 0 := by
  have ht := (average_eq_zero_iff _
    (fun p : Equiv.Perm Coord => div_nonneg
      (add_nonneg (hF (fun i j => H (p i) j)) (hF (fun i j => H j (p i))))
      (by norm_num))).mp hzero π
  have h₁ := hF (fun i j => H (π i) j)
  have h₂ := hF (fun i j => H j (π i))
  constructor <;> linarith

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem pair_product_zero_of_certificate {H : CMatrix} {q : Charge}
    (h : PairCertificateIdentity H q) (π : Equiv.Perm Coord) :
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) q = 0 := by
  have hL := pairAverage_nonneg H (fun K => Complex.normSq (pairL K))
    (fun K => Complex.normSq_nonneg _)
  have hg := pairAverage_nonneg H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _)
  have hz : pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0 := by
    unfold PairCertificateIdentity at h
    linarith
  have ht := (pairAverage_zero_terms H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _) hz π).1
  exact Complex.normSq_eq_zero.mp ht

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6

theorem pairPerm_0_1_witness :
    (permuteCharge pairPerm_0_1.symm alpha = alpha ∨
      permuteCharge pairPerm_0_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_1.symm qCross = doubleDifference 0 1 ∨
      permuteCharge pairPerm_0_1.symm qSame = doubleDifference 0 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_0_2_witness :
    (permuteCharge pairPerm_0_2.symm alpha = alpha ∨
      permuteCharge pairPerm_0_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_2.symm qCross = doubleDifference 0 2 ∨
      permuteCharge pairPerm_0_2.symm qSame = doubleDifference 0 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_0_3_witness :
    (permuteCharge pairPerm_0_3.symm alpha = alpha ∨
      permuteCharge pairPerm_0_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_3.symm qCross = doubleDifference 0 3 ∨
      permuteCharge pairPerm_0_3.symm qSame = doubleDifference 0 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_0_4_witness :
    (permuteCharge pairPerm_0_4.symm alpha = alpha ∨
      permuteCharge pairPerm_0_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_4.symm qCross = doubleDifference 0 4 ∨
      permuteCharge pairPerm_0_4.symm qSame = doubleDifference 0 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_0_5_witness :
    (permuteCharge pairPerm_0_5.symm alpha = alpha ∨
      permuteCharge pairPerm_0_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_5.symm qCross = doubleDifference 0 5 ∨
      permuteCharge pairPerm_0_5.symm qSame = doubleDifference 0 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_0_witness :
    (permuteCharge pairPerm_1_0.symm alpha = alpha ∨
      permuteCharge pairPerm_1_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_0.symm qCross = doubleDifference 1 0 ∨
      permuteCharge pairPerm_1_0.symm qSame = doubleDifference 1 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_1_2_witness :
    (permuteCharge pairPerm_1_2.symm alpha = alpha ∨
      permuteCharge pairPerm_1_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_2.symm qCross = doubleDifference 1 2 ∨
      permuteCharge pairPerm_1_2.symm qSame = doubleDifference 1 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_1_3_witness :
    (permuteCharge pairPerm_1_3.symm alpha = alpha ∨
      permuteCharge pairPerm_1_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_3.symm qCross = doubleDifference 1 3 ∨
      permuteCharge pairPerm_1_3.symm qSame = doubleDifference 1 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_4_witness :
    (permuteCharge pairPerm_1_4.symm alpha = alpha ∨
      permuteCharge pairPerm_1_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_4.symm qCross = doubleDifference 1 4 ∨
      permuteCharge pairPerm_1_4.symm qSame = doubleDifference 1 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_1_5_witness :
    (permuteCharge pairPerm_1_5.symm alpha = alpha ∨
      permuteCharge pairPerm_1_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_5.symm qCross = doubleDifference 1 5 ∨
      permuteCharge pairPerm_1_5.symm qSame = doubleDifference 1 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_0_witness :
    (permuteCharge pairPerm_2_0.symm alpha = alpha ∨
      permuteCharge pairPerm_2_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_0.symm qCross = doubleDifference 2 0 ∨
      permuteCharge pairPerm_2_0.symm qSame = doubleDifference 2 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_2_1_witness :
    (permuteCharge pairPerm_2_1.symm alpha = alpha ∨
      permuteCharge pairPerm_2_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_1.symm qCross = doubleDifference 2 1 ∨
      permuteCharge pairPerm_2_1.symm qSame = doubleDifference 2 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

theorem pairPerm_2_3_witness :
    (permuteCharge pairPerm_2_3.symm alpha = alpha ∨
      permuteCharge pairPerm_2_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_3.symm qCross = doubleDifference 2 3 ∨
      permuteCharge pairPerm_2_3.symm qSame = doubleDifference 2 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_4_witness :
    (permuteCharge pairPerm_2_4.symm alpha = alpha ∨
      permuteCharge pairPerm_2_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_4.symm qCross = doubleDifference 2 4 ∨
      permuteCharge pairPerm_2_4.symm qSame = doubleDifference 2 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_2_5_witness :
    (permuteCharge pairPerm_2_5.symm alpha = alpha ∨
      permuteCharge pairPerm_2_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_5.symm qCross = doubleDifference 2 5 ∨
      permuteCharge pairPerm_2_5.symm qSame = doubleDifference 2 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_0_witness :
    (permuteCharge pairPerm_3_0.symm alpha = alpha ∨
      permuteCharge pairPerm_3_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_0.symm qCross = doubleDifference 3 0 ∨
      permuteCharge pairPerm_3_0.symm qSame = doubleDifference 3 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_1_witness :
    (permuteCharge pairPerm_3_1.symm alpha = alpha ∨
      permuteCharge pairPerm_3_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_1.symm qCross = doubleDifference 3 1 ∨
      permuteCharge pairPerm_3_1.symm qSame = doubleDifference 3 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_2_witness :
    (permuteCharge pairPerm_3_2.symm alpha = alpha ∨
      permuteCharge pairPerm_3_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_2.symm qCross = doubleDifference 3 2 ∨
      permuteCharge pairPerm_3_2.symm qSame = doubleDifference 3 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_3_4_witness :
    (permuteCharge pairPerm_3_4.symm alpha = alpha ∨
      permuteCharge pairPerm_3_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_4.symm qCross = doubleDifference 3 4 ∨
      permuteCharge pairPerm_3_4.symm qSame = doubleDifference 3 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_3_5_witness :
    (permuteCharge pairPerm_3_5.symm alpha = alpha ∨
      permuteCharge pairPerm_3_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_5.symm qCross = doubleDifference 3 5 ∨
      permuteCharge pairPerm_3_5.symm qSame = doubleDifference 3 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_4_0_witness :
    (permuteCharge pairPerm_4_0.symm alpha = alpha ∨
      permuteCharge pairPerm_4_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_0.symm qCross = doubleDifference 4 0 ∨
      permuteCharge pairPerm_4_0.symm qSame = doubleDifference 4 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_1_witness :
    (permuteCharge pairPerm_4_1.symm alpha = alpha ∨
      permuteCharge pairPerm_4_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_1.symm qCross = doubleDifference 4 1 ∨
      permuteCharge pairPerm_4_1.symm qSame = doubleDifference 4 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_2_witness :
    (permuteCharge pairPerm_4_2.symm alpha = alpha ∨
      permuteCharge pairPerm_4_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_2.symm qCross = doubleDifference 4 2 ∨
      permuteCharge pairPerm_4_2.symm qSame = doubleDifference 4 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_4_3_witness :
    (permuteCharge pairPerm_4_3.symm alpha = alpha ∨
      permuteCharge pairPerm_4_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_3.symm qCross = doubleDifference 4 3 ∨
      permuteCharge pairPerm_4_3.symm qSame = doubleDifference 4 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_4_5_witness :
    (permuteCharge pairPerm_4_5.symm alpha = alpha ∨
      permuteCharge pairPerm_4_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_5.symm qCross = doubleDifference 4 5 ∨
      permuteCharge pairPerm_4_5.symm qSame = doubleDifference 4 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_5_0_witness :
    (permuteCharge pairPerm_5_0.symm alpha = alpha ∨
      permuteCharge pairPerm_5_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_0.symm qCross = doubleDifference 5 0 ∨
      permuteCharge pairPerm_5_0.symm qSame = doubleDifference 5 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_1_witness :
    (permuteCharge pairPerm_5_1.symm alpha = alpha ∨
      permuteCharge pairPerm_5_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_1.symm qCross = doubleDifference 5 1 ∨
      permuteCharge pairPerm_5_1.symm qSame = doubleDifference 5 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_2_witness :
    (permuteCharge pairPerm_5_2.symm alpha = alpha ∨
      permuteCharge pairPerm_5_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_2.symm qCross = doubleDifference 5 2 ∨
      permuteCharge pairPerm_5_2.symm qSame = doubleDifference 5 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

theorem pairPerm_5_3_witness :
    (permuteCharge pairPerm_5_3.symm alpha = alpha ∨
      permuteCharge pairPerm_5_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_3.symm qCross = doubleDifference 5 3 ∨
      permuteCharge pairPerm_5_3.symm qSame = doubleDifference 5 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pairPerm_5_4_witness :
    (permuteCharge pairPerm_5_4.symm alpha = alpha ∨
      permuteCharge pairPerm_5_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_4.symm qCross = doubleDifference 5 4 ∨
      permuteCharge pairPerm_5_4.symm qSame = doubleDifference 5 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pair_permutation_witness (i j : Coord) (hij : i ≠ j) :
    ∃ π : Equiv.Perm Coord,
      (permuteCharge π.symm alpha = alpha ∨ permuteCharge π.symm alpha = -alpha) ∧
      (permuteCharge π.symm qCross = doubleDifference i j ∨
        permuteCharge π.symm qSame = doubleDifference i j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_0_1, pairPerm_0_1_witness⟩
  · exact ⟨pairPerm_0_2, pairPerm_0_2_witness⟩
  · exact ⟨pairPerm_0_3, pairPerm_0_3_witness⟩
  · exact ⟨pairPerm_0_4, pairPerm_0_4_witness⟩
  · exact ⟨pairPerm_0_5, pairPerm_0_5_witness⟩
  · exact ⟨pairPerm_1_0, pairPerm_1_0_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_1_2, pairPerm_1_2_witness⟩
  · exact ⟨pairPerm_1_3, pairPerm_1_3_witness⟩
  · exact ⟨pairPerm_1_4, pairPerm_1_4_witness⟩
  · exact ⟨pairPerm_1_5, pairPerm_1_5_witness⟩
  · exact ⟨pairPerm_2_0, pairPerm_2_0_witness⟩
  · exact ⟨pairPerm_2_1, pairPerm_2_1_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_2_3, pairPerm_2_3_witness⟩
  · exact ⟨pairPerm_2_4, pairPerm_2_4_witness⟩
  · exact ⟨pairPerm_2_5, pairPerm_2_5_witness⟩
  · exact ⟨pairPerm_3_0, pairPerm_3_0_witness⟩
  · exact ⟨pairPerm_3_1, pairPerm_3_1_witness⟩
  · exact ⟨pairPerm_3_2, pairPerm_3_2_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_3_4, pairPerm_3_4_witness⟩
  · exact ⟨pairPerm_3_5, pairPerm_3_5_witness⟩
  · exact ⟨pairPerm_4_0, pairPerm_4_0_witness⟩
  · exact ⟨pairPerm_4_1, pairPerm_4_1_witness⟩
  · exact ⟨pairPerm_4_2, pairPerm_4_2_witness⟩
  · exact ⟨pairPerm_4_3, pairPerm_4_3_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_4_5, pairPerm_4_5_witness⟩
  · exact ⟨pairPerm_5_0, pairPerm_5_0_witness⟩
  · exact ⟨pairPerm_5_1, pairPerm_5_1_witness⟩
  · exact ⟨pairPerm_5_2, pairPerm_5_2_witness⟩
  · exact ⟨pairPerm_5_3, pairPerm_5_3_witness⟩
  · exact ⟨pairPerm_5_4, pairPerm_5_4_witness⟩
  · exact False.elim (hij rfl)

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Dichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem doubleDifference_zero_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) (ha : g H alpha ≠ 0) (i j : Coord) (hij : i ≠ j) :
    g H (doubleDifference i j) = 0 := by
  obtain ⟨π, hπα, hπq⟩ := pair_permutation_witness i j hij
  have hn : g (fun i j => H (π i) j) alpha ≠ 0 := by
    rw [g_row_permutation]
    rcases hπα with h | h
    · rw [h]
      exact ha
    · rw [h, g_neg hH]
      exact fun hzero => ha ((map_eq_zero (starRingEnd ℂ)).mp hzero)
  rcases hπq with h | h
  · have hz := (mul_eq_zero.mp (hp π).1).resolve_left hn
    rwa [g_row_permutation, h] at hz
  · have hz := (mul_eq_zero.mp (hp π).2).resolve_left hn
    rwa [g_row_permutation, h] at hz

theorem pair_products_row_permutation {H : CMatrix} (hp : PairProductsZero H)
    (π : Equiv.Perm Coord) : PairProductsZero (fun i j => H (π i) j) := by
  intro σ
  exact hp (σ.trans π)

/-- The manuscript's single-matrix dichotomy, conditional here only on the two
explicit pair-product identities. The finite certificate supplies them. -/
theorem dichotomy_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) : FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  classical
  by_cases hzero : FourierZero H
  · exact Or.inl hzero
  · right
    obtain ⟨π, hπ⟩ := not_forall.mp hzero
    let K : CMatrix := fun i j => H (π i) j
    have hK : IsHadamard K := hH.permutations π (Equiv.refl _)
    have hKp : PairProductsZero K := pair_products_row_permutation hp π
    have hKsquare : IsHadamard (fun i j => K i j ^ 2) :=
      square_isHadamard_of_doubleDifference_zero hK
        (doubleDifference_zero_of_pair_products hK hKp hπ)
    have h := hKsquare.permutations π.symm (Equiv.refl _)
    simpa only [K, Equiv.apply_symm_apply, Equiv.refl_apply] using h

theorem dichotomy_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  apply dichotomy_of_pair_products hH
  intro π
  exact ⟨pair_product_zero_of_certificate hcross π, pair_product_zero_of_certificate hsame π⟩

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairAverage
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem injectiveMoment_empty (H : CMatrix) :
    injectiveMoment H (0 : Matrix (Fin 0) (Fin 0) ℤ) = 1 := by
  let : Nonempty ((Fin 0 ↪ Coord) × (Fin 0 ↪ Coord)) :=
    ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty⟩
  unfold injectiveMoment
  have hf : (fun s : (Fin 0 ↪ Coord) × (Fin 0 ↪ Coord) =>
      ((exponentMonomial H (0 : Matrix (Fin 0) (Fin 0) ℤ) s.1 s.2).re +
        (exponentMonomial H.transpose (0 : Matrix (Fin 0) (Fin 0) ℤ) s.1 s.2).re) / 2) =
      (fun _ => (1 : ℝ)) := by
    funext s
    norm_num [exponentMonomial]
  rw [hf]
  exact average_const 1

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Terms
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

private theorem charge0_0 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) = pairW := by decide +kernel

private theorem charge0_1 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) = -pairW := by decide +kernel

theorem termPolynomial0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term0 = (3 : ℂ) * ((g H pairW) * (conj (g H pairW))) := by
  have hc : (term0.coefficient : ℂ) = (3 : ℂ) := by norm_num [term0]
  change (term0.coefficient : ℂ) * (∏ j : Fin 2, g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) * 1)) = _
  rw [charge0_0, charge0_1]
  simp only [g_neg hH]
  ring

private theorem charge1_0 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge1_1 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 0) := by decide +kernel

private theorem charge1_2 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term1 = (-6 : ℂ) * ((g H pairW) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term1.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term1]
  change (term1.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge1_0, charge1_1, charge1_2]
  simp only [g_neg hH]
  ring

private theorem charge2_0 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge2_1 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 1) := by decide +kernel

private theorem charge2_2 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term2 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term2.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term2]
  change (term2.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge2_0, charge2_1, charge2_2]
  simp only [g_neg hH]
  ring

private theorem charge3_0 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge3_1 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 2) := by decide +kernel

private theorem charge3_2 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term3 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term3.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term3]
  change (term3.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge3_0, charge3_1, charge3_2]
  simp only [g_neg hH]
  ring

private theorem charge4_0 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge4_1 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 3) := by decide +kernel

private theorem charge4_2 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term4 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term4.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term4]
  change (term4.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge4_0, charge4_1, charge4_2]
  simp only [g_neg hH]
  ring

private theorem charge5_0 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 0) := by decide +kernel

private theorem charge5_1 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 0) := by decide +kernel

private theorem charge5_2 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term5 = (-6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H pairW))) := by
  have hc : (term5.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term5]
  change (term5.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge5_0, charge5_1, charge5_2]
  simp only [g_neg hH]
  ring

private theorem charge6_0 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge6_1 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge6_2 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge6_3 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term6 = (12 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term6.coefficient : ℂ) = (12 : ℂ) := by norm_num [term6]
  change (term6.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (12 : ℂ) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge6_0, charge6_1, charge6_2, charge6_3]
  simp only [g_neg hH]
  ring

private theorem charge7_0 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge7_1 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge7_2 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge7_3 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term7 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term7.coefficient : ℂ) = (6 : ℂ) := by norm_num [term7]
  change (term7.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge7_0, charge7_1, charge7_2, charge7_3]
  simp only [g_neg hH]
  ring

private theorem charge8_0 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge8_1 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge8_2 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge8_3 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term8 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term8.coefficient : ℂ) = (6 : ℂ) := by norm_num [term8]
  change (term8.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge8_0, charge8_1, charge8_2, charge8_3]
  simp only [g_neg hH]
  ring

private theorem charge9_0 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge9_1 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge9_2 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge9_3 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term9 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term9.coefficient : ℂ) = (6 : ℂ) := by norm_num [term9]
  change (term9.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge9_0, charge9_1, charge9_2, charge9_3]
  simp only [g_neg hH]
  ring

private theorem charge10_0 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 1) := by decide +kernel

private theorem charge10_1 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 1) := by decide +kernel

private theorem charge10_2 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term10 = (-3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H pairW))) := by
  have hc : (term10.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term10]
  change (term10.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge10_0, charge10_1, charge10_2]
  simp only [g_neg hH]
  ring

private theorem charge11_0 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge11_1 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge11_2 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge11_3 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term11 = (6 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term11.coefficient : ℂ) = (6 : ℂ) := by norm_num [term11]
  change (term11.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge11_0, charge11_1, charge11_2, charge11_3]
  simp only [g_neg hH]
  ring

private theorem charge12_0 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge12_1 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge12_2 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge12_3 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term12 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term12.coefficient : ℂ) = (3 : ℂ) := by norm_num [term12]
  change (term12.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge12_0, charge12_1, charge12_2, charge12_3]
  simp only [g_neg hH]
  ring

private theorem charge13_0 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge13_1 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge13_2 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge13_3 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term13 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term13.coefficient : ℂ) = (3 : ℂ) := by norm_num [term13]
  change (term13.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge13_0, charge13_1, charge13_2, charge13_3]
  simp only [g_neg hH]
  ring

private theorem charge14_0 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge14_1 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge14_2 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge14_3 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term14 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term14.coefficient : ℂ) = (3 : ℂ) := by norm_num [term14]
  change (term14.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge14_0, charge14_1, charge14_2, charge14_3]
  simp only [g_neg hH]
  ring

private theorem charge15_0 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 2) := by decide +kernel

private theorem charge15_1 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 2) := by decide +kernel

private theorem charge15_2 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term15 = (-3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H pairW))) := by
  have hc : (term15.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term15]
  change (term15.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge15_0, charge15_1, charge15_2]
  simp only [g_neg hH]
  ring

private theorem charge16_0 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge16_1 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge16_2 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge16_3 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term16 = (6 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term16.coefficient : ℂ) = (6 : ℂ) := by norm_num [term16]
  change (term16.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge16_0, charge16_1, charge16_2, charge16_3]
  simp only [g_neg hH]
  ring

private theorem charge17_0 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge17_1 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge17_2 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge17_3 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term17 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term17.coefficient : ℂ) = (3 : ℂ) := by norm_num [term17]
  change (term17.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge17_0, charge17_1, charge17_2, charge17_3]
  simp only [g_neg hH]
  ring

private theorem charge18_0 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge18_1 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge18_2 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge18_3 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term18 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term18.coefficient : ℂ) = (3 : ℂ) := by norm_num [term18]
  change (term18.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge18_0, charge18_1, charge18_2, charge18_3]
  simp only [g_neg hH]
  ring

private theorem charge19_0 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge19_1 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge19_2 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge19_3 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term19 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term19.coefficient : ℂ) = (3 : ℂ) := by norm_num [term19]
  change (term19.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge19_0, charge19_1, charge19_2, charge19_3]
  simp only [g_neg hH]
  ring

private theorem charge20_0 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 3) := by decide +kernel

private theorem charge20_1 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 3) := by decide +kernel

private theorem charge20_2 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term20 = (-3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H pairW))) := by
  have hc : (term20.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term20]
  change (term20.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge20_0, charge20_1, charge20_2]
  simp only [g_neg hH]
  ring

private theorem charge21_0 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge21_1 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge21_2 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge21_3 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term21 = (6 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term21.coefficient : ℂ) = (6 : ℂ) := by norm_num [term21]
  change (term21.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge21_0, charge21_1, charge21_2, charge21_3]
  simp only [g_neg hH]
  ring

private theorem charge22_0 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge22_1 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge22_2 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge22_3 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term22 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term22.coefficient : ℂ) = (3 : ℂ) := by norm_num [term22]
  change (term22.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge22_0, charge22_1, charge22_2, charge22_3]
  simp only [g_neg hH]
  ring

private theorem charge23_0 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge23_1 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge23_2 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge23_3 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term23 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term23.coefficient : ℂ) = (3 : ℂ) := by norm_num [term23]
  change (term23.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge23_0, charge23_1, charge23_2, charge23_3]
  simp only [g_neg hH]
  ring

private theorem charge24_0 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge24_1 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge24_2 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge24_3 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term24 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term24.coefficient : ℂ) = (3 : ℂ) := by norm_num [term24]
  change (term24.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge24_0, charge24_1, charge24_2, charge24_3]
  simp only [g_neg hH]
  ring

private theorem charge26_0 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = alpha := by decide +kernel

private theorem charge26_1 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = qSame := by decide +kernel

private theorem charge26_2 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -alpha := by decide +kernel

private theorem charge26_3 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -qSame := by decide +kernel

theorem termPolynomial26 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term26 = (1 : ℂ) * ((g H alpha) * (g H qSame) * (conj (g H alpha)) * (conj (g H qSame))) := by
  have hc : (term26.coefficient : ℂ) = (1 : ℂ) := by norm_num [term26]
  change (term26.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (1 : ℂ) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge26_0, charge26_1, charge26_2, charge26_3]
  simp only [g_neg hH]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Grid
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem pairSummand_sum (H : CMatrix) : (∑ r, pairSummand H r) = pairL H := by
  simp [pairSummand, pairL, pairCoefficient, Fin.sum_univ_succ]

private theorem grid0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 0) = 3 * (pairSummand H 0 * conj (pairSummand H 0)) := by
  change termPolynomial H term0 = _
  rw [termPolynomial0 hH]
  simp [pairSummand, map_neg]

private theorem grid1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 1) = 3 * (pairSummand H 0 * conj (pairSummand H 1)) := by
  change termPolynomial H term1 = _
  rw [termPolynomial1 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 2) = 3 * (pairSummand H 0 * conj (pairSummand H 2)) := by
  change termPolynomial H term2 = _
  rw [termPolynomial2 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 3) = 3 * (pairSummand H 0 * conj (pairSummand H 3)) := by
  change termPolynomial H term3 = _
  rw [termPolynomial3 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 4) = 3 * (pairSummand H 0 * conj (pairSummand H 4)) := by
  change termPolynomial H term4 = _
  rw [termPolynomial4 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 0) = 3 * (pairSummand H 1 * conj (pairSummand H 0)) := by
  change termPolynomial H term5 = _
  rw [termPolynomial5 hH]
  simp [pairSummand, map_neg]
  ring

private theorem grid6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 1) = 3 * (pairSummand H 1 * conj (pairSummand H 1)) := by
  change termPolynomial H term6 = _
  rw [termPolynomial6 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 2) = 3 * (pairSummand H 1 * conj (pairSummand H 2)) := by
  change termPolynomial H term7 = _
  rw [termPolynomial7 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 3) = 3 * (pairSummand H 1 * conj (pairSummand H 3)) := by
  change termPolynomial H term8 = _
  rw [termPolynomial8 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 4) = 3 * (pairSummand H 1 * conj (pairSummand H 4)) := by
  change termPolynomial H term9 = _
  rw [termPolynomial9 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 0) = 3 * (pairSummand H 2 * conj (pairSummand H 0)) := by
  change termPolynomial H term10 = _
  rw [termPolynomial10 hH]
  simp [pairSummand, map_neg]

private theorem grid11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 1) = 3 * (pairSummand H 2 * conj (pairSummand H 1)) := by
  change termPolynomial H term11 = _
  rw [termPolynomial11 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 2) = 3 * (pairSummand H 2 * conj (pairSummand H 2)) := by
  change termPolynomial H term12 = _
  rw [termPolynomial12 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 3) = 3 * (pairSummand H 2 * conj (pairSummand H 3)) := by
  change termPolynomial H term13 = _
  rw [termPolynomial13 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 4) = 3 * (pairSummand H 2 * conj (pairSummand H 4)) := by
  change termPolynomial H term14 = _
  rw [termPolynomial14 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 0) = 3 * (pairSummand H 3 * conj (pairSummand H 0)) := by
  change termPolynomial H term15 = _
  rw [termPolynomial15 hH]
  simp [pairSummand, map_neg]

private theorem grid16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 1) = 3 * (pairSummand H 3 * conj (pairSummand H 1)) := by
  change termPolynomial H term16 = _
  rw [termPolynomial16 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 2) = 3 * (pairSummand H 3 * conj (pairSummand H 2)) := by
  change termPolynomial H term17 = _
  rw [termPolynomial17 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 3) = 3 * (pairSummand H 3 * conj (pairSummand H 3)) := by
  change termPolynomial H term18 = _
  rw [termPolynomial18 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 4) = 3 * (pairSummand H 3 * conj (pairSummand H 4)) := by
  change termPolynomial H term19 = _
  rw [termPolynomial19 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 0) = 3 * (pairSummand H 4 * conj (pairSummand H 0)) := by
  change termPolynomial H term20 = _
  rw [termPolynomial20 hH]
  simp [pairSummand, map_neg]

private theorem grid21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 1) = 3 * (pairSummand H 4 * conj (pairSummand H 1)) := by
  change termPolynomial H term21 = _
  rw [termPolynomial21 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 2) = 3 * (pairSummand H 4 * conj (pairSummand H 2)) := by
  change termPolynomial H term22 = _
  rw [termPolynomial22 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 3) = 3 * (pairSummand H 4 * conj (pairSummand H 3)) := by
  change termPolynomial H term23 = _
  rw [termPolynomial23 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 4) = 3 * (pairSummand H 4 * conj (pairSummand H 4)) := by
  change termPolynomial H term24 = _
  rw [termPolynomial24 hH]
  simp [pairSummand, map_mul]
  ring

theorem termGrid_polynomial {H : CMatrix} (hH : IsHadamard H) (r s : Fin 5) :
    termPolynomial H (termGrid r s) = 3 * (pairSummand H r * conj (pairSummand H s)) := by
  fin_cases r
  · fin_cases s
    · exact grid0 hH
    · exact grid1 hH
    · exact grid2 hH
    · exact grid3 hH
    · exact grid4 hH
  · fin_cases s
    · exact grid5 hH
    · exact grid6 hH
    · exact grid7 hH
    · exact grid8 hH
    · exact grid9 hH
  · fin_cases s
    · exact grid10 hH
    · exact grid11 hH
    · exact grid12 hH
    · exact grid13 hH
    · exact grid14 hH
  · fin_cases s
    · exact grid15 hH
    · exact grid16 hH
    · exact grid17 hH
    · exact grid18 hH
    · exact grid19 hH
  · fin_cases s
    · exact grid20 hH
    · exact grid21 hH
    · exact grid22 hH
    · exact grid23 hH
    · exact grid24 hH

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem sum_grid_polynomial (x : Fin 5 → ℂ) :
    (∑ r, ∑ s, 3 * (x r * conj (x s))) = 3 * ((∑ r, x r) * conj (∑ s, x s)) := by
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem termGrid_at0 : termGrid 0 0 = term0 := rfl
private theorem termGrid_at1 : termGrid 0 1 = term1 := rfl
private theorem termGrid_at2 : termGrid 0 2 = term2 := rfl
private theorem termGrid_at3 : termGrid 0 3 = term3 := rfl
private theorem termGrid_at4 : termGrid 0 4 = term4 := rfl
private theorem termGrid_at5 : termGrid 1 0 = term5 := rfl
private theorem termGrid_at6 : termGrid 1 1 = term6 := rfl
private theorem termGrid_at7 : termGrid 1 2 = term7 := rfl
private theorem termGrid_at8 : termGrid 1 3 = term8 := rfl
private theorem termGrid_at9 : termGrid 1 4 = term9 := rfl
private theorem termGrid_at10 : termGrid 2 0 = term10 := rfl
private theorem termGrid_at11 : termGrid 2 1 = term11 := rfl
private theorem termGrid_at12 : termGrid 2 2 = term12 := rfl
private theorem termGrid_at13 : termGrid 2 3 = term13 := rfl
private theorem termGrid_at14 : termGrid 2 4 = term14 := rfl
private theorem termGrid_at15 : termGrid 3 0 = term15 := rfl
private theorem termGrid_at16 : termGrid 3 1 = term16 := rfl
private theorem termGrid_at17 : termGrid 3 2 = term17 := rfl
private theorem termGrid_at18 : termGrid 3 3 = term18 := rfl
private theorem termGrid_at19 : termGrid 3 4 = term19 := rfl
private theorem termGrid_at20 : termGrid 4 0 = term20 := rfl
private theorem termGrid_at21 : termGrid 4 1 = term21 := rfl
private theorem termGrid_at22 : termGrid 4 2 = term22 := rfl
private theorem termGrid_at23 : termGrid 4 3 = term23 := rfl
private theorem termGrid_at24 : termGrid 4 4 = term24 := rfl

private theorem terms1_at0 : terms1 0 = term0 := rfl
private theorem terms1_at1 : terms1 1 = term1 := rfl
private theorem terms1_at2 : terms1 2 = term2 := rfl
private theorem terms1_at3 : terms1 3 = term3 := rfl
private theorem terms1_at4 : terms1 4 = term4 := rfl
private theorem terms1_at5 : terms1 5 = term5 := rfl
private theorem terms1_at6 : terms1 6 = term6 := rfl
private theorem terms1_at7 : terms1 7 = term7 := rfl
private theorem terms1_at8 : terms1 8 = term8 := rfl
private theorem terms1_at9 : terms1 9 = term9 := rfl
private theorem terms1_at10 : terms1 10 = term10 := rfl
private theorem terms1_at11 : terms1 11 = term11 := rfl
private theorem terms1_at12 : terms1 12 = term12 := rfl
private theorem terms1_at13 : terms1 13 = term13 := rfl
private theorem terms1_at14 : terms1 14 = term14 := rfl
private theorem terms1_at15 : terms1 15 = term15 := rfl
private theorem terms1_at16 : terms1 16 = term16 := rfl
private theorem terms1_at17 : terms1 17 = term17 := rfl
private theorem terms1_at18 : terms1 18 = term18 := rfl
private theorem terms1_at19 : terms1 19 = term19 := rfl
private theorem terms1_at20 : terms1 20 = term20 := rfl
private theorem terms1_at21 : terms1 21 = term21 := rfl
private theorem terms1_at22 : terms1 22 = term22 := rfl
private theorem terms1_at23 : terms1 23 = term23 := rfl
private theorem terms1_at24 : terms1 24 = term24 := rfl
private theorem terms1_at25 : terms1 25 = term26 := rfl
theorem sum_terms1 (F : Term → ℂ) :
    (∑ i : Fin 26, F (terms1 i)) = (∑ r : Fin 5, ∑ s : Fin 5, F (termGrid r s)) + F term26 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms1 0) + (F (terms1 1) + (F (terms1 2) + (F (terms1 3) + (F (terms1 4) + (F (terms1 5) + (F (terms1 6) + (F (terms1 7) + (F (terms1 8) + (F (terms1 9) + (F (terms1 10) + (F (terms1 11) + (F (terms1 12) + (F (terms1 13) + (F (terms1 14) + (F (terms1 15) + (F (terms1 16) + (F (terms1 17) + (F (terms1 18) + (F (terms1 19) + (F (terms1 20) + (F (terms1 21) + (F (terms1 22) + (F (terms1 23) + (F (terms1 24) + (F (terms1 25) + 0)))))))))))))))))))))))))) = ((F (termGrid 0 0) + (F (termGrid 0 1) + (F (termGrid 0 2) + (F (termGrid 0 3) + (F (termGrid 0 4) + 0))))) + ((F (termGrid 1 0) + (F (termGrid 1 1) + (F (termGrid 1 2) + (F (termGrid 1 3) + (F (termGrid 1 4) + 0))))) + ((F (termGrid 2 0) + (F (termGrid 2 1) + (F (termGrid 2 2) + (F (termGrid 2 3) + (F (termGrid 2 4) + 0))))) + ((F (termGrid 3 0) + (F (termGrid 3 1) + (F (termGrid 3 2) + (F (termGrid 3 3) + (F (termGrid 3 4) + 0))))) + ((F (termGrid 4 0) + (F (termGrid 4 1) + (F (termGrid 4 2) + (F (termGrid 4 3) + (F (termGrid 4 4) + 0))))) + 0))))) + F term26
  simp only [terms1_at0, terms1_at1, terms1_at2, terms1_at3, terms1_at4, terms1_at5, terms1_at6, terms1_at7, terms1_at8, terms1_at9, terms1_at10, terms1_at11, terms1_at12, terms1_at13, terms1_at14, terms1_at15, terms1_at16, terms1_at17, terms1_at18, terms1_at19, terms1_at20, terms1_at21, terms1_at22, terms1_at23, terms1_at24, terms1_at25, termGrid_at0, termGrid_at1, termGrid_at2, termGrid_at3, termGrid_at4, termGrid_at5, termGrid_at6, termGrid_at7, termGrid_at8, termGrid_at9, termGrid_at10, termGrid_at11, termGrid_at12, termGrid_at13, termGrid_at14, termGrid_at15, termGrid_at16, termGrid_at17, termGrid_at18, termGrid_at19, termGrid_at20, termGrid_at21, termGrid_at22, termGrid_at23, termGrid_at24, add_zero, add_assoc]

theorem pair_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, termPolynomial H (terms1 i)) =
      3 * (pairL H * conj (pairL H)) +
        (g H alpha * g H qSame) * conj (g H alpha * g H qSame) := by
  rw [sum_terms1]
  simp_rw [termGrid_polynomial hH]
  rw [sum_grid_polynomial, pairSummand_sum, termPolynomial26 hH]
  simp only [map_mul, one_mul]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairInterpretation
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem pairAverage_add (H : CMatrix) (F G : CMatrix → ℝ) :
    pairAverage H (fun K => F K + G K) = pairAverage H F + pairAverage H G := by
  have h (π : Equiv.Perm Coord) :
      ((F (fun i j => H (π i) j) + G (fun i j => H (π i) j)) +
        (F (fun i j => H j (π i)) + G (fun i j => H j (π i)))) / 2 =
      (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2 +
        (G (fun i j => H (π i) j) + G (fun i j => H j (π i))) / 2 := by ring
  simp only [pairAverage, h, average_add]

theorem pairAverage_mul (H : CMatrix) (c : ℝ) (F : CMatrix → ℝ) :
    pairAverage H (fun K => c * F K) = c * pairAverage H F := by
  unfold pairAverage
  have h (π : Equiv.Perm Coord) :
      (c * F (fun i j => H (π i) j) + c * F (fun i j => H j (π i))) / 2 =
      c * ((F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2) := by ring
  simp_rw [h]
  exact average_mul c _

theorem pairAverage_sum {ι : Type*} [Fintype ι] (H : CMatrix) (F : ι → CMatrix → ℝ) :
    pairAverage H (fun K => ∑ i, F i K) = ∑ i, pairAverage H (F i) := by
  simp only [pairAverage, ← Finset.sum_add_distrib, div_eq_mul_inv,
    Finset.sum_mul, average_sum]

theorem pairAverage_congr_hadamard {H : CMatrix} (hH : IsHadamard H)
    {F G : CMatrix → ℝ} (h : ∀ K, IsHadamard K → F K = G K) :
    pairAverage H F = pairAverage H G := by
  apply average_congr
  intro π
  have h₁ : IsHadamard (fun i j => H (π i) j) := by
    simpa only [Equiv.refl_apply] using hH.permutations π (Equiv.refl Coord)
  have h₂ : IsHadamard (fun i j => H j (π i)) := by
    simpa only [Equiv.refl_apply, Matrix.transpose_apply] using
      hH.transpose.permutations π (Equiv.refl Coord)
  rw [h _ h₁, h _ h₂]

namespace Certificate.PairTargetSemantics

theorem termPolynomial_re (H : CMatrix) (t : Term) :
    (termPolynomial H t).re = (t.coefficient : ℝ) * (∏ j, g H (fun i => t.charges i j)).re := by
  simp [termPolynomial, Complex.mul_re]

theorem pair_real_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
      (∏ j, g H (fun k => (terms1 i).charges k j)).re) =
      3 * Complex.normSq (pairL H) + Complex.normSq (g H alpha * g H qSame) := by
  have h := congrArg Complex.re (pair_polynomial1 hH)
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa only [Complex.re_sum, termPolynomial_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem expanded_identity1 {H : CMatrix} (hH : IsHadamard H) :
    expanded1 H = 3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
      pairAverage H (fun K => Complex.normSq (g K alpha * g K qSame)) := by
  calc
    _ = pairAverage H (fun K => ∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
        (∏ j, g K (fun k => (terms1 i).charges k j)).re) := by
      simp only [pairAverage_sum, pairAverage_mul, expanded1, weightedAverage]
    _ = pairAverage H (fun K => 3 * Complex.normSq (pairL K) +
        Complex.normSq (g K alpha * g K qSame)) :=
      pairAverage_congr_hadamard hH (fun _ hK => pair_real_polynomial1 hK)
    _ = _ := by rw [pairAverage_add, pairAverage_mul]

end Certificate.PairTargetSemantics
end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck254 : pairMerged254 = Integer.Sparse.merge (Integer.Sparse.scale (-302313060) (rows 1)) (Integer.Sparse.scale (207408600) (rows 2)) := by decide +kernel

theorem pairMergedZero254 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged254 x = 0 := by
  rw [pairMergeCheck254, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck255 : pairMerged255 = Integer.Sparse.merge (Integer.Sparse.scale (-55755000) (rows 0)) pairMerged254 := by decide +kernel

theorem pairMergedZero255 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged255 x = 0 := by
  rw [pairMergeCheck255, Integer.Sparse.eval_merge]
  rw [pairMergedZero254 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck256 : pairMerged256 = Integer.Sparse.merge (Integer.Sparse.scale (-45274194) (rows 4)) (Integer.Sparse.scale (24898104) (rows 5)) := by decide +kernel

theorem pairMergedZero256 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged256 x = 0 := by
  rw [pairMergeCheck256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck257 : pairMerged257 = Integer.Sparse.merge (Integer.Sparse.scale (27823824) (rows 3)) pairMerged256 := by decide +kernel

theorem pairMergedZero257 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged257 x = 0 := by
  rw [pairMergeCheck257, Integer.Sparse.eval_merge]
  rw [pairMergedZero256 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck258 : pairMerged258 = Integer.Sparse.merge pairMerged255 pairMerged257 := by decide +kernel

theorem pairMergedZero258 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged258 x = 0 := by
  rw [pairMergeCheck258, Integer.Sparse.eval_merge]
  rw [pairMergedZero255 x h, pairMergedZero257 x h]
  simp only [add_zero]

theorem pairMergeCheck259 : pairMerged259 = Integer.Sparse.merge (Integer.Sparse.scale (-42819840) (rows 7)) (Integer.Sparse.scale (-2349648) (rows 8)) := by decide +kernel

theorem pairMergedZero259 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged259 x = 0 := by
  rw [pairMergeCheck259, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck260 : pairMerged260 = Integer.Sparse.merge (Integer.Sparse.scale (61467336) (rows 6)) pairMerged259 := by decide +kernel

theorem pairMergedZero260 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged260 x = 0 := by
  rw [pairMergeCheck260, Integer.Sparse.eval_merge]
  rw [pairMergedZero259 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck261 : pairMerged261 = Integer.Sparse.merge (Integer.Sparse.scale (4220748) (rows 9)) (Integer.Sparse.scale (1111320) (rows 10)) := by decide +kernel

theorem pairMergedZero261 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged261 x = 0 := by
  rw [pairMergeCheck261, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck262 : pairMerged262 = Integer.Sparse.merge (Integer.Sparse.scale (-2268000) (rows 11)) (Integer.Sparse.scale (-11113200) (rows 12)) := by decide +kernel

theorem pairMergedZero262 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged262 x = 0 := by
  rw [pairMergeCheck262, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck263 : pairMerged263 = Integer.Sparse.merge pairMerged261 pairMerged262 := by decide +kernel

theorem pairMergedZero263 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged263 x = 0 := by
  rw [pairMergeCheck263, Integer.Sparse.eval_merge]
  rw [pairMergedZero261 x h, pairMergedZero262 x h]
  simp only [add_zero]

theorem pairMergeCheck264 : pairMerged264 = Integer.Sparse.merge pairMerged260 pairMerged263 := by decide +kernel

theorem pairMergedZero264 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged264 x = 0 := by
  rw [pairMergeCheck264, Integer.Sparse.eval_merge]
  rw [pairMergedZero260 x h, pairMergedZero263 x h]
  simp only [add_zero]

theorem pairMergeCheck265 : pairMerged265 = Integer.Sparse.merge pairMerged258 pairMerged264 := by decide +kernel

theorem pairMergedZero265 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged265 x = 0 := by
  rw [pairMergeCheck265, Integer.Sparse.eval_merge]
  rw [pairMergedZero258 x h, pairMergedZero264 x h]
  simp only [add_zero]

theorem pairMergeCheck266 : pairMerged266 = Integer.Sparse.merge (Integer.Sparse.scale (6393492) (rows 14)) (Integer.Sparse.scale (272160) (rows 15)) := by decide +kernel

theorem pairMergedZero266 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged266 x = 0 := by
  rw [pairMergeCheck266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck267 : pairMerged267 = Integer.Sparse.merge (Integer.Sparse.scale (-555660) (rows 13)) pairMerged266 := by decide +kernel

theorem pairMergedZero267 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged267 x = 0 := by
  rw [pairMergeCheck267, Integer.Sparse.eval_merge]
  rw [pairMergedZero266 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck268 : pairMerged268 = Integer.Sparse.merge (Integer.Sparse.scale (6483834) (rows 16)) (Integer.Sparse.scale (-1272348) (rows 17)) := by decide +kernel

theorem pairMergedZero268 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged268 x = 0 := by
  rw [pairMergeCheck268, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck269 : pairMerged269 = Integer.Sparse.merge (Integer.Sparse.scale (-1124928) (rows 18)) (Integer.Sparse.scale (-24284610) (rows 19)) := by decide +kernel

theorem pairMergedZero269 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged269 x = 0 := by
  rw [pairMergeCheck269, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck270 : pairMerged270 = Integer.Sparse.merge pairMerged268 pairMerged269 := by decide +kernel

theorem pairMergedZero270 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged270 x = 0 := by
  rw [pairMergeCheck270, Integer.Sparse.eval_merge]
  rw [pairMergedZero268 x h, pairMergedZero269 x h]
  simp only [add_zero]

theorem pairMergeCheck271 : pairMerged271 = Integer.Sparse.merge pairMerged267 pairMerged270 := by decide +kernel

theorem pairMergedZero271 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged271 x = 0 := by
  rw [pairMergeCheck271, Integer.Sparse.eval_merge]
  rw [pairMergedZero267 x h, pairMergedZero270 x h]
  simp only [add_zero]

theorem pairMergeCheck272 : pairMerged272 = Integer.Sparse.merge (Integer.Sparse.scale (5928552) (rows 21)) (Integer.Sparse.scale (3525984) (rows 22)) := by decide +kernel

theorem pairMergedZero272 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged272 x = 0 := by
  rw [pairMergeCheck272, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck273 : pairMerged273 = Integer.Sparse.merge (Integer.Sparse.scale (-18510660) (rows 20)) pairMerged272 := by decide +kernel

theorem pairMergedZero273 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged273 x = 0 := by
  rw [pairMergeCheck273, Integer.Sparse.eval_merge]
  rw [pairMergedZero272 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck274 : pairMerged274 = Integer.Sparse.merge (Integer.Sparse.scale (-2667168) (rows 23)) (Integer.Sparse.scale (-23879772) (rows 24)) := by decide +kernel

theorem pairMergedZero274 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged274 x = 0 := by
  rw [pairMergeCheck274, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck275 : pairMerged275 = Integer.Sparse.merge (Integer.Sparse.scale (5100732) (rows 25)) (Integer.Sparse.scale (-569268) (rows 26)) := by decide +kernel

theorem pairMergedZero275 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged275 x = 0 := by
  rw [pairMergeCheck275, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck276 : pairMerged276 = Integer.Sparse.merge pairMerged274 pairMerged275 := by decide +kernel

theorem pairMergedZero276 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged276 x = 0 := by
  rw [pairMergeCheck276, Integer.Sparse.eval_merge]
  rw [pairMergedZero274 x h, pairMergedZero275 x h]
  simp only [add_zero]

theorem pairMergeCheck277 : pairMerged277 = Integer.Sparse.merge pairMerged273 pairMerged276 := by decide +kernel

theorem pairMergedZero277 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged277 x = 0 := by
  rw [pairMergeCheck277, Integer.Sparse.eval_merge]
  rw [pairMergedZero273 x h, pairMergedZero276 x h]
  simp only [add_zero]

theorem pairMergeCheck278 : pairMerged278 = Integer.Sparse.merge pairMerged271 pairMerged277 := by decide +kernel

theorem pairMergedZero278 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged278 x = 0 := by
  rw [pairMergeCheck278, Integer.Sparse.eval_merge]
  rw [pairMergedZero271 x h, pairMergedZero277 x h]
  simp only [add_zero]

theorem pairMergeCheck279 : pairMerged279 = Integer.Sparse.merge pairMerged265 pairMerged278 := by decide +kernel

theorem pairMergedZero279 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged279 x = 0 := by
  rw [pairMergeCheck279, Integer.Sparse.eval_merge]
  rw [pairMergedZero265 x h, pairMergedZero278 x h]
  simp only [add_zero]

theorem pairMergeCheck280 : pairMerged280 = Integer.Sparse.merge (Integer.Sparse.scale (1315440) (rows 28)) (Integer.Sparse.scale (-5406912) (rows 29)) := by decide +kernel

theorem pairMergedZero280 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged280 x = 0 := by
  rw [pairMergeCheck280, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck281 : pairMerged281 = Integer.Sparse.merge (Integer.Sparse.scale (-8544690) (rows 27)) pairMerged280 := by decide +kernel

theorem pairMergedZero281 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged281 x = 0 := by
  rw [pairMergeCheck281, Integer.Sparse.eval_merge]
  rw [pairMergedZero280 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck282 : pairMerged282 = Integer.Sparse.merge (Integer.Sparse.scale (1625022) (rows 31)) (Integer.Sparse.scale (-8954064) (rows 32)) := by decide +kernel

theorem pairMergedZero282 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged282 x = 0 := by
  rw [pairMergeCheck282, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck283 : pairMerged283 = Integer.Sparse.merge (Integer.Sparse.scale (2703456) (rows 30)) pairMerged282 := by decide +kernel

theorem pairMergedZero283 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged283 x = 0 := by
  rw [pairMergeCheck283, Integer.Sparse.eval_merge]
  rw [pairMergedZero282 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck284 : pairMerged284 = Integer.Sparse.merge pairMerged281 pairMerged283 := by decide +kernel

theorem pairMergedZero284 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged284 x = 0 := by
  rw [pairMergeCheck284, Integer.Sparse.eval_merge]
  rw [pairMergedZero281 x h, pairMergedZero283 x h]
  simp only [add_zero]

theorem pairMergeCheck285 : pairMerged285 = Integer.Sparse.merge (Integer.Sparse.scale (-1298430) (rows 34)) (Integer.Sparse.scale (3027780) (rows 36)) := by decide +kernel

theorem pairMergedZero285 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged285 x = 0 := by
  rw [pairMergeCheck285, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck286 : pairMerged286 = Integer.Sparse.merge (Integer.Sparse.scale (1429974) (rows 33)) pairMerged285 := by decide +kernel

theorem pairMergedZero286 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged286 x = 0 := by
  rw [pairMergeCheck286, Integer.Sparse.eval_merge]
  rw [pairMergedZero285 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck287 : pairMerged287 = Integer.Sparse.merge (Integer.Sparse.scale (-260820) (rows 37)) (Integer.Sparse.scale (15354360) (rows 39)) := by decide +kernel

theorem pairMergedZero287 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged287 x = 0 := by
  rw [pairMergeCheck287, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck288 : pairMerged288 = Integer.Sparse.merge (Integer.Sparse.scale (2140992) (rows 40)) (Integer.Sparse.scale (-1007559) (rows 41)) := by decide +kernel

theorem pairMergedZero288 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged288 x = 0 := by
  rw [pairMergeCheck288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck289 : pairMerged289 = Integer.Sparse.merge pairMerged287 pairMerged288 := by decide +kernel

theorem pairMergedZero289 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged289 x = 0 := by
  rw [pairMergeCheck289, Integer.Sparse.eval_merge]
  rw [pairMergedZero287 x h, pairMergedZero288 x h]
  simp only [add_zero]

theorem pairMergeCheck290 : pairMerged290 = Integer.Sparse.merge pairMerged286 pairMerged289 := by decide +kernel

theorem pairMergedZero290 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged290 x = 0 := by
  rw [pairMergeCheck290, Integer.Sparse.eval_merge]
  rw [pairMergedZero286 x h, pairMergedZero289 x h]
  simp only [add_zero]

theorem pairMergeCheck291 : pairMerged291 = Integer.Sparse.merge pairMerged284 pairMerged290 := by decide +kernel

theorem pairMergedZero291 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged291 x = 0 := by
  rw [pairMergeCheck291, Integer.Sparse.eval_merge]
  rw [pairMergedZero284 x h, pairMergedZero290 x h]
  simp only [add_zero]

theorem pairMergeCheck292 : pairMerged292 = Integer.Sparse.merge (Integer.Sparse.scale (5472684) (rows 43)) (Integer.Sparse.scale (166320) (rows 45)) := by decide +kernel

theorem pairMergedZero292 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged292 x = 0 := by
  rw [pairMergeCheck292, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck293 : pairMerged293 = Integer.Sparse.merge (Integer.Sparse.scale (277830) (rows 42)) pairMerged292 := by decide +kernel

theorem pairMergedZero293 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged293 x = 0 := by
  rw [pairMergeCheck293, Integer.Sparse.eval_merge]
  rw [pairMergedZero292 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck294 : pairMerged294 = Integer.Sparse.merge (Integer.Sparse.scale (399168) (rows 46)) (Integer.Sparse.scale (-212058) (rows 47)) := by decide +kernel

theorem pairMergedZero294 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged294 x = 0 := by
  rw [pairMergeCheck294, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck295 : pairMerged295 = Integer.Sparse.merge (Integer.Sparse.scale (-117936) (rows 48)) (Integer.Sparse.scale (184464) (rows 49)) := by decide +kernel

theorem pairMergedZero295 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged295 x = 0 := by
  rw [pairMergeCheck295, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck296 : pairMerged296 = Integer.Sparse.merge pairMerged294 pairMerged295 := by decide +kernel

theorem pairMergedZero296 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged296 x = 0 := by
  rw [pairMergeCheck296, Integer.Sparse.eval_merge]
  rw [pairMergedZero294 x h, pairMergedZero295 x h]
  simp only [add_zero]

theorem pairMergeCheck297 : pairMerged297 = Integer.Sparse.merge pairMerged293 pairMerged296 := by decide +kernel

theorem pairMergedZero297 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged297 x = 0 := by
  rw [pairMergeCheck297, Integer.Sparse.eval_merge]
  rw [pairMergedZero293 x h, pairMergedZero296 x h]
  simp only [add_zero]

theorem pairMergeCheck298 : pairMerged298 = Integer.Sparse.merge (Integer.Sparse.scale (-567000) (rows 51)) (Integer.Sparse.scale (-15876) (rows 52)) := by decide +kernel

theorem pairMergedZero298 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged298 x = 0 := by
  rw [pairMergeCheck298, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck299 : pairMerged299 = Integer.Sparse.merge (Integer.Sparse.scale (155358) (rows 50)) pairMerged298 := by decide +kernel

theorem pairMergedZero299 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged299 x = 0 := by
  rw [pairMergeCheck299, Integer.Sparse.eval_merge]
  rw [pairMergedZero298 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck300 : pairMerged300 = Integer.Sparse.merge (Integer.Sparse.scale (-8134560) (rows 53)) (Integer.Sparse.scale (-579474) (rows 54)) := by decide +kernel

theorem pairMergedZero300 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged300 x = 0 := by
  rw [pairMergeCheck300, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck301 : pairMerged301 = Integer.Sparse.merge (Integer.Sparse.scale (-1623888) (rows 55)) (Integer.Sparse.scale (408240) (rows 57)) := by decide +kernel

theorem pairMergedZero301 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged301 x = 0 := by
  rw [pairMergeCheck301, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck302 : pairMerged302 = Integer.Sparse.merge pairMerged300 pairMerged301 := by decide +kernel

theorem pairMergedZero302 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged302 x = 0 := by
  rw [pairMergeCheck302, Integer.Sparse.eval_merge]
  rw [pairMergedZero300 x h, pairMergedZero301 x h]
  simp only [add_zero]

theorem pairMergeCheck303 : pairMerged303 = Integer.Sparse.merge pairMerged299 pairMerged302 := by decide +kernel

theorem pairMergedZero303 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged303 x = 0 := by
  rw [pairMergeCheck303, Integer.Sparse.eval_merge]
  rw [pairMergedZero299 x h, pairMergedZero302 x h]
  simp only [add_zero]

theorem pairMergeCheck304 : pairMerged304 = Integer.Sparse.merge pairMerged297 pairMerged303 := by decide +kernel

theorem pairMergedZero304 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged304 x = 0 := by
  rw [pairMergeCheck304, Integer.Sparse.eval_merge]
  rw [pairMergedZero297 x h, pairMergedZero303 x h]
  simp only [add_zero]

theorem pairMergeCheck305 : pairMerged305 = Integer.Sparse.merge pairMerged291 pairMerged304 := by decide +kernel

theorem pairMergedZero305 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged305 x = 0 := by
  rw [pairMergeCheck305, Integer.Sparse.eval_merge]
  rw [pairMergedZero291 x h, pairMergedZero304 x h]
  simp only [add_zero]

theorem pairMergeCheck306 : pairMerged306 = Integer.Sparse.merge pairMerged279 pairMerged305 := by decide +kernel

theorem pairMergedZero306 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged306 x = 0 := by
  rw [pairMergeCheck306, Integer.Sparse.eval_merge]
  rw [pairMergedZero279 x h, pairMergedZero305 x h]
  simp only [add_zero]

theorem pairMergeCheck307 : pairMerged307 = Integer.Sparse.merge (Integer.Sparse.scale (10670940) (rows 59)) (Integer.Sparse.scale (1762992) (rows 60)) := by decide +kernel

theorem pairMergedZero307 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged307 x = 0 := by
  rw [pairMergeCheck307, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck308 : pairMerged308 = Integer.Sparse.merge (Integer.Sparse.scale (513702) (rows 58)) pairMerged307 := by decide +kernel

theorem pairMergedZero308 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged308 x = 0 := by
  rw [pairMergeCheck308, Integer.Sparse.eval_merge]
  rw [pairMergedZero307 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck309 : pairMerged309 = Integer.Sparse.merge (Integer.Sparse.scale (5288976) (rows 62)) (Integer.Sparse.scale (4604040) (rows 63)) := by decide +kernel

theorem pairMergedZero309 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged309 x = 0 := by
  rw [pairMergeCheck309, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck310 : pairMerged310 = Integer.Sparse.merge (Integer.Sparse.scale (3900960) (rows 61)) pairMerged309 := by decide +kernel

theorem pairMergedZero310 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged310 x = 0 := by
  rw [pairMergeCheck310, Integer.Sparse.eval_merge]
  rw [pairMergedZero309 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck311 : pairMerged311 = Integer.Sparse.merge pairMerged308 pairMerged310 := by decide +kernel

theorem pairMergedZero311 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged311 x = 0 := by
  rw [pairMergeCheck311, Integer.Sparse.eval_merge]
  rw [pairMergedZero308 x h, pairMergedZero310 x h]
  simp only [add_zero]

theorem pairMergeCheck312 : pairMerged312 = Integer.Sparse.merge (Integer.Sparse.scale (585144) (rows 67)) (Integer.Sparse.scale (-12678120) (rows 68)) := by decide +kernel

theorem pairMergedZero312 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged312 x = 0 := by
  rw [pairMergeCheck312, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck313 : pairMerged313 = Integer.Sparse.merge (Integer.Sparse.scale (-3525984) (rows 65)) pairMerged312 := by decide +kernel

theorem pairMergedZero313 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged313 x = 0 := by
  rw [pairMergeCheck313, Integer.Sparse.eval_merge]
  rw [pairMergedZero312 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck314 : pairMerged314 = Integer.Sparse.merge (Integer.Sparse.scale (31026240) (rows 69)) (Integer.Sparse.scale (1623888) (rows 71)) := by decide +kernel

theorem pairMergedZero314 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged314 x = 0 := by
  rw [pairMergeCheck314, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck315 : pairMerged315 = Integer.Sparse.merge (Integer.Sparse.scale (-458136) (rows 72)) (Integer.Sparse.scale (229068) (rows 74)) := by decide +kernel

theorem pairMergedZero315 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged315 x = 0 := by
  rw [pairMergeCheck315, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck316 : pairMerged316 = Integer.Sparse.merge pairMerged314 pairMerged315 := by decide +kernel

theorem pairMergedZero316 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged316 x = 0 := by
  rw [pairMergeCheck316, Integer.Sparse.eval_merge]
  rw [pairMergedZero314 x h, pairMergedZero315 x h]
  simp only [add_zero]

theorem pairMergeCheck317 : pairMerged317 = Integer.Sparse.merge pairMerged313 pairMerged316 := by decide +kernel

theorem pairMergedZero317 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged317 x = 0 := by
  rw [pairMergeCheck317, Integer.Sparse.eval_merge]
  rw [pairMergedZero313 x h, pairMergedZero316 x h]
  simp only [add_zero]

theorem pairMergeCheck318 : pairMerged318 = Integer.Sparse.merge pairMerged311 pairMerged317 := by decide +kernel

theorem pairMergedZero318 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged318 x = 0 := by
  rw [pairMergeCheck318, Integer.Sparse.eval_merge]
  rw [pairMergedZero311 x h, pairMergedZero317 x h]
  simp only [add_zero]

theorem pairMergeCheck319 : pairMerged319 = Integer.Sparse.merge (Integer.Sparse.scale (-838026) (rows 76)) (Integer.Sparse.scale (-3433185) (rows 77)) := by decide +kernel

theorem pairMergedZero319 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged319 x = 0 := by
  rw [pairMergeCheck319, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck320 : pairMerged320 = Integer.Sparse.merge (Integer.Sparse.scale (768852) (rows 75)) pairMerged319 := by decide +kernel

theorem pairMergedZero320 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged320 x = 0 := by
  rw [pairMergeCheck320, Integer.Sparse.eval_merge]
  rw [pairMergedZero319 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck321 : pairMerged321 = Integer.Sparse.merge (Integer.Sparse.scale (-561330) (rows 78)) (Integer.Sparse.scale (2806650) (rows 79)) := by decide +kernel

theorem pairMergedZero321 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged321 x = 0 := by
  rw [pairMergeCheck321, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck322 : pairMerged322 = Integer.Sparse.merge (Integer.Sparse.scale (4320540) (rows 80)) (Integer.Sparse.scale (-10560375) (rows 81)) := by decide +kernel

theorem pairMergedZero322 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged322 x = 0 := by
  rw [pairMergeCheck322, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck323 : pairMerged323 = Integer.Sparse.merge pairMerged321 pairMerged322 := by decide +kernel

theorem pairMergedZero323 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged323 x = 0 := by
  rw [pairMergeCheck323, Integer.Sparse.eval_merge]
  rw [pairMergedZero321 x h, pairMergedZero322 x h]
  simp only [add_zero]

theorem pairMergeCheck324 : pairMerged324 = Integer.Sparse.merge pairMerged320 pairMerged323 := by decide +kernel

theorem pairMergedZero324 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged324 x = 0 := by
  rw [pairMergeCheck324, Integer.Sparse.eval_merge]
  rw [pairMergedZero320 x h, pairMergedZero323 x h]
  simp only [add_zero]

theorem pairMergeCheck325 : pairMerged325 = Integer.Sparse.merge (Integer.Sparse.scale (1122660) (rows 83)) (Integer.Sparse.scale (-1296162) (rows 84)) := by decide +kernel

theorem pairMergedZero325 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged325 x = 0 := by
  rw [pairMergeCheck325, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck326 : pairMerged326 = Integer.Sparse.merge (Integer.Sparse.scale (838026) (rows 82)) pairMerged325 := by decide +kernel

theorem pairMergedZero326 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged326 x = 0 := by
  rw [pairMergeCheck326, Integer.Sparse.eval_merge]
  rw [pairMergedZero325 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck327 : pairMerged327 = Integer.Sparse.merge (Integer.Sparse.scale (-1551312) (rows 85)) (Integer.Sparse.scale (1093176) (rows 86)) := by decide +kernel

theorem pairMergedZero327 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged327 x = 0 := by
  rw [pairMergeCheck327, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck328 : pairMerged328 = Integer.Sparse.merge (Integer.Sparse.scale (458136) (rows 87)) (Integer.Sparse.scale (2129652) (rows 89)) := by decide +kernel

theorem pairMergedZero328 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged328 x = 0 := by
  rw [pairMergeCheck328, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck329 : pairMerged329 = Integer.Sparse.merge pairMerged327 pairMerged328 := by decide +kernel

theorem pairMergedZero329 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged329 x = 0 := by
  rw [pairMergeCheck329, Integer.Sparse.eval_merge]
  rw [pairMergedZero327 x h, pairMergedZero328 x h]
  simp only [add_zero]

theorem pairMergeCheck330 : pairMerged330 = Integer.Sparse.merge pairMerged326 pairMerged329 := by decide +kernel

theorem pairMergedZero330 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged330 x = 0 := by
  rw [pairMergeCheck330, Integer.Sparse.eval_merge]
  rw [pairMergedZero326 x h, pairMergedZero329 x h]
  simp only [add_zero]

theorem pairMergeCheck331 : pairMerged331 = Integer.Sparse.merge pairMerged324 pairMerged330 := by decide +kernel

theorem pairMergedZero331 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged331 x = 0 := by
  rw [pairMergeCheck331, Integer.Sparse.eval_merge]
  rw [pairMergedZero324 x h, pairMergedZero330 x h]
  simp only [add_zero]

theorem pairMergeCheck332 : pairMerged332 = Integer.Sparse.merge pairMerged318 pairMerged331 := by decide +kernel

theorem pairMergedZero332 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged332 x = 0 := by
  rw [pairMergeCheck332, Integer.Sparse.eval_merge]
  rw [pairMergedZero318 x h, pairMergedZero331 x h]
  simp only [add_zero]

theorem pairMergeCheck333 : pairMerged333 = Integer.Sparse.merge (Integer.Sparse.scale (-360612) (rows 91)) (Integer.Sparse.scale (405972) (rows 92)) := by decide +kernel

theorem pairMergedZero333 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged333 x = 0 := by
  rw [pairMergeCheck333, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck334 : pairMerged334 = Integer.Sparse.merge (Integer.Sparse.scale (458136) (rows 90)) pairMerged333 := by decide +kernel

theorem pairMergedZero334 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged334 x = 0 := by
  rw [pairMergeCheck334, Integer.Sparse.eval_merge]
  rw [pairMergedZero333 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck335 : pairMerged335 = Integer.Sparse.merge (Integer.Sparse.scale (-2041200) (rows 96)) (Integer.Sparse.scale (-1796256) (rows 97)) := by decide +kernel

theorem pairMergedZero335 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged335 x = 0 := by
  rw [pairMergeCheck335, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck336 : pairMerged336 = Integer.Sparse.merge (Integer.Sparse.scale (-3075408) (rows 93)) pairMerged335 := by decide +kernel

theorem pairMergedZero336 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged336 x = 0 := by
  rw [pairMergeCheck336, Integer.Sparse.eval_merge]
  rw [pairMergedZero335 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck337 : pairMerged337 = Integer.Sparse.merge pairMerged334 pairMerged336 := by decide +kernel

theorem pairMergedZero337 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged337 x = 0 := by
  rw [pairMergeCheck337, Integer.Sparse.eval_merge]
  rw [pairMergedZero334 x h, pairMergedZero336 x h]
  simp only [add_zero]

theorem pairMergeCheck338 : pairMerged338 = Integer.Sparse.merge (Integer.Sparse.scale (-1728216) (rows 99)) (Integer.Sparse.scale (1122660) (rows 100)) := by decide +kernel

theorem pairMergedZero338 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged338 x = 0 := by
  rw [pairMergeCheck338, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck339 : pairMerged339 = Integer.Sparse.merge (Integer.Sparse.scale (2806650) (rows 98)) pairMerged338 := by decide +kernel

theorem pairMergedZero339 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged339 x = 0 := by
  rw [pairMergeCheck339, Integer.Sparse.eval_merge]
  rw [pairMergedZero338 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck340 : pairMerged340 = Integer.Sparse.merge (Integer.Sparse.scale (-3375540) (rows 101)) (Integer.Sparse.scale (360612) (rows 102)) := by decide +kernel

theorem pairMergedZero340 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged340 x = 0 := by
  rw [pairMergeCheck340, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck341 : pairMerged341 = Integer.Sparse.merge (Integer.Sparse.scale (56700) (rows 103)) (Integer.Sparse.scale (27216) (rows 104)) := by decide +kernel

theorem pairMergedZero341 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged341 x = 0 := by
  rw [pairMergeCheck341, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck342 : pairMerged342 = Integer.Sparse.merge pairMerged340 pairMerged341 := by decide +kernel

theorem pairMergedZero342 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged342 x = 0 := by
  rw [pairMergeCheck342, Integer.Sparse.eval_merge]
  rw [pairMergedZero340 x h, pairMergedZero341 x h]
  simp only [add_zero]

theorem pairMergeCheck343 : pairMerged343 = Integer.Sparse.merge pairMerged339 pairMerged342 := by decide +kernel

theorem pairMergedZero343 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged343 x = 0 := by
  rw [pairMergeCheck343, Integer.Sparse.eval_merge]
  rw [pairMergedZero339 x h, pairMergedZero342 x h]
  simp only [add_zero]

theorem pairMergeCheck344 : pairMerged344 = Integer.Sparse.merge pairMerged337 pairMerged343 := by decide +kernel

theorem pairMergedZero344 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged344 x = 0 := by
  rw [pairMergeCheck344, Integer.Sparse.eval_merge]
  rw [pairMergedZero337 x h, pairMergedZero343 x h]
  simp only [add_zero]

theorem pairMergeCheck345 : pairMerged345 = Integer.Sparse.merge (Integer.Sparse.scale (-38556) (rows 107)) (Integer.Sparse.scale (-158760) (rows 109)) := by decide +kernel

theorem pairMergedZero345 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged345 x = 0 := by
  rw [pairMergeCheck345, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck346 : pairMerged346 = Integer.Sparse.merge (Integer.Sparse.scale (1360800) (rows 105)) pairMerged345 := by decide +kernel

theorem pairMergedZero346 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged346 x = 0 := by
  rw [pairMergeCheck346, Integer.Sparse.eval_merge]
  rw [pairMergedZero345 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck347 : pairMerged347 = Integer.Sparse.merge (Integer.Sparse.scale (-113400) (rows 110)) (Integer.Sparse.scale (-272160) (rows 111)) := by decide +kernel

theorem pairMergedZero347 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged347 x = 0 := by
  rw [pairMergeCheck347, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck348 : pairMerged348 = Integer.Sparse.merge (Integer.Sparse.scale (77112) (rows 112)) (Integer.Sparse.scale (-408240) (rows 113)) := by decide +kernel

theorem pairMergedZero348 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged348 x = 0 := by
  rw [pairMergeCheck348, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck349 : pairMerged349 = Integer.Sparse.merge pairMerged347 pairMerged348 := by decide +kernel

theorem pairMergedZero349 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged349 x = 0 := by
  rw [pairMergeCheck349, Integer.Sparse.eval_merge]
  rw [pairMergedZero347 x h, pairMergedZero348 x h]
  simp only [add_zero]

theorem pairMergeCheck350 : pairMerged350 = Integer.Sparse.merge pairMerged346 pairMerged349 := by decide +kernel

theorem pairMergedZero350 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged350 x = 0 := by
  rw [pairMergeCheck350, Integer.Sparse.eval_merge]
  rw [pairMergedZero346 x h, pairMergedZero349 x h]
  simp only [add_zero]

theorem pairMergeCheck351 : pairMerged351 = Integer.Sparse.merge (Integer.Sparse.scale (-47628) (rows 115)) (Integer.Sparse.scale (-108864) (rows 116)) := by decide +kernel

theorem pairMergedZero351 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged351 x = 0 := by
  rw [pairMergeCheck351, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck352 : pairMerged352 = Integer.Sparse.merge (Integer.Sparse.scale (170100) (rows 114)) pairMerged351 := by decide +kernel

theorem pairMergedZero352 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged352 x = 0 := by
  rw [pairMergeCheck352, Integer.Sparse.eval_merge]
  rw [pairMergedZero351 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck353 : pairMerged353 = Integer.Sparse.merge (Integer.Sparse.scale (27216) (rows 123)) (Integer.Sparse.scale (1156680) (rows 128)) := by decide +kernel

theorem pairMergedZero353 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged353 x = 0 := by
  rw [pairMergeCheck353, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck354 : pairMerged354 = Integer.Sparse.merge (Integer.Sparse.scale (-1156680) (rows 129)) (Integer.Sparse.scale (-54432) (rows 130)) := by decide +kernel

theorem pairMergedZero354 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged354 x = 0 := by
  rw [pairMergeCheck354, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck355 : pairMerged355 = Integer.Sparse.merge pairMerged353 pairMerged354 := by decide +kernel

theorem pairMergedZero355 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged355 x = 0 := by
  rw [pairMergeCheck355, Integer.Sparse.eval_merge]
  rw [pairMergedZero353 x h, pairMergedZero354 x h]
  simp only [add_zero]

theorem pairMergeCheck356 : pairMerged356 = Integer.Sparse.merge pairMerged352 pairMerged355 := by decide +kernel

theorem pairMergedZero356 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged356 x = 0 := by
  rw [pairMergeCheck356, Integer.Sparse.eval_merge]
  rw [pairMergedZero352 x h, pairMergedZero355 x h]
  simp only [add_zero]

theorem pairMergeCheck357 : pairMerged357 = Integer.Sparse.merge pairMerged350 pairMerged356 := by decide +kernel

theorem pairMergedZero357 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged357 x = 0 := by
  rw [pairMergeCheck357, Integer.Sparse.eval_merge]
  rw [pairMergedZero350 x h, pairMergedZero356 x h]
  simp only [add_zero]

theorem pairMergeCheck358 : pairMerged358 = Integer.Sparse.merge pairMerged344 pairMerged357 := by decide +kernel

theorem pairMergedZero358 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged358 x = 0 := by
  rw [pairMergeCheck358, Integer.Sparse.eval_merge]
  rw [pairMergedZero344 x h, pairMergedZero357 x h]
  simp only [add_zero]

theorem pairMergeCheck359 : pairMerged359 = Integer.Sparse.merge pairMerged332 pairMerged358 := by decide +kernel

theorem pairMergedZero359 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged359 x = 0 := by
  rw [pairMergeCheck359, Integer.Sparse.eval_merge]
  rw [pairMergedZero332 x h, pairMergedZero358 x h]
  simp only [add_zero]

theorem pairMergeCheck360 : pairMerged360 = Integer.Sparse.merge pairMerged306 pairMerged359 := by decide +kernel

theorem pairMergedZero360 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged360 x = 0 := by
  rw [pairMergeCheck360, Integer.Sparse.eval_merge]
  rw [pairMergedZero306 x h, pairMergedZero359 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairTargetPermutation1 : List.Perm target1 pairMerged360 := by decide +kernel

theorem mergeConsequence1 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval target1 x = 0 := by
  rw [Integer.Sparse.eval_perm pairTargetPermutation1]
  exact pairMergedZero360 x h

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem targetZero1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval PairData.target1 (momentVector H) = 0 :=
  PairData.mergeConsequence1 _ (allRowsSound_e hH)

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem finalReindex1 : List.Perm
    (Integer.Sparse.reindex PairSourceBridge.coordinateMap PairData.target1) integerMerge49 := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem certificate_zero1 {H : CMatrix} (hH : IsHadamard H) : expanded1 H = 0 := by
  have hz := PairSourceBridge.targetZero1 hH
  unfold PairSourceBridge.momentVector at hz
  rw [← Integer.Sparse.eval_reindex] at hz
  rw [Integer.Sparse.eval_perm finalReindex1] at hz
  have he := expandedIdentity1_e hH
  rw [hz] at he
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_FourierTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem pair_same_certificate {H : CMatrix} (hH : IsHadamard H) :
    PairCertificateIdentity H qSame := by
  unfold PairCertificateIdentity
  rw [← Certificate.PairTargetSemantics.expanded_identity1 hH]
  exact Certificate.PairTargetSemantics.certificate_zero1 hH

/-- The exact pair certificates imply the manuscript's complete dichotomy. -/
theorem exact_dichotomy {H : CMatrix} (hH : IsHadamard H) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) :=
  dichotomy_of_pair_certificates hH (pair_cross_certificate_e hH) (pair_same_certificate hH)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_norm_le_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) : ‖rowFourier H ρ a‖ ≤ 1 := by
  rw [rowFourier_eq_g]
  exact g_norm_le_one hH _

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_abs_le_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    |mixedMoment B A label| ≤ 1 := by
  apply abs_average_le_one
  intro r
  apply abs_average_le_one
  intro ρ
  apply abs_average_le_one
  intro τ
  apply (Complex.abs_re_le_norm _).trans
  rw [mixedIntegrand, Complex.norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun j _ => rowFourier_norm_le_one (relativeMatrix_isHadamard B hB r _) ρ _)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem complete_family_fourier_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    AllTransitionsFourierZero B := by
  intro r s
  rcases exact_dichotomy (relativeMatrix_isHadamard B hB r s) with hz | hs
  · exact hz
  · exact (complete_family_square_not_hadamard_e B hB r s hs).elim

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Families
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and cardinality lemmas. These reductions do not establish the
no-seven or completion theorem, which remain separate proof obligations. -/

noncomputable section
namespace MUB6

theorem IsMUBFamily.reindex {m n : ℕ} {B : Fin n → Basis} (hB : IsMUBFamily B)
    (f : Fin m → Fin n) (hf : Function.Injective f) : IsMUBFamily (B ∘ f) := by
  intro r s hrs i j
  exact hB (f r) (f s) (fun h => hrs (hf h)) i j

theorem attainable_mono {m n : ℕ} (hmn : m ≤ n) (hn : Attainable n) :
    Attainable m := by
  rcases hn with ⟨B, hB⟩
  exact ⟨B ∘ Fin.castLE hmn, hB.reindex _ (Fin.castLE_injective hmn)⟩

theorem no_six_of_completion (hcompletion : SixExtendToSeven)
    (hseven : ¬ Attainable 7) : ¬ Attainable 6 := by
  rintro ⟨B, hB⟩
  rcases hcompletion B hB with ⟨C, hC, _⟩
  exact hseven ⟨C, hC⟩

theorem family_size_le_five_of_no_six (hsix : ¬ Attainable 6)
    (n : ℕ) (hn : Attainable n) : n ≤ 5 := by
  by_contra h
  have h6 : 6 ≤ n := by omega
  exact hsix (attainable_mono h6 hn)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Meaning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem Code.abs_moment_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (c : Code) :
    |c.moment B| ≤ 1 := mixedMoment_abs_le_one B hB _ _

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem familyPairVector_abs_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (i : Fin 909) :
    |familyPairVector B i| ≤ 1 := by
  apply abs_average_le_one
  intro r
  apply abs_average_le_one
  intro s
  exact injectiveMoment_abs_le_one (relativeMatrix_isHadamard B hB r s) _

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem mixedVector_abs_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (i : Master) :
    |mixedVector B i| ≤ 1 := by
  cases i with
  | inl i => exact familyPairVector_abs_le_one B hB i
  | inr i => exact Code.abs_moment_le_one B hB (codes i)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem numericVector_abs_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (i : Fin 3237) :
    |numericVector B i| ≤ 1 := mixedVector_abs_le_one B hB (keyMap i)

theorem numericVector_zero (B : Fin 7 → Basis) : numericVector B 0 = 1 := by
  change familyPairVector B 0 = 1
  have h (H : CMatrix) : PairSemantics.momentVector H 0 = 1 := by
    change injectiveMoment H (0 : Matrix (Fin 0) (Fin 0) ℤ) = 1
    exact injectiveMoment_empty H
  unfold familyPairVector familyAverage
  simp only [h, average_const]

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.Integer.Sparse

variable {ι κ : Type*}

theorem eval_substitute (v : Sparse κ) (rows : κ → Sparse ι) (x : ι → ℝ) :
    eval (substitute v rows) x = eval v (fun k => eval (rows k) x) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_scale, eval_cons] at *
    rw [ih]

theorem eval_mul_left (v : Sparse ι) (x : ι → ℝ) (c : ℝ) :
    eval v (fun i => c * x i) = c * eval v x := by
  induction v with
  | nil => simp
  | cons p v ih => simp only [eval_cons, ih] <;> ring

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_JointBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An orthonormal eigenbasis for a commuting symmetric family

This is the finite-dimensional simultaneous spectral step in the completion
argument. It specializes mathlib's joint-eigenspace decomposition and retains
an explicit common eigenvalue for each basis vector and each operator.
-/

namespace MUB6.Weiner

open Module
open scoped Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype ι] in
lemma jointSubspace_span (T : ι → End ℂ E) (hsym : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise (Commute on T)) : (⨆ χ, jointSubspace T χ) = ⊤ := by
  apply top_unique
  rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm]
  apply iSup_le
  intro γ
  by_cases hγ : (⨅ i, (T i).eigenspace (γ i)) = ⊥
  · rw [hγ]
    exact bot_le
  · let χ : JointIndex T := fun i =>
      ⟨γ i, fun hi => hγ (eq_bot_iff.mpr ((iInf_le _ i).trans (le_of_eq hi)))⟩
    exact le_iSup_of_le χ le_rfl

omit [Fintype ι] [FiniteDimensional ℂ E] in
lemma jointSubspace_orthogonal (T : ι → End ℂ E) (hsym : ∀ i, (T i).IsSymmetric) :
    OrthogonalFamily ℂ (fun χ => jointSubspace T χ)
      (fun χ => (jointSubspace T χ).subtypeₗᵢ) := by
  have hinj : Function.Injective (fun χ : JointIndex T => fun i => (χ i : ℂ)) := by
    intro χ ψ h
    funext i
    exact Subtype.ext (congrFun h i)
  exact (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym).comp hinj

/-- A finite commuting family of symmetric complex linear operators admits a
single orthonormal basis of simultaneous eigenvectors. -/
theorem exists_joint_eigenbasis (T : ι → End ℂ E)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
      (ev : Fin (finrank ℂ E) → ι → ℂ),
      ∀ j i, T i (b j) = ev j i • b j := by
  classical
  have hortho := jointSubspace_orthogonal T hsym
  have hinternal : DirectSum.IsInternal (jointSubspace T) :=
    hortho.isInternal_iff.mpr (by simp [jointSubspace_span T hsym hcomm])
  let b := hinternal.subordinateOrthonormalBasis rfl hortho
  let ev : Fin (finrank ℂ E) → ι → ℂ := fun j i =>
    (hinternal.subordinateOrthonormalBasisIndex rfl j hortho i : ℂ)
  refine ⟨b, ev, ?_⟩
  intro j i
  have hj := hinternal.subordinateOrthonormalBasis_subordinate rfl j hortho
  exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hj i)

omit [FiniteDimensional ℂ E] in
/-- Every coordinate projection of an eigenbasis commutes with the operator.
This argument only uses the basis expansions, so no separate claim about the
reality of the eigenvalues is needed. -/
theorem commute_rankOne_of_eigenbasis {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ ℂ E) (T : End ℂ E) (ev : κ → ℂ)
    (heig : ∀ j, T (b j) = ev j • b j) (i : κ) :
    Commute T (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap := by
  classical
  change T.comp (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap =
    (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap.comp T
  apply b.toBasis.ext
  intro j
  by_cases hij : i = j
  · subst j
    simp [InnerProductSpace.rankOne_apply, heig]
  · simp [InnerProductSpace.rankOne_apply, heig,
      orthonormal_iff_ite.mp b.orthonormal i j, hij]

/-- The simultaneous eigenbasis can equivalently be characterized by its
commuting rank-one coordinate projections. -/
theorem exists_joint_projection_basis (T : ι → End ℂ E)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      ∀ i j, Commute (T i) (InnerProductSpace.rankOne ℂ (b j) (b j)).toLinearMap := by
  obtain ⟨b, ev, heig⟩ := exists_joint_eigenbasis T hsym hcomm
  exact ⟨b, fun i j => commute_rankOne_of_eigenbasis b (T i) (fun j => ev j i)
    (fun j => heig j i) j⟩

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_ProjectionBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-one projectors fixed by a realigned orthogonal projection

The fixed space of the complement operator contains the projectors of an
orthonormal basis. This is the spectral part of the completion argument.
-/

namespace MUB6.Weiner

open Matrix Module
open scoped BigOperators Function

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma toEuclideanLin_projector (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (projector v) = (InnerProductSpace.rankOne ℂ v v).toLinearMap := by
  rw [projector, ← InnerProductSpace.symm_toEuclideanLin_rankOne]
  exact LinearEquiv.apply_symm_apply _ _

omit [Fintype n] [DecidableEq n] in
lemma hermitianColumn_isHermitian (C : Matrix (n × n) (n × n) ℂ)
    (p : Bool × (n × n)) : (hermitianColumn C p).IsHermitian := by
  rcases p with ⟨b, p⟩
  cases b <;> simp only [hermitianColumn, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (realPart (superColumn C p)).property
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (imaginaryPart (superColumn C p)).property

omit [DecidableEq n] in
lemma hermitianColumn_fixed (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (p : Bool × (n × n)) : applySuper C (hermitianColumn C p) = hermitianColumn C p := by
  have hf := superColumn_fixed C hidem p.2
  have hs : applySuper C (superColumn C p.2)ᴴ = (superColumn C p.2)ᴴ := by
    rw [applySuper_conjTranspose C hherm hidem hreal, hf]
  rcases p with ⟨b, p⟩
  cases b <;> simp only [hermitianColumn, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · rw [realPart_apply_coe, applySuper_real_smul, applySuper_add]
    simp only [Matrix.star_eq_conjTranspose, hf, hs]
  · rw [imaginaryPart_apply_coe, applySuper_smul, applySuper_real_smul, applySuper_sub]
    simp only [Matrix.star_eq_conjTranspose, hf, hs]

/-- Every unital, Hermitian, idempotent, realigned superoperator fixes all the
rank-one coordinate projectors of some orthonormal basis. -/
theorem exists_fixed_projection_basis (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1) :
    ∃ b : OrthonormalBasis (Fin (Fintype.card n)) ℂ (EuclideanSpace ℂ n),
      ∀ j, applySuper C (projector (b j)) = projector (b j) := by
  classical
  let M := hermitianColumn C
  let T : Bool × (n × n) → End ℂ (EuclideanSpace ℂ n) :=
    fun p => Matrix.toEuclideanLin (M p)
  have hsym : ∀ p, (T p).IsSymmetric := fun p =>
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hermitianColumn_isHermitian C p)
  have hcomm : Pairwise (Commute on T) := by
    intro p q _
    have h := super_fixedPoints_commute C hherm hidem hreal hunital (M p) (M q)
      (hermitianColumn_fixed C hherm hidem hreal p)
      (hermitianColumn_fixed C hherm hidem hreal q)
    exact h.map (Matrix.toLpLinAlgEquiv 2)
  obtain ⟨b₀, hb₀⟩ := exists_joint_projection_basis T hsym hcomm
  have hdim : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace
  let b := b₀.reindex (finCongr hdim)
  refine ⟨b, ?_⟩
  intro j
  let Q := projector (b j)
  have hQM (p : Bool × (n × n)) : Commute Q (M p) := by
    apply (Matrix.toLpLinAlgEquiv 2).injective
    simp only [map_mul]
    change Matrix.toEuclideanLin Q * T p = T p * Matrix.toEuclideanLin Q
    change Matrix.toEuclideanLin (projector (b j)) * T p =
      T p * Matrix.toEuclideanLin (projector (b j))
    rw [toEuclideanLin_projector]
    have h := (hb₀ p ((finCongr hdim).symm j)).symm.eq
    simpa only [b, OrthonormalBasis.reindex_apply] using h
  have hQA (p : n × n) : Commute Q (superColumn C p) := by
    rw [← realPart_add_I_smul_imaginaryPart (superColumn C p)]
    exact (hQM (false, p)).add_right ((hQM (true, p)).smul_right Complex.I)
  rw [applySuper_eq_kraus_columns C hherm hidem hreal]
  change kraus (superColumn C) Q = Q
  have hunit : ∑ p, (superColumn C p)ᴴ * superColumn C p = 1 := by
    simpa only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus, Matrix.mul_one]
      using hunital
  calc
    kraus (superColumn C) Q = ∑ p, (superColumn C p)ᴴ * (superColumn C p) * Q := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.mul_assoc, (hQA p).eq, ← Matrix.mul_assoc]
    _ = (∑ p, (superColumn C p)ᴴ * superColumn C p) * Q := by rw [Matrix.sum_mul]
    _ = Q := by rw [hunit, Matrix.one_mul]

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Completion
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weiner completion in dimension six

The missing orthonormal basis is obtained by simultaneously diagonalizing the
commutative fixed space of the complementary Hilbert--Schmidt projection.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma unbiased_of_complement_fixed (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B)
    (b : MUB6.Basis)
    (hfixed : ∀ j, applySuper (complementMatrix (fun r => basisCoordinates (B r)))
      (projector (b j)) = projector (b j)) :
    ∀ r i j, Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6 := by
  intro r i j
  have hv : complementMatrix (fun r => basisCoordinates (B r)) *ᵥ
      projectorVector (basisCoordinates b j) = projectorVector (basisCoordinates b j) := by
    funext p
    exact congrArg (fun X : CMatrix => X p.1 p.2) (hfixed j)
  have h := dotProduct_fixed_of_image
    (complementMatrix (fun r => basisCoordinates (B r))) (complementMatrix_hermitian _)
    (projectorVector (basisCoordinates (B r) i)) (projectorVector (basisCoordinates b j))
    traceVector (1 / 6 : ℂ) (basis_complement_projectorVector B hB r i) hv
  rw [basis_projector_inner, traceVector_dot_projectorVector, Complex.star_def,
    Complex.mul_conj] at h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact hre

/-- Every family of six mutually unbiased orthonormal bases of `ℂ⁶` has a
seventh orthonormal basis unbiased to each of them. -/
theorem exists_unbiased_basis (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    ∃ b : MUB6.Basis, ∀ r i j,
      Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6 := by
  have h : ∃ b : MUB6.Basis, ∀ j,
      applySuper (complementMatrix (fun r => basisCoordinates (B r)))
        (projector (b j)) = projector (b j) := by
    have h₀ := exists_fixed_projection_basis (complementMatrix (fun r => basisCoordinates (B r)))
      (complementMatrix_hermitian _) (basis_complement_idempotent B hB)
      (complementMatrix_realigned _) (basis_complement_unital B)
    have hcard : Fintype.card Coord = 6 := Fintype.card_fin 6
    rw [hcard] at h₀
    exact h₀
  obtain ⟨b, hb⟩ := h
  exact ⟨b, unbiased_of_complement_fixed B hB b hb⟩

lemma appendBasis_castSucc (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) (r : Fin 6) :
    appendBasis B b r.castSucc = B r := by simp [appendBasis]

lemma appendBasis_last (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) :
    appendBasis B b (Fin.last 6) = b :=
  Fin.lastCases_last

lemma appendBasis_isMUB (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) (b : MUB6.Basis)
    (hb : ∀ r i j, Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6) :
    IsMUBFamily (appendBasis B b) := by
  unfold IsMUBFamily
  intro r
  refine Fin.lastCases ?_ ?_ r
  · intro s
    refine Fin.lastCases ?_ ?_ s
    · intro hrs
      exact (hrs rfl).elim
    · intro s _ i j
      rw [appendBasis_last, appendBasis_castSucc, ← inner_conj_symm]
      simpa only [Complex.normSq_conj] using hb s j i
  · intro r s
    refine Fin.lastCases ?_ ?_ s
    · intro _ i j
      simpa only [appendBasis_castSucc, appendBasis_last] using hb r i j
    · intro s hrs i j
      have hne : r ≠ s := fun h => hrs (congrArg Fin.castSucc h)
      simpa only [appendBasis_castSucc] using hB r s hne i j

/-- Weiner's completion theorem, specialized to six-dimensional complex
Hilbert space, with the original six bases retained at their original indices. -/
theorem six_extend_to_seven (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    ∃ C : Fin 7 → MUB6.Basis, IsMUBFamily C ∧ ∀ r, C r.castSucc = B r := by
  obtain ⟨b, hb⟩ := exists_unbiased_basis B hB
  exact ⟨appendBasis B b, appendBasis_isMUB B hB b hb, appendBasis_castSucc B b⟩

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck33 : originalBlock33 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock33 keyMomentRows) := by decide +kernel

theorem originalBlockEval33 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock33 x =
      Integer.Sparse.eval keyPolynomialBlock33 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck33, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck36 : originalBlock36 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock36 keyMomentRows) := by decide +kernel

theorem originalBlockEval36 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock36 x =
      Integer.Sparse.eval keyPolynomialBlock36 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck36, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck37 : originalBlock37 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock37 keyMomentRows) := by decide +kernel

theorem originalBlockEval37 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock37 x =
      Integer.Sparse.eval keyPolynomialBlock37 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck37, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck38 : originalBlock38 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock38 keyMomentRows) := by decide +kernel

theorem originalBlockEval38 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock38 x =
      Integer.Sparse.eval keyPolynomialBlock38 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck38, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck39 : originalBlock39 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock39 keyMomentRows) := by decide +kernel

theorem originalBlockEval39 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock39 x =
      Integer.Sparse.eval keyPolynomialBlock39 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck39, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck40 : originalBlock40 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock40 keyMomentRows) := by decide +kernel

theorem originalBlockEval40 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock40 x =
      Integer.Sparse.eval keyPolynomialBlock40 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck40, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck41 : originalBlock41 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock41 keyMomentRows) := by decide +kernel

theorem originalBlockEval41 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock41 x =
      Integer.Sparse.eval keyPolynomialBlock41 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck41, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck42 : originalBlock42 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock42 keyMomentRows) := by decide +kernel

theorem originalBlockEval42 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock42 x =
      Integer.Sparse.eval keyPolynomialBlock42 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck42, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck43 : originalBlock43 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock43 keyMomentRows) := by decide +kernel

theorem originalBlockEval43 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock43 x =
      Integer.Sparse.eval keyPolynomialBlock43 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck43, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck44 : originalBlock44 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock44 keyMomentRows) := by decide +kernel

theorem originalBlockEval44 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock44 x =
      Integer.Sparse.eval keyPolynomialBlock44 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck44, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck19 : originalBlock19 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock19 keyMomentRows) := by decide +kernel

theorem originalBlockEval19 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock19 x =
      Integer.Sparse.eval keyPolynomialBlock19 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck19, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck20 : originalBlock20 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock20 keyMomentRows) := by decide +kernel

theorem originalBlockEval20 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock20 x =
      Integer.Sparse.eval keyPolynomialBlock20 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck20, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck21 : originalBlock21 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock21 keyMomentRows) := by decide +kernel

theorem originalBlockEval21 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock21 x =
      Integer.Sparse.eval keyPolynomialBlock21 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck21, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck22 : originalBlock22 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock22 keyMomentRows) := by decide +kernel

theorem originalBlockEval22 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock22 x =
      Integer.Sparse.eval keyPolynomialBlock22 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck22, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck23 : originalBlock23 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock23 keyMomentRows) := by decide +kernel

theorem originalBlockEval23 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock23 x =
      Integer.Sparse.eval keyPolynomialBlock23 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck23, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck24 : originalBlock24 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock24 keyMomentRows) := by decide +kernel

theorem originalBlockEval24 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock24 x =
      Integer.Sparse.eval keyPolynomialBlock24 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck24, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck25 : originalBlock25 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock25 keyMomentRows) := by decide +kernel

theorem originalBlockEval25 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock25 x =
      Integer.Sparse.eval keyPolynomialBlock25 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck25, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck26 : originalBlock26 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock26 keyMomentRows) := by decide +kernel

theorem originalBlockEval26 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock26 x =
      Integer.Sparse.eval keyPolynomialBlock26 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck26, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck27 : originalBlock27 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock27 keyMomentRows) := by decide +kernel

theorem originalBlockEval27 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock27 x =
      Integer.Sparse.eval keyPolynomialBlock27 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck27, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck28 : originalBlock28 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock28 keyMomentRows) := by decide +kernel

theorem originalBlockEval28 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock28 x =
      Integer.Sparse.eval keyPolynomialBlock28 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck28, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck29 : originalBlock29 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock29 keyMomentRows) := by decide +kernel

theorem originalBlockEval29 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock29 x =
      Integer.Sparse.eval keyPolynomialBlock29 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck29, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck30 : originalBlock30 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock30 keyMomentRows) := by decide +kernel

theorem originalBlockEval30 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock30 x =
      Integer.Sparse.eval keyPolynomialBlock30 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck30, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck31 : originalBlock31 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock31 keyMomentRows) := by decide +kernel

theorem originalBlockEval31 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock31 x =
      Integer.Sparse.eval keyPolynomialBlock31 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck31, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck32 : originalBlock32 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock32 keyMomentRows) := by decide +kernel

theorem originalBlockEval32 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock32 x =
      Integer.Sparse.eval keyPolynomialBlock32 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck32, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck34 : originalBlock34 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock34 keyMomentRows) := by decide +kernel

theorem originalBlockEval34 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock34 x =
      Integer.Sparse.eval keyPolynomialBlock34 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck34, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck35 : originalBlock35 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock35 keyMomentRows) := by decide +kernel

theorem originalBlockEval35 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock35 x =
      Integer.Sparse.eval keyPolynomialBlock35 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck35, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck0 : originalBlock0 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock0 keyMomentRows) := by decide +kernel

theorem originalBlockEval0 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock0 x =
      Integer.Sparse.eval keyPolynomialBlock0 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck0, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck1 : originalBlock1 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock1 keyMomentRows) := by decide +kernel

theorem originalBlockEval1 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock1 x =
      Integer.Sparse.eval keyPolynomialBlock1 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck1, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck10 : originalBlock10 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock10 keyMomentRows) := by decide +kernel

theorem originalBlockEval10 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock10 x =
      Integer.Sparse.eval keyPolynomialBlock10 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck10, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck11 : originalBlock11 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock11 keyMomentRows) := by decide +kernel

theorem originalBlockEval11 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock11 x =
      Integer.Sparse.eval keyPolynomialBlock11 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck11, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck12 : originalBlock12 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock12 keyMomentRows) := by decide +kernel

theorem originalBlockEval12 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock12 x =
      Integer.Sparse.eval keyPolynomialBlock12 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck12, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck13 : originalBlock13 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock13 keyMomentRows) := by decide +kernel

theorem originalBlockEval13 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock13 x =
      Integer.Sparse.eval keyPolynomialBlock13 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck13, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck14 : originalBlock14 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock14 keyMomentRows) := by decide +kernel

theorem originalBlockEval14 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock14 x =
      Integer.Sparse.eval keyPolynomialBlock14 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck14, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck15 : originalBlock15 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock15 keyMomentRows) := by decide +kernel

theorem originalBlockEval15 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock15 x =
      Integer.Sparse.eval keyPolynomialBlock15 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck15, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck16 : originalBlock16 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock16 keyMomentRows) := by decide +kernel

theorem originalBlockEval16 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock16 x =
      Integer.Sparse.eval keyPolynomialBlock16 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck16, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck17 : originalBlock17 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock17 keyMomentRows) := by decide +kernel

theorem originalBlockEval17 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock17 x =
      Integer.Sparse.eval keyPolynomialBlock17 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck17, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck18 : originalBlock18 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock18 keyMomentRows) := by decide +kernel

theorem originalBlockEval18 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock18 x =
      Integer.Sparse.eval keyPolynomialBlock18 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck18, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck2 : originalBlock2 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock2 keyMomentRows) := by decide +kernel

theorem originalBlockEval2 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock2 x =
      Integer.Sparse.eval keyPolynomialBlock2 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck2, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck3 : originalBlock3 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock3 keyMomentRows) := by decide +kernel

theorem originalBlockEval3 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock3 x =
      Integer.Sparse.eval keyPolynomialBlock3 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck3, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck4 : originalBlock4 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock4 keyMomentRows) := by decide +kernel

theorem originalBlockEval4 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock4 x =
      Integer.Sparse.eval keyPolynomialBlock4 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck4, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck5 : originalBlock5 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock5 keyMomentRows) := by decide +kernel

theorem originalBlockEval5 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock5 x =
      Integer.Sparse.eval keyPolynomialBlock5 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck5, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck6 : originalBlock6 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock6 keyMomentRows) := by decide +kernel

theorem originalBlockEval6 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock6 x =
      Integer.Sparse.eval keyPolynomialBlock6 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck6, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck7 : originalBlock7 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock7 keyMomentRows) := by decide +kernel

theorem originalBlockEval7 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock7 x =
      Integer.Sparse.eval keyPolynomialBlock7 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck7, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck8 : originalBlock8 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock8 keyMomentRows) := by decide +kernel

theorem originalBlockEval8 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock8 x =
      Integer.Sparse.eval keyPolynomialBlock8 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck8, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck9 : originalBlock9 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock9 keyMomentRows) := by decide +kernel

theorem originalBlockEval9 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock9 x =
      Integer.Sparse.eval keyPolynomialBlock9 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck9, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode0Check : originalNode0 = Integer.Sparse.mergeBy originalLess originalBlock0 originalBlock1 := by decide +kernel

theorem originalNodeEval0 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode0 x =
      Integer.Sparse.eval keyPolynomialNode0 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode0Check, Integer.Sparse.eval_mergeBy, originalBlockEval0, originalBlockEval1]
  rw [keyPolynomialNode0, Integer.Sparse.eval_append]

theorem originalNode1Check : originalNode1 = Integer.Sparse.mergeBy originalLess originalBlock3 originalBlock4 := by decide +kernel

theorem originalNodeEval1 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode1 x =
      Integer.Sparse.eval keyPolynomialNode1 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode1Check, Integer.Sparse.eval_mergeBy, originalBlockEval3, originalBlockEval4]
  rw [keyPolynomialNode1, Integer.Sparse.eval_append]

theorem originalNode2Check : originalNode2 = Integer.Sparse.mergeBy originalLess originalBlock2 originalNode1 := by decide +kernel

theorem originalNodeEval2 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode2 x =
      Integer.Sparse.eval keyPolynomialNode2 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode2Check, Integer.Sparse.eval_mergeBy, originalBlockEval2, originalNodeEval1]
  rw [keyPolynomialNode2, Integer.Sparse.eval_append]

theorem originalNode3Check : originalNode3 = Integer.Sparse.mergeBy originalLess originalNode0 originalNode2 := by decide +kernel

theorem originalNodeEval3 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode3 x =
      Integer.Sparse.eval keyPolynomialNode3 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode3Check, Integer.Sparse.eval_mergeBy, originalNodeEval0, originalNodeEval2]
  rw [keyPolynomialNode3, Integer.Sparse.eval_append]

theorem originalNode4Check : originalNode4 = Integer.Sparse.mergeBy originalLess originalBlock6 originalBlock7 := by decide +kernel

theorem originalNodeEval4 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode4 x =
      Integer.Sparse.eval keyPolynomialNode4 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode4Check, Integer.Sparse.eval_mergeBy, originalBlockEval6, originalBlockEval7]
  rw [keyPolynomialNode4, Integer.Sparse.eval_append]

theorem originalNode5Check : originalNode5 = Integer.Sparse.mergeBy originalLess originalBlock5 originalNode4 := by decide +kernel

theorem originalNodeEval5 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode5 x =
      Integer.Sparse.eval keyPolynomialNode5 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode5Check, Integer.Sparse.eval_mergeBy, originalBlockEval5, originalNodeEval4]
  rw [keyPolynomialNode5, Integer.Sparse.eval_append]

theorem originalNode6Check : originalNode6 = Integer.Sparse.mergeBy originalLess originalBlock9 originalBlock10 := by decide +kernel

theorem originalNodeEval6 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode6 x =
      Integer.Sparse.eval keyPolynomialNode6 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode6Check, Integer.Sparse.eval_mergeBy, originalBlockEval9, originalBlockEval10]
  rw [keyPolynomialNode6, Integer.Sparse.eval_append]

theorem originalNode7Check : originalNode7 = Integer.Sparse.mergeBy originalLess originalBlock8 originalNode6 := by decide +kernel

theorem originalNodeEval7 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode7 x =
      Integer.Sparse.eval keyPolynomialNode7 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode7Check, Integer.Sparse.eval_mergeBy, originalBlockEval8, originalNodeEval6]
  rw [keyPolynomialNode7, Integer.Sparse.eval_append]

theorem originalNode8Check : originalNode8 = Integer.Sparse.mergeBy originalLess originalNode5 originalNode7 := by decide +kernel

theorem originalNodeEval8 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode8 x =
      Integer.Sparse.eval keyPolynomialNode8 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode8Check, Integer.Sparse.eval_mergeBy, originalNodeEval5, originalNodeEval7]
  rw [keyPolynomialNode8, Integer.Sparse.eval_append]

theorem originalNode9Check : originalNode9 = Integer.Sparse.mergeBy originalLess originalNode3 originalNode8 := by decide +kernel

theorem originalNodeEval9 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode9 x =
      Integer.Sparse.eval keyPolynomialNode9 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode9Check, Integer.Sparse.eval_mergeBy, originalNodeEval3, originalNodeEval8]
  rw [keyPolynomialNode9, Integer.Sparse.eval_append]

theorem originalNode10Check : originalNode10 = Integer.Sparse.mergeBy originalLess originalBlock11 originalBlock12 := by decide +kernel

theorem originalNodeEval10 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode10 x =
      Integer.Sparse.eval keyPolynomialNode10 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode10Check, Integer.Sparse.eval_mergeBy, originalBlockEval11, originalBlockEval12]
  rw [keyPolynomialNode10, Integer.Sparse.eval_append]

theorem originalNode11Check : originalNode11 = Integer.Sparse.mergeBy originalLess originalBlock14 originalBlock15 := by decide +kernel

theorem originalNodeEval11 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode11 x =
      Integer.Sparse.eval keyPolynomialNode11 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode11Check, Integer.Sparse.eval_mergeBy, originalBlockEval14, originalBlockEval15]
  rw [keyPolynomialNode11, Integer.Sparse.eval_append]

theorem originalNode12Check : originalNode12 = Integer.Sparse.mergeBy originalLess originalBlock13 originalNode11 := by decide +kernel

theorem originalNodeEval12 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode12 x =
      Integer.Sparse.eval keyPolynomialNode12 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode12Check, Integer.Sparse.eval_mergeBy, originalBlockEval13, originalNodeEval11]
  rw [keyPolynomialNode12, Integer.Sparse.eval_append]

theorem originalNode13Check : originalNode13 = Integer.Sparse.mergeBy originalLess originalNode10 originalNode12 := by decide +kernel

theorem originalNodeEval13 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode13 x =
      Integer.Sparse.eval keyPolynomialNode13 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode13Check, Integer.Sparse.eval_mergeBy, originalNodeEval10, originalNodeEval12]
  rw [keyPolynomialNode13, Integer.Sparse.eval_append]

theorem originalNode14Check : originalNode14 = Integer.Sparse.mergeBy originalLess originalBlock17 originalBlock18 := by decide +kernel

theorem originalNodeEval14 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode14 x =
      Integer.Sparse.eval keyPolynomialNode14 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode14Check, Integer.Sparse.eval_mergeBy, originalBlockEval17, originalBlockEval18]
  rw [keyPolynomialNode14, Integer.Sparse.eval_append]

theorem originalNode15Check : originalNode15 = Integer.Sparse.mergeBy originalLess originalBlock16 originalNode14 := by decide +kernel

theorem originalNodeEval15 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode15 x =
      Integer.Sparse.eval keyPolynomialNode15 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode15Check, Integer.Sparse.eval_mergeBy, originalBlockEval16, originalNodeEval14]
  rw [keyPolynomialNode15, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode16Check : originalNode16 = Integer.Sparse.mergeBy originalLess originalBlock20 originalBlock21 := by decide +kernel

theorem originalNodeEval16 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode16 x =
      Integer.Sparse.eval keyPolynomialNode16 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode16Check, Integer.Sparse.eval_mergeBy, originalBlockEval20, originalBlockEval21]
  rw [keyPolynomialNode16, Integer.Sparse.eval_append]

theorem originalNode17Check : originalNode17 = Integer.Sparse.mergeBy originalLess originalBlock19 originalNode16 := by decide +kernel

theorem originalNodeEval17 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode17 x =
      Integer.Sparse.eval keyPolynomialNode17 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode17Check, Integer.Sparse.eval_mergeBy, originalBlockEval19, originalNodeEval16]
  rw [keyPolynomialNode17, Integer.Sparse.eval_append]

theorem originalNode18Check : originalNode18 = Integer.Sparse.mergeBy originalLess originalNode15 originalNode17 := by decide +kernel

theorem originalNodeEval18 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode18 x =
      Integer.Sparse.eval keyPolynomialNode18 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode18Check, Integer.Sparse.eval_mergeBy, originalNodeEval15, originalNodeEval17]
  rw [keyPolynomialNode18, Integer.Sparse.eval_append]

theorem originalNode19Check : originalNode19 = Integer.Sparse.mergeBy originalLess originalNode13 originalNode18 := by decide +kernel

theorem originalNodeEval19 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode19 x =
      Integer.Sparse.eval keyPolynomialNode19 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode19Check, Integer.Sparse.eval_mergeBy, originalNodeEval13, originalNodeEval18]
  rw [keyPolynomialNode19, Integer.Sparse.eval_append]

theorem originalNode20Check : originalNode20 = Integer.Sparse.mergeBy originalLess originalNode9 originalNode19 := by decide +kernel

theorem originalNodeEval20 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode20 x =
      Integer.Sparse.eval keyPolynomialNode20 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode20Check, Integer.Sparse.eval_mergeBy, originalNodeEval9, originalNodeEval19]
  rw [keyPolynomialNode20, Integer.Sparse.eval_append]

theorem originalNode21Check : originalNode21 = Integer.Sparse.mergeBy originalLess originalBlock22 originalBlock23 := by decide +kernel

theorem originalNodeEval21 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode21 x =
      Integer.Sparse.eval keyPolynomialNode21 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode21Check, Integer.Sparse.eval_mergeBy, originalBlockEval22, originalBlockEval23]
  rw [keyPolynomialNode21, Integer.Sparse.eval_append]

theorem originalNode22Check : originalNode22 = Integer.Sparse.mergeBy originalLess originalBlock25 originalBlock26 := by decide +kernel

theorem originalNodeEval22 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode22 x =
      Integer.Sparse.eval keyPolynomialNode22 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode22Check, Integer.Sparse.eval_mergeBy, originalBlockEval25, originalBlockEval26]
  rw [keyPolynomialNode22, Integer.Sparse.eval_append]

theorem originalNode23Check : originalNode23 = Integer.Sparse.mergeBy originalLess originalBlock24 originalNode22 := by decide +kernel

theorem originalNodeEval23 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode23 x =
      Integer.Sparse.eval keyPolynomialNode23 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode23Check, Integer.Sparse.eval_mergeBy, originalBlockEval24, originalNodeEval22]
  rw [keyPolynomialNode23, Integer.Sparse.eval_append]

theorem originalNode24Check : originalNode24 = Integer.Sparse.mergeBy originalLess originalNode21 originalNode23 := by decide +kernel

theorem originalNodeEval24 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode24 x =
      Integer.Sparse.eval keyPolynomialNode24 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode24Check, Integer.Sparse.eval_mergeBy, originalNodeEval21, originalNodeEval23]
  rw [keyPolynomialNode24, Integer.Sparse.eval_append]

theorem originalNode25Check : originalNode25 = Integer.Sparse.mergeBy originalLess originalBlock28 originalBlock29 := by decide +kernel

theorem originalNodeEval25 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode25 x =
      Integer.Sparse.eval keyPolynomialNode25 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode25Check, Integer.Sparse.eval_mergeBy, originalBlockEval28, originalBlockEval29]
  rw [keyPolynomialNode25, Integer.Sparse.eval_append]

theorem originalNode26Check : originalNode26 = Integer.Sparse.mergeBy originalLess originalBlock27 originalNode25 := by decide +kernel

theorem originalNodeEval26 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode26 x =
      Integer.Sparse.eval keyPolynomialNode26 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode26Check, Integer.Sparse.eval_mergeBy, originalBlockEval27, originalNodeEval25]
  rw [keyPolynomialNode26, Integer.Sparse.eval_append]

theorem originalNode27Check : originalNode27 = Integer.Sparse.mergeBy originalLess originalBlock31 originalBlock32 := by decide +kernel

theorem originalNodeEval27 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode27 x =
      Integer.Sparse.eval keyPolynomialNode27 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode27Check, Integer.Sparse.eval_mergeBy, originalBlockEval31, originalBlockEval32]
  rw [keyPolynomialNode27, Integer.Sparse.eval_append]

theorem originalNode28Check : originalNode28 = Integer.Sparse.mergeBy originalLess originalBlock30 originalNode27 := by decide +kernel

theorem originalNodeEval28 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode28 x =
      Integer.Sparse.eval keyPolynomialNode28 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode28Check, Integer.Sparse.eval_mergeBy, originalBlockEval30, originalNodeEval27]
  rw [keyPolynomialNode28, Integer.Sparse.eval_append]

theorem originalNode29Check : originalNode29 = Integer.Sparse.mergeBy originalLess originalNode26 originalNode28 := by decide +kernel

theorem originalNodeEval29 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode29 x =
      Integer.Sparse.eval keyPolynomialNode29 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode29Check, Integer.Sparse.eval_mergeBy, originalNodeEval26, originalNodeEval28]
  rw [keyPolynomialNode29, Integer.Sparse.eval_append]

theorem originalNode30Check : originalNode30 = Integer.Sparse.mergeBy originalLess originalNode24 originalNode29 := by decide +kernel

theorem originalNodeEval30 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode30 x =
      Integer.Sparse.eval keyPolynomialNode30 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode30Check, Integer.Sparse.eval_mergeBy, originalNodeEval24, originalNodeEval29]
  rw [keyPolynomialNode30, Integer.Sparse.eval_append]

theorem originalNode31Check : originalNode31 = Integer.Sparse.mergeBy originalLess originalBlock34 originalBlock35 := by decide +kernel

theorem originalNodeEval31 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode31 x =
      Integer.Sparse.eval keyPolynomialNode31 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode31Check, Integer.Sparse.eval_mergeBy, originalBlockEval34, originalBlockEval35]
  rw [keyPolynomialNode31, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode32Check : originalNode32 = Integer.Sparse.mergeBy originalLess originalBlock33 originalNode31 := by decide +kernel

theorem originalNodeEval32 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode32 x =
      Integer.Sparse.eval keyPolynomialNode32 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode32Check, Integer.Sparse.eval_mergeBy, originalBlockEval33, originalNodeEval31]
  rw [keyPolynomialNode32, Integer.Sparse.eval_append]

theorem originalNode33Check : originalNode33 = Integer.Sparse.mergeBy originalLess originalBlock37 originalBlock38 := by decide +kernel

theorem originalNodeEval33 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode33 x =
      Integer.Sparse.eval keyPolynomialNode33 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode33Check, Integer.Sparse.eval_mergeBy, originalBlockEval37, originalBlockEval38]
  rw [keyPolynomialNode33, Integer.Sparse.eval_append]

theorem originalNode34Check : originalNode34 = Integer.Sparse.mergeBy originalLess originalBlock36 originalNode33 := by decide +kernel

theorem originalNodeEval34 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode34 x =
      Integer.Sparse.eval keyPolynomialNode34 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode34Check, Integer.Sparse.eval_mergeBy, originalBlockEval36, originalNodeEval33]
  rw [keyPolynomialNode34, Integer.Sparse.eval_append]

theorem originalNode35Check : originalNode35 = Integer.Sparse.mergeBy originalLess originalNode32 originalNode34 := by decide +kernel

theorem originalNodeEval35 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode35 x =
      Integer.Sparse.eval keyPolynomialNode35 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode35Check, Integer.Sparse.eval_mergeBy, originalNodeEval32, originalNodeEval34]
  rw [keyPolynomialNode35, Integer.Sparse.eval_append]

theorem originalNode36Check : originalNode36 = Integer.Sparse.mergeBy originalLess originalBlock40 originalBlock41 := by decide +kernel

theorem originalNodeEval36 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode36 x =
      Integer.Sparse.eval keyPolynomialNode36 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode36Check, Integer.Sparse.eval_mergeBy, originalBlockEval40, originalBlockEval41]
  rw [keyPolynomialNode36, Integer.Sparse.eval_append]

theorem originalNode37Check : originalNode37 = Integer.Sparse.mergeBy originalLess originalBlock39 originalNode36 := by decide +kernel

theorem originalNodeEval37 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode37 x =
      Integer.Sparse.eval keyPolynomialNode37 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode37Check, Integer.Sparse.eval_mergeBy, originalBlockEval39, originalNodeEval36]
  rw [keyPolynomialNode37, Integer.Sparse.eval_append]

theorem originalNode38Check : originalNode38 = Integer.Sparse.mergeBy originalLess originalBlock43 originalBlock44 := by decide +kernel

theorem originalNodeEval38 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode38 x =
      Integer.Sparse.eval keyPolynomialNode38 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode38Check, Integer.Sparse.eval_mergeBy, originalBlockEval43, originalBlockEval44]
  rw [keyPolynomialNode38, Integer.Sparse.eval_append]

theorem originalNode39Check : originalNode39 = Integer.Sparse.mergeBy originalLess originalBlock42 originalNode38 := by decide +kernel

theorem originalNodeEval39 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode39 x =
      Integer.Sparse.eval keyPolynomialNode39 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode39Check, Integer.Sparse.eval_mergeBy, originalBlockEval42, originalNodeEval38]
  rw [keyPolynomialNode39, Integer.Sparse.eval_append]

theorem originalNode40Check : originalNode40 = Integer.Sparse.mergeBy originalLess originalNode37 originalNode39 := by decide +kernel

theorem originalNodeEval40 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode40 x =
      Integer.Sparse.eval keyPolynomialNode40 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode40Check, Integer.Sparse.eval_mergeBy, originalNodeEval37, originalNodeEval39]
  rw [keyPolynomialNode40, Integer.Sparse.eval_append]

theorem originalNode41Check : originalNode41 = Integer.Sparse.mergeBy originalLess originalNode35 originalNode40 := by decide +kernel

theorem originalNodeEval41 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode41 x =
      Integer.Sparse.eval keyPolynomialNode41 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode41Check, Integer.Sparse.eval_mergeBy, originalNodeEval35, originalNodeEval40]
  rw [keyPolynomialNode41, Integer.Sparse.eval_append]

theorem originalNode42Check : originalNode42 = Integer.Sparse.mergeBy originalLess originalNode30 originalNode41 := by decide +kernel

theorem originalNodeEval42 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode42 x =
      Integer.Sparse.eval keyPolynomialNode42 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode42Check, Integer.Sparse.eval_mergeBy, originalNodeEval30, originalNodeEval41]
  rw [keyPolynomialNode42, Integer.Sparse.eval_append]

theorem originalNode43Check : originalNode43 = Integer.Sparse.mergeBy originalLess originalNode20 originalNode42 := by decide +kernel

theorem originalNodeEval43 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode43 x =
      Integer.Sparse.eval keyPolynomialNode43 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode43Check, Integer.Sparse.eval_mergeBy, originalNodeEval20, originalNodeEval42]
  rw [keyPolynomialNode43, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode89Check : originalNode89 = Integer.Sparse.mergeBy originalLess originalNode43 originalNode88 := by decide +kernel

theorem originalNodeEval89 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode89 x =
      Integer.Sparse.eval keyPolynomialNode89 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode89Check, Integer.Sparse.eval_mergeBy, originalNodeEval43, originalNodeEval88_e]
  rw [keyPolynomialNode89, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyPolynomialCheck : keyPolynomialNode89 = GramAssembly.polynomial := by decide +kernel

theorem originalPolynomialEval (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalPolynomial x =
      Integer.Sparse.eval GramAssembly.polynomial (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNodeEval89, keyPolynomialCheck]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

/-- The collected mixed polynomial is the genuine nonnegative Gram expression. -/
theorem originalGramIdentity (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval originalPolynomial (originalVector B) =
      GramNonnegative.sourceGram B := by
  rw [originalPolynomialEval]
  have h : (fun i => Integer.Sparse.eval (keyMomentRows i) (originalVector B)) =
      (fun i => 5 * GramNormalization.eval B (GramAssembly.key i)) :=
    funext fun i => (allKeyMoments_e B hB i).symm
  rw [h, Integer.Sparse.eval_mul_left]
  exact GramAssembly.interpretation_e B hB

/-- The exact integer target has the manuscript's Gram interpretation, including
both its factor of five and its common integer denominator. -/
theorem rawGramIdentity (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination =
      (MixedData.denominator : ℝ) * GramNonnegative.sourceGram B := by
  rw [originalReductionEval_e B hB hF, originalGramIdentity B hB]
  rfl

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Results_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier vanishing and bounds on mutually unbiased bases, using actual mixed moments and the six-to-seven completion theorem. -/

noncomputable section

namespace MUB6

/-- Endpoint 2: seven mutually unbiased orthonormal bases in `ℂ⁶` cannot exist. -/
theorem no_seven_mutually_unbiased_bases : ¬Attainable 7 := by
  rintro ⟨B, hB⟩
  have hF := complete_family_fourier_zero B hB
  exact Certificate.MixedData.false_of_gram_interpretation_e B hB
    (Certificate.MixedSemantics.numericVector B)
    (Certificate.MixedSemantics.numericVector_abs_le_one B hB)
    (Certificate.MixedSemantics.numericVector_zero B)
    (Certificate.MixedSourceBridge.allRowsSound_e B hB hF)
    (Certificate.MixedTargetSemantics.rawGramIdentity B hB hF)

/-- Weiner completion in dimension six, preserving all six original bases. -/
theorem six_extend_to_seven : SixExtendToSeven :=
  Weiner.six_extend_to_seven

/-- Every finite family of mutually unbiased bases in `ℂ⁶` has size at most five. -/
theorem family_size_le_five_e_oai (n : ℕ) (hn : Attainable n) : n ≤ 5 :=
  family_size_le_five_of_no_six
    (no_six_of_completion six_extend_to_seven no_seven_mutually_unbiased_bases) n hn

end MUB6

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.family_size_le_five_e_oai := @OAI.MUB6.family_size_le_five_e_oai
