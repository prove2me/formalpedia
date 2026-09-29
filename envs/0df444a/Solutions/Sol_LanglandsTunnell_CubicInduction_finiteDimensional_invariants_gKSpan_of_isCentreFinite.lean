-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.finiteDimensional_invariants_gKSpan_of_isCentreFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a416d1d4-aa1c-5aa6-bbb3-c60dc932b458

import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Lie.UniversalEnveloping
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite

set_option autoImplicit false

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieRingModule.ofAssociativeModule

section CarryC8b

namespace CasimirCentral

open Matrix Finset

variable {A : Type*} [Ring A]

private def admRel (e : Fin 3 → Fin 3 → A) : Prop :=
  ∀ i j k l : Fin 3, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)

private def admgen (e : Fin 3 → Fin 3 → A) : Matrix (Fin 3) (Fin 3) A := Matrix.of fun i j => e i j

private def cas (e : Fin 3 → Fin 3 → A) (n : ℕ) : A := (admgen e ^ n).trace

private theorem cas_one (e : Fin 3 → Fin 3 → A) : cas e 1 = ∑ i, e i i := by
  simp [cas, admgen, Matrix.trace]

private theorem cas_two (e : Fin 3 → Fin 3 → A) : cas e 2 = ∑ i, ∑ j, e i j * e j i := by
  simp [cas, admgen, Matrix.trace, pow_two, Matrix.mul_apply]

private theorem cas_three (e : Fin 3 → Fin 3 → A) : cas e 3 = ∑ i, ∑ j, ∑ k, e i j * (e j k * e k i) := by
  simp only [cas, admgen, Matrix.trace, Matrix.diag_apply, pow_succ, pow_zero, one_mul, Matrix.mul_apply,
      Matrix.of_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc]

private def _root_.CasimirCentral.admder (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x : A) : A := x * e a b - e a b * x

p2m_export "CasimirCentral" "admder"
private theorem admder_mul (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x y : A) :
    admder e a b (x * y) = admder e a b x * y + x * admder e a b y := by
  simp only [admder]
  noncomm_ring

private theorem der_add (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x y : A) :
    admder e a b (x + y) = admder e a b x + admder e a b y := by
  simp only [admder]
  noncomm_ring

private theorem der_sum (e : Fin 3 → Fin 3 → A) (a b : Fin 3) {ι : Type*} (s : Finset ι) (f : ι → A) :
    admder e a b (∑ i ∈ s, f i) = ∑ i ∈ s, admder e a b (f i) := by
  simp only [admder, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

private def derM (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  Matrix.of fun i j => admder e a b (X i j)

private theorem derM_mul (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X admY : Matrix (Fin 3) (Fin 3) A) :
    derM e a b (X * admY) = derM e a b X * admY + X * derM e a b admY := by
  ext i j
  simp only [derM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, der_sum, admder_mul, Finset.sum_add_distrib]

private theorem trace_derM (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) :
    (derM e a b X).trace = admder e a b X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, derM, Matrix.of_apply, der_sum]

private def admunit (a b : Fin 3) : Matrix (Fin 3) (Fin 3) A := Matrix.single b a (1 : A)

private theorem derM_gen {e : Fin 3 → Fin 3 → A} (he : admRel e) (a b : Fin 3) :
    derM e a b (admgen e) = admgen e * admunit a b - admunit a b * admgen e := by
  ext i j
  have h := he i j a b
  simp only [derM, Matrix.of_apply, admder, admgen, Matrix.sub_apply, admunit]
  rw [h]
  congr 1
  · by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
  · by_cases hi : i = b
    · subst hi
      simp
    · simp [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]
      intro h'
      exact absurd h'.symm hi

private theorem derM_gen_pow {e : Fin 3 → Fin 3 → A} (he : admRel e) (a b : Fin 3) (n : ℕ) :
    derM e a b (admgen e ^ n) = admgen e ^ n * admunit a b - admunit a b * admgen e ^ n := by
  induction n with
  | zero =>
    ext i j
    simp only [pow_zero, mul_one, one_mul, sub_self, derM, admder, Matrix.of_apply, Matrix.zero_apply,
        Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, derM_mul, ih, derM_gen he]
    noncomm_ring

private theorem trace_mul_unit (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) :
    (X * admunit a b).trace = (admunit a b * X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, admunit, Matrix.mul_apply, Matrix.single, Matrix.of_apply, mul_ite,
      ite_mul,
    mul_one, one_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]

private theorem cas_mul_gen {e : Fin 3 → Fin 3 → A} (he : admRel e) (n : ℕ) (a b : Fin 3) :
    cas e n * e a b = e a b * cas e n := by
  have h : admder e a b (cas e n) = 0 := by
    rw [cas, ← trace_derM, derM_gen_pow he, Matrix.trace_sub, trace_mul_unit, sub_self]
  simpa [admder, sub_eq_zero] using h

private theorem commute_gen_pow_entry (e : Fin 3 → Fin 3 → A) {x : A} (hx : ∀ a b, x * e a b = e a b * x) (n : ℕ)
    (i j : Fin 3) : x * (admgen e ^ n) i j = (admgen e ^ n) i j * x := by
  induction n generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [admgen, Matrix.of_apply] at ih ⊢
    rw [← mul_assoc, ih i k, mul_assoc, hx k j, ← mul_assoc]

private theorem commute_cas_of_commute_gen (e : Fin 3 → Fin 3 → A) {x : A} (hx : ∀ a b, x * e a b = e a b * x)
    (n : ℕ) : x * cas e n = cas e n * x := by
  simp only [cas, Matrix.trace, Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => commute_gen_pow_entry e hx n i i

private theorem cas_mul_cas {e : Fin 3 → Fin 3 → A} (he : admRel e) (m n : ℕ) : cas e m * cas e n = cas e n * cas e m
    :=
  commute_cas_of_commute_gen e (fun a b => cas_mul_gen he m a b) n

private theorem cas_mul_word {e : Fin 3 → Fin 3 → A} (he : admRel e) (n : ℕ) (w : List (Fin 3 × Fin 3)) :
    cas e n * (w.map fun ij => e ij.1 ij.2).prod = (w.map fun ij => e ij.1 ij.2).prod * cas e n := by
  induction w with
  | nil => simp
  | cons ij w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, cas_mul_gen he n, mul_assoc, ih, ← mul_assoc]

private example : admRel fun i j : Fin 3 => (Matrix.single i j (1 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro i j k l
  have h1 : (Matrix.single i j (1 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.single k l 1 =
      if j = k then Matrix.single i l 1 else 0 := by
    by_cases h : j = k
    · subst h; simp
    · simp [h, Matrix.single_mul_single_of_ne]
  have h2 : (Matrix.single k l (1 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.single i j 1 =
      if l = i then Matrix.single k j 1 else 0 := by
    by_cases h : l = i
    · subst h; simp
    · simp [h, Matrix.single_mul_single_of_ne]
  rw [h1, h2]

private example (e : Fin 3 → Fin 3 → A) :
    cas e 2 = ∑ i : Fin 3, (e i 0 * e 0 i + e i 1 * e 1 i + e i 2 * e 2 i) := by
  rw [cas_two]
  simp [Fin.sum_univ_three, add_assoc]

end CasimirCentral

open MvPolynomial Matrix

namespace SymRestriction

private abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}

private abbrev admP : Type := MvPolynomial admIdx ℂ

private def admY : Matrix (Fin 3) (Fin 3) admP :=
  Matrix.of fun a b => if h : a ≤ b then X ⟨(a, b), h⟩ else X ⟨(b, a), le_of_not_ge h⟩

private theorem Y_symm (a b : Fin 3) : admY a b = admY b a := by
  unfold admY
  simp only [Matrix.of_apply]
  by_cases hab : a ≤ b <;> by_cases hba : b ≤ a
  · have : a = b := le_antisymm hab hba
    subst this
    rfl
  · simp [hab, hba]
  · simp [hab, hba]
  · exact absurd (le_of_not_ge hab) hba

private theorem Y_transpose : admY.transpose = admY :=
  Matrix.ext fun a b => Y_symm b a

private def admK (i j : Fin 3) : Matrix (Fin 3) (Fin 3) admP := Matrix.single i j 1 - Matrix.single j i 1

private theorem K_transpose (i j : Fin 3) : (admK i j).transpose = -admK i j := by
  unfold admK
  rw [transpose_sub, transpose_single, transpose_single, neg_sub]

private theorem comm_symm (i j : Fin 3) (a b : Fin 3) :
    (admK i j * admY - admY * admK i j) a b = (admK i j * admY - admY * admK i j) b a := by
  have h : (admK i j * admY - admY * admK i j).transpose = admK i j * admY - admY * admK i j := by
    rw [transpose_sub, transpose_mul, transpose_mul, Y_transpose, K_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, sub_neg_eq_add, neg_add_eq_sub]
  conv_rhs => rw [← h]
  rfl

private def admD (i j : Fin 3) : Derivation ℂ admP admP :=
  mkDerivation ℂ fun v : admIdx => (admK i j * admY - admY * admK i j) v.1.1 v.1.2

private theorem D_Y (i j a b : Fin 3) : admD i j (admY a b) = (admK i j * admY - admY * admK i j) a b := by
  unfold admD
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X]
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X, comm_symm]

private def DM (i j : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) : Matrix (Fin 3) (Fin 3) admP := M.map (admD i j)

private theorem DM_mul (i j : Fin 3) (M N : Matrix (Fin 3) (Fin 3) admP) :
    DM i j (M * N) = DM i j M * N + M * DM i j N := by
  refine Matrix.ext fun a b => ?_
  simp only [DM, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem DM_one (i j : Fin 3) : DM i j (1 : Matrix (Fin 3) (Fin 3) admP) = 0 := by
  refine Matrix.ext fun a b => ?_
  by_cases hab : a = b
  · subst hab
    simp [DM]
  · simp [DM, Matrix.one_apply_ne hab]

private theorem DM_Y (i j : Fin 3) : DM i j admY = admK i j * admY - admY * admK i j :=
  Matrix.ext fun a b => D_Y i j a b

private theorem DM_Y_pow (i j : Fin 3) (n : ℕ) : DM i j (admY ^ n) = admK i j * admY ^ n - admY ^ n * admK i j := by
  induction n with
  | zero => rw [pow_zero, DM_one, Matrix.mul_one, Matrix.one_mul, sub_self]
  | succ n ih =>
    rw [pow_succ, DM_mul, ih, DM_Y]
    noncomm_ring

private theorem D_trace (i j : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) : admD i j M.trace = (DM i j M).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, DM, Matrix.map_apply]

private theorem D_trace_Y_pow (i j : Fin 3) (n : ℕ) : admD i j ((admY ^ n).trace) = 0 := by
  rw [D_trace, DM_Y_pow, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

private theorem single_mul_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (Matrix.single i j (1 : admP) * M) a b = if a = i then M j b else 0 := by
  by_cases h : a = i
  · subst h
    simp
  · simp [h]

private theorem mul_single_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (M * Matrix.single i j (1 : admP)) a b = if b = j then M a i else 0 := by
  by_cases h : b = j
  · subst h
    simp
  · simp [h]

private theorem D_Y_eq (i j a b : Fin 3) :
    admD i j (admY a b) =
      ((if a = i then admY j b else 0) - (if a = j then admY i b else 0)) -
        ((if b = j then admY a i else 0) - (if b = i then admY a j else 0)) := by
  rw [D_Y]
  simp only [admK, Matrix.sub_apply, Matrix.sub_mul, Matrix.mul_sub, single_mul_entry, mul_single_entry]

section Distinct

variable (i j k : Fin 3)

private theorem D_Y_ii (hij : i ≠ j) : admD i j (admY i i) = 2 * admY i j := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false]
  rw [Y_symm j i]
  ring

private theorem D_Y_jj (hij : i ≠ j) : admD i j (admY j j) = -(2 * admY i j) := by
  rw [D_Y_eq]
  simp only [if_true, if_false, Ne.symm hij]
  rw [Y_symm j i]
  ring

private theorem D_Y_ij (hij : i ≠ j) : admD i j (admY i j) = admY j j - admY i i := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false, Ne.symm hij]
  ring

private theorem D_Y_ik (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY i k) = admY j k := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false, Ne.symm hik, Ne.symm hjk]
  ring

private theorem D_Y_jk (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY j k) = -admY i k := by
  rw [D_Y_eq]
  simp only [if_true, if_false, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  ring

private theorem D_Y_kk (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY k k) = 0 := by
  rw [D_Y_eq]
  simp [Ne.symm hik, Ne.symm hjk]

private theorem D_C_mul (c : ℂ) (x : admP) : admD i j (C c * x) = C c * admD i j x := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

private theorem C2I_mul_C2I : (C (2 * Complex.I) : admP) * C (2 * Complex.I) = -4 := by
  rw [← C_mul, show (2 * Complex.I) * (2 * Complex.I) = (-4 : ℂ) by ring_nf; simp [Complex.I_sq]]
  simp only [map_neg, map_ofNat]

private theorem CI_mul_CI : (C Complex.I : admP) * C Complex.I = -1 := by
  rw [← C_mul, Complex.I_mul_I]
  simp

private def eig : Fin 6 → admP :=
  ![admY i i + admY j j, (admY i i - admY j j) + C (2 * Complex.I) * admY i j, (admY i i - admY j j) - C (2 *
      Complex.I) * admY i j, admY k k,
    admY i k + C Complex.I * admY j k, admY i k - C Complex.I * admY j k]

private def wtv : Fin 6 → ℂ := ![0, -(2 * Complex.I), 2 * Complex.I, 0, -Complex.I, Complex.I]

private theorem D_eig_u (hij : i ≠ j) : admD i j (admY i i + admY j j) = (0 : ℂ) • (admY i i + admY j j) := by
  rw [map_add, D_Y_ii i j hij, D_Y_jj i j hij, zero_smul]
  ring

private theorem D_eig_z (hij : i ≠ j) :
    admD i j ((admY i i - admY j j) + C (2 * Complex.I) * admY i j) =
      (-(2 * Complex.I)) • ((admY i i - admY j j) + C (2 * Complex.I) * admY i j) := by
  rw [map_add, map_sub, D_C_mul, D_Y_ii i j hij, D_Y_jj i j hij, D_Y_ij i j hij, smul_eq_C_mul, map_neg]
  linear_combination (admY i j) * C2I_mul_C2I

private theorem D_eig_z' (hij : i ≠ j) :
    admD i j ((admY i i - admY j j) - C (2 * Complex.I) * admY i j) =
      (2 * Complex.I) • ((admY i i - admY j j) - C (2 * Complex.I) * admY i j) := by
  rw [map_sub, map_sub, D_C_mul, D_Y_ii i j hij, D_Y_jj i j hij, D_Y_ij i j hij, smul_eq_C_mul]
  linear_combination (admY i j) * C2I_mul_C2I

private theorem D_eig_t (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY k k) = (0 : ℂ) • admY k k := by
  rw [D_Y_kk i j k hik hjk, zero_smul]

private theorem D_eig_v (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    admD i j (admY i k + C Complex.I * admY j k) = (-Complex.I) • (admY i k + C Complex.I * admY j k) := by
  rw [map_add, D_C_mul, D_Y_ik i j k hij hik hjk, D_Y_jk i j k hij hik hjk, smul_eq_C_mul, map_neg]
  linear_combination (admY j k) * CI_mul_CI

private theorem D_eig_v' (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    admD i j (admY i k - C Complex.I * admY j k) = Complex.I • (admY i k - C Complex.I * admY j k) := by
  rw [map_sub, D_C_mul, D_Y_ik i j k hij hik hjk, D_Y_jk i j k hij hik hjk, smul_eq_C_mul]
  linear_combination (admY j k) * CI_mul_CI

private theorem D_eig (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : Fin 6) :
    admD i j (eig i j k n) = wtv n • eig i j k n := by
  fin_cases n
  · exact D_eig_u i j hij
  · exact D_eig_z i j hij
  · exact D_eig_z' i j hij
  · exact D_eig_t i j k hik hjk
  · exact D_eig_v i j k hij hik hjk
  · exact D_eig_v' i j k hij hik hjk

private abbrev admQ : Type := MvPolynomial (Fin 6) ℂ

private def admE : Derivation ℂ admQ admQ := mkDerivation ℂ fun n : Fin 6 => wtv n • X n

private theorem E_X (n : Fin 6) : admE (X n) = wtv n • X n := mkDerivation_X _ _ _

private theorem E_C (a : ℂ) : admE (C a) = 0 := by
  rw [← algebraMap_eq]
  exact Derivation.map_algebraMap _ _

private theorem D_C' (i j : Fin 3) (a : ℂ) : admD i j (C a) = 0 := by
  rw [← algebraMap_eq]
  exact Derivation.map_algebraMap _ _

private def Φ : admQ →ₐ[ℂ] admP := aeval (eig i j k)

private theorem Φ_X (n : Fin 6) : Φ i j k (X n) = eig i j k n := aeval_X _ _

private theorem Φ_C (a : ℂ) : Φ i j k (C a) = C a := by
  rw [Φ, aeval_C, algebraMap_eq]

private theorem D_Φ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : admQ) : admD i j (Φ i j k f) = Φ i j k (admE f) :=
    by
  induction f using MvPolynomial.induction_on with
  | C a => rw [Φ_C, D_C', E_C, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f n hf =>
    simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul, Φ_X, D_eig i j k hij hik hjk, hf, E_X, map_smul]

private theorem Y_mem_range (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : Fin 3) : admY a b ∈ (Φ i j k).range := by
  have r1 : (C (1 / 2 : ℂ) : admP) * 2 = 1 := by
    rw [show (2 : admP) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  have r3 : (C (-Complex.I / 4) : admP) * C (2 * Complex.I) * 2 = 1 := by
    rw [show (2 : admP) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul]
    rw [show -Complex.I / 4 * (2 * Complex.I) * 2 = -(Complex.I * Complex.I) by ring, Complex.I_mul_I]
    norm_num
  have r4 : (C (-Complex.I / 2) : admP) * C Complex.I * 2 = 1 := by
    rw [show (2 : admP) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul]
    rw [show -Complex.I / 2 * Complex.I * 2 = -(Complex.I * Complex.I) by ring, Complex.I_mul_I]
    norm_num
  have tri : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k := by
    intro a
    revert i j k a
    decide

  have hii : admY i i ∈ (Φ i j k).range := by
    refine (AlgHom.mem_range (Φ i j k)).2 ⟨C (1 / 2) * (X 0 + C (1 / 2) * (X 1 + X 2)), ?_⟩
    simp only [map_mul (Φ i j k), map_add (Φ i j k), Φ_C, Φ_X, eig, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (C (1 / 2 : ℂ) * (admY i i - admY j j) + admY i i) * r1
  have hjj : admY j j ∈ (Φ i j k).range := by
    refine (AlgHom.mem_range (Φ i j k)).2 ⟨C (1 / 2) * (X 0 - C (1 / 2) * (X 1 + X 2)), ?_⟩
    simp only [map_mul (Φ i j k), map_add (Φ i j k), map_sub (Φ i j k), Φ_C, Φ_X, eig, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-(C (1 / 2 : ℂ) * (admY i i - admY j j)) + admY j j) * r1
  have hkk : admY k k ∈ (Φ i j k).range := (AlgHom.mem_range (Φ i j k)).2 ⟨X 3, by rw [Φ_X]; rfl⟩
  have hij' : admY i j ∈ (Φ i j k).range := by
    refine (AlgHom.mem_range (Φ i j k)).2 ⟨C (-Complex.I / 4) * (X 1 - X 2), ?_⟩
    simp only [map_mul (Φ i j k), map_sub (Φ i j k), Φ_C, Φ_X, eig, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (admY i j) * r3
  have hik' : admY i k ∈ (Φ i j k).range := by
    refine (AlgHom.mem_range (Φ i j k)).2 ⟨C (1 / 2) * (X 4 + X 5), ?_⟩
    simp only [map_mul (Φ i j k), map_add (Φ i j k), Φ_C, Φ_X, eig, Fin.isValue, Matrix.cons_val]
    linear_combination (admY i k) * r1
  have hjk' : admY j k ∈ (Φ i j k).range := by
    refine (AlgHom.mem_range (Φ i j k)).2 ⟨C (-Complex.I / 2) * (X 4 - X 5), ?_⟩
    simp only [map_mul (Φ i j k), map_sub (Φ i j k), Φ_C, Φ_X, eig, Fin.isValue, Matrix.cons_val]
    linear_combination (admY j k) * r4
  rcases tri a with rfl | rfl | rfl <;> rcases tri b with rfl | rfl | rfl
  · exact hii
  · exact hij'
  · exact hik'
  · rw [Y_symm]; exact hij'
  · exact hjj
  · exact hjk'
  · rw [Y_symm]; exact hik'
  · rw [Y_symm]; exact hjk'
  · exact hkk

private theorem Φ_surjective (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Surjective (Φ i j k) := by
  have hrange : (Φ i j k).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨w, rfl⟩
    have hw : (X w : admP) = admY w.1.1 w.1.2 := by simp [admY, w.2]
    rw [hw]
    exact Y_mem_range i j k hij hik hjk _ _
  exact fun p => by
    have : p ∈ (Φ i j k).range := hrange ▸ Algebra.mem_top
    exact this

private def ψval (a b : Fin 3) : admQ :=
  if a = b then
    (if a = i then C (1 / 2) * (X 0 + C (1 / 2) * (X 1 + X 2))
      else if a = j then C (1 / 2) * (X 0 - C (1 / 2) * (X 1 + X 2)) else X 3)
  else if a = k ∨ b = k then
    (if a = i ∨ b = i then C (1 / 2) * (X 4 + X 5) else C (-Complex.I / 2) * (X 4 - X 5))
  else C (-Complex.I / 4) * (X 1 - X 2)

private def Ψ : admP →ₐ[ℂ] admQ := aeval fun w : admIdx => ψval i j k w.1.1 w.1.2

private theorem Ψ_C (a : ℂ) : Ψ i j k (C a) = C a := by
  rw [Ψ, aeval_C, algebraMap_eq]

private theorem Ψ_Y (a b : Fin 3) (hab : a ≤ b) : Ψ i j k (admY a b) = ψval i j k a b := by
  have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
  rw [hY, Ψ, aeval_X]

private theorem Ψ_Y' (a b : Fin 3) : Ψ i j k (admY a b) = ψval i j k a b ∨ Ψ i j k (admY a b) = ψval i j k b a := by
  by_cases hab : a ≤ b
  · exact Or.inl (Ψ_Y i j k a b hab)
  · right
    rw [Y_symm, Ψ_Y i j k b a (le_of_not_ge hab)]

private theorem Ψ_Φ_X (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : Fin 6) : Ψ i j k (Φ i j k (X n)) = X n := by
  have r1 : (C (1 / 2 : ℂ) : admQ) * 2 = 1 := by
    rw [show (2 : admQ) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  have r3 : (C (2 * Complex.I) : admQ) * C (-Complex.I / 4) * 2 = 1 := by
    rw [show (2 : admQ) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul]
    rw [show 2 * Complex.I * (-Complex.I / 4) * 2 = -(Complex.I * Complex.I) by ring, Complex.I_mul_I]
    norm_num
  have r4 : (C Complex.I : admQ) * C (-Complex.I / 2) * 2 = 1 := by
    rw [show (2 : admQ) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul]
    rw [show Complex.I * (-Complex.I / 2) * 2 = -(Complex.I * Complex.I) by ring, Complex.I_mul_I]
    norm_num

  have vii : Ψ i j k (admY i i) = C (1 / 2) * (X 0 + C (1 / 2) * (X 1 + X 2)) := by
    rw [Ψ_Y i j k i i le_rfl]; simp [ψval]
  have vjj : Ψ i j k (admY j j) = C (1 / 2) * (X 0 - C (1 / 2) * (X 1 + X 2)) := by
    rw [Ψ_Y i j k j j le_rfl]; simp [ψval, Ne.symm hij]
  have vkk : Ψ i j k (admY k k) = X 3 := by
    rw [Ψ_Y i j k k k le_rfl]; simp [ψval, Ne.symm hik, Ne.symm hjk]
  have vij : Ψ i j k (admY i j) = C (-Complex.I / 4) * (X 1 - X 2) := by
    rcases Ψ_Y' i j k i j with h | h <;> rw [h] <;> simp [ψval, hij, Ne.symm hij, hik, hjk]
  have vik : Ψ i j k (admY i k) = C (1 / 2) * (X 4 + X 5) := by
    rcases Ψ_Y' i j k i k with h | h <;> rw [h] <;> simp [ψval, hik, Ne.symm hik]
  have vjk : Ψ i j k (admY j k) = C (-Complex.I / 2) * (X 4 - X 5) := by
    rcases Ψ_Y' i j k j k with h | h <;> rw [h] <;> simp [ψval, hjk, Ne.symm hjk, Ne.symm hij, Ne.symm hik]
  rw [Φ_X]
  fin_cases n <;>
    simp only [eig, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  · rw [map_add, vii, vjj]
    linear_combination (X 0 : admQ) * r1
  · rw [map_add, map_sub, map_mul, Ψ_C, vii, vjj, vij]
    linear_combination (C (1 / 2 : ℂ) * (X 1 + X 2) + X 1 - C (2 * Complex.I) * C (-Complex.I / 4) * (X 1 - X 2) :
        admQ)
        * r1 + (C (1 / 2 : ℂ) * (X 1 - X 2) : admQ) * r3
  · rw [map_sub, map_sub, map_mul, Ψ_C, vii, vjj, vij]
    linear_combination (C (1 / 2 : ℂ) * (X 1 + X 2) + X 2 + C (2 * Complex.I) * C (-Complex.I / 4) * (X 1 - X 2) :
        admQ)
        * r1 + (-(C (1 / 2 : ℂ) * (X 1 - X 2)) : admQ) * r3
  · exact vkk
  · rw [map_add, map_mul, Ψ_C, vik, vjk]
    linear_combination (X 4 - C Complex.I * C (-Complex.I / 2) * (X 4 - X 5) : admQ) * r1
        + (C (1 / 2 : ℂ) * (X 4 - X 5) : admQ) * r4
  · rw [map_sub, map_mul, Ψ_C, vik, vjk]
    linear_combination (X 5 + C Complex.I * C (-Complex.I / 2) * (X 4 - X 5) : admQ) * r1
        + (-(C (1 / 2 : ℂ) * (X 4 - X 5)) : admQ) * r4

private theorem Φ_injective (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Injective (Φ i j k) := by
  have h : (Ψ i j k).comp (Φ i j k) = AlgHom.id ℂ admQ :=
    algHom_ext fun n => by rw [AlgHom.comp_apply, Ψ_Φ_X i j k hij hik hjk, AlgHom.id_apply]
  intro f g hfg
  have := congrArg (Ψ i j k) hfg
  rwa [← AlgHom.comp_apply, h, ← AlgHom.comp_apply (Ψ i j k), h, AlgHom.id_apply, AlgHom.id_apply] at this

end Distinct

private def wsum (m : Fin 6 →₀ ℕ) : ℂ := ∑ n : Fin 6, (m n : ℂ) * wtv n

private theorem E_monomial (m : Fin 6 →₀ ℕ) (r : ℂ) : admE (monomial m r) = wsum m • monomial m r := by
  unfold admE
  rw [mkDerivation_monomial]
  simp only [smul_eq_mul]
  have hterm : ∀ n ∈ m.support,
      monomial (m - Finsupp.single n 1) ((m n : ℕ) : ℂ) * (wtv n • X n) =
        ((m n : ℂ) * wtv n) • monomial m (1 : ℂ) := by
    intro n hn
    have hle : Finsupp.single n 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hn))
    rw [X, mul_smul_comm, monomial_mul, mul_one, tsub_add_cancel_of_le hle, smul_monomial, smul_monomial, smul_eq_mul,
      smul_eq_mul, mul_one, mul_comm]
  have hw : wsum m = ∑ n ∈ m.support, (m n : ℂ) * wtv n := by
    unfold wsum
    refine (Finset.sum_subset (Finset.subset_univ _) fun n _ hn => ?_).symm
    rw [Finsupp.mem_support_iff, not_not] at hn
    simp [hn]
  calc r • (m.sum fun n e => monomial (m - Finsupp.single n 1) (e : ℂ) * (wtv n • X n))
      = r • ∑ n ∈ m.support, ((m n : ℂ) * wtv n) • monomial m (1 : ℂ) := by
        rw [Finsupp.sum]
        exact congrArg (r • ·) (Finset.sum_congr rfl hterm)
    _ = wsum m • monomial m r := by
        rw [← Finset.sum_smul, ← hw, smul_comm, smul_monomial, smul_eq_mul, mul_one]

private theorem wsum_eq_zero_of_mem_support {f : admQ} (hf : admE f = 0) {m : Fin 6 →₀ ℕ} (hm : m ∈ f.support) :
    wsum m = 0 := by
  have h1 : coeff m (admE f) = wsum m * coeff m f := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum, coeff_sum]
    simp only [E_monomial, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' f.support m]
    simp [hm]
  rw [hf, coeff_zero] at h1
  have h2 : coeff m f ≠ 0 := mem_support_iff.1 hm
  exact (mul_eq_zero.1 h1.symm).resolve_right h2

private theorem balanced_of_wsum_eq_zero {m : Fin 6 →₀ ℕ} (h : wsum m = 0) : 2 * m 2 + m 5 = 2 * m 1 + m 4 := by
  unfold wsum at h
  rw [Fin.sum_univ_six] at h
  simp only [wtv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, zero_add] at h
  have h' : ((2 * m 2 + m 5 : ℕ) : ℂ) * Complex.I = ((2 * m 1 + m 4 : ℕ) : ℂ) * Complex.I := by
    push_cast
    linear_combination h
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h'

private def restrictDiag : admP →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval fun w : admIdx => if w.1.1 = w.1.2 then X w.1.1 else 0

private theorem restrictDiag_Y (a b : Fin 3) : restrictDiag (admY a b) = if a = b then X a else 0 := by
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, restrictDiag, aeval_X]
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, restrictDiag, aeval_X]
    have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
    simp [hne, Ne.symm hne]

private theorem restrictDiag_C (c : ℂ) : restrictDiag (C c) = C c := by
  rw [restrictDiag, aeval_C, algebraMap_eq]

section Distinct₂

variable (i j k : Fin 3)

private def ρ : admQ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![X i + X j, X i - X j, X i - X j, X k, 0, 0]

private theorem restrictDiag_comp_Φ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    restrictDiag.comp (Φ i j k) = ρ i j k := by
  refine algHom_ext fun n => ?_
  rw [AlgHom.comp_apply, Φ_X, ρ, aeval_X]
  fin_cases n <;>
    simp only [eig, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul,
      restrictDiag_Y, restrictDiag_C, if_true, hij, hik, hjk, if_false, mul_zero, add_zero, sub_zero]

private theorem rename_swap_ρ_monomial (hik : i ≠ k) (hjk : j ≠ k) (m : Fin 6 →₀ ℕ) (r : ℂ)
    (hm : 2 * m 2 + m 5 = 2 * m 1 + m 4) :
    rename (Equiv.swap i j) (ρ i j k (monomial m r)) = ρ i j k (monomial m r) := by
  rw [ρ, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_six]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons, map_mul, map_pow, map_add, map_sub, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), map_zero, AlgHom.commutes]
  by_cases h45 : m 4 = 0 ∧ m 5 = 0
  · obtain ⟨h4, h5⟩ := h45
    have h12 : m 2 = m 1 := by omega
    have e1 : (X j + X i : MvPolynomial (Fin 3) ℂ) = X i + X j := add_comm _ _
    have e2 : (X j - X i : MvPolynomial (Fin 3) ℂ) ^ m 1 * (X j - X i) ^ m 1 =
        (X i - X j) ^ m 1 * (X i - X j) ^ m 1 := by
      rw [← mul_pow, ← mul_pow, ← neg_sub (X i) (X j), neg_mul_neg]
    rw [h4, h5, h12, pow_zero, mul_assoc ((X j + X i : MvPolynomial (Fin 3) ℂ) ^ m 0), e2, e1]
    ring
  · have hz : (0 : MvPolynomial (Fin 3) ℂ) ^ m 4 * (0 : MvPolynomial (Fin 3) ℂ) ^ m 5 = 0 := by
      rcases not_and_or.1 h45 with h4 | h5
      · rw [zero_pow h4, zero_mul]
      · rw [zero_pow h5, mul_zero]
    simp only [mul_assoc]
    rw [hz]
    simp only [mul_zero]

private theorem rename_swap_restrictDiag (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : admP) (hp : admD i j p = 0) :
    rename (Equiv.swap i j) (restrictDiag p) = restrictDiag p := by
  obtain ⟨f, rfl⟩ := Φ_surjective i j k hij hik hjk p
  have hEf : admE f = 0 := by
    apply Φ_injective i j k hij hik hjk
    rw [← D_Φ i j k hij hik hjk, hp, map_zero]
  have hρ : restrictDiag (Φ i j k f) = ρ i j k f := by
    rw [← AlgHom.comp_apply, restrictDiag_comp_Φ i j k hij hik hjk]
  rw [hρ]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact rename_swap_ρ_monomial i j k hik hjk m _
    (balanced_of_wsum_eq_zero (wsum_eq_zero_of_mem_support hEf hm))

end Distinct₂

private def wt : admIdx → ℕ := fun v => if v.1.1 = v.1.2 then 0 else 1

private theorem wt_le_one (v : admIdx) : wt v ≤ 1 := by
  unfold wt
  split_ifs <;> omega

private abbrev IsWH (q : admP) (n : ℕ) : Prop := IsWeightedHomogeneous wt q n

private abbrev wcomp (n : ℕ) : admP →ₗ[ℂ] admP := weightedHomogeneousComponent wt n

private theorem isWH_sub {q r : admP} {n : ℕ} (hq : IsWH q n) (hr : IsWH r n) : IsWH (q - r) n :=
  (weightedHomogeneousSubmodule ℂ wt n).sub_mem hq hr

private theorem isWH_neg {q : admP} {n : ℕ} (hq : IsWH q n) : IsWH (-q) n :=
  (weightedHomogeneousSubmodule ℂ wt n).neg_mem hq

private theorem isWH_smul {q : admP} {n : ℕ} (c : ℂ) (hq : IsWH q n) : IsWH (c • q) n :=
  (weightedHomogeneousSubmodule ℂ wt n).smul_mem c hq

private theorem isWH_two_mul {q : admP} {n : ℕ} (hq : IsWH q n) : IsWH (2 * q) n := by
  have h : (2 : admP) * q = (2 : ℂ) • q := by rw [smul_eq_C_mul, map_ofNat]
  rw [h]
  exact isWH_smul 2 hq

private theorem isWH_Y (a b : Fin 3) : IsWH (admY a b) (if a = b then 0 else 1) := by
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY]
    simpa [wt] using isWeightedHomogeneous_X (R := ℂ) wt (⟨(a, b), hab⟩ : admIdx)
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
    rw [hY]
    simpa [wt, hne, Ne.symm hne] using isWeightedHomogeneous_X (R := ℂ) wt (⟨(b, a), le_of_not_ge hab⟩ : admIdx)

private theorem isWH_Y_diag (a : Fin 3) : IsWH (admY a a) 0 := by simpa using isWH_Y a a

private theorem isWH_Y_off {a b : Fin 3} (hab : a ≠ b) : IsWH (admY a b) 1 := by simpa [hab] using isWH_Y a b

private def zidx (i j : Fin 3) : admIdx := if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), le_of_not_ge h⟩

private theorem X_zidx (i j : Fin 3) : (X (zidx i j) : admP) = admY i j := by
  unfold zidx admY
  simp only [Matrix.of_apply]
  split_ifs <;> rfl

private theorem wt_zidx {i j : Fin 3} (hij : i ≠ j) : wt (zidx i j) = 1 := by
  unfold zidx wt
  split_ifs <;> simp_all

private theorem zidx_eq_of_le {a b : Fin 3} (hab : a ≤ b) : zidx a b = ⟨(a, b), hab⟩ := by
  simp [zidx, hab]

private theorem zidx_eq_of_ge {a b : Fin 3} (hab : b ≤ a) (hne : a ≠ b) : zidx a b = ⟨(b, a), hab⟩ := by
  have h : ¬ a ≤ b := fun h => hne (le_antisymm h hab)
  simp [zidx, h]

private theorem D_expand (i j : Fin 3) (q : admP) : admD i j q = ∑ v : admIdx, admD i j (X v) * pderiv v q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum, mul_comm p]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring

private theorem isWH_pderiv {q : admP} {n : ℕ} (hq : IsWH q n) (v : admIdx) : IsWH (pderiv v q) (n - wt v) := by
  intro m hm
  rw [q.as_sum, map_sum, coeff_sum] at hm
  obtain ⟨m', -, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [pderiv_monomial, coeff_monomial] at hm'
  split_ifs at hm' with hmm
  · subst hmm
    have hmv : m' v ≠ 0 := by
      intro h
      simp [h] at hm'
    have hcoef : coeff m' q ≠ 0 := left_ne_zero_of_mul hm'
    have hw : Finsupp.weight wt m' = n := hq hcoef
    have hle : Finsupp.single v 1 ≤ m' := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hmv)
    have h2 : Finsupp.weight wt (m' - Finsupp.single v 1) + Finsupp.weight wt (Finsupp.single v 1) =
        Finsupp.weight wt m' := by
      rw [← map_add, tsub_add_cancel_of_le hle]
    rw [Finsupp.weight_single, one_smul] at h2
    omega
  · exact absurd rfl hm'

section Distinct

variable (i j k : Fin 3)

private theorem isWH_D_zidx (hij : i ≠ j) : IsWH (admD i j (X (zidx i j))) 0 := by
  rw [X_zidx, D_Y_ij i j hij]
  exact isWH_sub (isWH_Y_diag j) (isWH_Y_diag i)

private theorem D_zidx_ne_zero (hij : i ≠ j) : admD i j (X (zidx i j)) ≠ 0 := by
  rw [X_zidx, D_Y_ij i j hij, sub_ne_zero]
  have h1 : admY j j = X (⟨(j, j), le_rfl⟩ : admIdx) := by simp [admY]
  have h2 : admY i i = X (⟨(i, i), le_rfl⟩ : admIdx) := by simp [admY]
  rw [h1, h2]
  intro h
  exact hij (congrArg (fun v : admIdx => v.1.1) (X_injective h)).symm

private theorem tri (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Fin 3) : x = i ∨ x = j ∨ x = k := by
  revert i j k x
  decide

private theorem isWH_D_X_one (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : admIdx) (hv : v ≠ zidx i j) :
    IsWH (admD i j (X v)) 1 := by
  obtain ⟨⟨a, b⟩, hab⟩ := v
  have hX : (X (⟨(a, b), hab⟩ : admIdx) : admP) = admY a b := by simp [admY, hab]
  rw [hX]
  rcases tri i j k hij hik hjk a with ha | ha | ha <;> rcases tri i j k hij hik hjk b with hb | hb | hb <;>
    subst a <;> subst b
  · rw [D_Y_ii i j hij]; exact isWH_two_mul (isWH_Y_off hij)
  · exact absurd (zidx_eq_of_le hab).symm hv
  · rw [D_Y_ik i j k hij hik hjk]; exact isWH_Y_off hjk
  · exact absurd (zidx_eq_of_ge hab hij).symm hv
  · rw [D_Y_jj i j hij]; exact isWH_neg (isWH_two_mul (isWH_Y_off hij))
  · rw [D_Y_jk i j k hij hik hjk]; exact isWH_neg (isWH_Y_off hik)
  · rw [Y_symm, D_Y_ik i j k hij hik hjk]; exact isWH_Y_off hjk
  · rw [Y_symm, D_Y_jk i j k hij hik hjk]; exact isWH_neg (isWH_Y_off hik)
  · rw [D_Y_kk i j k hik hjk]; exact isWeightedHomogeneous_zero (R := ℂ) wt 1

private theorem comp_D_of_isWH (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {h : admP} {e : ℕ} (hh : IsWH h e) {n : ℕ}
    (hn : n < e) :
    wcomp n (admD i j h) = if n + 1 = e then admD i j (X (zidx i j)) * pderiv (zidx i j) h else 0 := by
  rw [D_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (zidx i j)), map_add, map_sum]
  have hz : IsWH (admD i j (X (zidx i j)) * pderiv (zidx i j) h) (0 + (e - wt (zidx i j))) :=
    IsWeightedHomogeneous.mul (isWH_D_zidx i j hij) (isWH_pderiv hh _)
  rw [wt_zidx hij] at hz
  have hrest : ∑ v ∈ Finset.univ.erase (zidx i j), wcomp n (admD i j (X v) * pderiv v h) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv' : v ≠ zidx i j := Finset.ne_of_mem_erase hv
    have h1 : IsWH (admD i j (X v) * pderiv v h) (1 + (e - wt v)) :=
      IsWeightedHomogeneous.mul (isWH_D_X_one i j k hij hik hjk v hv') (isWH_pderiv hh v)
    have hw := wt_le_one v
    exact h1.weightedHomogeneousComponent_ne n (by omega)
  rw [hrest, add_zero]
  split_ifs with hne
  · have : n = 0 + (e - 1) := by omega
    rw [this]
    exact hz.weightedHomogeneousComponent_same
  · exact hz.weightedHomogeneousComponent_ne n (by omega)

private theorem comp_D_tail (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {r : admP} {d : ℕ} (hd : d ≠ 0)
    (hr : ∀ n ≤ d, wcomp n r = 0) : wcomp (d - 1) (admD i j r) = 0 := by
  have hfin := weightedHomogeneousComponent_finsupp (w := wt) r
  conv_lhs => rw [← sum_weightedHomogeneousComponent wt r, finsum_eq_sum _ hfin, map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases le_or_gt m d with hm | hm
  · rw [hr m hm, map_zero, map_zero]
  · have hhom : IsWH (wcomp m r) m := weightedHomogeneousComponent_isWeightedHomogeneous m r
    rw [comp_D_of_isWH i j k hij hik hjk hhom (by omega), if_neg (by omega)]

end Distinct

private def killOff : admP →ₐ[ℂ] admP := aeval fun v : admIdx => if v.1.1 = v.1.2 then X v else 0

private def admemb : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] admP := rename fun a : Fin 3 => (⟨(a, a), le_rfl⟩ : admIdx)

private theorem emb_restrictDiag (q : admP) : admemb (restrictDiag q) = killOff q := by
  suffices h : admemb.comp restrictDiag = killOff from AlgHom.congr_fun h q
  refine algHom_ext fun v => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := v
  by_cases h : a = b
  · subst h
    simp [admemb, restrictDiag, killOff]
  · simp [admemb, restrictDiag, killOff, h]

private theorem weight_eq_zero_iff (m : admIdx →₀ ℕ) :
    Finsupp.weight wt m = 0 ↔ ∀ v ∈ m.support, v.1.1 = v.1.2 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  have hmv : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  unfold wt
  split_ifs with h <;> simp [h, hmv]

private theorem killOff_monomial (m : admIdx →₀ ℕ) (c : ℂ) :
    killOff (monomial m c) = if Finsupp.weight wt m = 0 then monomial m c else 0 := by
  rw [killOff, aeval_monomial, algebraMap_eq]
  split_ifs with hw
  · rw [weight_eq_zero_iff] at hw
    rw [monomial_eq]
    congr 1
    exact Finsupp.prod_congr fun v hv => by rw [if_pos (hw v hv)]
  · rw [weight_eq_zero_iff] at hw
    push Not at hw
    obtain ⟨v, hv, hne⟩ := hw
    rw [Finsupp.prod, Finset.prod_eq_zero hv (by rw [if_neg hne]; exact zero_pow (Finsupp.mem_support_iff.1 hv)),
      mul_zero]

private theorem comp_zero_monomial (m : admIdx →₀ ℕ) (c : ℂ) :
    wcomp 0 (monomial m c) = if Finsupp.weight wt m = 0 then monomial m c else 0 := by
  ext n
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hn hm hm
  · rfl
  · rw [coeff_monomial, if_neg (fun h => hm (by rw [h]; exact hn)), coeff_zero]
  · rw [coeff_monomial, if_neg (fun h => hn (by rw [← h]; exact hm))]
  · rfl

private theorem killOff_eq_comp_zero (q : admP) : killOff q = wcomp 0 q := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c => rw [killOff_monomial, comp_zero_monomial]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

private theorem comp_zero_eq_zero_of_restrictDiag {p : admP} (h0 : restrictDiag p = 0) : wcomp 0 p = 0 := by
  rw [← killOff_eq_comp_zero, ← emb_restrictDiag, h0, map_zero]

private theorem exists_third (a b : Fin 3) (hab : a ≠ b) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  revert a b
  decide

private theorem eq_zero_of_restrictDiag_eq_zero {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0)
    (h0 : restrictDiag p = 0) : p = 0 := by
  classical
  by_contra hne
  have hex : ∃ n, wcomp n p ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [← sum_weightedHomogeneousComponent wt p]
    exact finsum_eq_zero_of_forall_eq_zero hall
  set d := Nat.find hex with hd_def
  have hd : wcomp d p ≠ 0 := Nat.find_spec hex
  have hmin : ∀ n, n < d → wcomp n p = 0 := fun n hn => by
    have := Nat.find_min hex hn
    push Not at this
    exact this
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    rw [h]
    exact comp_zero_eq_zero_of_restrictDiag h0
  set h := wcomp d p with hh
  have hhom : IsWH h d := weightedHomogeneousComponent_isWeightedHomogeneous d p
  have htail : ∀ n ≤ d, wcomp n (p - h) = 0 := by
    intro n hn
    rw [map_sub]
    rcases hn.lt_or_eq with hlt | rfl
    · rw [hmin n hlt, hhom.weightedHomogeneousComponent_ne n hlt.ne, sub_zero]
    · rw [hhom.weightedHomogeneousComponent_same]
      exact sub_self _

  have hoff : ∀ v : admIdx, wt v ≠ 0 → pderiv v h = 0 := by
    intro v hv
    obtain ⟨⟨a, b⟩, hab⟩ := v
    have hab' : a ≠ b := by
      intro h
      apply hv
      simp [wt, h]
    obtain ⟨c, hac, hbc⟩ := exists_third a b hab'
    have hz : zidx a b = ⟨(a, b), hab⟩ := zidx_eq_of_le hab
    rw [← hz]
    have h1 := comp_D_of_isWH a b c hab' hac hbc hhom (n := d - 1) (by omega)
    rw [if_pos (by omega)] at h1
    have h2 : admD a b h = -admD a b (p - h) := by rw [map_sub, hp, zero_sub, neg_neg]
    rw [h2, map_neg, comp_D_tail a b c hab' hac hbc hd0 htail, neg_zero] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (D_zidx_ne_zero a b hab')

  have heuler := hhom.sum_weight_X_mul_pderiv
  rw [Finset.sum_eq_zero (fun v _ => ?_)] at heuler
  · rw [← Nat.cast_smul_eq_nsmul ℂ] at heuler
    exact hd ((smul_eq_zero.1 heuler.symm).resolve_left (Nat.cast_ne_zero.2 hd0))
  · by_cases hv : wt v = 0
    · rw [hv, zero_smul]
    · rw [hoff v hv, mul_zero, smul_zero]

private def traces (n : Fin 3) : admP := (admY ^ ((n : ℕ) + 1)).trace

private def psums (n : Fin 3) : MvPolynomial (Fin 3) ℂ := psum (Fin 3) ℂ ((n : ℕ) + 1)

private theorem Y_map_restrictDiag :
    admY.map restrictDiag = Matrix.diagonal fun a : Fin 3 => (X a : MvPolynomial (Fin 3) ℂ) := by
  ext a b
  rw [Matrix.map_apply, restrictDiag_Y, Matrix.diagonal_apply]

private theorem restrictDiag_trace_pow (m : ℕ) : restrictDiag ((admY ^ m).trace) = psum (Fin 3) ℂ m := by
  have h1 : (admY ^ m).map restrictDiag = (admY.map restrictDiag) ^ m := by
    simpa only [AlgHom.mapMatrix_apply] using map_pow restrictDiag.mapMatrix admY m
  rw [Y_map_restrictDiag, Matrix.diagonal_pow] at h1
  simp only [Matrix.trace, Matrix.diag, map_sum, psum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := congrFun (congrFun h1 a) a
  rw [Matrix.map_apply, Matrix.diagonal_apply_eq] at this
  exact this

private theorem restrictDiag_traces (n : Fin 3) : restrictDiag (traces n) = psums n := restrictDiag_trace_pow _

private theorem D_aeval_traces (i j : Fin 3) (G : MvPolynomial (Fin 3) ℂ) : admD i j (aeval traces G) = 0 := by
  induction G using MvPolynomial.induction_on with
  | C c => rw [aeval_C, Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p n hp =>
    rw [map_mul, aeval_X, Derivation.leibniz, hp, smul_zero, add_zero, traces, D_trace_Y_pow, smul_zero]

private theorem isSymmetric_restrictDiag {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0) :
    (restrictDiag p).IsSymmetric := by
  intro e
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy hf =>
    rw [Equiv.Perm.coe_mul, ← rename_rename, hf]
    obtain ⟨z, hxz, hyz⟩ := exists_third x y hxy
    exact rename_swap_restrictDiag x y z hxy hxz hyz p (hp x y)

private abbrev R3 : Subalgebra ℂ (MvPolynomial (Fin 3) ℂ) := (aeval (R := ℂ) psums).range

private theorem psum_mem {m : ℕ} (h1 : 1 ≤ m) (h3 : m ≤ 3) : psum (Fin 3) ℂ m ∈ R3 := by
  rw [AlgHom.mem_range]
  refine ⟨X ⟨m - 1, by omega⟩, ?_⟩
  rw [aeval_X, psums]
  congr 1
  exact Nat.sub_add_cancel h1

private theorem esymm_mem (k : ℕ) : k ≤ 3 → esymm (Fin 3) ℂ k ∈ R3 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk3
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [esymm_zero]
      exact R3.one_mem
    · have hmem : (k : MvPolynomial (Fin 3) ℂ) * esymm (Fin 3) ℂ k ∈ R3 := by
        rw [mul_esymm_eq_sum (Fin 3) ℂ k]
        refine R3.mul_mem (R3.pow_mem (R3.neg_mem R3.one_mem) _) (R3.sum_mem fun a ha => ?_)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        exact R3.mul_mem (R3.mul_mem (R3.pow_mem (R3.neg_mem R3.one_mem) _) (ih a.1 (by omega) (by omega)))
          (psum_mem (by omega) (by omega))
      have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have hk' : esymm (Fin 3) ℂ k = (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin 3) ℂ) * esymm (Fin 3) ℂ k) := by
        rw [← C_eq_coe_nat, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk0, C_1, one_mul]
      rw [hk']
      exact R3.smul_mem hmem _

private theorem aeval_esymm_mem (φ : MvPolynomial (Fin 3) ℂ) :
    aeval (fun i : Fin 3 => esymm (Fin 3) ℂ ((i : ℕ) + 1)) φ ∈ R3 := by
  induction φ using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C]
    exact R3.algebraMap_mem c
  | add p q hp hq =>
    rw [map_add]
    exact R3.add_mem hp hq
  | mul_X p n hp =>
    rw [map_mul, aeval_X]
    exact R3.mul_mem hp (esymm_mem _ (by omega))

private theorem exists_eq_aeval_traces {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0) :
    ∃ G : MvPolynomial (Fin 3) ℂ, p = aeval traces G := by
  obtain ⟨φ, hφ⟩ :=
    esymmAlgHom_surjective (σ := Fin 3) (n := 3) ℂ (by simp) ⟨restrictDiag p, isSymmetric_restrictDiag hp⟩
  have hq : restrictDiag p = aeval (fun i : Fin 3 => esymm (Fin 3) ℂ ((i : ℕ) + 1)) φ := by
    have h := congrArg Subtype.val hφ
    rw [esymmAlgHom_apply] at h
    exact h.symm
  have hmem : restrictDiag p ∈ R3 := hq ▸ aeval_esymm_mem φ
  obtain ⟨G, hG⟩ := (AlgHom.mem_range _).1 hmem
  refine ⟨G, ?_⟩
  have h2 : restrictDiag (aeval traces G) = aeval psums G := by
    rw [← AlgHom.comp_apply, comp_aeval]
    simp only [restrictDiag_traces]
  have hinv : ∀ i j : Fin 3, admD i j (p - aeval traces G) = 0 := fun i j => by
    rw [map_sub, hp, D_aeval_traces, sub_zero]
  have hres : restrictDiag (p - aeval traces G) = 0 := by
    rw [map_sub, h2, hG, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_restrictDiag_eq_zero hinv hres)

private example : restrictDiag (traces 0) = X 0 + X 1 + X 2 := by
  rw [restrictDiag_traces, psums, psum]
  simp [Fin.sum_univ_three]

private example : ∃ G : MvPolynomial (Fin 3) ℂ, (admY ^ 2).trace + 5 * admY.trace ^ 3 = aeval traces G := by
  refine exists_eq_aeval_traces fun i j => ?_
  have h1 : admD i j admY.trace = 0 := by simpa using D_trace_Y_pow i j 1
  have h5 : admD i j (5 : admP) = 0 := by
    rw [← map_ofNat (algebraMap ℂ admP) 5]
    exact Derivation.map_algebraMap _ _
  rw [map_add, D_trace_Y_pow, Derivation.leibniz, Derivation.leibniz_pow, h1, h5]
  simp only [smul_zero, add_zero]

end SymRestriction

namespace SymbolLemma

variable {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]

private def wordOp (g : ι → Module.End ℂ V) (l : List ι) : Module.End ℂ V := (l.map g).prod

private theorem wordOp_nil (g : ι → Module.End ℂ V) : wordOp g [] = 1 := by
  simp [wordOp]

private theorem wordOp_cons (g : ι → Module.End ℂ V) (x : ι) (l : List ι) : wordOp g (x :: l) = g x * wordOp g l := by
  simp [wordOp]

private theorem wordOp_append (g : ι → Module.End ℂ V) (l l' : List ι) :
    wordOp g (l ++ l') = wordOp g l * wordOp g l' := by
  simp [wordOp]

private def lengthSpan (g : ι → Module.End ℂ V) (n : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ l : List ι, l.length ≤ n ∧ wordOp g l = T}

private theorem wordOp_mem_lengthSpan (g : ι → Module.End ℂ V) {l : List ι} {n : ℕ} (h : l.length ≤ n) :
    wordOp g l ∈ lengthSpan g n :=
  Submodule.subset_span ⟨l, h, rfl⟩

private theorem one_mem_lengthSpan (g : ι → Module.End ℂ V) (n : ℕ) : (1 : Module.End ℂ V) ∈ lengthSpan g n := by
  rw [← wordOp_nil g]
  exact wordOp_mem_lengthSpan g (by simp)

private theorem lengthSpan_mono (g : ι → Module.End ℂ V) {m n : ℕ} (h : m ≤ n) : lengthSpan g m ≤ lengthSpan g n :=
  Submodule.span_mono fun _ hT => by
    obtain ⟨l, hl, rfl⟩ := hT
    exact ⟨l, hl.trans h, rfl⟩

private theorem letter_mul_mem (g : ι → Module.End ℂ V) (x : ι) {n : ℕ} {T : Module.End ℂ V}
    (hT : T ∈ lengthSpan g n) : g x * T ∈ lengthSpan g (n + 1) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨l, hl, rfl⟩ := hT
    rw [← wordOp_cons]
    exact wordOp_mem_lengthSpan g (by simpa using hl)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ ha

private theorem span_letters_mul_mem (g : ι → Module.End ℂ V) {S : Module.End ℂ V}
    (hS : S ∈ Submodule.span ℂ (Set.range g)) {n : ℕ} {T : Module.End ℂ V} (hT : T ∈ lengthSpan g n) :
    S * T ∈ lengthSpan g (n + 1) := by
  induction hS using Submodule.span_induction with
  | mem S hS =>
    obtain ⟨x, rfl⟩ := hS
    exact letter_mul_mem g x hT
  | zero => simp
  | add a b _ _ ha hb =>
    rw [add_mul]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ ha

private theorem wordOp_mul_mem (g : ι → Module.End ℂ V) {l : List ι} {m n : ℕ} (hl : l.length ≤ m)
    {T : Module.End ℂ V} (hT : T ∈ lengthSpan g n) : wordOp g l * T ∈ lengthSpan g (m + n) := by
  induction l generalizing m with
  | nil =>
    rw [wordOp_nil, one_mul]
    exact lengthSpan_mono g (Nat.le_add_left n m) hT
  | cons x l ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hl; omega⟩
    rw [wordOp_cons, mul_assoc]
    have h := letter_mul_mem g x (ih (by simpa using hl))
    exact lengthSpan_mono g (by omega) h

private theorem mul_mem_lengthSpan (g : ι → Module.End ℂ V) {m n : ℕ} {S T : Module.End ℂ V}
    (hS : S ∈ lengthSpan g m) (hT : T ∈ lengthSpan g n) : S * T ∈ lengthSpan g (m + n) := by
  induction hS using Submodule.span_induction with
  | mem S hS =>
    obtain ⟨l, hl, rfl⟩ := hS
    exact wordOp_mul_mem g hl hT
  | zero => simp
  | add a b _ _ ha hb =>
    rw [add_mul]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ ha

private theorem wordOp_sub_wordOp_mem_of_perm (g : ι → Module.End ℂ V)
    (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g))
    {l l' : List ι} (h : l.Perm l') : ∀ m : ℕ, l.length ≤ m + 1 → wordOp g l - wordOp g l' ∈ lengthSpan g m := by
  induction h with
  | nil =>
    intro m _
    simp
  | @cons x l₁ l₂ h₁₂ ih =>
    intro m hm
    rcases m with _ | m
    ·
      have hl₁ : l₁.length = 0 := by simp only [List.length_cons] at hm; omega
      have h0 : l₁ = [] := List.eq_nil_of_length_eq_zero hl₁
      have h0' : l₂ = [] := List.eq_nil_of_length_eq_zero (by rw [← h₁₂.length_eq]; exact hl₁)
      subst h0; subst h0'
      simp
    · rw [wordOp_cons, wordOp_cons, ← mul_sub]
      exact letter_mul_mem g x (ih m (by simp only [List.length_cons] at hm; omega))
  | @swap x y l =>
    intro m hm
    rw [wordOp_cons, wordOp_cons, wordOp_cons, wordOp_cons, ← mul_assoc, ← mul_assoc, ← sub_mul]
    simp only [List.length_cons] at hm
    have hl : l.length ≤ m - 1 := by omega
    have h := span_letters_mul_mem g (hg y x) (wordOp_mem_lengthSpan g hl)
    exact lengthSpan_mono g (by omega) h
  | @trans l₁ l₂ l₃ h₁₂ _ ih₁ ih₂ =>
    intro m hm
    have h := add_mem (ih₁ m hm) (ih₂ m (by rw [← h₁₂.length_eq]; exact hm))
    simpa using h

private def wordSym (l : List ι) : MvPolynomial ι ℂ := (l.map MvPolynomial.X).prod

private theorem wordSym_append (l l' : List ι) : wordSym (l ++ l') = wordSym l * wordSym l' := by
  simp [wordSym]

variable [DecidableEq ι]

private theorem wordSym_eq_monomial (l : List ι) :
    wordSym l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset ι)) (1 : ℂ) := by
  induction l with
  | nil =>
    simp [wordSym, MvPolynomial.monomial_zero']
  | cons x l ih =>
    have hX : (MvPolynomial.X x : MvPolynomial ι ℂ) = MvPolynomial.monomial (Finsupp.single x 1) 1 := rfl
    rw [wordSym, List.map_cons, List.prod_cons, ← wordSym, ih, hX, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]

private def reprWord (μ : ι →₀ ℕ) : List ι := (Multiset.toFinsupp.symm μ).toList

private theorem reprWord_perm (l : List ι) : (reprWord (Multiset.toFinsupp (l : Multiset ι))).Perm l := by
  rw [← Multiset.coe_eq_coe, reprWord, Multiset.coe_toList, AddEquiv.symm_apply_apply]

private theorem reprWord_length (l : List ι) : (reprWord (Multiset.toFinsupp (l : Multiset ι))).length = l.length :=
  (reprWord_perm l).length_eq

omit [DecidableEq ι] in
private theorem wordSym_cons (x : ι) (l : List ι) : wordSym (x :: l) = MvPolynomial.X x * wordSym l := by
  simp [wordSym]

private theorem toFinsupp_reprWord (μ : ι →₀ ℕ) : Multiset.toFinsupp ((reprWord μ : List ι) : Multiset ι) = μ := by
  rw [reprWord, Multiset.coe_toList, AddEquiv.apply_symm_apply]

private theorem reprWord_length_eq (μ : ι →₀ ℕ) : (reprWord μ).length = μ.degree := by
  rw [reprWord, Multiset.length_toList]
  change Multiset.card (Finsupp.toMultiset μ) = _
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

private def fword (l : List ι) : FreeAlgebra ℂ ι := (l.map (FreeAlgebra.ι ℂ)).prod

omit [DecidableEq ι] in
private theorem fword_nil : fword ([] : List ι) = 1 := by
  simp [fword]

omit [DecidableEq ι] in
private theorem fword_cons (x : ι) (l : List ι) : fword (x :: l) = FreeAlgebra.ι ℂ x * fword l := by
  simp [fword]

omit [DecidableEq ι] in
private theorem fword_append (l l' : List ι) : fword (l ++ l') = fword l * fword l' := by
  simp [fword]

private def filt (n : ℕ) : Submodule ℂ (FreeAlgebra ℂ ι) :=
  Submodule.span ℂ {a | ∃ l : List ι, l.length ≤ n ∧ fword l = a}

omit [DecidableEq ι] in
private theorem fword_mem_filt {l : List ι} {n : ℕ} (h : l.length ≤ n) : fword l ∈ filt n :=
  Submodule.subset_span ⟨l, h, rfl⟩

omit [DecidableEq ι] in

private theorem ι_mul_mem_filt (x : ι) {n : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt n) :
    FreeAlgebra.ι ℂ x * a ∈ filt (n + 1) := by
  rw [filt] at ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l, hl, rfl⟩ := h
    rw [← fword_cons]
    exact fword_mem_filt (by rw [List.length_cons]; omega)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ ha

omit [DecidableEq ι] in

private theorem mem_filt_mul_fword {m : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt m) (l : List ι) :
    a * fword l ∈ filt (m + l.length) := by
  rw [filt] at ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l', hl', rfl⟩ := h
    rw [← fword_append]
    exact fword_mem_filt (by rw [List.length_append]; omega)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [add_mul]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ ha

private def admop (g : ι → Module.End ℂ V) : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ g

omit [DecidableEq ι] in
private theorem op_ι (g : ι → Module.End ℂ V) (x : ι) : admop g (FreeAlgebra.ι ℂ x) = g x := by
  simp [admop]

omit [DecidableEq ι] in
private theorem op_fword (g : ι → Module.End ℂ V) (l : List ι) : admop g (fword l) = wordOp g l := by
  induction l with
  | nil => rw [fword_nil, map_one, wordOp_nil]
  | cons x l ih => rw [fword_cons, map_mul, op_ι, ih, wordOp_cons]

omit [DecidableEq ι] in
private theorem op_mem_lengthSpan (g : ι → Module.End ℂ V) {n : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt n) :
    admop g a ∈ lengthSpan g n := by
  rw [filt] at ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l, hl, rfl⟩ := h
    rw [op_fword]
    exact wordOp_mem_lengthSpan g hl
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

private def sym : FreeAlgebra ℂ ι →ₐ[ℂ] MvPolynomial ι ℂ := FreeAlgebra.lift ℂ MvPolynomial.X

omit [DecidableEq ι] in
private theorem sym_ι (x : ι) : sym (FreeAlgebra.ι ℂ x) = (MvPolynomial.X x : MvPolynomial ι ℂ) := by
  simp [sym]

omit [DecidableEq ι] in
private theorem sym_fword (l : List ι) : sym (fword l) = wordSym l := by
  induction l with
  | nil => rw [fword_nil, map_one, wordSym, List.map_nil, List.prod_nil]
  | cons x l ih => rw [fword_cons, map_mul, sym_ι, ih, wordSym_cons]

private def admL : MvPolynomial ι ℂ →ₗ[ℂ] FreeAlgebra ℂ ι :=
  (MvPolynomial.basisMonomials ι ℂ).constr ℂ fun μ => fword (reprWord μ)

private theorem L_monomial (μ : ι →₀ ℕ) (c : ℂ) : admL (MvPolynomial.monomial μ c) = c • fword (reprWord μ) := by
  have h1 : (MvPolynomial.monomial μ c : MvPolynomial ι ℂ) = c • MvPolynomial.basisMonomials ι ℂ μ := by
    simp [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial]
  rw [h1, map_smul, admL]
  erw [Module.Basis.constr_basis]

private theorem L_X (x : ι) : admL (MvPolynomial.X x : MvPolynomial ι ℂ) = FreeAlgebra.ι ℂ x := by
  have hrepr : reprWord (Finsupp.single x 1 : ι →₀ ℕ) = [x] := by
    rw [reprWord, ← Multiset.toFinsupp_singleton, AddEquiv.symm_apply_apply, Multiset.toList_singleton]
  rw [MvPolynomial.X, L_monomial, one_smul, hrepr, fword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]

private theorem sym_L (t : MvPolynomial ι ℂ) : sym (admL t) = t := by
  suffices h : (sym (ι := ι)).toLinearMap ∘ₗ admL = LinearMap.id from LinearMap.congr_fun h t
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun μ => ?_
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply, MvPolynomial.coe_basisMonomials]
  rw [L_monomial, one_smul, sym_fword, wordSym_eq_monomial, toFinsupp_reprWord]

private theorem L_mem_filt {t : MvPolynomial ι ℂ} {n : ℕ} (ht : t.IsHomogeneous n) : admL t ∈ filt n := by
  rw [t.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  rw [L_monomial]
  refine Submodule.smul_mem _ _ (fword_mem_filt ?_)
  rw [reprWord_length_eq, Finsupp.degree_eq_weight_one]
  exact (ht (MvPolynomial.mem_support_iff.1 hμ)).le

private theorem op_sub_op_L_sym_mem (g : ι → Module.End ℂ V)
    (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g))
    {n : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt n) :
    admop g a - admop g (admL (sym a)) ∈ lengthSpan g (n - 1) := by
  rw [filt] at ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l, hl, rfl⟩ := h
    rw [sym_fword, wordSym_eq_monomial, L_monomial, one_smul, op_fword, op_fword]
    exact wordOp_sub_wordOp_mem_of_perm g hg (reprWord_perm l).symm (n - 1) (by omega)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, map_add, map_add, map_add]
    have h := add_mem ha hb
    convert h using 1
    abel
  | smul z a _ ha =>
    rw [map_smul, map_smul, map_smul, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ ha

section Bracket

variable (g : ι → Module.End ℂ V) (δ : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)) (κ : Module.End ℂ V)

private theorem exists_bracket_wordOp (hbr : ∀ x : ι, κ * g x - g x * κ = admop g (admL (δ (MvPolynomial.X x))))
    (hδ : ∀ x : ι, (δ (MvPolynomial.X x)).IsHomogeneous 1) (l : List ι) :
    ∃ a ∈ filt l.length, κ * wordOp g l - wordOp g l * κ = admop g a ∧ sym a = δ (wordSym l) := by
  induction l with
  | nil =>
    refine ⟨0, zero_mem _, ?_, ?_⟩
    · rw [wordOp_nil, mul_one, one_mul, sub_self, map_zero]
    · rw [map_zero, wordSym, List.map_nil, List.prod_nil, Derivation.map_one_eq_zero]
  | cons x l ih =>
    obtain ⟨b, hb, hbop, hbsym⟩ := ih
    refine ⟨admL (δ (MvPolynomial.X x)) * fword l + FreeAlgebra.ι ℂ x * b, ?_, ?_, ?_⟩
    · rw [List.length_cons]
      refine add_mem ?_ (ι_mul_mem_filt x hb)
      have h1 := mem_filt_mul_fword (L_mem_filt (hδ x)) l
      rwa [add_comm] at h1
    · rw [map_add, map_mul, map_mul, op_ι, op_fword, ← hbr x, ← hbop, wordOp_cons]
      noncomm_ring
    · rw [map_add, map_mul, map_mul, sym_ι, sym_fword, sym_L, hbsym, wordSym_cons, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul]
      ring

private theorem bracket_op_L_sub_mem (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g))
    (hbr : ∀ x : ι, κ * g x - g x * κ = admop g (admL (δ (MvPolynomial.X x))))
    (hδ : ∀ x : ι, (δ (MvPolynomial.X x)).IsHomogeneous 1) {n : ℕ} {t : MvPolynomial ι ℂ} (ht : t.IsHomogeneous n) :
    κ * admop g (admL t) - admop g (admL t) * κ - admop g (admL (δ t)) ∈ lengthSpan g (n - 1) := by
  let Φ : MvPolynomial ι ℂ →ₗ[ℂ] Module.End ℂ V :=
    LinearMap.mulLeft ℂ κ ∘ₗ (admop g).toLinearMap ∘ₗ admL - LinearMap.mulRight ℂ κ ∘ₗ (admop g).toLinearMap ∘ₗ admL
      - (admop g).toLinearMap ∘ₗ admL ∘ₗ (δ : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ)
  have hΦ : ∀ s : MvPolynomial ι ℂ, Φ s = κ * admop g (admL s) - admop g (admL s) * κ - admop g (admL (δ s)) := fun s
      => rfl
  rw [← hΦ, t.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : μ.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact ht (MvPolynomial.mem_support_iff.1 hμ)
  have hc : (MvPolynomial.monomial μ) (MvPolynomial.coeff μ t) =
      MvPolynomial.coeff μ t • (MvPolynomial.monomial μ (1 : ℂ) : MvPolynomial ι ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨a, ha, haop, hasym⟩ := exists_bracket_wordOp g δ κ hbr hδ (reprWord μ)
  rw [reprWord_length_eq, hdeg] at ha
  have hsym' : δ (MvPolynomial.monomial μ (1 : ℂ)) = sym a := by
    rw [hasym, wordSym_eq_monomial, toFinsupp_reprWord]
  rw [hΦ, L_monomial, one_smul, op_fword, haop, hsym']
  exact op_sub_op_L_sym_mem g hg ha

end Bracket

private example (g : ι → Module.End ℂ V) (x : ι) : admop g (admL (MvPolynomial.X x : MvPolynomial ι ℂ)) = g x := by
  rw [L_X, op_ι]

private example (x y : ι) :
    sym (fword [x, y]) = MvPolynomial.X x * MvPolynomial.X y ∧
      sym (fword [y, x]) = MvPolynomial.X x * MvPolynomial.X y := by
  constructor
  · rw [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one]
  · rw [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one, mul_comm]

private example (g : ι → Module.End ℂ V)
    (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g)) (x y : ι) :
    g x * g y - admop g (admL (MvPolynomial.X x * MvPolynomial.X y)) ∈ lengthSpan g 1 := by
  have h := op_sub_op_L_sym_mem g hg (fword_mem_filt (l := [x, y]) (n := 2) le_rfl)
  rwa [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one, op_fword, wordOp_cons,
    wordOp_cons, wordOp_nil, mul_one] at h

end SymbolLemma

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial Matrix

private abbrev Letter : Type := admIdx ⊕ (Fin 3 × Fin 3)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def letters (e : Fin 3 → Fin 3 → Module.End ℂ V) : Letter → Module.End ℂ V
  | Sum.inl v => (2⁻¹ : ℂ) • (e v.1.1 v.1.2 + e v.1.2 v.1.1)
  | Sum.inr ij => e ij.1 ij.2 - e ij.2 ij.1

private theorem letters_inr (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) :
    letters e (Sum.inr (i, j)) = e i j - e j i := rfl

private def pIdx (a b : Fin 3) : admIdx := if h : a ≤ b then ⟨(a, b), h⟩ else ⟨(b, a), le_of_not_ge h⟩

private theorem Y_eq_X_pIdx (a b : Fin 3) : admY a b = X (pIdx a b) := by
  unfold admY pIdx
  simp only [Matrix.of_apply]
  split_ifs <;> rfl

private theorem letters_inl_pIdx (e : Fin 3 → Fin 3 → Module.End ℂ V) (a b : Fin 3) :
    letters e (Sum.inl (pIdx a b)) = (2⁻¹ : ℂ) • (e a b + e b a) := by
  unfold pIdx
  split_ifs
  · rfl
  · show (2⁻¹ : ℂ) • (e b a + e a b) = _
    rw [add_comm]

private def admfe (i j : Fin 3) : FreeAlgebra ℂ Letter :=
  FreeAlgebra.ι ℂ (Sum.inl (pIdx i j) : Letter) + (2⁻¹ : ℂ) • FreeAlgebra.ι ℂ (Sum.inr (i, j) : Letter)

private theorem op_fe (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) : admop (letters e) (admfe i j) = e i j := by
  rw [admfe, map_add, map_smul, op_ι, op_ι, letters_inl_pIdx, letters_inr]
  module

private def admproj : MvPolynomial Letter ℂ →ₐ[ℂ] admP :=
  aeval (Sum.elim (fun v : admIdx => (X v : admP)) fun _ : Fin 3 × Fin 3 => (0 : admP))

private theorem proj_X_inl (v : admIdx) : admproj (X (Sum.inl v : Letter)) = X v := by
  simp [admproj]

private theorem proj_X_inr (ij : Fin 3 × Fin 3) : admproj (X (Sum.inr ij : Letter)) = 0 := by
  simp [admproj]

private def admemb : admP →ₐ[ℂ] MvPolynomial Letter ℂ := rename Sum.inl

private theorem emb_X (v : admIdx) : admemb (X v) = X (Sum.inl v : Letter) := by
  simp [admemb]

private theorem proj_emb (s : admP) : admproj (admemb s) = s := by
  simp only [admproj, admemb, aeval_rename]
  exact aeval_X_left_apply s

private def psym : FreeAlgebra ℂ Letter →ₐ[ℂ] admP := admproj.comp sym

private theorem psym_ι_inl (v : admIdx) : psym (FreeAlgebra.ι ℂ (Sum.inl v : Letter)) = X v := by
  rw [psym, AlgHom.comp_apply, sym_ι, proj_X_inl]

private theorem psym_ι_inr (ij : Fin 3 × Fin 3) : psym (FreeAlgebra.ι ℂ (Sum.inr ij : Letter)) = 0 := by
  rw [psym, AlgHom.comp_apply, sym_ι, proj_X_inr]

private theorem psym_fe (i j : Fin 3) : psym (admfe i j) = admY i j := by
  rw [admfe, map_add, map_smul, psym_ι_inl, psym_ι_inr, smul_zero, add_zero, Y_eq_X_pIdx]

private theorem map_cas {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (e : Fin 3 → Fin 3 → A) (n : ℕ) :
    φ (cas e n) = cas (fun i j => φ (e i j)) n := by
  have h1 : (admgen e ^ n).map φ = admgen (fun i j => φ (e i j)) ^ n := by
    have h := map_pow φ.mapMatrix (admgen e) n
    simp only [RingHom.mapMatrix_apply] at h
    rw [h]
    congr 1
  unfold cas
  simp only [Matrix.trace, Matrix.diag, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := congrFun (congrFun h1 a) a
  rw [Matrix.map_apply] at this
  exact this

private theorem op_cas (e : Fin 3 → Fin 3 → Module.End ℂ V) (k : ℕ) : admop (letters e) (cas admfe k) = cas e k := by
  have h := map_cas (admop (letters e)).toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, op_fe] at h
  exact h

private theorem psym_cas (k : ℕ) : psym (cas admfe k) = (admY ^ k).trace := by
  have h := map_cas psym.toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, psym_fe] at h
  rw [h]
  unfold cas
  congr 2

private theorem ι_mem_filt_one (x : Letter) : FreeAlgebra.ι ℂ x ∈ filt 1 := by
  have h := fword_mem_filt (l := [x]) (n := 1) le_rfl
  simpa [fword] using h

private theorem filt_mono' {m n : ℕ} (h : m ≤ n) : (filt m : Submodule ℂ (FreeAlgebra ℂ Letter)) ≤ filt n :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

private theorem one_mem_filt (n : ℕ) : (1 : FreeAlgebra ℂ Letter) ∈ filt n := by
  have h := fword_mem_filt (l := ([] : List Letter)) (n := n) (Nat.zero_le n)
  simpa [fword] using h

private theorem fe_mem_filt (i j : Fin 3) : admfe i j ∈ filt 1 :=
  add_mem (ι_mem_filt_one _) (Submodule.smul_mem _ _ (ι_mem_filt_one _))

private theorem mul_mem_filt {m n : ℕ} {a b : FreeAlgebra ℂ Letter} (ha : a ∈ filt m) (hb : b ∈ filt n) :
    a * b ∈ filt (m + n) := by
  rw [filt] at hb
  induction hb using Submodule.span_induction with
  | mem b h =>
    obtain ⟨l, hl, rfl⟩ := h
    exact filt_mono' (by omega) (mem_filt_mul_fword ha l)
  | zero => simp
  | add b c _ _ hb hc =>
    rw [mul_add]
    exact add_mem hb hc
  | smul z b _ hb =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hb

private theorem gen_fe_pow_entry_mem_filt (k : ℕ) (a b : Fin 3) : (admgen admfe ^ k) a b ∈ filt k := by
  induction k generalizing a b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact one_mem_filt 0
    · exact zero_mem _
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Submodule.sum_mem _ fun c _ => mul_mem_filt (ih a c) (fe_mem_filt c b)

private theorem cas_mem_filt (k : ℕ) : cas admfe k ∈ filt k := by
  unfold cas
  exact Submodule.sum_mem _ fun a _ => gen_fe_pow_entry_mem_filt k a a

private theorem isHomogeneous_sym_fe (i j : Fin 3) : (sym (admfe i j)).IsHomogeneous 1 := by
  rw [admfe, map_add, map_smul, sym_ι, sym_ι]
  refine (isHomogeneous_X ℂ _).add ?_
  rw [smul_eq_C_mul]
  simpa using (isHomogeneous_C Letter (2⁻¹ : ℂ)).mul (isHomogeneous_X ℂ (Sum.inr (i, j) : Letter))

private theorem isHomogeneous_pow_entry {σ : Type*} (M : Matrix (Fin 3) (Fin 3) (MvPolynomial σ ℂ))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) (k : ℕ) (a b : Fin 3) : ((M ^ k) a b).IsHomogeneous k := by
  induction k generalizing a b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact isHomogeneous_one σ ℂ
    · exact isHomogeneous_zero σ ℂ 0
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact IsHomogeneous.sum _ _ _ fun c _ => (ih a c).mul (hM c b)

private theorem isHomogeneous_gen_pow_entry (f : Fin 3 → Fin 3 → MvPolynomial Letter ℂ)
    (hf : ∀ i j, (f i j).IsHomogeneous 1) (k : ℕ) (a b : Fin 3) : ((admgen f ^ k) a b).IsHomogeneous k :=
  isHomogeneous_pow_entry (admgen f) (fun i j => hf i j) k a b

private theorem isHomogeneous_sym_cas (k : ℕ) : (sym (cas admfe k)).IsHomogeneous k := by
  have h := map_cas sym.toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  unfold cas
  exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_gen_pow_entry _ isHomogeneous_sym_fe k a a

private def tw (k : Fin 3) : ℕ := (k : ℕ) + 1

private theorem weight_tw (α : Fin 3 →₀ ℕ) : Finsupp.weight tw α = α 0 * 1 + α 1 * 2 + α 2 * 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [Fin.sum_univ_three, tw]
  · intro i
    simp

private theorem isHomogeneous_Y_entry (a b : Fin 3) : (admY a b).IsHomogeneous 1 := by
  rw [Y_eq_X_pIdx]
  exact isHomogeneous_X ℂ _

private theorem isHomogeneous_traces (k : Fin 3) : (traces k).IsHomogeneous (tw k) := by
  unfold traces tw
  exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_pow_entry admY isHomogeneous_Y_entry _ a a

private theorem aeval_traces_monomial_one (α : Fin 3 →₀ ℕ) :
    aeval traces (monomial α (1 : ℂ)) = traces 0 ^ α 0 * traces 1 ^ α 1 * traces 2 ^ α 2 := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]

private theorem isHomogeneous_aeval_traces_monomial (α : Fin 3 →₀ ℕ) (c : ℂ) :
    (aeval traces (monomial α c)).IsHomogeneous (Finsupp.weight tw α) := by
  have hc : (monomial α c : MvPolynomial (Fin 3) ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul, smul_eq_C_mul, aeval_traces_monomial_one, weight_tw]
  have h := ((isHomogeneous_C admIdx c).mul
    ((((isHomogeneous_traces 0).pow (α 0)).mul ((isHomogeneous_traces 1).pow (α 1))).mul
      ((isHomogeneous_traces 2).pow (α 2))))
  convert h using 1
  simp [tw]
  ring

private theorem isHomogeneous_aeval_traces_of_isWeightedHomogeneous {G : MvPolynomial (Fin 3) ℂ} {m : ℕ}
    (hG : IsWeightedHomogeneous tw G m) : (aeval traces G).IsHomogeneous m := by
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun α hα => ?_
  have h := isHomogeneous_aeval_traces_monomial α (coeff α G)
  rwa [hG (mem_support_iff.1 hα)] at h

private theorem exists_isWeightedHomogeneous_aeval_traces_eq {n : ℕ} {s : admP} (hs : s.IsHomogeneous n)
    (hD : ∀ i j : Fin 3, admD i j s = 0) :
    ∃ G : MvPolynomial (Fin 3) ℂ, IsWeightedHomogeneous tw G n ∧ aeval traces G = s := by
  obtain ⟨G, hG⟩ := exists_eq_aeval_traces hD
  refine ⟨weightedHomogeneousComponent tw n G, weightedHomogeneousComponent_isWeightedHomogeneous n G, ?_⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := tw) G
  have hsum : s = ∑ m ∈ hfin.toFinset, aeval traces (weightedHomogeneousComponent tw m G) := by
    conv_lhs => rw [hG, ← sum_weightedHomogeneousComponent tw G, finsum_eq_sum _ hfin, map_sum]
  have hcomp : homogeneousComponent n s = s :=
    (homogeneousComponent_of_mem ((mem_homogeneousSubmodule n s).2 hs)).trans (if_pos rfl)
  have hterm : ∀ m, homogeneousComponent n (aeval traces (weightedHomogeneousComponent tw m G)) =
      if n = m then aeval traces (weightedHomogeneousComponent tw m G) else 0 := fun m =>
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule m _).2
      (isHomogeneous_aeval_traces_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous m G)))
  have hkey : s = if n ∈ hfin.toFinset then aeval traces (weightedHomogeneousComponent tw n G) else 0 := by
    conv_lhs => rw [← hcomp, hsum, map_sum]
    simp only [hterm]
    rw [Finset.sum_ite_eq]
  by_cases hn : n ∈ hfin.toFinset
  · rw [hkey, if_pos hn]
  · have hzero : weightedHomogeneousComponent tw n G = 0 := by
      have h' := hn
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h'
      exact h'
    rw [hkey, if_neg hn, hzero, map_zero]

section OnF

variable (e : Fin 3 → Fin 3 → Module.End ℂ V) (F : Submodule ℂ V)

private def QF (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ w : List Letter, w.length ≤ n ∧ ∃ f ∈ F, wordOp (letters e) w f = v}

private theorem QF_mono {m n : ℕ} (h : m ≤ n) : QF e F m ≤ QF e F n :=
  Submodule.span_mono fun _ ⟨w, hw, hf⟩ => ⟨w, hw.trans h, hf⟩

private theorem wordOp_apply_mem_QF {w : List Letter} {n : ℕ} (hw : w.length ≤ n) {f : V} (hf : f ∈ F) :
    wordOp (letters e) w f ∈ QF e F n :=
  Submodule.subset_span ⟨w, hw, f, hf, rfl⟩

private theorem apply_mem_QF {n : ℕ} {T : Module.End ℂ V} (hT : T ∈ lengthSpan (letters e) n) {f : V} (hf : f ∈ F) :
    T f ∈ QF e F n := by
  rw [lengthSpan] at hT
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact wordOp_apply_mem_QF e F hw hf
  | zero => simp
  | add S T _ _ hS hT =>
    rw [LinearMap.add_apply]
    exact add_mem hS hT
  | smul z T _ hT =>
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ hT

variable {e F}
variable (hg : ∀ x y : Letter, letters e x * letters e y - letters e y * letters e x ∈
    Submodule.span ℂ (Set.range (letters e)))
variable (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0)
include hg hF

private theorem wordOp_apply_mem_QF_of_inr_mem {w : List Letter} {ij : Fin 3 × Fin 3} (hij : (Sum.inr ij : Letter) ∈ w)
    {f : V} (hf : f ∈ F) : wordOp (letters e) w f ∈ QF e F (w.length - 1) := by
  set x : Letter := Sum.inr ij with hx
  obtain ⟨s, t, hst⟩ := List.append_of_mem hij
  have hperm : w.Perm (s ++ t ++ [x]) := by
    rw [hst]
    exact List.perm_middle.trans (List.perm_append_singleton x (s ++ t)).symm
  have hlen : w.length ≤ w.length - 1 + 1 := by
    have := List.length_pos_of_mem hij
    omega
  have hsub := wordOp_sub_wordOp_mem_of_perm (letters e) hg hperm (w.length - 1) hlen
  have hzero : wordOp (letters e) (s ++ t ++ [x]) f = 0 := by
    rw [wordOp_append, wordOp_cons, wordOp_nil, mul_one, Module.End.mul_apply, hx, hF ij f hf, map_zero]
  have hw : wordOp (letters e) w f = (wordOp (letters e) w - wordOp (letters e) (s ++ t ++ [x])) f := by
    rw [LinearMap.sub_apply, hzero, sub_zero]
  rw [hw]
  exact apply_mem_QF e F hsub hf

private theorem op_L_monomial_apply_mem {μ : Letter →₀ ℕ} {ij : Fin 3 × Fin 3} (hμ : μ (Sum.inr ij) ≠ 0) {f : V}
    (hf : f ∈ F) : admop (letters e) (admL (monomial μ (1 : ℂ))) f ∈ QF e F (μ.degree - 1) := by
  rw [L_monomial, one_smul, op_fword]
  have hmem : (Sum.inr ij : Letter) ∈ reprWord μ := by
    rw [reprWord, Multiset.mem_toList]
    change (Sum.inr ij : Letter) ∈ Finsupp.toMultiset μ
    rw [Finsupp.mem_toMultiset]
    exact Finsupp.mem_support_iff.2 hμ
  have h := wordOp_apply_mem_QF_of_inr_mem hg hF hmem hf
  rwa [reprWord_length_eq] at h

omit hg hF in
private theorem proj_monomial_of_inr {μ : Letter →₀ ℕ} {ij : Fin 3 × Fin 3} (hμ : μ (Sum.inr ij) ≠ 0) :
    admproj (monomial μ (1 : ℂ)) = 0 := by
  show aeval _ (monomial μ (1 : ℂ)) = 0
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hμ) ?_
  simp [zero_pow hμ]

omit hg hF in
private theorem emb_proj_monomial_of_forall {μ : Letter →₀ ℕ} (hμ : ∀ ij : Fin 3 × Fin 3, μ (Sum.inr ij) = 0) :
    admemb (admproj (monomial μ (1 : ℂ))) = monomial μ 1 := by
  have key : ∀ x ∈ μ.support, admemb (admproj (X x)) = (X x : MvPolynomial Letter ℂ) := by
    intro x hx
    rcases x with v | ij
    · rw [proj_X_inl, emb_X]
    · exact absurd (hμ ij) (Finsupp.mem_support_iff.1 hx)
  rw [monomial_eq, map_one, one_mul, Finsupp.prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [map_pow, map_pow, key x hx]

private theorem op_L_sub_op_L_emb_proj_apply_mem {n : ℕ} {u : MvPolynomial Letter ℂ} (hu : u.IsHomogeneous n) {f : V}
    (hf : f ∈ F) : admop (letters e) (admL u) f - admop (letters e) (admL (admemb (admproj u))) f ∈ QF e F (n - 1) :=
        by
  let Θ : MvPolynomial Letter ℂ →ₗ[ℂ] V := LinearMap.applyₗ f ∘ₗ (admop (letters e)).toLinearMap ∘ₗ admL
  let Ψ : MvPolynomial Letter ℂ →ₗ[ℂ] V := Θ - Θ ∘ₗ admemb.toLinearMap ∘ₗ admproj.toLinearMap
  have hΨ : ∀ t : MvPolynomial Letter ℂ,
      Ψ t = admop (letters e) (admL t) f - admop (letters e) (admL (admemb (admproj t))) f := fun _ => rfl
  rw [← hΨ, u.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : μ.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hu (mem_support_iff.1 hμ)
  have hc : (monomial μ) (coeff μ u) = coeff μ u • (monomial μ (1 : ℂ) : MvPolynomial Letter ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [hΨ]
  by_cases hk : ∃ ij : Fin 3 × Fin 3, μ (Sum.inr ij) ≠ 0
  · obtain ⟨ij, hij⟩ := hk
    rw [proj_monomial_of_inr hij, map_zero, map_zero, map_zero, LinearMap.zero_apply, sub_zero, ← hdeg]
    exact op_L_monomial_apply_mem hg hF hij hf
  · push Not at hk
    rw [emb_proj_monomial_of_forall hk, sub_self]
    exact zero_mem _

omit hg hF in
private theorem pow_mem_filt {m : ℕ} {a : FreeAlgebra ℂ Letter} (ha : a ∈ filt m) (j : ℕ) : a ^ j ∈ filt (j * m) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_mul]
    exact one_mem_filt 0
  | succ j ih =>
    rw [pow_succ, add_mul, one_mul]
    exact mul_mem_filt ih ha

private def casMon (α : Fin 3 →₀ ℕ) : FreeAlgebra ℂ Letter := cas admfe 1 ^ α 0 * cas admfe 2 ^ α 1 * cas admfe 3 ^ α 2

omit hg hF in
private theorem casMon_mem_filt (α : Fin 3 →₀ ℕ) : casMon α ∈ filt (Finsupp.weight tw α) := by
  rw [weight_tw, casMon]
  exact mul_mem_filt (mul_mem_filt (pow_mem_filt (cas_mem_filt 1) _) (pow_mem_filt (cas_mem_filt 2) _))
    (pow_mem_filt (cas_mem_filt 3) _)

omit hg hF in
private theorem isHomogeneous_sym_casMon (α : Fin 3 →₀ ℕ) : (sym (casMon α)).IsHomogeneous (Finsupp.weight tw α) := by
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, weight_tw]
  have h := (((isHomogeneous_sym_cas 1).pow (α 0)).mul ((isHomogeneous_sym_cas 2).pow (α 1))).mul
    ((isHomogeneous_sym_cas 3).pow (α 2))
  convert h using 1
  ring

omit hg hF in
private theorem proj_sym_casMon (α : Fin 3 →₀ ℕ) : admproj (sym (casMon α)) = aeval traces (monomial α (1 : ℂ)) := by
  change psym (casMon α) = _
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, psym_cas, psym_cas, psym_cas, aeval_traces_monomial_one]
  simp [traces]

omit hg hF in
private theorem op_casMon (α : Fin 3 →₀ ℕ) :
    admop (letters e) (casMon α) = cas e 1 ^ α 0 * cas e 2 ^ α 1 * cas e 3 ^ α 2 := by
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, op_cas, op_cas, op_cas]

omit hg hF in
private theorem admpow_apply_mem {Z : Submodule ℂ V} {T : Module.End ℂ V} (hT : ∀ z ∈ Z, T z ∈ Z) (j : ℕ) {z : V}
    (hz : z ∈ Z) : (T ^ j) z ∈ Z := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hT _ ih

omit hg hF in

private theorem op_casMon_apply_mem {Z : Submodule ℂ V} (hFZ : F ≤ Z) (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z)
    (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z) (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z)
    (α : Fin 3 →₀ ℕ) {f : V} (hf : f ∈ F) : admop (letters e) (casMon α) f ∈ Z := by
  rw [op_casMon, Module.End.mul_apply, Module.End.mul_apply]
  exact admpow_apply_mem hZ₁ _ (admpow_apply_mem hZ₂ _ (admpow_apply_mem hZ₃ _ (hFZ hf)))

private theorem op_L_emb_aeval_traces_monomial_apply_mem {Z : Submodule ℂ V} (hFZ : F ≤ Z)
    (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z) (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z)
    (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z) (α : Fin 3 →₀ ℕ) {f : V} (hf : f ∈ F) :
    admop (letters e) (admL (admemb (aeval traces (monomial α (1 : ℂ))))) f ∈ Z ⊔ QF e F (Finsupp.weight tw α - 1) :=
        by
  have h1 : admop (letters e) (casMon α) f ∈ Z ⊔ QF e F (Finsupp.weight tw α - 1) :=
    Submodule.mem_sup_left (op_casMon_apply_mem hFZ hZ₁ hZ₂ hZ₃ α hf)
  have h2 : (admop (letters e) (casMon α) - admop (letters e) (admL (sym (casMon α)))) f ∈
      Z ⊔ QF e F (Finsupp.weight tw α - 1) :=
    Submodule.mem_sup_right (apply_mem_QF e F (op_sub_op_L_sym_mem (letters e) hg (casMon_mem_filt α)) hf)
  have h3 := Submodule.mem_sup_right (S := Z)
    (op_L_sub_op_L_emb_proj_apply_mem hg hF (isHomogeneous_sym_casMon α) hf)
  rw [← proj_sym_casMon]
  have hid : admop (letters e) (admL (admemb (admproj (sym (casMon α))))) f =
      admop (letters e) (casMon α) f - (admop (letters e) (casMon α) - admop (letters e) (admL (sym (casMon α)))) f -
        (admop (letters e) (admL (sym (casMon α))) f - admop (letters e) (admL (admemb (admproj (sym (casMon α))))) f)
            := by
    rw [LinearMap.sub_apply]
    abel
  rw [hid]
  exact sub_mem (sub_mem h1 h2) h3

private theorem op_L_emb_apply_mem_of_invariant {Z : Submodule ℂ V} (hFZ : F ≤ Z)
    (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z) (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z)
    (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z) {n : ℕ} {s : admP} (hs : s.IsHomogeneous n)
    (hD : ∀ i j : Fin 3, admD i j s = 0)
    {f : V} (hf : f ∈ F) : admop (letters e) (admL (admemb s)) f ∈ Z ⊔ QF e F (n - 1) := by
  obtain ⟨G, hG, rfl⟩ := exists_isWeightedHomogeneous_aeval_traces_eq hs hD
  let Θ : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] V :=
    LinearMap.applyₗ f ∘ₗ (admop (letters e)).toLinearMap ∘ₗ admL ∘ₗ admemb.toLinearMap ∘ₗ (aeval traces).toLinearMap
  have hΘ : ∀ H : MvPolynomial (Fin 3) ℂ, Θ H = admop (letters e) (admL (admemb (aeval traces H))) f := fun _ => rfl
  rw [← hΘ, G.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hc : (monomial α) (coeff α G) = coeff α G • (monomial α (1 : ℂ) : MvPolynomial (Fin 3) ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [hΘ, ← hG (mem_support_iff.1 hα)]
  exact op_L_emb_aeval_traces_monomial_apply_mem hg hF hFZ hZ₁ hZ₂ hZ₃ α hf

end OnF

private example : ∃ G : MvPolynomial (Fin 3) ℂ, IsWeightedHomogeneous tw G 2 ∧ aeval traces G = (admY ^ 2).trace :=
  exists_isWeightedHomogeneous_aeval_traces_eq
    (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_pow_entry admY isHomogeneous_Y_entry 2 a a)
    (fun i j => D_trace_Y_pow i j 2)

private example (e : Fin 3 → Fin 3 → Module.End ℂ V) :
    admop (letters e) (casMon (Finsupp.single 0 1 + Finsupp.single 2 1)) = cas e 1 * cas e 3 := by
  rw [op_casMon]
  simp

private example (i j : Fin 3) : psym (admfe i j) = psym (admfe j i) := by
  rw [psym_fe, psym_fe, Y_symm]

end Adm0

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def admcm (a b : Module.End ℂ V) : Module.End ℂ V := a * b - b * a

private theorem cm_add_left (a a' b : Module.End ℂ V) : admcm (a + a') b = admcm a b + admcm a' b := by
  simp only [admcm, add_mul, mul_add]
  abel

private theorem cm_add_right (a b b' : Module.End ℂ V) : admcm a (b + b') = admcm a b + admcm a b' := by
  simp only [admcm, add_mul, mul_add]
  abel

private theorem cm_sub_left (a a' b : Module.End ℂ V) : admcm (a - a') b = admcm a b - admcm a' b := by
  simp only [admcm, sub_mul, mul_sub]
  abel

private theorem cm_sub_right (a b b' : Module.End ℂ V) : admcm a (b - b') = admcm a b - admcm a b' := by
  simp only [admcm, sub_mul, mul_sub]
  abel

private theorem cm_smul_left (z : ℂ) (a b : Module.End ℂ V) : admcm (z • a) b = z • admcm a b := by
  simp only [admcm, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem cm_smul_right (z : ℂ) (a b : Module.End ℂ V) : admcm a (z • b) = z • admcm a b := by
  simp only [admcm, smul_mul_assoc, mul_smul_comm, smul_sub]

private def LS (e : Fin 3 → Fin 3 → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ (Set.range (letters e))

private theorem e_mem_LS (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) : e i j ∈ LS e := by
  have h : e i j = letters e (Sum.inl (pIdx i j)) + (2⁻¹ : ℂ) • letters e (Sum.inr (i, j)) := by
    rw [letters_inl_pIdx, letters_inr]
    module
  rw [h]
  exact add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

section Table

variable {e : Fin 3 → Fin 3 → Module.End ℂ V} (he : admRel e)
include he

private theorem cm_e_mem_LS (a b c d : Fin 3) : admcm (e a b) (e c d) ∈ LS e := by
  rw [admcm, he]
  split_ifs
  · exact sub_mem (e_mem_LS e _ _) (e_mem_LS e _ _)
  · rw [sub_zero]
    exact e_mem_LS e _ _
  · rw [zero_sub]
    exact neg_mem (e_mem_LS e _ _)
  · rw [sub_self]
    exact zero_mem _

private theorem closure_letters (x y : Letter) :
    letters e x * letters e y - letters e y * letters e x ∈ Submodule.span ℂ (Set.range (letters e)) := by
  change admcm (letters e x) (letters e y) ∈ LS e
  rcases x with v | ⟨i, j⟩ <;> rcases y with w | ⟨k, l⟩ <;>
    simp only [letters, cm_add_left, cm_add_right, cm_sub_left, cm_sub_right, cm_smul_left, cm_smul_right] <;>
    repeat' first | exact cm_e_mem_LS he _ _ _ _ | apply add_mem | apply sub_mem | apply Submodule.smul_mem

end Table

private def ktab (i j : Fin 3) (kl : Fin 3 × Fin 3) : MvPolynomial Letter ℂ :=
  ((if j = kl.1 then X (Sum.inr (i, kl.2) : Letter) else 0) +
      (if i = kl.2 then X (Sum.inr (j, kl.1) : Letter) else 0)) -
    ((if j = kl.2 then X (Sum.inr (i, kl.1) : Letter) else 0) +
      (if i = kl.1 then X (Sum.inr (j, kl.2) : Letter) else 0))

private def rot (i j : Fin 3) : Derivation ℂ (MvPolynomial Letter ℂ) (MvPolynomial Letter ℂ) :=
  mkDerivation ℂ (Sum.elim (fun v : admIdx => admemb (-(admD i j (X v : admP)))) (ktab i j))

private theorem rot_X_inl (i j : Fin 3) (v : admIdx) : rot i j (X (Sum.inl v : Letter)) = admemb (-(admD i j (X v :
    admP))) := by
  rw [rot, mkDerivation_X]
  rfl

private theorem rot_X_inr (i j : Fin 3) (kl : Fin 3 × Fin 3) : rot i j (X (Sum.inr kl : Letter)) = ktab i j kl := by
  rw [rot, mkDerivation_X]
  rfl

private theorem pIdx_idx (v : admIdx) : pIdx v.1.1 v.1.2 = v := by
  unfold pIdx
  rw [dif_pos v.2]

private theorem X_idx_eq_Y (v : admIdx) : (X v : admP) = admY v.1.1 v.1.2 := by
  rw [Y_eq_X_pIdx, pIdx_idx]

private theorem emb_Y (c d : Fin 3) : admemb (admY c d) = X (Sum.inl (pIdx c d) : Letter) := by
  rw [Y_eq_X_pIdx, emb_X]

private theorem isHomogeneous_ite' {σ : Type*} (p : Prop) [Decidable p] {q : MvPolynomial σ ℂ}
    (hq : q.IsHomogeneous 1) : (if p then q else 0).IsHomogeneous 1 := by
  split_ifs
  · exact hq
  · exact isHomogeneous_zero σ ℂ 1

private theorem isHomogeneous_rot_X (i j : Fin 3) (x : Letter) : (rot i j (X x)).IsHomogeneous 1 := by
  rcases x with v | kl
  · rw [rot_X_inl]
    have h1 : (admD i j (X v : admP)).IsHomogeneous 1 := by
      rw [X_idx_eq_Y, D_Y_eq]
      exact ((isHomogeneous_ite' _ (isHomogeneous_Y_entry _ _)).sub
        (isHomogeneous_ite' _ (isHomogeneous_Y_entry _ _))).sub
        ((isHomogeneous_ite' _ (isHomogeneous_Y_entry _ _)).sub (isHomogeneous_ite' _ (isHomogeneous_Y_entry _ _)))
    exact h1.neg.rename_isHomogeneous (f := Sum.inl)
  · rw [rot_X_inr, ktab]
    exact ((isHomogeneous_ite' _ (isHomogeneous_X ℂ _)).add (isHomogeneous_ite' _ (isHomogeneous_X ℂ _))).sub
      ((isHomogeneous_ite' _ (isHomogeneous_X ℂ _)).add (isHomogeneous_ite' _ (isHomogeneous_X ℂ _)))

private theorem rot_emb (i j : Fin 3) (s : admP) : rot i j (admemb s) = admemb (-(admD i j s)) := by
  induction s using MvPolynomial.induction_on with
  | C c => simp only [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Derivation.map_algebraMap, neg_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, neg_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, emb_X, Derivation.leibniz, rot_X_inl, hp, Derivation.leibniz, neg_add, map_add, map_neg, map_neg,
      map_neg, map_neg, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul, emb_X]
    ring

section Brackets

variable {e : Fin 3 → Fin 3 → Module.End ℂ V} (he : admRel e)
include he

private theorem bracket_inl (i j a b : Fin 3) :
    letters e (Sum.inr (i, j)) * letters e (Sum.inl (pIdx a b)) -
        letters e (Sum.inl (pIdx a b)) * letters e (Sum.inr (i, j)) =
      admop (letters e) (admL (rot i j (X (Sum.inl (pIdx a b) : Letter)))) := by
  have he' : ∀ i j k l : Fin 3,
      e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0) := he
  change admcm _ _ = _
  rw [rot_X_inl, ← Y_eq_X_pIdx, D_Y_eq, letters_inr, letters_inl_pIdx, cm_sub_left, cm_smul_right, cm_smul_right,
    cm_add_right, cm_add_right]
  simp only [admcm, he', map_neg, map_sub, apply_ite admemb, apply_ite admL, apply_ite (admop (letters e)), map_zero,
      emb_Y, L_X,
    op_ι, letters_inl_pIdx]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> simp <;> module

private theorem bracket_inr (i j k l : Fin 3) :
    letters e (Sum.inr (i, j)) * letters e (Sum.inr (k, l)) - letters e (Sum.inr (k, l)) * letters e (Sum.inr (i, j)) =
      admop (letters e) (admL (rot i j (X (Sum.inr (k, l) : Letter)))) := by
  have he' : ∀ i j k l : Fin 3,
      e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0) := he
  change admcm _ _ = _
  rw [rot_X_inr, ktab, letters_inr, letters_inr, cm_sub_left, cm_sub_right, cm_sub_right]
  simp only [admcm, he', map_add, map_sub, apply_ite admL, apply_ite (admop (letters e)), map_zero, L_X, op_ι,
      letters_inr]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp <;> module

private theorem bracket_letter (i j : Fin 3) (x : Letter) :
    letters e (Sum.inr (i, j)) * letters e x - letters e x * letters e (Sum.inr (i, j)) =
      admop (letters e) (admL (rot i j (X x))) := by
  rcases x with v | ⟨k, l⟩
  · have h := bracket_inl he i j v.1.1 v.1.2
    rwa [pIdx_idx] at h
  · exact bracket_inr he i j k l

private theorem rot_bracket_mem (i j : Fin 3) {n : ℕ} {t : admP} (ht : t.IsHomogeneous n) :
    letters e (Sum.inr (i, j)) * admop (letters e) (admL (admemb t)) - admop (letters e) (admL (admemb t)) * letters e
        (Sum.inr (i, j)) +
        admop (letters e) (admL (admemb (admD i j t))) ∈ lengthSpan (letters e) (n - 1) := by
  have hemb : (admemb t).IsHomogeneous n := ht.rename_isHomogeneous (f := Sum.inl)
  have h := bracket_op_L_sub_mem (letters e) (rot i j) (letters e (Sum.inr (i, j))) (closure_letters he)
    (bracket_letter he i j) (isHomogeneous_rot_X i j) hemb
  rw [rot_emb, map_neg, map_neg, map_neg, sub_neg_eq_add] at h
  exact h

end Brackets

private example : rot 0 1 (X (Sum.inl (pIdx 0 0) : Letter)) = -((2 : ℂ) • X (Sum.inl (pIdx 0 1) : Letter)) := by
  rw [rot_X_inl, ← Y_eq_X_pIdx, D_Y_eq]
  simp [emb_Y, Y_symm, two_smul]

private example : rot 0 1 (X (Sum.inr (1, 2) : Letter)) = X (Sum.inr (0, 2) : Letter) := by
  rw [rot_X_inr, ktab]
  simp

end Adm0

end CarryC8b

namespace FischerForm

open MvPolynomial Finset

variable {σ : Type*}

private def wt (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

private theorem wt_pos (α : σ →₀ ℕ) : 0 < wt α := by
  unfold wt Finsupp.prod
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

section Form

variable [DecidableEq σ]

private def admform (p q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ p.support ∪ q.support, (wt α : ℂ) * p.coeff α * star (q.coeff α)

private theorem form_eq_sum {p q : MvPolynomial σ ℂ} {S : Finset (σ →₀ ℕ)} (hS : p.support ∪ q.support ⊆ S) :
    admform p q = ∑ α ∈ S, (wt α : ℂ) * p.coeff α * star (q.coeff α) := by
  unfold admform
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [Finset.mem_union, not_or] at hα
  rw [notMem_support_iff.1 hα.1]
  simp

private theorem form_lin (z : ℂ) (p₁ p₂ q : MvPolynomial σ ℂ) :
    admform (z • p₁ + p₂) q = z * admform p₁ q + admform p₂ q := by
  set S : Finset (σ →₀ ℕ) := (z • p₁ + p₂).support ∪ p₁.support ∪ p₂.support ∪ q.support with hSdef
  have h₀ : (z • p₁ + p₂).support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  have h₁ : p₁.support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  have h₂ : p₂.support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  rw [form_eq_sum h₀, form_eq_sum h₁, form_eq_sum h₂, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add, coeff_smul, smul_eq_mul]
  ring

private theorem form_symm (p q : MvPolynomial σ ℂ) : admform q p = star (admform p q) := by
  unfold admform
  rw [star_sum, Finset.union_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [star_mul, star_mul, star_star, star_natCast]
  ring

private theorem form_pos {p : MvPolynomial σ ℂ} (hp : p ≠ 0) : 0 < (admform p p).re := by
  unfold admform
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ α : σ →₀ ℕ,
      ((wt α : ℂ) * p.coeff α * star (p.coeff α)).re = (wt α : ℝ) * Complex.normSq (p.coeff α) := by
    intro α
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  simp only [hterm]
  obtain ⟨α, hα⟩ : p.support.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h => hp (support_eq_empty.1 h)
  refine Finset.sum_pos' (fun β _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) ⟨α, hα, ?_⟩
  exact mul_pos (Nat.cast_pos.2 (wt_pos α)) (Complex.normSq_pos.2 (mem_support_iff.1 hα))

private theorem form_zero_left (q : MvPolynomial σ ℂ) : admform (0 : MvPolynomial σ ℂ) q = 0 := by
  unfold admform
  simp

private theorem form_add_left (p₁ p₂ q : MvPolynomial σ ℂ) : admform (p₁ + p₂) q = admform p₁ q + admform p₂ q := by
  simpa using form_lin 1 p₁ p₂ q

private theorem form_smul_left (z : ℂ) (p q : MvPolynomial σ ℂ) : admform (z • p) q = z * admform p q := by
  simpa [form_zero_left] using form_lin z p 0 q

private theorem form_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    admform (∑ i ∈ s, f i) q = ∑ i ∈ s, admform (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih]

private theorem form_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ ℂ) (g : ι → MvPolynomial σ ℂ) :
    admform p (∑ i ∈ s, g i) = ∑ i ∈ s, admform p (g i) := by
  rw [form_symm, form_sum_left, star_sum]
  exact Finset.sum_congr rfl fun i _ => (form_symm (g i) p).symm

private theorem form_smul_right (z : ℂ) (p q : MvPolynomial σ ℂ) : admform p (z • q) = star z * admform p q := by
  rw [form_symm, form_smul_left, star_mul', ← form_symm]

private theorem form_monomial (γ β : σ →₀ ℕ) (c d : ℂ) :
    admform (monomial γ c) (monomial β d) = if γ = β then (wt β : ℂ) * c * star d else 0 := by
  have hS : (monomial γ c).support ∪ (monomial β d).support ⊆ {γ, β} := by
    refine Finset.union_subset ?_ ?_
    · exact support_monomial_subset.trans (by simp)
    · exact support_monomial_subset.trans (by simp)
  rw [form_eq_sum hS]
  by_cases hγβ : γ = β
  · subst hγβ
    simp [coeff_monomial]
  · rw [Finset.sum_pair hγβ, if_neg hγβ]
    simp [coeff_monomial, hγβ, Ne.symm hγβ]

end Form

private theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    homogeneousSubmodule σ ℂ n ≤ restrictTotalDegree σ ℂ n := by
  intro p hp
  rw [mem_restrictTotalDegree]
  by_cases h0 : p = 0
  · simp [h0]
  · exact ((mem_homogeneousSubmodule n p).1 hp).totalDegree h0 |>.le

section Der

variable [Fintype σ]

private def admder (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ∑ i : σ, ∑ j : σ, A i j • (LinearMap.mulLeft ℂ (X j : MvPolynomial σ ℂ)).comp (pderiv i).toLinearMap

private theorem der_apply (A : σ → σ → ℂ) (p : MvPolynomial σ ℂ) :
    admder A p = ∑ i : σ, ∑ j : σ, A i j • (X j * pderiv i p) := by
  simp [admder]

private theorem der_monomial_isHomogeneous (A : σ → σ → ℂ) (α : σ →₀ ℕ) (c : ℂ) :
    (admder A (monomial α c)).IsHomogeneous α.degree := by
  rw [der_apply]
  refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ => ?_
  rw [smul_eq_C_mul]
  refine (zero_add α.degree) ▸ (isHomogeneous_C σ (A i j)).mul ?_
  rw [pderiv_monomial]
  by_cases hi : α i = 0
  · simp [hi]
    exact isHomogeneous_zero σ ℂ _
  · have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hi
    have hdeg : (1 : ℕ) + (α - Finsupp.single i 1).degree = α.degree := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single, add_comm]
    rw [← hdeg]
    exact (isHomogeneous_X ℂ j).mul (isHomogeneous_monomial _ rfl)

private theorem der_mem_homogeneousSubmodule (A : σ → σ → ℂ) {n : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ homogeneousSubmodule σ ℂ n) : admder A p ∈ homogeneousSubmodule σ ℂ n := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : α.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.1 hα)
  rw [mem_homogeneousSubmodule, ← hd]
  exact der_monomial_isHomogeneous A α _

private scoped instance finiteDimensional_homogeneousSubmodule (n : ℕ) :
    FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

private theorem der_monomial (A : σ → σ → ℂ) (α : σ →₀ ℕ) (c : ℂ) :
    admder A (monomial α c) =
      ∑ i : σ, ∑ j : σ, A i j • monomial (Finsupp.single j 1 + (α - Finsupp.single i 1)) (c * (α i : ℂ)) := by
  rw [der_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end Der

section Skew

variable [Fintype σ] [DecidableEq σ]

private theorem wt_add_single (γ : σ →₀ ℕ) (i : σ) : wt (γ + Finsupp.single i 1) = (γ i + 1) * wt γ := by
  unfold wt
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  have h : ∀ k : σ,
      ((γ + Finsupp.single i 1 : σ →₀ ℕ) k).factorial = (if k = i then γ i + 1 else 1) * (γ k).factorial := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [Nat.factorial_succ]
    · simp [hk]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

private theorem ite_weight_swap (α β : σ →₀ ℕ) (i j : σ) :
    (if Finsupp.single j 1 + (α - Finsupp.single i 1) = β then (wt β : ℂ) * (α i : ℂ) else 0) =
      if α = Finsupp.single i 1 + (β - Finsupp.single j 1) then (wt α : ℂ) * (β j : ℂ) else 0 := by
  by_cases hαi : α i = 0
  · have hR : α ≠ Finsupp.single i 1 + (β - Finsupp.single j 1) := by
      intro h
      have := congrArg (fun f : σ →₀ ℕ => f i) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      omega
    rw [if_neg hR, hαi]
    split_ifs <;> simp
  by_cases hβj : β j = 0
  · have hL : Finsupp.single j 1 + (α - Finsupp.single i 1) ≠ β := by
      intro h
      have := congrArg (fun f : σ →₀ ℕ => f j) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      omega
    rw [if_neg hL, hβj]
    split_ifs <;> simp

  obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single i 1 :=
    ⟨α - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hαi))).symm⟩
  obtain ⟨β', rfl⟩ : ∃ β', β = β' + Finsupp.single j 1 :=
    ⟨β - Finsupp.single j 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hβj))).symm⟩
  simp only [add_tsub_cancel_right]
  have hc₁ : (Finsupp.single j 1 + α' = β' + Finsupp.single j 1) ↔ α' = β' := by
    rw [add_comm]
    exact add_left_inj _
  have hc₂ : (α' + Finsupp.single i 1 = Finsupp.single i 1 + β') ↔ α' = β' := by
    rw [add_comm (Finsupp.single i 1) β']
    exact add_left_inj _
  simp only [hc₁, hc₂]
  by_cases h : α' = β'
  · subst h
    rw [if_pos rfl, if_pos rfl, wt_add_single, wt_add_single]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  · rw [if_neg h, if_neg h]

private theorem form_der_monomial {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (α β : σ →₀ ℕ) (c d : ℂ) :
    admform (admder A (monomial α c)) (monomial β d) = -admform (monomial α c) (admder A (monomial β d)) := by
  rw [der_monomial, der_monomial, form_sum_left, form_sum_right]
  simp only [form_sum_left, form_sum_right, form_smul_left, form_smul_right, form_monomial, hA]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hk := ite_weight_swap α β j i
  simp only [star_mul', star_natCast, neg_mul, neg_neg]
  split_ifs at hk ⊢ with h₁ h₂ h₃
  · rw [← h₂]
    linear_combination (A j i * c * star d) * hk
  · linear_combination (A j i * c * star d) * hk
  · rw [← h₃]
    linear_combination (A j i * c * star d) * hk
  · simp

private theorem form_der_skew {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (p q : MvPolynomial σ ℂ) :
    admform (admder A p) q = -admform p (admder A q) := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  conv_rhs => rw [p.as_sum, q.as_sum]
  rw [map_sum, form_sum_left, map_sum, form_sum_left]
  simp only [form_sum_right]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  exact form_der_monomial hA α β _ _

private theorem form_der_der_symm {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (p q : MvPolynomial σ ℂ) :
    admform (admder A (admder A p)) q = admform p (admder A (admder A q)) := by
  rw [form_der_skew hA, form_der_skew hA, neg_neg]

end Skew

private example [DecidableEq σ] (i : σ) : admform (X i ^ 2 : MvPolynomial σ ℂ) (X i ^ 2) = 2 := by
  have hX : (X i ^ 2 : MvPolynomial σ ℂ) = monomial (Finsupp.single i 2) 1 := by
    rw [X_pow_eq_monomial]
  rw [hX]
  unfold admform
  rw [Finset.union_self, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  unfold wt
  rw [Finsupp.prod_single_index (by simp)]
  simp [Nat.factorial]

private example [Fintype σ] [DecidableEq σ] (A : σ → σ → ℂ) (k : σ) :
    admder A (X k) = ∑ j : σ, A k j • (X j : MvPolynomial σ ℂ) := by
  rw [der_apply]
  simp only [pderiv_X, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp
  · intro i _ hik
    simp [Ne.symm hik]
  · intro h
    exact absurd (Finset.mem_univ k) h

end FischerForm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm"

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem form_zero_left (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    {n : W} (hn : n ∈ M₀) : B 0 n = 0 := by
  have h := hlin (-1) 0 M₀.zero_mem 0 M₀.zero_mem n hn
  rw [smul_zero, add_zero] at h
  linear_combination h

private def orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) : Submodule ℂ W where
  carrier := {w | w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0}
  add_mem' {a b} ha hb := ⟨M₀.add_mem ha.1 hb.1, fun n hn => by
    have h := hlin 1 a ha.1 b hb.1 n (hNM hn)
    rw [one_smul, one_mul, ha.2 n hn, hb.2 n hn, add_zero] at h
    exact h⟩
  zero_mem' := ⟨M₀.zero_mem, fun n hn => form_zero_left M₀ B hlin (hNM hn)⟩
  smul_mem' z a ha := ⟨M₀.smul_mem z ha.1, fun n hn => by
    have h := hlin z a ha.1 0 M₀.zero_mem n (hNM hn)
    rw [add_zero, ha.2 n hn, mul_zero, zero_add, form_zero_left M₀ B hlin (hNM hn)] at h
    exact h⟩

private theorem mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (w : W) : w ∈ orthoIn M₀ N B hlin hNM ↔ w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0 := Iff.rfl

private theorem orthoIn_mapsTo (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (admD : W → W) (hDM : ∀ w ∈ M₀, admD w ∈ M₀) (hDN : ∀ n ∈ N, admD n ∈ N)
    (hskew : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (admD w) w' = - B w (admD w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, admD w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hDM w hw.1, fun n hn => ?_⟩
  rw [hskew w hw.1 n (hNM hn), hw.2 (admD n) (hDN n hn), neg_zero]

private theorem orthoIn_mapsTo_of_isometry (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, ∃ n' ∈ N, T n' = n)
    (hTB : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) (T w') = B w w') :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hTM w hw.1, fun n hn => ?_⟩
  obtain ⟨n', hn', rfl⟩ := hTN n hn
  rw [hTB w hw.1 n' (hNM hn')]
  exact hw.2 n' hn'

private theorem eq_zero_of_mem_orthoIn {Z : Type*} [AddCommGroup Z] (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) (Λ : W → Z)
    (hker : ∀ w ∈ M₀, Λ w = 0 → w ∈ N) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, Λ w = 0 → w = 0 := by
  intro w hw hΛ
  by_contra hne
  have h := hpos w hw.1 hne
  rw [hw.2 w (hker w hw.1 hΛ), Complex.zero_re] at h
  exact lt_irrefl _ h

private theorem exists_ne_zero_mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] (hlt : N < M₀) :
    ∃ w ∈ orthoIn M₀ N B hlin hNM, w ≠ 0 := by
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNM

  let b := Module.finBasis ℂ N
  let φ : M₀ →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    { toFun := fun w i => B w (b i)
      map_add' := fun x y => by
        funext i
        have h := hlin 1 x x.2 y y.2 (b i) (hNM (b i).2)
        rw [one_smul, one_mul] at h
        simpa using h
      map_smul' := fun z x => by
        funext i
        have h := hlin z x x.2 0 M₀.zero_mem (b i) (hNM (b i).2)
        rw [add_zero, form_zero_left M₀ B hlin (hNM (b i).2), add_zero] at h
        simpa using h }

  have hker : ∀ x : M₀, φ x = 0 → (x : W) ∈ orthoIn M₀ N B hlin hNM := by
    intro x hx
    refine ⟨x.2, fun n hn => ?_⟩

    have hrepr : (⟨n, hn⟩ : N) = ∑ i, b.repr ⟨n, hn⟩ i • b i := (b.sum_repr ⟨n, hn⟩).symm
    have hn' : n = ∑ i, b.repr ⟨n, hn⟩ i • (b i : W) := by
      have := congrArg Subtype.val hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this

    have hsum : ∀ (s : Finset (Fin (Module.finrank ℂ N))),
        B (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) x = ∑ i ∈ s, b.repr ⟨n, hn⟩ i * B (b i) x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact form_zero_left M₀ B hlin x.2
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        have hmem : (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) ∈ M₀ :=
          M₀.sum_mem fun i _ => M₀.smul_mem _ (hNM (b i).2)
        exact hlin _ _ (hNM (b j).2) _ hmem x x.2
    have hBn : B n x = ∑ i, b.repr ⟨n, hn⟩ i * B (b i) x := by
      conv_lhs => rw [hn']
      exact hsum Finset.univ
    rw [hsymm n (hNM hn) x x.2, hBn]
    have hzero : (∑ i, b.repr ⟨n, hn⟩ i * B (b i) x) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : B (b i) x = 0 := by
        rw [hsymm x x.2 (b i) (hNM (b i).2)]
        have := congrFun hx i
        simp only [Pi.zero_apply] at this
        change B x (b i) = 0 at this
        rw [this, map_zero]
      rw [hi, mul_zero]
    rw [hzero, map_zero]

  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ N := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ N) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ N := by simp
  have hlt' : Module.finrank ℂ N < Module.finrank ℂ M₀ := Submodule.finrank_lt_finrank_of_lt hlt
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker φ) := by omega
  have hnebot : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnebot
  exact ⟨(x : W), hker x (LinearMap.mem_ker.1 hx), fun h => hx0 (Subtype.ext h)⟩

private theorem eq_zero_of_mem_inf_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) {w : W} (hwN : w ∈ N) (hwP : w ∈ orthoIn M₀ N B hlin hNM) : w = 0 := by
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hwP
  by_contra hne
  have h := hpos w hwM hne
  rw [hperp w hwN, Complex.zero_re] at h
  exact lt_irrefl _ h

private theorem sup_orthoIn_eq (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] :
    N ⊔ orthoIn M₀ N B hlin hNM = M₀ := by
  have hPM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  refine le_antisymm (sup_le hNM hPM) ?_
  by_contra hcon
  have hlt : N ⊔ orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne (sup_le hNM hPM) fun h => hcon h.ge
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_orthoIn M₀ (N ⊔ orthoIn M₀ N B hlin hNM) B hlin hsymm
    (sup_le hNM hPM) hlt
  obtain ⟨hwM, hwperp⟩ := (mem_orthoIn M₀ _ B hlin (sup_le hNM hPM) w).1 hw
  have hwP : w ∈ orthoIn M₀ N B hlin hNM :=
    (mem_orthoIn M₀ N B hlin hNM w).2 ⟨hwM, fun n hn => hwperp n (Submodule.mem_sup_left hn)⟩
  have hself : B w w = 0 := hwperp w (Submodule.mem_sup_right hwP)
  have := hpos w hwM hw0
  rw [hself, Complex.zero_re] at this
  exact lt_irrefl _ this

private theorem orthoIn_mapsTo_comp (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T₁ T₂ : W → W)
    (h₁ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ w ∈ orthoIn M₀ N B hlin hNM)
    (h₂ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₂ w ∈ orthoIn M₀ N B hlin hNM) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ (T₂ w) ∈ orthoIn M₀ N B hlin hNM :=
  fun w hw => h₁ _ (h₂ w hw)

private theorem exists_mem_orthoIn_map_eq_of_killed {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    [FiniteDimensional ℂ M₀] (Φ : W →ₗ[ℂ] Z) (δ : W → W) (δ' : Z → Z)
    (hδM : ∀ x ∈ M₀, δ x ∈ M₀)
    (hδP : ∀ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right,
      δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right)
    (hcomm : ∀ x ∈ M₀, Φ (δ x) = δ' (Φ x))
    {v₀ : Z} (hv : ∃ y ∈ M₀, Φ y = v₀) (hkill : δ' v₀ = 0) :
    ∃ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right, Φ x = v₀ ∧ δ x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have hdec := sup_orthoIn_eq M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hsymm hpos inf_le_right
  rw [← hdec] at hy
  obtain ⟨n, hn, x, hx, rfl⟩ := Submodule.mem_sup.1 hy
  have hnK : Φ n = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hn).1
  have hxM : x ∈ M₀ := ((mem_orthoIn M₀ _ B hlin inf_le_right x).1 hx).1
  have hΦx : Φ x = Φ (n + x) := by rw [map_add, hnK, zero_add]
  refine ⟨x, hx, hΦx, ?_⟩
  have hδx : δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right := hδP x hx
  have hδK : δ x ∈ LinearMap.ker Φ ⊓ M₀ := by
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hδM x hxM⟩
    rw [hcomm x hxM, hΦx, hkill]
  exact eq_zero_of_mem_inf_orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hpos inf_le_right hδK hδx

private theorem exists_mem_orthoIn_map_eq_of_killed' {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (M₀ admE : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hEM : admE ≤ M₀) [FiniteDimensional ℂ admE] (Φ : W →ₗ[ℂ] Z) (δ : W → W) (δ' : Z → Z)
    (hδM : ∀ x ∈ M₀, δ x ∈ M₀)
    (hδP : ∀ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right,
      δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right)
    (hcomm : ∀ x ∈ M₀, Φ (δ x) = δ' (Φ x))
    (hproj : ∀ z ∈ LinearMap.ker Φ ⊓ M₀, ∃ e ∈ LinearMap.ker Φ ⊓ admE, ∀ x ∈ admE, B x z = B x e)
    {v₀ : Z} (hv : ∃ y ∈ admE, Φ y = v₀) (hkill : δ' v₀ = 0) :
    ∃ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right, Φ x = v₀ ∧ δ x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have hlinE : ∀ (z : ℂ), ∀ w₁ ∈ admE, ∀ w₂ ∈ admE, ∀ w' ∈ admE, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w' :=
    fun z w₁ h₁ w₂ h₂ w' h' => hlin z w₁ (hEM h₁) w₂ (hEM h₂) w' (hEM h')
  have hsymmE : ∀ w ∈ admE, ∀ w' ∈ admE, B w' w = (starRingEnd ℂ) (B w w') :=
    fun w hw w' hw' => hsymm w (hEM hw) w' (hEM hw')
  have hposE : ∀ w ∈ admE, w ≠ 0 → 0 < (B w w).re := fun w hw => hpos w (hEM hw)
  have hdec := sup_orthoIn_eq admE (LinearMap.ker Φ ⊓ admE) B hlinE hsymmE hposE inf_le_right
  rw [← hdec] at hy
  obtain ⟨n, hn, x, hx, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨hxE, hxperp⟩ := (mem_orthoIn admE _ B hlinE inf_le_right x).1 hx
  have hnK : Φ n = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hn).1
  have hΦx : Φ x = Φ (n + x) := by rw [map_add, hnK, zero_add]

  have hxW : x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right := by
    refine (mem_orthoIn M₀ _ B hlin inf_le_right x).2 ⟨hEM hxE, fun z hz => ?_⟩
    obtain ⟨e, he, hpair⟩ := hproj z hz
    rw [hpair x hxE]
    exact hxperp e he
  refine ⟨x, hxW, hΦx, ?_⟩
  have hδx := hδP x hxW
  have hδK : δ x ∈ LinearMap.ker Φ ⊓ M₀ := by
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hδM x (hEM hxE)⟩
    rw [hcomm x (hEM hxE), hΦx, hkill]
  exact eq_zero_of_mem_inf_orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hpos inf_le_right hδK hδx

private theorem orthoIn_mapsTo_of_symm (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, T n ∈ N)
    (hsym : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) w' = B w (T w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hw
  refine (mem_orthoIn M₀ N B hlin hNM (T w)).2 ⟨hTM w hwM, fun n hn => ?_⟩
  rw [hsym w hwM n (hNM hn)]
  exact hperp (T n) (hTN n hn)

private theorem exists_eigen_decomposition :
    ∀ (n : ℕ) (M₀ : Submodule ℂ W) [FiniteDimensional ℂ M₀], Module.finrank ℂ M₀ = n →
      ∀ (B : W → W → ℂ),
        (∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') →
        (∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w')) →
        (∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) →
        ∀ (Ω : W →ₗ[ℂ] W), (∀ w ∈ M₀, Ω w ∈ M₀) → (∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w')) →
          ∀ z ∈ M₀, ∃ (s : Finset ℂ) (f : ℂ → W),
            (∀ μ ∈ s, f μ ∈ M₀ ∧ Ω (f μ) = μ • f μ) ∧ z = ∑ μ ∈ s, f μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M₀ _ hn B hlin hsymm hpos Ω hΩM hΩsymm z hz
  by_cases hn0 : n = 0
  ·
    have hbot : M₀ = ⊥ := Submodule.finrank_eq_zero.1 (hn.trans hn0)
    rw [hbot] at hz
    refine ⟨∅, fun _ => 0, fun μ hμ => absurd hμ (by simp), ?_⟩
    rw [Finset.sum_empty]; exact (Submodule.mem_bot ℂ).1 hz

  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : Nontrivial M₀ := by
    rw [← Module.finrank_pos_iff (R := ℂ)]; omega
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Ω.restrict hΩM)
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hyW : Ω (y : W) = c • (y : W) := by
    have h := hy.apply_eq_smul
    have h' := congrArg Subtype.val h
    rw [LinearMap.restrict_apply] at h'
    simpa using h'
  have hy0 : (y : W) ≠ 0 := fun h => hy.2 (Subtype.ext h)

  set N : Submodule ℂ W := Submodule.span ℂ {(y : W)} with hNdef
  have hNM : N ≤ M₀ := by
    rw [hNdef, Submodule.span_le]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]; exact y.2
  have hNΩ : ∀ m ∈ N, Ω m ∈ N := by
    intro m hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [map_smul, hyW]
    exact N.smul_mem a (N.smul_mem c (Submodule.mem_span_singleton_self (y : W)))
  have hFM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  haveI : FiniteDimensional ℂ (orthoIn M₀ N B hlin hNM) := Submodule.finiteDimensional_of_le hFM
  have hyF : (y : W) ∉ orthoIn M₀ N B hlin hNM := by
    intro hyF
    have h := ((mem_orthoIn M₀ N B hlin hNM _).1 hyF).2 (y : W) (Submodule.mem_span_singleton_self _)
    have hp := hpos (y : W) y.2 hy0
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hFlt : orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne hFM fun h => hyF (by rw [h]; exact y.2)
  have hFrank : Module.finrank ℂ (orthoIn M₀ N B hlin hNM) < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hFlt

  have hdec := sup_orthoIn_eq M₀ N B hlin hsymm hpos hNM
  rw [← hdec] at hz
  obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm

  have hFΩ : ∀ w ∈ orthoIn M₀ N B hlin hNM, Ω w ∈ orthoIn M₀ N B hlin hNM :=
    orthoIn_mapsTo_of_symm M₀ N B hlin hNM Ω hΩM hNΩ hΩsymm
  obtain ⟨s, f, hf, hxsum⟩ := ih (Module.finrank ℂ (orthoIn M₀ N B hlin hNM)) hFrank
    (orthoIn M₀ N B hlin hNM) rfl B
    (fun z w₁ h₁ w₂ h₂ w' h' => hlin z w₁ (hFM h₁) w₂ (hFM h₂) w' (hFM h'))
    (fun w hw w' hw' => hsymm w (hFM hw) w' (hFM hw'))
    (fun w hw => hpos w (hFM hw)) Ω hFΩ
    (fun w hw w' hw' => hΩsymm w (hFM hw) w' (hFM hw')) x hx

  classical
  refine ⟨insert c s, fun μ => (if μ ∈ s then f μ else 0) + (if μ = c then a • (y : W) else 0), ?_, ?_⟩
  · intro μ hμ
    constructor
    · refine M₀.add_mem ?_ ?_
      · split_ifs with h
        · exact hFM (hf μ h).1
        · exact M₀.zero_mem
      · split_ifs with h
        · exact M₀.smul_mem a y.2
        · exact M₀.zero_mem
    · rw [map_add, smul_add]
      congr 1
      · split_ifs with h
        · exact (hf μ h).2
        · simp
      · split_ifs with h
        · rw [map_smul, hyW, h, smul_comm]
        · simp
  · rw [Finset.sum_add_distrib]
    have h1 : ∑ μ ∈ insert c s, (if μ ∈ s then f μ else 0) = ∑ μ ∈ s, f μ := by
      by_cases hcs : c ∈ s
      · rw [Finset.insert_eq_of_mem hcs]
        exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
      · rw [Finset.sum_insert hcs, if_neg hcs, zero_add]
        exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
    have h2 : ∑ μ ∈ insert c s, (if μ = c then a • (y : W) else 0) = a • (y : W) := by
      rw [Finset.sum_ite_eq' (insert c s) c]
      exact if_pos (Finset.mem_insert_self c s)
    rw [h1, h2, ← hxsum, add_comm]

end Piece
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm"

namespace S5Split

open Adm0 SymRestriction FischerForm MvPolynomial

private abbrev R9 : Type := MvPolynomial (Fin 3 × Fin 3) ℂ

private def a9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℤ :=
  (if x.1 = i ∧ y = (j, x.2) then 1 else 0) - (if x.1 = j ∧ y = (i, x.2) then 1 else 0) -
    (if x.2 = j ∧ y = (x.1, i) then 1 else 0) + (if x.2 = i ∧ y = (x.1, j) then 1 else 0)

private theorem a9_antisymm (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, a9 i j x y = -a9 i j y x := by
  fin_cases i <;> fin_cases j <;> decide

private def A9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℂ := (a9 i j x y : ℂ)

private theorem A9_skew (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, star (A9 i j x y) = -A9 i j y x := by
  intro x y
  rw [A9, A9, a9_antisymm i j x y]
  push_cast
  rw [star_neg, Complex.star_def, map_intCast]

private def D9 (i j : Fin 3) : R9 →ₗ[ℂ] R9 := FischerForm.admder (A9 i j)

private theorem D9_X (i j : Fin 3) (x : Fin 3 × Fin 3) :
    D9 i j (X x) = ∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) := by
  rw [D9, der_apply]
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [pderiv_X_self, mul_one]
  · intro a _ hax
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [pderiv_X_of_ne (Ne.symm hax), mul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

private theorem admder_mul {τ : Type*} [Fintype τ] (A : τ → τ → ℂ) (p q : MvPolynomial τ ℂ) :
    FischerForm.admder A (p * q) = p * FischerForm.admder A q + q * FischerForm.admder A p := by
  simp only [der_apply, Derivation.leibniz, smul_eq_mul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section Nine

variable (n : ℕ)

private abbrev M9 : Submodule ℂ R9 := homogeneousSubmodule (Fin 3 × Fin 3) ℂ n

private scoped instance : FiniteDimensional ℂ (M9 n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

private theorem D9_mem_M9 (i j : Fin 3) {r : R9} (hr : r ∈ M9 n) : D9 i j r ∈ M9 n :=
  der_mem_homogeneousSubmodule (A9 i j) hr

private def T9 : (Fin 3 × Fin 3 → M9 n) →ₗ[ℂ] R9 :=
  ∑ ij : Fin 3 × Fin 3, (D9 ij.1 ij.2).comp ((M9 n).subtype.comp (LinearMap.proj ij))

private theorem T9_apply (q : Fin 3 × Fin 3 → M9 n) : T9 n q = ∑ ij : Fin 3 × Fin 3, D9 ij.1 ij.2 (q ij : R9) := by
  simp [T9]

private abbrev N9 : Submodule ℂ R9 := LinearMap.range (T9 n)

private theorem N9_le_M9 : N9 n ≤ M9 n := by
  rintro _ ⟨q, rfl⟩
  rw [T9_apply]
  exact Submodule.sum_mem _ fun ij _ => D9_mem_M9 n ij.1 ij.2 (q ij).2

private theorem D9_mem_N9 (i j : Fin 3) {r : R9} (hr : r ∈ M9 n) : D9 i j r ∈ N9 n := by
  refine ⟨Pi.single (i, j) ⟨r, hr⟩, ?_⟩
  rw [T9_apply, Finset.sum_eq_single (i, j)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem hlin9 : ∀ (z : ℂ), ∀ w₁ ∈ M9 n, ∀ w₂ ∈ M9 n, ∀ w' ∈ M9 n,
    admform (z • w₁ + w₂) w' = z * admform w₁ w' + admform w₂ w' := by
  intro z w₁ _ w₂ _ w' _
  rw [form_add_left, form_smul_left]

private theorem hsymm9 : ∀ w ∈ M9 n, ∀ w' ∈ M9 n, admform w' w = (starRingEnd ℂ) (admform w w') := by
  intro w _ w' _
  rw [form_symm]
  rfl

private theorem hpos9 : ∀ w ∈ M9 n, w ≠ 0 → 0 < (admform w w).re := fun _ _ hw => form_pos hw

private theorem D9_eq_zero_of_mem_orthoIn {x : R9} (hx : x ∈ orthoIn (M9 n) (N9 n) admform (hlin9 n) (N9_le_M9 n))
    (i j : Fin 3) : D9 i j x = 0 := by
  obtain ⟨hxM, hperp⟩ := (mem_orthoIn _ _ _ _ _ x).1 hx
  by_contra hne
  have h1 : admform (D9 i j x) (D9 i j x) = -admform x (D9 i j (D9 i j x)) := form_der_skew (A9_skew i j) x (D9 i j x)
  have h2 : admform x (D9 i j (D9 i j x)) = 0 := hperp _ (D9_mem_N9 n i j (D9_mem_M9 n i j hxM))
  have h3 := form_pos hne
  rw [h1, h2, neg_zero] at h3
  simp at h3

private theorem exists_split9 {r : R9} (hr : r ∈ M9 n) :
    ∃ s ∈ M9 n, (∀ i j : Fin 3, D9 i j s = 0) ∧
      ∃ q : Fin 3 × Fin 3 → M9 n, r = s + ∑ ij : Fin 3 × Fin 3, D9 ij.1 ij.2 (q ij : R9) := by
  have hdec := sup_orthoIn_eq (M9 n) (N9 n) admform (hlin9 n) (hsymm9 n) (hpos9 n) (N9_le_M9 n)
  rw [← hdec] at hr
  obtain ⟨m, hm, s, hs, rfl⟩ := Submodule.mem_sup.1 hr
  obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hm
  refine ⟨s, ((mem_orthoIn _ _ _ _ _ s).1 hs).1, fun i j => D9_eq_zero_of_mem_orthoIn n hs i j, q, ?_⟩
  rw [T9_apply, add_comm]

end Nine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm"

section Six

private def toP : R9 →ₐ[ℂ] admP := rename fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2

private def ofP : admP →ₐ[ℂ] R9 := rename fun v : admIdx => v.1

private theorem toP_ofP (p : admP) : toP (ofP p) = p := by
  rw [toP, ofP, rename_rename]
  have h : ((fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2) ∘ fun v : admIdx => v.1) = id := funext fun v => pIdx_idx v
  rw [h, rename_id]
  rfl

private theorem toP_X (ab : Fin 3 × Fin 3) : toP (X ab) = admY ab.1 ab.2 := by
  rw [toP, rename_X, Y_eq_X_pIdx]

private theorem toP_isHomogeneous {n : ℕ} {r : R9} (hr : r ∈ M9 n) : (toP r).IsHomogeneous n :=
  ((mem_homogeneousSubmodule n r).1 hr).rename_isHomogeneous

private theorem toP_D9_X (i j : Fin 3) (ab : Fin 3 × Fin 3) : toP (D9 i j (X ab)) = admD i j (toP (X ab)) := by
  rw [D9_X, map_sum, toP_X, D_Y_eq]
  simp only [map_smul, toP_X]
  obtain ⟨a, b⟩ := ab
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [A9, a9, Fintype.sum_prod_type, Fin.sum_univ_three] <;> module

private theorem toP_D9 (i j : Fin 3) (r : R9) : toP (D9 i j r) = admD i j (toP r) := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    have h9 : D9 i j (C c : R9) = 0 := by
      rw [D9, der_apply]
      simp
    rw [h9, map_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    have hX := toP_D9_X i j x
    simp only [D9] at hp hX ⊢
    rw [admder_mul, map_add, map_mul, map_mul, hp, hX, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm]

private theorem exists_splitting {n : ℕ} {p : admP} (hp : p.IsHomogeneous n) :
    ∃ s : admP, s.IsHomogeneous n ∧ (∀ i j : Fin 3, admD i j s = 0) ∧
      ∃ q : Fin 3 × Fin 3 → admP, (∀ ij, (q ij).IsHomogeneous n) ∧ p = s + ∑ ij : Fin 3 × Fin 3, admD ij.1 ij.2 (q ij)
          := by
  have hr : ofP p ∈ M9 n := (mem_homogeneousSubmodule n _).2 (hp.rename_isHomogeneous (f := fun v : admIdx => v.1))
  obtain ⟨s, hsM, hsD, q, hq⟩ := exists_split9 n hr
  refine ⟨toP s, toP_isHomogeneous hsM, fun i j => by rw [← toP_D9, hsD i j, map_zero],
    fun ij => toP (q ij : R9), fun ij => toP_isHomogeneous (q ij).2, ?_⟩
  have h := congrArg toP hq
  rw [toP_ofP, map_add, map_sum] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun ij _ => toP_D9 ij.1 ij.2 _

end Six
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm"

private example : a9 0 1 (0, 0) (1, 0) = 1 ∧ a9 0 1 (0, 0) (0, 1) = 1 ∧ a9 0 1 (0, 0) (0, 0) = 0 := by decide

private example : toP (X (0, 1)) = toP (X (1, 0)) := by
  rw [toP_X, toP_X, Y_symm]

private example (v : admIdx) : toP (ofP (X v)) = X v := toP_ofP _

end S5Split
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace Induct

open SymbolLemma CasimirCentral SymRestriction Adm0 S5Split MvPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem isHomogeneous_wordSym (w : List Letter) :
    (wordSym w : MvPolynomial Letter ℂ).IsHomogeneous w.length := by
  induction w with
  | nil => exact isHomogeneous_one Letter ℂ
  | cons x w ih =>
    rw [wordSym_cons, List.length_cons, add_comm]
    exact (isHomogeneous_X ℂ x).mul ih

private theorem isHomogeneous_proj {n : ℕ} {u : MvPolynomial Letter ℂ} (hu : u.IsHomogeneous n) :
    (admproj u).IsHomogeneous n := by
  have h := hu.aeval (n := 1) (Sum.elim (fun v : admIdx => (X v : admP)) fun _ : Fin 3 × Fin 3 => (0 : admP)) fun x =>
      ?_
  · simp at h
    exact h
  · rcases x with v | ij
    · exact isHomogeneous_X ℂ v
    · exact isHomogeneous_zero admIdx ℂ 1

section Main

variable (e : Fin 3 → Fin 3 → Module.End ℂ V) (F : Submodule ℂ V)

private def Qall : Submodule ℂ V := ⨆ n : ℕ, QF e F n

private def KQ : Submodule ℂ V := ⨆ ij : Fin 3 × Fin 3, (Qall e F).map (letters e (Sum.inr ij))

variable {e F}

private theorem mem_Qall {n : ℕ} {y : V} (hy : y ∈ QF e F n) : y ∈ Qall e F := Submodule.mem_iSup_of_mem n hy

private theorem rot_apply_mem_KQ (ij : Fin 3 × Fin 3) {y : V} (hy : y ∈ Qall e F) :
    letters e (Sum.inr ij) y ∈ KQ e F :=
  Submodule.mem_iSup_of_mem ij (Submodule.mem_map_of_mem hy)

variable (he : admRel e) (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0) {Z : Submodule ℂ V}
  (hFZ : F ≤ Z) (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z) (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z) (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z)
include he hF hFZ hZ₁ hZ₂ hZ₃

omit hFZ hZ₁ hZ₂ hZ₃ in

private theorem op_L_emb_D_apply_mem {n : ℕ} {q : admP} (hq : q.IsHomogeneous (n + 1)) (i j : Fin 3) {f : V} (hf : f ∈
    F)
    (ih : QF e F n ≤ Z ⊔ KQ e F) : admop (letters e) (admL (admemb (admD i j q))) f ∈ Z ⊔ KQ e F := by
  set κ : Module.End ℂ V := letters e (Sum.inr (i, j)) with hκ
  set T : Module.End ℂ V := admop (letters e) (admL (admemb q)) with hT
  have hbr := rot_bracket_mem he i j hq
  rw [Nat.add_sub_cancel] at hbr

  have h1 : (κ * T - T * κ + admop (letters e) (admL (admemb (admD i j q)))) f ∈ QF e F n := apply_mem_QF e F hbr hf

  have hκf : κ f = 0 := hF (i, j) f hf

  have hTf : T f ∈ Qall e F := by
    refine mem_Qall (n := n + 1) (apply_mem_QF e F ?_ hf)
    exact op_mem_lengthSpan _ (L_mem_filt (hq.rename_isHomogeneous (f := Sum.inl)))
  have hexpand : admop (letters e) (admL (admemb (admD i j q))) f =
      (κ * T - T * κ + admop (letters e) (admL (admemb (admD i j q)))) f - κ (T f) := by
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, hκf, map_zero]
    abel
  rw [hexpand]
  exact sub_mem (ih h1) (Submodule.mem_sup_right (rot_apply_mem_KQ (i, j) hTf))

private theorem op_L_apply_mem {n : ℕ} {u : MvPolynomial Letter ℂ} (hu : u.IsHomogeneous (n + 1)) {f : V} (hf : f ∈ F)
    (ih : QF e F n ≤ Z ⊔ KQ e F) : admop (letters e) (admL u) f ∈ Z ⊔ KQ e F := by
  have hg := closure_letters he

  have hproj := op_L_sub_op_L_emb_proj_apply_mem hg hF hu hf
  rw [Nat.add_sub_cancel] at hproj
  have hu' : admop (letters e) (admL u) f =
      (admop (letters e) (admL u) f - admop (letters e) (admL (admemb (admproj u))) f) + admop (letters e) (admL
          (admemb (admproj u))) f := by
    abel
  rw [hu']
  refine add_mem (ih hproj) ?_

  obtain ⟨s, hs, hsD, q, hq, hsplit⟩ := exists_splitting (isHomogeneous_proj hu)
  rw [hsplit]
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply]
  refine add_mem ?_ (Submodule.sum_mem _ fun ij _ => ?_)
  · have h := op_L_emb_apply_mem_of_invariant hg hF hFZ hZ₁ hZ₂ hZ₃ hs hsD hf
    rw [Nat.add_sub_cancel] at h
    rcases Submodule.mem_sup.1 h with ⟨z, hz, y, hy, hzy⟩
    rw [← hzy]
    exact add_mem (Submodule.mem_sup_left hz) (ih hy)
  · exact op_L_emb_D_apply_mem he hF (hq ij) ij.1 ij.2 hf ih

private theorem QF_le_sup (n : ℕ) : QF e F n ≤ Z ⊔ KQ e F := by
  induction n with
  | zero =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, f, hf, rfl⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hw), wordOp_nil, Module.End.one_apply]
    exact Submodule.mem_sup_left (hFZ hf)
  | succ n ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, f, hf, rfl⟩
    by_cases hwn : w.length ≤ n
    · exact ih (wordOp_apply_mem_QF e F hwn hf)
    · have hlen : w.length = n + 1 := by omega

      have hcan := op_sub_op_L_sym_mem (letters e) (closure_letters he) (fword_mem_filt (l := w) hlen.le)
      rw [Nat.add_sub_cancel, op_fword] at hcan
      have h1 : (wordOp (letters e) w - admop (letters e) (admL (sym (fword w)))) f ∈ QF e F n := apply_mem_QF e F
          hcan hf
      have hsym : (sym (fword w)).IsHomogeneous (n + 1) := by
        rw [sym_fword, ← hlen]
        exact isHomogeneous_wordSym w
      have hw' : wordOp (letters e) w f =
          (wordOp (letters e) w - admop (letters e) (admL (sym (fword w)))) f + admop (letters e) (admL (sym (fword
              w))) f := by
        rw [LinearMap.sub_apply, sub_add_cancel]
      rw [hw']
      exact add_mem (ih h1) (op_L_apply_mem he hF hFZ hZ₁ hZ₂ hZ₃ hsym hf ih)

private theorem Qall_le_sup : Qall e F ≤ Z ⊔ KQ e F := iSup_le fun n => QF_le_sup he hF hFZ hZ₁ hZ₂ hZ₃ n

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

private example (x y : Letter) : (wordSym [x, y] : MvPolynomial Letter ℂ).IsHomogeneous 2 := isHomogeneous_wordSym _

private example (ij : Fin 3 × Fin 3) : (admproj (X (Sum.inr ij : Letter))).IsHomogeneous 1 :=
  isHomogeneous_proj (isHomogeneous_X ℂ _)

end Induct
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace ZFinite

open Submodule

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def admorbit (C : Module.End ℂ V) (v : V) : Submodule ℂ V :=
  span ℂ (Set.range fun k : ℕ => (C ^ k) v)

private def IsFin (C : Module.End ℂ V) (v : V) : Prop := (admorbit C v).FG

private theorem pow_apply_mem_orbit (C : Module.End ℂ V) (v : V) (k : ℕ) : (C ^ k) v ∈ admorbit C v :=
  subset_span ⟨k, rfl⟩

private theorem self_mem_orbit (C : Module.End ℂ V) (v : V) : v ∈ admorbit C v := by
  simpa using pow_apply_mem_orbit C v 0

private theorem pow_mul_comm {C admD : Module.End ℂ V} (hCD : C * admD = admD * C) (k : ℕ) : C ^ k * admD = admD * C ^
    k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, hCD, ← mul_assoc, ih, mul_assoc]

private theorem orbit_zero (C : Module.End ℂ V) : admorbit C 0 = ⊥ := by
  refine (span_le.2 ?_).antisymm bot_le
  rintro _ ⟨k, rfl⟩
  simp

private theorem isFin_zero (C : Module.End ℂ V) : IsFin C (0 : V) := by
  unfold IsFin
  rw [orbit_zero]
  exact fg_bot

private theorem orbit_add_le (C : Module.End ℂ V) (v w : V) : admorbit C (v + w) ≤ admorbit C v ⊔ admorbit C w := by
  refine span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  simp only [SetLike.mem_coe, map_add]
  exact add_mem_sup (pow_apply_mem_orbit C v k) (pow_apply_mem_orbit C w k)

private theorem isFin_add (C : Module.End ℂ V) {v w : V} (hv : IsFin C v) (hw : IsFin C w) : IsFin C (v + w) :=
  (hv.sup hw).of_le (orbit_add_le C v w)

private theorem orbit_smul_le (C : Module.End ℂ V) (z : ℂ) (v : V) : admorbit C (z • v) ≤ admorbit C v := by
  refine span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  simp only [SetLike.mem_coe, map_smul]
  exact smul_mem _ _ (pow_apply_mem_orbit C v k)

private theorem isFin_smul (C : Module.End ℂ V) (z : ℂ) {v : V} (hv : IsFin C v) : IsFin C (z • v) :=
  hv.of_le (orbit_smul_le C z v)

private def finVectors (C : Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | IsFin C v}
  zero_mem' := isFin_zero C
  add_mem' := isFin_add C
  smul_mem' := fun z _ hv => isFin_smul C z hv

private theorem mem_finVectors {C : Module.End ℂ V} {v : V} : v ∈ finVectors C ↔ IsFin C v := Iff.rfl

private theorem orbit_apply_le_map {C admD : Module.End ℂ V} (hCD : C * admD = admD * C) (v : V) :
    admorbit C (admD v) ≤ (admorbit C v).map admD := by
  refine span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨(C ^ k) v, pow_apply_mem_orbit C v k, ?_⟩
  change (admD * C ^ k) v = (C ^ k) (admD v)
  rw [← pow_mul_comm hCD, Module.End.mul_apply]

private theorem isFin_apply {C admD : Module.End ℂ V} (hCD : C * admD = admD * C) {v : V} (hv : IsFin C v) :
    IsFin C (admD v) :=
  (hv.map admD).of_le (orbit_apply_le_map hCD v)

private def orbitSpan (C : Module.End ℂ V) (W : Submodule ℂ V) : Submodule ℂ V :=
  span ℂ {v | ∃ w ∈ W, ∃ k : ℕ, (C ^ k) w = v}

private theorem le_orbitSpan (C : Module.End ℂ V) (W : Submodule ℂ V) : W ≤ orbitSpan C W := fun w hw =>
  subset_span ⟨w, hw, 0, by simp⟩

private theorem apply_mem_orbitSpan (C : Module.End ℂ V) (W : Submodule ℂ V) {v : V} (hv : v ∈ orbitSpan C W) :
    C v ∈ orbitSpan C W := by
  induction hv using span_induction with
  | mem v hv =>
    obtain ⟨w, hw, k, rfl⟩ := hv
    exact subset_span ⟨w, hw, k + 1, by rw [pow_succ', Module.End.mul_apply]⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [map_smul]
    exact smul_mem _ _ ha

private theorem apply_mem_orbitSpan_of_comm {C admD : Module.End ℂ V} (hCD : C * admD = admD * C) {W : Submodule ℂ V}
    (hW : ∀ w ∈ W, admD w ∈ W) {v : V} (hv : v ∈ orbitSpan C W) : admD v ∈ orbitSpan C W := by
  induction hv using span_induction with
  | mem v hv =>
    obtain ⟨w, hw, k, rfl⟩ := hv
    refine subset_span ⟨admD w, hW w hw, k, ?_⟩
    change (C ^ k * admD) w = admD ((C ^ k) w)
    rw [pow_mul_comm hCD, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | smul z a _ ha =>
    rw [map_smul]
    exact smul_mem _ _ ha

private theorem orbitSpan_le_iSup (C : Module.End ℂ V) (W : Submodule ℂ V) :
    orbitSpan C W ≤ ⨆ w : W, admorbit C (w : V) := by
  refine span_le.2 ?_
  rintro _ ⟨w, hw, k, rfl⟩
  exact mem_iSup_of_mem ⟨w, hw⟩ (pow_apply_mem_orbit C w k)

private theorem orbitSpan_span_le (C : Module.End ℂ V) (s : Set V) :
    orbitSpan C (span ℂ s) ≤ ⨆ x : s, admorbit C (x : V) := by
  refine span_le.2 ?_
  rintro _ ⟨w, hw, k, rfl⟩

  let T : Submodule ℂ V := ⨆ x : s, admorbit C (x : V)
  have hT : ∀ x ∈ s, ∀ j : ℕ, (C ^ j) x ∈ T := fun x hx j => mem_iSup_of_mem ⟨x, hx⟩ (pow_apply_mem_orbit C x j)
  have key : ∀ v ∈ span ℂ s, ∀ j : ℕ, (C ^ j) v ∈ T := by
    intro v hv
    induction hv using span_induction with
    | mem x hx => exact hT x hx
    | zero => intro j; simp
    | add a b _ _ ha hb =>
      intro j
      rw [map_add]
      exact add_mem (ha j) (hb j)
    | smul z a _ ha =>
      intro j
      rw [map_smul]
      exact smul_mem _ _ (ha j)
  exact key w hw k

private theorem orbitSpan_fg (C : Module.End ℂ V) {W : Submodule ℂ V} (hW : W.FG) (hfin : ∀ w ∈ W, IsFin C w) :
    (orbitSpan C W).FG := by
  obtain ⟨s, hs⟩ := hW
  have hs' : (s : Set V) ⊆ W := hs ▸ subset_span
  have hsup : (⨆ x : (s : Set V), admorbit C (x : V)).FG := by
    haveI : Finite (s : Set V) := s.finite_toSet.to_subtype
    exact fg_iSup _ fun x => hfin x (hs' x.2)
  refine hsup.of_le ?_
  rw [← hs]
  exact orbitSpan_span_le C s

private theorem isFin_of_mem_orbitSpan {C admD : Module.End ℂ V} (hCD : admD * C = C * admD) {W : Submodule ℂ V}
    (hW : ∀ w ∈ W, IsFin admD w) {v : V} (hv : v ∈ orbitSpan C W) : IsFin admD v := by
  rw [← mem_finVectors]
  refine (span_le.2 ?_) hv
  rintro _ ⟨w, hw, k, rfl⟩
  rw [SetLike.mem_coe, mem_finVectors]
  induction k with
  | zero => simpa using hW w hw
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact isFin_apply hCD ih

private theorem pow_apply_mem_span_of_monic (C : Module.End ℂ V) {N : ℕ} {a : Fin (N + 1) → ℂ}
    (ha : a (Fin.last N) = 1) {v : V} (hrel : ∑ m : Fin (N + 1), a m • (C ^ (m : ℕ)) v = 0) (k : ℕ) :
    (C ^ k) v ∈ span ℂ (Set.range fun i : Fin N => (C ^ (i : ℕ)) v) := by
  set S : Submodule ℂ V := span ℂ (Set.range fun i : Fin N => (C ^ (i : ℕ)) v) with hS

  have htop : (C ^ N) v ∈ S := by
    rw [Fin.sum_univ_castSucc] at hrel
    simp only [Fin.val_castSucc, Fin.val_last, ha, one_smul] at hrel
    rw [eq_neg_of_add_eq_zero_right hrel]
    refine neg_mem (sum_mem fun i _ => smul_mem _ _ ?_)
    exact subset_span ⟨i, rfl⟩

  have hstab : ∀ x ∈ S, C x ∈ S := by
    intro x hx
    induction hx using span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      change (C * C ^ (i : ℕ)) v ∈ S
      rw [← pow_succ']
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.2) with h | h
      · exact subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
      · have h' : (i : ℕ) + 1 = N := h
        rw [h']
        exact htop
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | smul z y _ hy =>
      rw [map_smul]
      exact smul_mem _ _ hy

  have hv : v ∈ S := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have ha' : a 0 = 1 := by simpa using ha
      rw [Fin.sum_univ_castSucc] at hrel
      simp [ha'] at hrel
      rw [hrel]
      exact zero_mem _
    · have h0 : (C ^ (((⟨0, hN⟩ : Fin N) : ℕ))) v ∈ S := subset_span ⟨⟨0, hN⟩, rfl⟩
      simpa using h0
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hstab _ ih

private theorem isFin_of_monic (C : Module.End ℂ V) {v : V}
    (h : ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C ^ (m : ℕ)) v = 0) :
    IsFin C v := by
  obtain ⟨N, a, ha, hrel⟩ := h
  refine (fg_span (Set.finite_range fun i : Fin N => (C ^ (i : ℕ)) v)).of_le ?_
  refine span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  exact pow_apply_mem_span_of_monic C ha hrel k

private def zSpan (C₁ C₂ C₃ : Module.End ℂ V) (F : Submodule ℂ V) : Submodule ℂ V :=
  orbitSpan C₃ (orbitSpan C₂ (orbitSpan C₁ F))

private theorem le_zSpan (C₁ C₂ C₃ : Module.End ℂ V) (F : Submodule ℂ V) : F ≤ zSpan C₁ C₂ C₃ F :=
  (le_orbitSpan C₁ F).trans ((le_orbitSpan C₂ _).trans (le_orbitSpan C₃ _))

private theorem zSpan_stable {C₁ C₂ C₃ : Module.End ℂ V} (h₁₂ : C₁ * C₂ = C₂ * C₁) (h₁₃ : C₁ * C₃ = C₃ * C₁)
    (h₂₃ : C₂ * C₃ = C₃ * C₂) (F : Submodule ℂ V) :
    (∀ v ∈ zSpan C₁ C₂ C₃ F, C₁ v ∈ zSpan C₁ C₂ C₃ F) ∧ (∀ v ∈ zSpan C₁ C₂ C₃ F, C₂ v ∈ zSpan C₁ C₂ C₃ F) ∧
      ∀ v ∈ zSpan C₁ C₂ C₃ F, C₃ v ∈ zSpan C₁ C₂ C₃ F := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => apply_mem_orbitSpan C₃ _ hv⟩
  · refine apply_mem_orbitSpan_of_comm h₁₃.symm (fun w hw => ?_) hv
    exact apply_mem_orbitSpan_of_comm h₁₂.symm (fun u hu => apply_mem_orbitSpan C₁ F hu) hw
  · exact apply_mem_orbitSpan_of_comm h₂₃.symm (fun w hw => apply_mem_orbitSpan C₂ _ hw) hv

private theorem zSpan_fg {C₁ C₂ C₃ : Module.End ℂ V} (h₁₂ : C₁ * C₂ = C₂ * C₁) (h₁₃ : C₁ * C₃ = C₃ * C₁)
    (h₂₃ : C₂ * C₃ = C₃ * C₂) {F : Submodule ℂ V} (hF : F.FG)
    (hrel : ∀ f ∈ F,
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₁ ^ (m : ℕ)) f = 0) ∧
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₂ ^ (m : ℕ)) f = 0) ∧
      ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₃ ^ (m : ℕ)) f = 0) :
    (zSpan C₁ C₂ C₃ F).FG := by
  have hf₁ : ∀ f ∈ F, IsFin C₁ f := fun f hf => isFin_of_monic C₁ (hrel f hf).1
  have hf₂ : ∀ f ∈ F, IsFin C₂ f := fun f hf => isFin_of_monic C₂ (hrel f hf).2.1
  have hf₃ : ∀ f ∈ F, IsFin C₃ f := fun f hf => isFin_of_monic C₃ (hrel f hf).2.2

  have hW₁ : (orbitSpan C₁ F).FG := orbitSpan_fg C₁ hF hf₁
  have hW₁₂ : ∀ v ∈ orbitSpan C₁ F, IsFin C₂ v := fun v hv => isFin_of_mem_orbitSpan h₁₂.symm hf₂ hv
  have hW₁₃ : ∀ v ∈ orbitSpan C₁ F, IsFin C₃ v := fun v hv => isFin_of_mem_orbitSpan h₁₃.symm hf₃ hv

  have hW₂ : (orbitSpan C₂ (orbitSpan C₁ F)).FG := orbitSpan_fg C₂ hW₁ hW₁₂
  have hW₂₃ : ∀ v ∈ orbitSpan C₂ (orbitSpan C₁ F), IsFin C₃ v := fun v hv =>
    isFin_of_mem_orbitSpan h₂₃.symm hW₁₃ hv
  exact orbitSpan_fg C₃ hW₂ hW₂₃

private theorem finiteDimensional_zSpan {C₁ C₂ C₃ : Module.End ℂ V} (h₁₂ : C₁ * C₂ = C₂ * C₁)
    (h₁₃ : C₁ * C₃ = C₃ * C₁) (h₂₃ : C₂ * C₃ = C₃ * C₂) {F : Submodule ℂ V} [FiniteDimensional ℂ F]
    (hrel : ∀ f ∈ F,
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₁ ^ (m : ℕ)) f = 0) ∧
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₂ ^ (m : ℕ)) f = 0) ∧
      ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (C₃ ^ (m : ℕ)) f = 0) :
    FiniteDimensional ℂ (zSpan C₁ C₂ C₃ F) :=
  (fg_iff_finiteDimensional _).1 (zSpan_fg h₁₂ h₁₃ h₂₃ ((fg_iff_finiteDimensional F).2 ‹_›) hrel)

private example (C : Module.End ℂ V) {v : V} (hrel : ∑ m : Fin 1, (fun _ => (1 : ℂ)) m • (C ^ (m : ℕ)) v = 0)
    (k : ℕ) : (C ^ k) v = 0 := by
  have h := pow_apply_mem_span_of_monic C (N := 0) (a := fun _ => (1 : ℂ)) rfl hrel k
  have hempty : (Set.range fun i : Fin 0 => (C ^ (i : ℕ)) v) = ∅ := Set.range_eq_empty _
  rw [hempty, span_empty, mem_bot] at h
  exact h

private example (C : Module.End ℂ V) {v : V} (h : (C ^ 2) v = v) : IsFin C v := by
  refine isFin_of_monic C ⟨2, ![-1, 0, 1], rfl, ?_⟩
  simp [Fin.sum_univ_succ, h]

end ZFinite
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace Adm0Assembly

open Adm0 Induct CasimirCentral ZFinite SymbolLemma

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

section Piece

variable (e : Fin 3 → Fin 3 → Module.End ℂ V) (F : Submodule ℂ V)

private def admInv : Submodule ℂ V := Qall e F ⊓ ⨅ ij : Fin 3 × Fin 3, LinearMap.ker (letters e (Sum.inr ij))

variable {e F}

private theorem mem_Inv {x : V} : x ∈ admInv e F ↔ x ∈ Qall e F ∧ ∀ ij : Fin 3 × Fin 3, letters e (Sum.inr ij) x = 0
    := by
  simp [admInv, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem letter_apply_mem_QF (x : Letter) {n : ℕ} {y : V} (hy : y ∈ QF e F n) :
    letters e x y ∈ QF e F (n + 1) := by
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, f, hf, rfl⟩ := hv
    have h : letters e x (wordOp (letters e) w f) = wordOp (letters e) (x :: w) f := by
      rw [wordOp_cons, Module.End.mul_apply]
    rw [h]
    exact wordOp_apply_mem_QF e F (by simpa using hw) hf
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul z a _ ha => rw [map_smul]; exact Submodule.smul_mem _ z ha

private theorem letter_apply_mem_Qall (x : Letter) {y : V} (hy : y ∈ Qall e F) : letters e x y ∈ Qall e F := by
  induction hy using Submodule.iSup_induction' with
  | mem n v hv => exact mem_Qall (letter_apply_mem_QF x hv)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

private theorem KQ_le_Qall : KQ e F ≤ Qall e F :=
  iSup_le fun ij => Submodule.map_le_iff_le_comap.2 fun _ hy => letter_apply_mem_Qall (Sum.inr ij) hy

private theorem Inv_le_Qall : admInv e F ≤ Qall e F := inf_le_left

variable (B : V → V → ℂ)
  (hlin : ∀ (z : ℂ), ∀ w₁ ∈ Qall e F, ∀ w₂ ∈ Qall e F, ∀ w' ∈ Qall e F,
    B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
  (hsymm : ∀ w ∈ Qall e F, ∀ w' ∈ Qall e F, B w' w = (starRingEnd ℂ) (B w w'))
  (hpos : ∀ w ∈ Qall e F, w ≠ 0 → 0 < (B w w).re)
include hlin

private theorem B_add_left {w₁ w₂ w' : V} (h₁ : w₁ ∈ Qall e F) (h₂ : w₂ ∈ Qall e F) (h' : w' ∈ Qall e F) :
    B (w₁ + w₂) w' = B w₁ w' + B w₂ w' := by
  simpa using hlin 1 w₁ h₁ w₂ h₂ w' h'

private theorem B_zero_left {w' : V} (h' : w' ∈ Qall e F) : B 0 w' = 0 := form_zero_left (Qall e F) B hlin h'

private theorem B_sum_left {ι : Type*} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, u i ∈ Qall e F) {w' : V}
    (h' : w' ∈ Qall e F) : B (∑ i ∈ s, u i) w' = ∑ i ∈ s, B (u i) w' := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_left B hlin h']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, B_add_left B hlin (hu a (Finset.mem_insert_self a s))
      (Submodule.sum_mem _ fun i hi => hu i (Finset.mem_insert_of_mem hi)) h',
      ih fun i hi => hu i (Finset.mem_insert_of_mem hi)]

include hsymm in
private theorem B_zero_right {w : V} (hw : w ∈ Qall e F) : B w 0 = 0 := by
  rw [hsymm 0 (Submodule.zero_mem _) w hw, B_zero_left B hlin hw, map_zero]

include hpos in

private theorem eq_zero_of_sum_sq_apply_eq_zero {ι : Type*} (s : Finset ι) (T : ι → Module.End ℂ V)
    (hT : ∀ i ∈ s, ∀ y ∈ Qall e F, T i y ∈ Qall e F)
    (hTskew : ∀ i ∈ s, ∀ x ∈ Qall e F, ∀ y ∈ Qall e F, B (T i x) y = -B x (T i y))
    {x : V} (hx : x ∈ Qall e F) (h0 : ∑ i ∈ s, T i (T i x) = 0) : ∀ i ∈ s, T i x = 0 := by
  have hsum : ∑ i ∈ s, B (T i (T i x)) x = 0 := by
    rw [← B_sum_left B hlin s _ (fun i hi => hT i hi _ (hT i hi x hx)) hx, h0, B_zero_left B hlin hx]
  have hterm : ∀ i ∈ s, B (T i (T i x)) x = -B (T i x) (T i x) := fun i hi => hTskew i hi _ (hT i hi x hx) x hx
  have hre : ∑ i ∈ s, (B (T i x) (T i x)).re = 0 := by
    have h := congrArg Complex.re hsum
    rw [Complex.re_sum, Finset.sum_congr rfl fun i hi => by rw [hterm i hi]] at h
    simpa [Finset.sum_neg_distrib] using h
  have hnn : ∀ i ∈ s, 0 ≤ (B (T i x) (T i x)).re := by
    intro i hi
    by_cases hz : T i x = 0
    · rw [hz, B_zero_left B hlin (Submodule.zero_mem _)]
      simp
    · exact (hpos _ (hT i hi x hx) hz).le
  intro i hi
  by_contra hne
  have hlt := hpos _ (hT i hi x hx) hne
  rw [(Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre i hi] at hlt
  exact lt_irrefl _ hlt

include hpos in

private theorem mem_Inv_of_sum_sq
    (hskew : ∀ ij : Fin 3 × Fin 3, ∀ x ∈ Qall e F, ∀ y ∈ Qall e F,
      B (letters e (Sum.inr ij) x) y = -B x (letters e (Sum.inr ij) y)) {x : V} (hx : x ∈ Qall e F)
    (h0 : ∑ ij : Fin 3 × Fin 3, letters e (Sum.inr ij) (letters e (Sum.inr ij) x) = 0) : x ∈ admInv e F :=
  mem_Inv.2 ⟨hx, fun ij => eq_zero_of_sum_sq_apply_eq_zero B hlin hpos Finset.univ (fun ij => letters e (Sum.inr ij))
    (fun _ _ _ hy => letter_apply_mem_Qall _ hy) (fun ij _ => hskew ij) hx h0 ij (Finset.mem_univ ij)⟩

include hsymm hpos in

private theorem Inv_inf_KQ_eq_bot
    (hskew : ∀ ij : Fin 3 × Fin 3, ∀ x ∈ Qall e F, ∀ y ∈ Qall e F,
      B (letters e (Sum.inr ij) x) y = -B x (letters e (Sum.inr ij) y)) :
    admInv e F ⊓ KQ e F = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxI, hxK⟩
  obtain ⟨hxQ, hkill⟩ := mem_Inv.1 hxI
  have key : ∀ u ∈ KQ e F, u ∈ Qall e F ∧ B u x = 0 := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem ij u hu =>
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hu
      refine ⟨letter_apply_mem_Qall _ hy, ?_⟩
      rw [hskew ij y hy x hxQ, hkill ij, B_zero_right B hlin hsymm hy, neg_zero]
    | zero => exact ⟨Submodule.zero_mem _, B_zero_left B hlin hxQ⟩
    | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [B_add_left B hlin ha.1 hb.1 hxQ, ha.2, hb.2, add_zero]⟩
  by_contra hne
  have h := hpos x hxQ hne
  rw [(key x hxK).2] at h
  simp at h

include hsymm hpos in

private theorem finiteDimensional_Inv
    (hskew : ∀ ij : Fin 3 × Fin 3, ∀ x ∈ Qall e F, ∀ y ∈ Qall e F,
      B (letters e (Sum.inr ij) x) y = -B x (letters e (Sum.inr ij) y))
    (he : admRel e) (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0) {Z : Submodule ℂ V}
    [FiniteDimensional ℂ Z] (hFZ : F ≤ Z) (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z) (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z)
    (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z) : FiniteDimensional ℂ (admInv e F) := by
  have hbot := Inv_inf_KQ_eq_bot B hlin hsymm hpos hskew
  have hle : admInv e F ≤ Z ⊔ KQ e F := Inv_le_Qall.trans (Qall_le_sup he hF hFZ hZ₁ hZ₂ hZ₃)
  have hrange : ∀ x : admInv e F, (KQ e F).mkQ (x : V) ∈ Z.map (KQ e F).mkQ := by
    intro x
    obtain ⟨z, hz, k, hk, hzk⟩ := Submodule.mem_sup.1 (hle x.2)
    refine Submodule.mem_map.2 ⟨z, hz, ?_⟩
    rw [← hzk, map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hk, add_zero]
  let φ : admInv e F →ₗ[ℂ] Z.map (KQ e F).mkQ :=
    LinearMap.codRestrict _ ((KQ e F).mkQ.comp (admInv e F).subtype) hrange
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (KQ e F).mkQ (x : V) = 0 := by simpa [φ] using congrArg Subtype.val hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    have hmem : (x : V) ∈ admInv e F ⊓ KQ e F := ⟨x.2, h1⟩
    rw [hbot] at hmem
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hmem)
  exact FiniteDimensional.of_injective φ hinj

include hsymm hpos in

private theorem finiteDimensional_Inv_of_centreFinite
    (hskew : ∀ ij : Fin 3 × Fin 3, ∀ x ∈ Qall e F, ∀ y ∈ Qall e F,
      B (letters e (Sum.inr ij) x) y = -B x (letters e (Sum.inr ij) y))
    (he : admRel e) (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0) [FiniteDimensional ℂ F]
    (hrel : ∀ f ∈ F,
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (cas e 1 ^ (m : ℕ)) f = 0) ∧
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (cas e 2 ^ (m : ℕ)) f = 0) ∧
      ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (cas e 3 ^ (m : ℕ)) f = 0) :
    FiniteDimensional ℂ (admInv e F) := by
  have h₁₂ := cas_mul_cas he 1 2
  have h₁₃ := cas_mul_cas he 1 3
  have h₂₃ := cas_mul_cas he 2 3
  haveI : FiniteDimensional ℂ (zSpan (cas e 1) (cas e 2) (cas e 3) F) := finiteDimensional_zSpan h₁₂ h₁₃ h₂₃ hrel
  obtain ⟨hZ₁, hZ₂, hZ₃⟩ := zSpan_stable h₁₂ h₁₃ h₂₃ F
  exact finiteDimensional_Inv B hlin hsymm hpos hskew he hF (le_zSpan _ _ _ F) hZ₁ hZ₂ hZ₃

end Piece
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

private example (e : Fin 3 → Fin 3 → Module.End ℂ V) (F : Submodule ℂ V)
    (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0) : F ≤ admInv e F := fun f hf =>
  mem_Inv.2 ⟨mem_Qall (n := 0) (by have h__af := wordOp_apply_mem_QF e F (w := []) le_rfl hf; simp at h__af; exact h__af), fun ij => hF ij f hf⟩

end Adm0Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace EnvBridge

open SymbolLemma CasimirCentral Adm0 Induct Adm0Assembly

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private def agen (act : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ W) : Fin 3 → Fin 3 → Module.End ℂ W :=
  fun i j => act (Matrix.single i j (1 : ℂ))

variable {act : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ W}

private theorem act_single_mul_single (i j k l : Fin 3) :
    act (Matrix.single i j (1 : ℂ) * Matrix.single k l 1) = if j = k then act (Matrix.single i l 1) else 0 := by
  split_ifs with hjk
  · subst hjk
    rw [Matrix.single_mul_single_same, one_mul]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ hjk, map_zero]

private theorem admRel_agen (hact : ∀ X Y : Matrix (Fin 3) (Fin 3) ℂ, act ⁅X, Y⁆ = ⁅act X, act Y⁆) :
    admRel (agen act) := by
  intro i j k l
  have h := hact (Matrix.single i j (1 : ℂ)) (Matrix.single k l 1)
  simp only [LieRing.of_associative_ring_bracket, map_sub, act_single_mul_single] at h
  simp only [agen]
  exact h.symm

private theorem letters_agen_inr (i j : Fin 3) :
    letters (agen act) (Sum.inr (i, j)) = act (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) := by
  rw [letters_inr, map_sub]
  rfl

private theorem letters_agen_eq (x : Letter) : ∃ M : Matrix (Fin 3) (Fin 3) ℂ, letters (agen act) x = act M := by
  rcases x with ⟨⟨⟨a, b⟩, -⟩⟩ | ⟨i, j⟩
  · refine ⟨(2⁻¹ : ℂ) • (Matrix.single a b 1 + Matrix.single b a 1), ?_⟩
    simp only [letters, agen, map_smul, map_add]
  · exact ⟨_, letters_agen_inr i j⟩

private theorem agen_apply_mem_Qall (i j : Fin 3) {F : Submodule ℂ W} {y : W} (hy : y ∈ Qall (agen act) F) :
    agen act i j y ∈ Qall (agen act) F := by
  have h₁ := letter_apply_mem_Qall (Sum.inl (pIdx i j)) hy
  have h₂ := letter_apply_mem_Qall (Sum.inr (i, j)) hy
  have hsum : agen act i j y =
      letters (agen act) (Sum.inl (pIdx i j)) y + (2⁻¹ : ℂ) • letters (agen act) (Sum.inr (i, j)) y := by
    rw [letters_inl_pIdx, letters_inr]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply]
    module
  rw [hsum]
  exact (Qall _ _).add_mem h₁ ((Qall _ _).smul_mem _ h₂)

private theorem act_apply_mem_Qall (X : Matrix (Fin 3) (Fin 3) ℂ) {F : Submodule ℂ W} {y : W}
    (hy : y ∈ Qall (agen act) F) : act X y ∈ Qall (agen act) F := by
  have hX : X = ∑ i : Fin 3, ∑ j : Fin 3, X i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hX]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    (Qall _ _).smul_mem _ (agen_apply_mem_Qall i j hy)

section Enveloping

variable [Module (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) W]
  [IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) W]
  (hι : ∀ (X : Matrix (Fin 3) (Fin 3) ℂ) (w : W), UniversalEnvelopingAlgebra.ι ℂ X • w = act X w)
include hι

private theorem smul_mem_Qall (u : UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) {F : Submodule ℂ W}
    {y : W} (hy : y ∈ Qall (agen act) F) : u • y ∈ Qall (agen act) F := by
  have hsurj : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :=
    RingCon.mkₐ_surjective _
  obtain ⟨t, rfl⟩ := hsurj u
  refine TensorAlgebra.induction (C := fun t => ∀ z ∈ Qall (agen act) F,
    UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix (Fin 3) (Fin 3) ℂ) t • z ∈ Qall (agen act) F)
    ?_ ?_ ?_ ?_ t y hy
  · intro r z hz
    rw [AlgHom.commutes, algebraMap_smul]
    exact (Qall _ _).smul_mem r hz
  · intro X z hz
    rw [← UniversalEnvelopingAlgebra.ι_apply, hι]
    exact act_apply_mem_Qall X hz
  · intro a b ha hb z hz
    rw [map_mul, mul_smul]
    exact ha _ (hb _ hz)
  · intro a b ha hb z hz
    rw [map_add, add_smul]
    exact (Qall _ _).add_mem (ha _ hz) (hb _ hz)

private theorem Qall_agen_eq (F : Submodule ℂ W) :
    Qall (agen act) F =
      (Submodule.span (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (F : Set W)).restrictScalars ℂ := by
  apply le_antisymm
  · refine iSup_le fun n => Submodule.span_le.2 ?_
    rintro _ ⟨w, -, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem]
    induction w with
    | nil =>
      rw [wordOp_nil, Module.End.one_apply]
      exact Submodule.subset_span hf
    | cons x w ih =>
      rw [wordOp_cons, Module.End.mul_apply]
      obtain ⟨M, hM⟩ := letters_agen_eq (act := act) x
      rw [hM, ← hι]
      exact Submodule.smul_mem _ _ ih
  · intro y hy
    rw [Submodule.restrictScalars_mem] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      have h := wordOp_apply_mem_QF (agen act) F (w := []) (n := 0) le_rfl hz
      rw [wordOp_nil, Module.End.one_apply] at h
      exact mem_Qall h
    | zero => exact (Qall _ _).zero_mem
    | add a b _ _ ha hb => exact (Qall _ _).add_mem ha hb
    | smul u z _ hz => exact smul_mem_Qall hι u hz

private theorem admInv_agen_eq (F : Submodule ℂ W) :
    admInv (agen act) F =
      (Submodule.span (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (F : Set W)).restrictScalars ℂ ⊓
        ⨅ i : Fin 3, ⨅ j : Fin 3, LinearMap.ker (act (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)) := by
  rw [admInv, Qall_agen_eq hι]
  congr 1
  simp only [← letters_agen_inr]
  apply le_antisymm
  · exact le_iInf fun i => le_iInf fun j => iInf_le _ (i, j)
  · exact le_iInf fun ij => (iInf_le _ ij.1).trans (iInf_le _ ij.2)

private theorem finiteDimensional_meet_shape (F : Submodule ℂ W)
    (h : FiniteDimensional ℂ ↥(admInv (agen act) F)) :
    FiniteDimensional ℂ ↥((Submodule.span (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ))
        (F : Set W)).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3, LinearMap.ker (act (Matrix.single i j (1 : ℂ) - Matrix.single j i 1))) := by
  rw [← admInv_agen_eq hι]
  exact h

end Enveloping
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

end EnvBridge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace Leg1Generic

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem finiteDimensional_comap_of_le (S P : Submodule ℂ M) (s : Finset M)
    (hle : P ≤ Submodule.span ℂ (s : Set M)) : FiniteDimensional ℂ (P.comap S.subtype) :=
  FiniteDimensional.of_injective
    (LinearMap.codRestrict (Submodule.span ℂ (s : Set M)) (S.subtype.comp (P.comap S.subtype).subtype)
      fun x => hle x.2)
    fun x y hxy => by
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)

private theorem coe_pow_apply {S : Submodule ℂ M} {T : Module.End ℂ S} {t : M → M}
    (h : ∀ ψ : S, ((T ψ : S) : M) = t ψ) (m : ℕ) (ψ : S) : (((T ^ m) ψ : S) : M) = t^[m] ψ := by
  induction m generalizing ψ with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, ih, h, Function.iterate_succ_apply]

private theorem monic_relation_of_coe {S : Submodule ℂ M} {T : Module.End ℂ S} {t : M → M}
    (h : ∀ ψ : S, ((T ψ : S) : M) = t ψ) (φ : S)
    (hrel : ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • t^[m] φ = 0) :
    ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m : Fin (N + 1), a m • (T ^ (m : ℕ)) φ = 0 := by
  obtain ⟨N, a, ha, hsum⟩ := hrel
  refine ⟨N, a, ha, Subtype.ext ?_⟩
  simpa only [Submodule.coe_sum, Submodule.coe_smul, coe_pow_apply h, Submodule.coe_zero] using hsum

end Leg1Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

namespace Leg1Layer

open LanglandsTunnell.CubicInduction (AdelicGL)
open LanglandsTunnell.CubicInduction.WhittakerBlock
open scoped LanglandsTunnell.CubicInduction.WhittakerBlock
open IsDedekindDomain NumberField AutomorphicForm
open CasimirCentral Adm0 Induct Adm0Assembly EnvBridge Leg1Generic

private theorem agen_derivAction3 (i j : Fin 3) : agen derivAction3 i j = archDerivₗ i j :=
  derivAction3_single i j

private theorem iota_smul (X : Matrix (Fin 3) (Fin 3) ℂ) (φ : smoothFunctions3) :
    UniversalEnvelopingAlgebra.ι ℂ X • φ = derivAction3 X φ := by
  show envelopingHom3 (UniversalEnvelopingAlgebra.ι ℂ X) φ = derivAction3 X φ
  rw [envelopingHom3_ι]

private def bottomSp (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ smoothFunctions3 :=
  (orthSpan f).comap smoothFunctions3.subtype

private theorem mem_bottomSp {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {φ : smoothFunctions3} :
    φ ∈ bottomSp f ↔ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ orthSpan f :=
  Iff.rfl

private theorem finiteDimensional_bottomSp {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfin : IsOrthFinite f) :
    FiniteDimensional ℂ (bottomSp f) := by
  obtain ⟨s, hs⟩ := hfin
  refine finiteDimensional_comap_of_le _ _ s (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk₁, hk₂, rfl⟩
  exact hs k hk₁ hk₂

private theorem coe_cas_one (φ : smoothFunctions3) :
    ((cas (agen derivAction3) 1 φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = casimir1 φ := by
  rw [cas_one]
  funext g
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, agen_derivAction3, coe_archDerivₗ_apply,
    casimir1]

private theorem coe_cas_two (φ : smoothFunctions3) :
    ((cas (agen derivAction3) 2 φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = casimir2 φ := by
  rw [cas_two]
  funext g
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply, agen_derivAction3,
    coe_archDerivₗ_apply, casimir2]

private theorem coe_cas_three (φ : smoothFunctions3) :
    ((cas (agen derivAction3) 3 φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = casimir3 φ := by
  rw [cas_three]
  funext g
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply, agen_derivAction3,
    coe_archDerivₗ_apply, casimir3]

private theorem rel_of_isCentreFinite {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hcentre : ∀ φ ∈ orthSpan f, IsCentreFinite φ) :
    ∀ φ ∈ bottomSp f,
      (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧
          ∑ m : Fin (N + 1), a m • (cas (agen derivAction3) 1 ^ (m : ℕ)) φ = 0) ∧
        (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧
            ∑ m : Fin (N + 1), a m • (cas (agen derivAction3) 2 ^ (m : ℕ)) φ = 0) ∧
          ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧
            ∑ m : Fin (N + 1), a m • (cas (agen derivAction3) 3 ^ (m : ℕ)) φ = 0 := by
  intro φ hφ
  obtain ⟨h₁, h₂, h₃⟩ := hcentre φ (mem_bottomSp.1 hφ)
  exact ⟨monic_relation_of_coe coe_cas_one φ h₁, monic_relation_of_coe coe_cas_two φ h₂,
    monic_relation_of_coe coe_cas_three φ h₃⟩

private theorem qall_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    Qall (agen derivAction3) (bottomSp f) = (gKSpan f).restrictScalars ℂ :=
  Qall_agen_eq iota_smul (bottomSp f)

private theorem admInv_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    admInv (agen derivAction3) (bottomSp f) = (gKSpan f).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3,
        LinearMap.ker (derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)) :=
  admInv_agen_eq iota_smul (bottomSp f)

end Leg1Layer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

open LanglandsTunnell LanglandsTunnell.CubicInduction
open IsDedekindDomain NumberField AutomorphicForm

open scoped LanglandsTunnell.CubicInduction.WhittakerBlock in
theorem solution
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hfin : WhittakerBlock.IsOrthFinite f)
    (hcentre : ∀ φ ∈ WhittakerBlock.orthSpan f, WhittakerBlock.IsCentreFinite φ)
    (hrot : ∀ i j : Fin 3, ∀ φ : WhittakerBlock.smoothFunctions3,
      (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ WhittakerBlock.orthSpan f →
        WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) φ = 0)
    (B : WhittakerBlock.smoothFunctions3 → WhittakerBlock.smoothFunctions3 → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ WhittakerBlock.gKSpan f, ∀ w₂ ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f,
      B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ WhittakerBlock.gKSpan f, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ i j : Fin 3, ∀ x ∈ WhittakerBlock.gKSpan f, ∀ y ∈ WhittakerBlock.gKSpan f,
      B (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) x) y =
        -B x (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) y)) :
    FiniteDimensional ℂ ↥((WhittakerBlock.gKSpan f).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3,
        LinearMap.ker (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1))) := by
  rw [← Leg1Layer.admInv_eq f]
  have hQ := Leg1Layer.qall_eq f
  haveI : FiniteDimensional ℂ (Leg1Layer.bottomSp f) := Leg1Layer.finiteDimensional_bottomSp hfin
  refine Adm0Assembly.finiteDimensional_Inv_of_centreFinite B ?_ ?_ ?_ ?_
    (EnvBridge.admRel_agen WhittakerBlock.derivAction3_lie) ?_ (Leg1Layer.rel_of_isCentreFinite hcentre)
  · intro z w₁ hw₁ w₂ hw₂ w' hw'
    rw [hQ] at hw₁ hw₂ hw'
    exact hlin z w₁ hw₁ w₂ hw₂ w' hw'
  · intro w hw w' hw'
    rw [hQ] at hw hw'
    exact hsymm w hw w' hw'
  · intro w hw hw0
    rw [hQ] at hw
    exact hpos w hw hw0
  · rintro ⟨i, j⟩ x hx y hy
    rw [hQ] at hx hy
    rw [EnvBridge.letters_agen_inr]
    exact hskew i j x hx y hy
  · rintro ⟨i, j⟩ φ hφ
    rw [EnvBridge.letters_agen_inr]
    exact hrot i j φ (Leg1Layer.mem_bottomSp.1 hφ)
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.S5Split"

end S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite (solution)
