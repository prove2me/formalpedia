-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ae9d5638-2014-5bf9-9a1e-ef2646c3cf3e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul

set_option autoImplicit false

noncomputable section

section CarryC8b

namespace CasimirCentral

open Matrix Finset

variable {A : Type*} [Ring A]

def admRel (e : Fin 3 → Fin 3 → A) : Prop :=
  ∀ i j k l : Fin 3, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)

def admgen (e : Fin 3 → Fin 3 → A) : Matrix (Fin 3) (Fin 3) A := Matrix.of fun i j => e i j

def cas (e : Fin 3 → Fin 3 → A) (n : ℕ) : A := (admgen e ^ n).trace

theorem cas_one (e : Fin 3 → Fin 3 → A) : cas e 1 = ∑ i, e i i := by
  simp [cas, admgen, Matrix.trace]

theorem cas_two (e : Fin 3 → Fin 3 → A) : cas e 2 = ∑ i, ∑ j, e i j * e j i := by
  simp [cas, admgen, Matrix.trace, pow_two, Matrix.mul_apply]

theorem cas_three (e : Fin 3 → Fin 3 → A) : cas e 3 = ∑ i, ∑ j, ∑ k, e i j * (e j k * e k i) := by
  simp only [cas, admgen, Matrix.trace, Matrix.diag_apply, pow_succ, pow_zero, one_mul, Matrix.mul_apply,
      Matrix.of_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc]

private def _root_.CasimirCentral.admder (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x : A) : A := x * e a b - e a b * x

p2m_export "CasimirCentral" "admder"
theorem admder_mul (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x y : A) :
    admder e a b (x * y) = admder e a b x * y + x * admder e a b y := by
  simp only [admder]
  noncomm_ring

theorem der_add (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x y : A) :
    admder e a b (x + y) = admder e a b x + admder e a b y := by
  simp only [admder]
  noncomm_ring

theorem der_sum (e : Fin 3 → Fin 3 → A) (a b : Fin 3) {ι : Type*} (s : Finset ι) (f : ι → A) :
    admder e a b (∑ i ∈ s, f i) = ∑ i ∈ s, admder e a b (f i) := by
  simp only [admder, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

def derM (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  Matrix.of fun i j => admder e a b (X i j)

theorem derM_mul (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X admY : Matrix (Fin 3) (Fin 3) A) :
    derM e a b (X * admY) = derM e a b X * admY + X * derM e a b admY := by
  ext i j
  simp only [derM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, der_sum, admder_mul, Finset.sum_add_distrib]

theorem trace_derM (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) :
    (derM e a b X).trace = admder e a b X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, derM, Matrix.of_apply, der_sum]

def admunit (a b : Fin 3) : Matrix (Fin 3) (Fin 3) A := Matrix.single b a (1 : A)

theorem derM_gen {e : Fin 3 → Fin 3 → A} (he : admRel e) (a b : Fin 3) :
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

theorem derM_gen_pow {e : Fin 3 → Fin 3 → A} (he : admRel e) (a b : Fin 3) (n : ℕ) :
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

theorem trace_mul_unit (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) :
    (X * admunit a b).trace = (admunit a b * X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, admunit, Matrix.mul_apply, Matrix.single, Matrix.of_apply, mul_ite,
      ite_mul,
    mul_one, one_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]

theorem cas_mul_gen {e : Fin 3 → Fin 3 → A} (he : admRel e) (n : ℕ) (a b : Fin 3) :
    cas e n * e a b = e a b * cas e n := by
  have h : admder e a b (cas e n) = 0 := by
    rw [cas, ← trace_derM, derM_gen_pow he, Matrix.trace_sub, trace_mul_unit, sub_self]
  simpa [admder, sub_eq_zero] using h

theorem commute_gen_pow_entry (e : Fin 3 → Fin 3 → A) {x : A} (hx : ∀ a b, x * e a b = e a b * x) (n : ℕ)
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

theorem commute_cas_of_commute_gen (e : Fin 3 → Fin 3 → A) {x : A} (hx : ∀ a b, x * e a b = e a b * x)
    (n : ℕ) : x * cas e n = cas e n * x := by
  simp only [cas, Matrix.trace, Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => commute_gen_pow_entry e hx n i i

theorem cas_mul_cas {e : Fin 3 → Fin 3 → A} (he : admRel e) (m n : ℕ) : cas e m * cas e n = cas e n * cas e m
    :=
  commute_cas_of_commute_gen e (fun a b => cas_mul_gen he m a b) n

theorem cas_mul_word {e : Fin 3 → Fin 3 → A} (he : admRel e) (n : ℕ) (w : List (Fin 3 × Fin 3)) :
    cas e n * (w.map fun ij => e ij.1 ij.2).prod = (w.map fun ij => e ij.1 ij.2).prod * cas e n := by
  induction w with
  | nil => simp
  | cons ij w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, cas_mul_gen he n, mul_assoc, ih, ← mul_assoc]

example : admRel fun i j : Fin 3 => (Matrix.single i j (1 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ) := by
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

example (e : Fin 3 → Fin 3 → A) :
    cas e 2 = ∑ i : Fin 3, (e i 0 * e 0 i + e i 1 * e 1 i + e i 2 * e 2 i) := by
  rw [cas_two]
  simp [Fin.sum_univ_three, add_assoc]

end CasimirCentral

open MvPolynomial Matrix

namespace SymRestriction

abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}

abbrev admP : Type := MvPolynomial admIdx ℂ

def admY : Matrix (Fin 3) (Fin 3) admP :=
  Matrix.of fun a b => if h : a ≤ b then X ⟨(a, b), h⟩ else X ⟨(b, a), le_of_not_ge h⟩

theorem Y_symm (a b : Fin 3) : admY a b = admY b a := by
  unfold admY
  simp only [Matrix.of_apply]
  by_cases hab : a ≤ b <;> by_cases hba : b ≤ a
  · have : a = b := le_antisymm hab hba
    subst this
    rfl
  · simp [hab, hba]
  · simp [hab, hba]
  · exact absurd (le_of_not_ge hab) hba

theorem Y_transpose : admY.transpose = admY :=
  Matrix.ext fun a b => Y_symm b a

def admK (i j : Fin 3) : Matrix (Fin 3) (Fin 3) admP := Matrix.single i j 1 - Matrix.single j i 1

theorem K_transpose (i j : Fin 3) : (admK i j).transpose = -admK i j := by
  unfold admK
  rw [transpose_sub, transpose_single, transpose_single, neg_sub]

theorem comm_symm (i j : Fin 3) (a b : Fin 3) :
    (admK i j * admY - admY * admK i j) a b = (admK i j * admY - admY * admK i j) b a := by
  have h : (admK i j * admY - admY * admK i j).transpose = admK i j * admY - admY * admK i j := by
    rw [transpose_sub, transpose_mul, transpose_mul, Y_transpose, K_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, sub_neg_eq_add, neg_add_eq_sub]
  conv_rhs => rw [← h]
  rfl

def admD (i j : Fin 3) : Derivation ℂ admP admP :=
  mkDerivation ℂ fun v : admIdx => (admK i j * admY - admY * admK i j) v.1.1 v.1.2

theorem D_Y (i j a b : Fin 3) : admD i j (admY a b) = (admK i j * admY - admY * admK i j) a b := by
  unfold admD
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X]
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X, comm_symm]

def DM (i j : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) : Matrix (Fin 3) (Fin 3) admP := M.map (admD i j)

theorem DM_mul (i j : Fin 3) (M N : Matrix (Fin 3) (Fin 3) admP) :
    DM i j (M * N) = DM i j M * N + M * DM i j N := by
  refine Matrix.ext fun a b => ?_
  simp only [DM, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem DM_one (i j : Fin 3) : DM i j (1 : Matrix (Fin 3) (Fin 3) admP) = 0 := by
  refine Matrix.ext fun a b => ?_
  by_cases hab : a = b
  · subst hab
    simp [DM]
  · simp [DM, Matrix.one_apply_ne hab]

theorem DM_Y (i j : Fin 3) : DM i j admY = admK i j * admY - admY * admK i j :=
  Matrix.ext fun a b => D_Y i j a b

theorem DM_Y_pow (i j : Fin 3) (n : ℕ) : DM i j (admY ^ n) = admK i j * admY ^ n - admY ^ n * admK i j := by
  induction n with
  | zero => rw [pow_zero, DM_one, Matrix.mul_one, Matrix.one_mul, sub_self]
  | succ n ih =>
    rw [pow_succ, DM_mul, ih, DM_Y]
    noncomm_ring

theorem D_trace (i j : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) : admD i j M.trace = (DM i j M).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, DM, Matrix.map_apply]

theorem D_trace_Y_pow (i j : Fin 3) (n : ℕ) : admD i j ((admY ^ n).trace) = 0 := by
  rw [D_trace, DM_Y_pow, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem single_mul_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (Matrix.single i j (1 : admP) * M) a b = if a = i then M j b else 0 := by
  by_cases h : a = i
  · subst h
    simp
  · simp [h]

theorem mul_single_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (M * Matrix.single i j (1 : admP)) a b = if b = j then M a i else 0 := by
  by_cases h : b = j
  · subst h
    simp
  · simp [h]

theorem D_Y_eq (i j a b : Fin 3) :
    admD i j (admY a b) =
      ((if a = i then admY j b else 0) - (if a = j then admY i b else 0)) -
        ((if b = j then admY a i else 0) - (if b = i then admY a j else 0)) := by
  rw [D_Y]
  simp only [admK, Matrix.sub_apply, Matrix.sub_mul, Matrix.mul_sub, single_mul_entry, mul_single_entry]

section Distinct

variable (i j k : Fin 3)

theorem D_Y_ii (hij : i ≠ j) : admD i j (admY i i) = 2 * admY i j := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false]
  rw [Y_symm j i]
  ring

theorem D_Y_jj (hij : i ≠ j) : admD i j (admY j j) = -(2 * admY i j) := by
  rw [D_Y_eq]
  simp only [if_true, if_false, Ne.symm hij]
  rw [Y_symm j i]
  ring

theorem D_Y_ij (hij : i ≠ j) : admD i j (admY i j) = admY j j - admY i i := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false, Ne.symm hij]
  ring

theorem D_Y_ik (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY i k) = admY j k := by
  rw [D_Y_eq]
  simp only [if_true, hij, if_false, Ne.symm hik, Ne.symm hjk]
  ring

theorem D_Y_jk (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY j k) = -admY i k := by
  rw [D_Y_eq]
  simp only [if_true, if_false, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  ring

theorem D_Y_kk (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY k k) = 0 := by
  rw [D_Y_eq]
  simp [Ne.symm hik, Ne.symm hjk]

theorem D_C_mul (c : ℂ) (x : admP) : admD i j (C c * x) = C c * admD i j x := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem C2I_mul_C2I : (C (2 * Complex.I) : admP) * C (2 * Complex.I) = -4 := by
  rw [← C_mul, show (2 * Complex.I) * (2 * Complex.I) = (-4 : ℂ) by ring_nf; simp [Complex.I_sq]]
  simp only [map_neg, map_ofNat]

theorem CI_mul_CI : (C Complex.I : admP) * C Complex.I = -1 := by
  rw [← C_mul, Complex.I_mul_I]
  simp

def eig : Fin 6 → admP :=
  ![admY i i + admY j j, (admY i i - admY j j) + C (2 * Complex.I) * admY i j, (admY i i - admY j j) - C (2 *
      Complex.I) * admY i j, admY k k,
    admY i k + C Complex.I * admY j k, admY i k - C Complex.I * admY j k]

def wtv : Fin 6 → ℂ := ![0, -(2 * Complex.I), 2 * Complex.I, 0, -Complex.I, Complex.I]

theorem D_eig_u (hij : i ≠ j) : admD i j (admY i i + admY j j) = (0 : ℂ) • (admY i i + admY j j) := by
  rw [map_add, D_Y_ii i j hij, D_Y_jj i j hij, zero_smul]
  ring

theorem D_eig_z (hij : i ≠ j) :
    admD i j ((admY i i - admY j j) + C (2 * Complex.I) * admY i j) =
      (-(2 * Complex.I)) • ((admY i i - admY j j) + C (2 * Complex.I) * admY i j) := by
  rw [map_add, map_sub, D_C_mul, D_Y_ii i j hij, D_Y_jj i j hij, D_Y_ij i j hij, smul_eq_C_mul, map_neg]
  linear_combination (admY i j) * C2I_mul_C2I

theorem D_eig_z' (hij : i ≠ j) :
    admD i j ((admY i i - admY j j) - C (2 * Complex.I) * admY i j) =
      (2 * Complex.I) • ((admY i i - admY j j) - C (2 * Complex.I) * admY i j) := by
  rw [map_sub, map_sub, D_C_mul, D_Y_ii i j hij, D_Y_jj i j hij, D_Y_ij i j hij, smul_eq_C_mul]
  linear_combination (admY i j) * C2I_mul_C2I

theorem D_eig_t (hik : i ≠ k) (hjk : j ≠ k) : admD i j (admY k k) = (0 : ℂ) • admY k k := by
  rw [D_Y_kk i j k hik hjk, zero_smul]

theorem D_eig_v (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    admD i j (admY i k + C Complex.I * admY j k) = (-Complex.I) • (admY i k + C Complex.I * admY j k) := by
  rw [map_add, D_C_mul, D_Y_ik i j k hij hik hjk, D_Y_jk i j k hij hik hjk, smul_eq_C_mul, map_neg]
  linear_combination (admY j k) * CI_mul_CI

theorem D_eig_v' (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    admD i j (admY i k - C Complex.I * admY j k) = Complex.I • (admY i k - C Complex.I * admY j k) := by
  rw [map_sub, D_C_mul, D_Y_ik i j k hij hik hjk, D_Y_jk i j k hij hik hjk, smul_eq_C_mul]
  linear_combination (admY j k) * CI_mul_CI

theorem D_eig (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : Fin 6) :
    admD i j (eig i j k n) = wtv n • eig i j k n := by
  fin_cases n
  · exact D_eig_u i j hij
  · exact D_eig_z i j hij
  · exact D_eig_z' i j hij
  · exact D_eig_t i j k hik hjk
  · exact D_eig_v i j k hij hik hjk
  · exact D_eig_v' i j k hij hik hjk

abbrev admQ : Type := MvPolynomial (Fin 6) ℂ

def admE : Derivation ℂ admQ admQ := mkDerivation ℂ fun n : Fin 6 => wtv n • X n

theorem E_X (n : Fin 6) : admE (X n) = wtv n • X n := mkDerivation_X _ _ _

theorem E_C (a : ℂ) : admE (C a) = 0 := by
  rw [← algebraMap_eq]
  exact Derivation.map_algebraMap _ _

theorem D_C' (i j : Fin 3) (a : ℂ) : admD i j (C a) = 0 := by
  rw [← algebraMap_eq]
  exact Derivation.map_algebraMap _ _

def Φ : admQ →ₐ[ℂ] admP := aeval (eig i j k)

theorem Φ_X (n : Fin 6) : Φ i j k (X n) = eig i j k n := aeval_X _ _

theorem Φ_C (a : ℂ) : Φ i j k (C a) = C a := by
  rw [Φ, aeval_C, algebraMap_eq]

theorem D_Φ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : admQ) : admD i j (Φ i j k f) = Φ i j k (admE f) :=
    by
  induction f using MvPolynomial.induction_on with
  | C a => rw [Φ_C, D_C', E_C, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f n hf =>
    simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul, Φ_X, D_eig i j k hij hik hjk, hf, E_X, map_smul]

theorem Y_mem_range (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : Fin 3) : admY a b ∈ (Φ i j k).range := by
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

theorem Φ_surjective (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Surjective (Φ i j k) := by
  have hrange : (Φ i j k).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨w, rfl⟩
    have hw : (X w : admP) = admY w.1.1 w.1.2 := by simp [admY, w.2]
    rw [hw]
    exact Y_mem_range i j k hij hik hjk _ _
  exact fun p => by
    have : p ∈ (Φ i j k).range := hrange ▸ Algebra.mem_top
    exact this

def ψval (a b : Fin 3) : admQ :=
  if a = b then
    (if a = i then C (1 / 2) * (X 0 + C (1 / 2) * (X 1 + X 2))
      else if a = j then C (1 / 2) * (X 0 - C (1 / 2) * (X 1 + X 2)) else X 3)
  else if a = k ∨ b = k then
    (if a = i ∨ b = i then C (1 / 2) * (X 4 + X 5) else C (-Complex.I / 2) * (X 4 - X 5))
  else C (-Complex.I / 4) * (X 1 - X 2)

def Ψ : admP →ₐ[ℂ] admQ := aeval fun w : admIdx => ψval i j k w.1.1 w.1.2

theorem Ψ_C (a : ℂ) : Ψ i j k (C a) = C a := by
  rw [Ψ, aeval_C, algebraMap_eq]

theorem Ψ_Y (a b : Fin 3) (hab : a ≤ b) : Ψ i j k (admY a b) = ψval i j k a b := by
  have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
  rw [hY, Ψ, aeval_X]

theorem Ψ_Y' (a b : Fin 3) : Ψ i j k (admY a b) = ψval i j k a b ∨ Ψ i j k (admY a b) = ψval i j k b a := by
  by_cases hab : a ≤ b
  · exact Or.inl (Ψ_Y i j k a b hab)
  · right
    rw [Y_symm, Ψ_Y i j k b a (le_of_not_ge hab)]

theorem Ψ_Φ_X (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : Fin 6) : Ψ i j k (Φ i j k (X n)) = X n := by
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

theorem Φ_injective (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Injective (Φ i j k) := by
  have h : (Ψ i j k).comp (Φ i j k) = AlgHom.id ℂ admQ :=
    algHom_ext fun n => by rw [AlgHom.comp_apply, Ψ_Φ_X i j k hij hik hjk, AlgHom.id_apply]
  intro f g hfg
  have := congrArg (Ψ i j k) hfg
  rwa [← AlgHom.comp_apply, h, ← AlgHom.comp_apply (Ψ i j k), h, AlgHom.id_apply, AlgHom.id_apply] at this

end Distinct

def wsum (m : Fin 6 →₀ ℕ) : ℂ := ∑ n : Fin 6, (m n : ℂ) * wtv n

theorem E_monomial (m : Fin 6 →₀ ℕ) (r : ℂ) : admE (monomial m r) = wsum m • monomial m r := by
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

theorem wsum_eq_zero_of_mem_support {f : admQ} (hf : admE f = 0) {m : Fin 6 →₀ ℕ} (hm : m ∈ f.support) :
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

theorem balanced_of_wsum_eq_zero {m : Fin 6 →₀ ℕ} (h : wsum m = 0) : 2 * m 2 + m 5 = 2 * m 1 + m 4 := by
  unfold wsum at h
  rw [Fin.sum_univ_six] at h
  simp only [wtv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, zero_add] at h
  have h' : ((2 * m 2 + m 5 : ℕ) : ℂ) * Complex.I = ((2 * m 1 + m 4 : ℕ) : ℂ) * Complex.I := by
    push_cast
    linear_combination h
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h'

def restrictDiag : admP →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval fun w : admIdx => if w.1.1 = w.1.2 then X w.1.1 else 0

theorem restrictDiag_Y (a b : Fin 3) : restrictDiag (admY a b) = if a = b then X a else 0 := by
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, restrictDiag, aeval_X]
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, restrictDiag, aeval_X]
    have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
    simp [hne, Ne.symm hne]

theorem restrictDiag_C (c : ℂ) : restrictDiag (C c) = C c := by
  rw [restrictDiag, aeval_C, algebraMap_eq]

section Distinct₂

variable (i j k : Fin 3)

def ρ : admQ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![X i + X j, X i - X j, X i - X j, X k, 0, 0]

theorem restrictDiag_comp_Φ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    restrictDiag.comp (Φ i j k) = ρ i j k := by
  refine algHom_ext fun n => ?_
  rw [AlgHom.comp_apply, Φ_X, ρ, aeval_X]
  fin_cases n <;>
    simp only [eig, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul,
      restrictDiag_Y, restrictDiag_C, if_true, hij, hik, hjk, if_false, mul_zero, add_zero, sub_zero]

theorem rename_swap_ρ_monomial (hik : i ≠ k) (hjk : j ≠ k) (m : Fin 6 →₀ ℕ) (r : ℂ)
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

theorem rename_swap_restrictDiag (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : admP) (hp : admD i j p = 0) :
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

def wt : admIdx → ℕ := fun v => if v.1.1 = v.1.2 then 0 else 1

theorem wt_le_one (v : admIdx) : wt v ≤ 1 := by
  unfold wt
  split_ifs <;> omega

abbrev IsWH (q : admP) (n : ℕ) : Prop := IsWeightedHomogeneous wt q n

abbrev wcomp (n : ℕ) : admP →ₗ[ℂ] admP := weightedHomogeneousComponent wt n

theorem isWH_sub {q r : admP} {n : ℕ} (hq : IsWH q n) (hr : IsWH r n) : IsWH (q - r) n :=
  (weightedHomogeneousSubmodule ℂ wt n).sub_mem hq hr

theorem isWH_neg {q : admP} {n : ℕ} (hq : IsWH q n) : IsWH (-q) n :=
  (weightedHomogeneousSubmodule ℂ wt n).neg_mem hq

theorem isWH_smul {q : admP} {n : ℕ} (c : ℂ) (hq : IsWH q n) : IsWH (c • q) n :=
  (weightedHomogeneousSubmodule ℂ wt n).smul_mem c hq

theorem isWH_two_mul {q : admP} {n : ℕ} (hq : IsWH q n) : IsWH (2 * q) n := by
  have h : (2 : admP) * q = (2 : ℂ) • q := by rw [smul_eq_C_mul, map_ofNat]
  rw [h]
  exact isWH_smul 2 hq

theorem isWH_Y (a b : Fin 3) : IsWH (admY a b) (if a = b then 0 else 1) := by
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY]
    simpa [wt] using isWeightedHomogeneous_X (R := ℂ) wt (⟨(a, b), hab⟩ : admIdx)
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
    rw [hY]
    simpa [wt, hne, Ne.symm hne] using isWeightedHomogeneous_X (R := ℂ) wt (⟨(b, a), le_of_not_ge hab⟩ : admIdx)

theorem isWH_Y_diag (a : Fin 3) : IsWH (admY a a) 0 := by simpa using isWH_Y a a

theorem isWH_Y_off {a b : Fin 3} (hab : a ≠ b) : IsWH (admY a b) 1 := by simpa [hab] using isWH_Y a b

def zidx (i j : Fin 3) : admIdx := if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), le_of_not_ge h⟩

theorem X_zidx (i j : Fin 3) : (X (zidx i j) : admP) = admY i j := by
  unfold zidx admY
  simp only [Matrix.of_apply]
  split_ifs <;> rfl

theorem wt_zidx {i j : Fin 3} (hij : i ≠ j) : wt (zidx i j) = 1 := by
  unfold zidx wt
  split_ifs <;> simp_all

theorem zidx_eq_of_le {a b : Fin 3} (hab : a ≤ b) : zidx a b = ⟨(a, b), hab⟩ := by
  simp [zidx, hab]

theorem zidx_eq_of_ge {a b : Fin 3} (hab : b ≤ a) (hne : a ≠ b) : zidx a b = ⟨(b, a), hab⟩ := by
  have h : ¬ a ≤ b := fun h => hne (le_antisymm h hab)
  simp [zidx, h]

theorem D_expand (i j : Fin 3) (q : admP) : admD i j q = ∑ v : admIdx, admD i j (X v) * pderiv v q := by
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

theorem isWH_pderiv {q : admP} {n : ℕ} (hq : IsWH q n) (v : admIdx) : IsWH (pderiv v q) (n - wt v) := by
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

theorem isWH_D_zidx (hij : i ≠ j) : IsWH (admD i j (X (zidx i j))) 0 := by
  rw [X_zidx, D_Y_ij i j hij]
  exact isWH_sub (isWH_Y_diag j) (isWH_Y_diag i)

theorem D_zidx_ne_zero (hij : i ≠ j) : admD i j (X (zidx i j)) ≠ 0 := by
  rw [X_zidx, D_Y_ij i j hij, sub_ne_zero]
  have h1 : admY j j = X (⟨(j, j), le_rfl⟩ : admIdx) := by simp [admY]
  have h2 : admY i i = X (⟨(i, i), le_rfl⟩ : admIdx) := by simp [admY]
  rw [h1, h2]
  intro h
  exact hij (congrArg (fun v : admIdx => v.1.1) (X_injective h)).symm

theorem tri (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Fin 3) : x = i ∨ x = j ∨ x = k := by
  revert i j k x
  decide

theorem isWH_D_X_one (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : admIdx) (hv : v ≠ zidx i j) :
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

theorem comp_D_of_isWH (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {h : admP} {e : ℕ} (hh : IsWH h e) {n : ℕ}
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

theorem comp_D_tail (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {r : admP} {d : ℕ} (hd : d ≠ 0)
    (hr : ∀ n ≤ d, wcomp n r = 0) : wcomp (d - 1) (admD i j r) = 0 := by
  have hfin := weightedHomogeneousComponent_finsupp (w := wt) r
  conv_lhs => rw [← sum_weightedHomogeneousComponent wt r, finsum_eq_sum _ hfin, map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases le_or_gt m d with hm | hm
  · rw [hr m hm, map_zero, map_zero]
  · have hhom : IsWH (wcomp m r) m := weightedHomogeneousComponent_isWeightedHomogeneous m r
    rw [comp_D_of_isWH i j k hij hik hjk hhom (by omega), if_neg (by omega)]

end Distinct

def killOff : admP →ₐ[ℂ] admP := aeval fun v : admIdx => if v.1.1 = v.1.2 then X v else 0

def admemb : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] admP := rename fun a : Fin 3 => (⟨(a, a), le_rfl⟩ : admIdx)

theorem emb_restrictDiag (q : admP) : admemb (restrictDiag q) = killOff q := by
  suffices h : admemb.comp restrictDiag = killOff from AlgHom.congr_fun h q
  refine algHom_ext fun v => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := v
  by_cases h : a = b
  · subst h
    simp [admemb, restrictDiag, killOff]
  · simp [admemb, restrictDiag, killOff, h]

theorem weight_eq_zero_iff (m : admIdx →₀ ℕ) :
    Finsupp.weight wt m = 0 ↔ ∀ v ∈ m.support, v.1.1 = v.1.2 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  have hmv : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  unfold wt
  split_ifs with h <;> simp [h, hmv]

theorem killOff_monomial (m : admIdx →₀ ℕ) (c : ℂ) :
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

theorem comp_zero_monomial (m : admIdx →₀ ℕ) (c : ℂ) :
    wcomp 0 (monomial m c) = if Finsupp.weight wt m = 0 then monomial m c else 0 := by
  ext n
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hn hm hm
  · rfl
  · rw [coeff_monomial, if_neg (fun h => hm (by rw [h]; exact hn)), coeff_zero]
  · rw [coeff_monomial, if_neg (fun h => hn (by rw [← h]; exact hm))]
  · rfl

theorem killOff_eq_comp_zero (q : admP) : killOff q = wcomp 0 q := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c => rw [killOff_monomial, comp_zero_monomial]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem comp_zero_eq_zero_of_restrictDiag {p : admP} (h0 : restrictDiag p = 0) : wcomp 0 p = 0 := by
  rw [← killOff_eq_comp_zero, ← emb_restrictDiag, h0, map_zero]

theorem exists_third (a b : Fin 3) (hab : a ≠ b) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  revert a b
  decide

theorem eq_zero_of_restrictDiag_eq_zero {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0)
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

def traces (n : Fin 3) : admP := (admY ^ ((n : ℕ) + 1)).trace

def psums (n : Fin 3) : MvPolynomial (Fin 3) ℂ := psum (Fin 3) ℂ ((n : ℕ) + 1)

theorem Y_map_restrictDiag :
    admY.map restrictDiag = Matrix.diagonal fun a : Fin 3 => (X a : MvPolynomial (Fin 3) ℂ) := by
  ext a b
  rw [Matrix.map_apply, restrictDiag_Y, Matrix.diagonal_apply]

theorem restrictDiag_trace_pow (m : ℕ) : restrictDiag ((admY ^ m).trace) = psum (Fin 3) ℂ m := by
  have h1 : (admY ^ m).map restrictDiag = (admY.map restrictDiag) ^ m := by
    simpa only [AlgHom.mapMatrix_apply] using map_pow restrictDiag.mapMatrix admY m
  rw [Y_map_restrictDiag, Matrix.diagonal_pow] at h1
  simp only [Matrix.trace, Matrix.diag, map_sum, psum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := congrFun (congrFun h1 a) a
  rw [Matrix.map_apply, Matrix.diagonal_apply_eq] at this
  exact this

theorem restrictDiag_traces (n : Fin 3) : restrictDiag (traces n) = psums n := restrictDiag_trace_pow _

theorem D_aeval_traces (i j : Fin 3) (G : MvPolynomial (Fin 3) ℂ) : admD i j (aeval traces G) = 0 := by
  induction G using MvPolynomial.induction_on with
  | C c => rw [aeval_C, Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p n hp =>
    rw [map_mul, aeval_X, Derivation.leibniz, hp, smul_zero, add_zero, traces, D_trace_Y_pow, smul_zero]

theorem isSymmetric_restrictDiag {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0) :
    (restrictDiag p).IsSymmetric := by
  intro e
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy hf =>
    rw [Equiv.Perm.coe_mul, ← rename_rename, hf]
    obtain ⟨z, hxz, hyz⟩ := exists_third x y hxy
    exact rename_swap_restrictDiag x y z hxy hxz hyz p (hp x y)

abbrev R3 : Subalgebra ℂ (MvPolynomial (Fin 3) ℂ) := (aeval (R := ℂ) psums).range

theorem psum_mem {m : ℕ} (h1 : 1 ≤ m) (h3 : m ≤ 3) : psum (Fin 3) ℂ m ∈ R3 := by
  rw [AlgHom.mem_range]
  refine ⟨X ⟨m - 1, by omega⟩, ?_⟩
  rw [aeval_X, psums]
  congr 1
  exact Nat.sub_add_cancel h1

theorem esymm_mem (k : ℕ) : k ≤ 3 → esymm (Fin 3) ℂ k ∈ R3 := by
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

theorem aeval_esymm_mem (φ : MvPolynomial (Fin 3) ℂ) :
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

theorem exists_eq_aeval_traces {p : admP} (hp : ∀ i j : Fin 3, admD i j p = 0) :
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

example : restrictDiag (traces 0) = X 0 + X 1 + X 2 := by
  rw [restrictDiag_traces, psums, psum]
  simp [Fin.sum_univ_three]

example : ∃ G : MvPolynomial (Fin 3) ℂ, (admY ^ 2).trace + 5 * admY.trace ^ 3 = aeval traces G := by
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

def wordOp (g : ι → Module.End ℂ V) (l : List ι) : Module.End ℂ V := (l.map g).prod

theorem wordOp_nil (g : ι → Module.End ℂ V) : wordOp g [] = 1 := by
  simp [wordOp]

theorem wordOp_cons (g : ι → Module.End ℂ V) (x : ι) (l : List ι) : wordOp g (x :: l) = g x * wordOp g l := by
  simp [wordOp]

theorem wordOp_append (g : ι → Module.End ℂ V) (l l' : List ι) :
    wordOp g (l ++ l') = wordOp g l * wordOp g l' := by
  simp [wordOp]

def lengthSpan (g : ι → Module.End ℂ V) (n : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ l : List ι, l.length ≤ n ∧ wordOp g l = T}

theorem wordOp_mem_lengthSpan (g : ι → Module.End ℂ V) {l : List ι} {n : ℕ} (h : l.length ≤ n) :
    wordOp g l ∈ lengthSpan g n :=
  Submodule.subset_span ⟨l, h, rfl⟩

theorem one_mem_lengthSpan (g : ι → Module.End ℂ V) (n : ℕ) : (1 : Module.End ℂ V) ∈ lengthSpan g n := by
  rw [← wordOp_nil g]
  exact wordOp_mem_lengthSpan g (by simp)

theorem lengthSpan_mono (g : ι → Module.End ℂ V) {m n : ℕ} (h : m ≤ n) : lengthSpan g m ≤ lengthSpan g n :=
  Submodule.span_mono fun _ hT => by
    obtain ⟨l, hl, rfl⟩ := hT
    exact ⟨l, hl.trans h, rfl⟩

theorem letter_mul_mem (g : ι → Module.End ℂ V) (x : ι) {n : ℕ} {T : Module.End ℂ V}
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

theorem span_letters_mul_mem (g : ι → Module.End ℂ V) {S : Module.End ℂ V}
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

theorem wordOp_mul_mem (g : ι → Module.End ℂ V) {l : List ι} {m n : ℕ} (hl : l.length ≤ m)
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

theorem mul_mem_lengthSpan (g : ι → Module.End ℂ V) {m n : ℕ} {S T : Module.End ℂ V}
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

theorem wordOp_sub_wordOp_mem_of_perm (g : ι → Module.End ℂ V)
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

def wordSym (l : List ι) : MvPolynomial ι ℂ := (l.map MvPolynomial.X).prod

theorem wordSym_append (l l' : List ι) : wordSym (l ++ l') = wordSym l * wordSym l' := by
  simp [wordSym]

variable [DecidableEq ι]

theorem wordSym_eq_monomial (l : List ι) :
    wordSym l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset ι)) (1 : ℂ) := by
  induction l with
  | nil =>
    simp [wordSym, MvPolynomial.monomial_zero']
  | cons x l ih =>
    have hX : (MvPolynomial.X x : MvPolynomial ι ℂ) = MvPolynomial.monomial (Finsupp.single x 1) 1 := rfl
    rw [wordSym, List.map_cons, List.prod_cons, ← wordSym, ih, hX, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]

def reprWord (μ : ι →₀ ℕ) : List ι := (Multiset.toFinsupp.symm μ).toList

theorem reprWord_perm (l : List ι) : (reprWord (Multiset.toFinsupp (l : Multiset ι))).Perm l := by
  rw [← Multiset.coe_eq_coe, reprWord, Multiset.coe_toList, AddEquiv.symm_apply_apply]

theorem reprWord_length (l : List ι) : (reprWord (Multiset.toFinsupp (l : Multiset ι))).length = l.length :=
  (reprWord_perm l).length_eq

omit [DecidableEq ι] in
theorem wordSym_cons (x : ι) (l : List ι) : wordSym (x :: l) = MvPolynomial.X x * wordSym l := by
  simp [wordSym]

theorem toFinsupp_reprWord (μ : ι →₀ ℕ) : Multiset.toFinsupp ((reprWord μ : List ι) : Multiset ι) = μ := by
  rw [reprWord, Multiset.coe_toList, AddEquiv.apply_symm_apply]

theorem reprWord_length_eq (μ : ι →₀ ℕ) : (reprWord μ).length = μ.degree := by
  rw [reprWord, Multiset.length_toList]
  change Multiset.card (Finsupp.toMultiset μ) = _
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

def fword (l : List ι) : FreeAlgebra ℂ ι := (l.map (FreeAlgebra.ι ℂ)).prod

omit [DecidableEq ι] in
theorem fword_nil : fword ([] : List ι) = 1 := by
  simp [fword]

omit [DecidableEq ι] in
theorem fword_cons (x : ι) (l : List ι) : fword (x :: l) = FreeAlgebra.ι ℂ x * fword l := by
  simp [fword]

omit [DecidableEq ι] in
theorem fword_append (l l' : List ι) : fword (l ++ l') = fword l * fword l' := by
  simp [fword]

def filt (n : ℕ) : Submodule ℂ (FreeAlgebra ℂ ι) :=
  Submodule.span ℂ {a | ∃ l : List ι, l.length ≤ n ∧ fword l = a}

omit [DecidableEq ι] in
theorem fword_mem_filt {l : List ι} {n : ℕ} (h : l.length ≤ n) : fword l ∈ filt n :=
  Submodule.subset_span ⟨l, h, rfl⟩

omit [DecidableEq ι] in

theorem ι_mul_mem_filt (x : ι) {n : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt n) :
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

theorem mem_filt_mul_fword {m : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt m) (l : List ι) :
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

def admop (g : ι → Module.End ℂ V) : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ g

omit [DecidableEq ι] in
theorem op_ι (g : ι → Module.End ℂ V) (x : ι) : admop g (FreeAlgebra.ι ℂ x) = g x := by
  simp [admop]

omit [DecidableEq ι] in
theorem op_fword (g : ι → Module.End ℂ V) (l : List ι) : admop g (fword l) = wordOp g l := by
  induction l with
  | nil => rw [fword_nil, map_one, wordOp_nil]
  | cons x l ih => rw [fword_cons, map_mul, op_ι, ih, wordOp_cons]

omit [DecidableEq ι] in
theorem op_mem_lengthSpan (g : ι → Module.End ℂ V) {n : ℕ} {a : FreeAlgebra ℂ ι} (ha : a ∈ filt n) :
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

def sym : FreeAlgebra ℂ ι →ₐ[ℂ] MvPolynomial ι ℂ := FreeAlgebra.lift ℂ MvPolynomial.X

omit [DecidableEq ι] in
theorem sym_ι (x : ι) : sym (FreeAlgebra.ι ℂ x) = (MvPolynomial.X x : MvPolynomial ι ℂ) := by
  simp [sym]

omit [DecidableEq ι] in
theorem sym_fword (l : List ι) : sym (fword l) = wordSym l := by
  induction l with
  | nil => rw [fword_nil, map_one, wordSym, List.map_nil, List.prod_nil]
  | cons x l ih => rw [fword_cons, map_mul, sym_ι, ih, wordSym_cons]

def admL : MvPolynomial ι ℂ →ₗ[ℂ] FreeAlgebra ℂ ι :=
  (MvPolynomial.basisMonomials ι ℂ).constr ℂ fun μ => fword (reprWord μ)

theorem L_monomial (μ : ι →₀ ℕ) (c : ℂ) : admL (MvPolynomial.monomial μ c) = c • fword (reprWord μ) := by
  have h1 : (MvPolynomial.monomial μ c : MvPolynomial ι ℂ) = c • MvPolynomial.basisMonomials ι ℂ μ := by
    simp [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial]
  rw [h1, map_smul, admL]
  erw [Module.Basis.constr_basis]

theorem L_X (x : ι) : admL (MvPolynomial.X x : MvPolynomial ι ℂ) = FreeAlgebra.ι ℂ x := by
  have hrepr : reprWord (Finsupp.single x 1 : ι →₀ ℕ) = [x] := by
    rw [reprWord, ← Multiset.toFinsupp_singleton, AddEquiv.symm_apply_apply, Multiset.toList_singleton]
  rw [MvPolynomial.X, L_monomial, one_smul, hrepr, fword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]

theorem sym_L (t : MvPolynomial ι ℂ) : sym (admL t) = t := by
  suffices h : (sym (ι := ι)).toLinearMap ∘ₗ admL = LinearMap.id from LinearMap.congr_fun h t
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun μ => ?_
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply, MvPolynomial.coe_basisMonomials]
  rw [L_monomial, one_smul, sym_fword, wordSym_eq_monomial, toFinsupp_reprWord]

theorem L_mem_filt {t : MvPolynomial ι ℂ} {n : ℕ} (ht : t.IsHomogeneous n) : admL t ∈ filt n := by
  rw [t.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  rw [L_monomial]
  refine Submodule.smul_mem _ _ (fword_mem_filt ?_)
  rw [reprWord_length_eq, Finsupp.degree_eq_weight_one]
  exact (ht (MvPolynomial.mem_support_iff.1 hμ)).le

theorem op_sub_op_L_sym_mem (g : ι → Module.End ℂ V)
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

theorem exists_bracket_wordOp (hbr : ∀ x : ι, κ * g x - g x * κ = admop g (admL (δ (MvPolynomial.X x))))
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

theorem bracket_op_L_sub_mem (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g))
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

example (g : ι → Module.End ℂ V) (x : ι) : admop g (admL (MvPolynomial.X x : MvPolynomial ι ℂ)) = g x := by
  rw [L_X, op_ι]

example (x y : ι) :
    sym (fword [x, y]) = MvPolynomial.X x * MvPolynomial.X y ∧
      sym (fword [y, x]) = MvPolynomial.X x * MvPolynomial.X y := by
  constructor
  · rw [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one]
  · rw [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one, mul_comm]

example (g : ι → Module.End ℂ V)
    (hg : ∀ i j : ι, g i * g j - g j * g i ∈ Submodule.span ℂ (Set.range g)) (x y : ι) :
    g x * g y - admop g (admL (MvPolynomial.X x * MvPolynomial.X y)) ∈ lengthSpan g 1 := by
  have h := op_sub_op_L_sym_mem g hg (fword_mem_filt (l := [x, y]) (n := 2) le_rfl)
  rwa [sym_fword, wordSym_cons, wordSym_cons, wordSym, List.map_nil, List.prod_nil, mul_one, op_fword, wordOp_cons,
    wordOp_cons, wordOp_nil, mul_one] at h

end SymbolLemma

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial Matrix

abbrev Letter : Type := admIdx ⊕ (Fin 3 × Fin 3)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def letters (e : Fin 3 → Fin 3 → Module.End ℂ V) : Letter → Module.End ℂ V
  | Sum.inl v => (2⁻¹ : ℂ) • (e v.1.1 v.1.2 + e v.1.2 v.1.1)
  | Sum.inr ij => e ij.1 ij.2 - e ij.2 ij.1

theorem letters_inr (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) :
    letters e (Sum.inr (i, j)) = e i j - e j i := rfl

def pIdx (a b : Fin 3) : admIdx := if h : a ≤ b then ⟨(a, b), h⟩ else ⟨(b, a), le_of_not_ge h⟩

theorem Y_eq_X_pIdx (a b : Fin 3) : admY a b = X (pIdx a b) := by
  unfold admY pIdx
  simp only [Matrix.of_apply]
  split_ifs <;> rfl

theorem letters_inl_pIdx (e : Fin 3 → Fin 3 → Module.End ℂ V) (a b : Fin 3) :
    letters e (Sum.inl (pIdx a b)) = (2⁻¹ : ℂ) • (e a b + e b a) := by
  unfold pIdx
  split_ifs
  · rfl
  · show (2⁻¹ : ℂ) • (e b a + e a b) = _
    rw [add_comm]

def admfe (i j : Fin 3) : FreeAlgebra ℂ Letter :=
  FreeAlgebra.ι ℂ (Sum.inl (pIdx i j) : Letter) + (2⁻¹ : ℂ) • FreeAlgebra.ι ℂ (Sum.inr (i, j) : Letter)

theorem op_fe (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) : admop (letters e) (admfe i j) = e i j := by
  rw [admfe, map_add, map_smul, op_ι, op_ι, letters_inl_pIdx, letters_inr]
  module

def admproj : MvPolynomial Letter ℂ →ₐ[ℂ] admP :=
  aeval (Sum.elim (fun v : admIdx => (X v : admP)) fun _ : Fin 3 × Fin 3 => (0 : admP))

theorem proj_X_inl (v : admIdx) : admproj (X (Sum.inl v : Letter)) = X v := by
  simp [admproj]

theorem proj_X_inr (ij : Fin 3 × Fin 3) : admproj (X (Sum.inr ij : Letter)) = 0 := by
  simp [admproj]

def admemb : admP →ₐ[ℂ] MvPolynomial Letter ℂ := rename Sum.inl

theorem emb_X (v : admIdx) : admemb (X v) = X (Sum.inl v : Letter) := by
  simp [admemb]

theorem proj_emb (s : admP) : admproj (admemb s) = s := by
  simp only [admproj, admemb, aeval_rename]
  exact aeval_X_left_apply s

def psym : FreeAlgebra ℂ Letter →ₐ[ℂ] admP := admproj.comp sym

theorem psym_ι_inl (v : admIdx) : psym (FreeAlgebra.ι ℂ (Sum.inl v : Letter)) = X v := by
  rw [psym, AlgHom.comp_apply, sym_ι, proj_X_inl]

theorem psym_ι_inr (ij : Fin 3 × Fin 3) : psym (FreeAlgebra.ι ℂ (Sum.inr ij : Letter)) = 0 := by
  rw [psym, AlgHom.comp_apply, sym_ι, proj_X_inr]

theorem psym_fe (i j : Fin 3) : psym (admfe i j) = admY i j := by
  rw [admfe, map_add, map_smul, psym_ι_inl, psym_ι_inr, smul_zero, add_zero, Y_eq_X_pIdx]

theorem map_cas {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (e : Fin 3 → Fin 3 → A) (n : ℕ) :
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

theorem op_cas (e : Fin 3 → Fin 3 → Module.End ℂ V) (k : ℕ) : admop (letters e) (cas admfe k) = cas e k := by
  have h := map_cas (admop (letters e)).toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, op_fe] at h
  exact h

theorem psym_cas (k : ℕ) : psym (cas admfe k) = (admY ^ k).trace := by
  have h := map_cas psym.toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, psym_fe] at h
  rw [h]
  unfold cas
  congr 2

theorem ι_mem_filt_one (x : Letter) : FreeAlgebra.ι ℂ x ∈ filt 1 := by
  have h := fword_mem_filt (l := [x]) (n := 1) le_rfl
  simpa [fword] using h

theorem filt_mono' {m n : ℕ} (h : m ≤ n) : (filt m : Submodule ℂ (FreeAlgebra ℂ Letter)) ≤ filt n :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem one_mem_filt (n : ℕ) : (1 : FreeAlgebra ℂ Letter) ∈ filt n := by
  have h := fword_mem_filt (l := ([] : List Letter)) (n := n) (Nat.zero_le n)
  simpa [fword] using h

theorem fe_mem_filt (i j : Fin 3) : admfe i j ∈ filt 1 :=
  add_mem (ι_mem_filt_one _) (Submodule.smul_mem _ _ (ι_mem_filt_one _))

theorem mul_mem_filt {m n : ℕ} {a b : FreeAlgebra ℂ Letter} (ha : a ∈ filt m) (hb : b ∈ filt n) :
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

theorem gen_fe_pow_entry_mem_filt (k : ℕ) (a b : Fin 3) : (admgen admfe ^ k) a b ∈ filt k := by
  induction k generalizing a b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact one_mem_filt 0
    · exact zero_mem _
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Submodule.sum_mem _ fun c _ => mul_mem_filt (ih a c) (fe_mem_filt c b)

theorem cas_mem_filt (k : ℕ) : cas admfe k ∈ filt k := by
  unfold cas
  exact Submodule.sum_mem _ fun a _ => gen_fe_pow_entry_mem_filt k a a

theorem isHomogeneous_sym_fe (i j : Fin 3) : (sym (admfe i j)).IsHomogeneous 1 := by
  rw [admfe, map_add, map_smul, sym_ι, sym_ι]
  refine (isHomogeneous_X ℂ _).add ?_
  rw [smul_eq_C_mul]
  simpa using (isHomogeneous_C Letter (2⁻¹ : ℂ)).mul (isHomogeneous_X ℂ (Sum.inr (i, j) : Letter))

theorem isHomogeneous_pow_entry {σ : Type*} (M : Matrix (Fin 3) (Fin 3) (MvPolynomial σ ℂ))
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

theorem isHomogeneous_gen_pow_entry (f : Fin 3 → Fin 3 → MvPolynomial Letter ℂ)
    (hf : ∀ i j, (f i j).IsHomogeneous 1) (k : ℕ) (a b : Fin 3) : ((admgen f ^ k) a b).IsHomogeneous k :=
  isHomogeneous_pow_entry (admgen f) (fun i j => hf i j) k a b

theorem isHomogeneous_sym_cas (k : ℕ) : (sym (cas admfe k)).IsHomogeneous k := by
  have h := map_cas sym.toRingHom admfe k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  unfold cas
  exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_gen_pow_entry _ isHomogeneous_sym_fe k a a

def tw (k : Fin 3) : ℕ := (k : ℕ) + 1

theorem weight_tw (α : Fin 3 →₀ ℕ) : Finsupp.weight tw α = α 0 * 1 + α 1 * 2 + α 2 * 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [Fin.sum_univ_three, tw]
  · intro i
    simp

theorem isHomogeneous_Y_entry (a b : Fin 3) : (admY a b).IsHomogeneous 1 := by
  rw [Y_eq_X_pIdx]
  exact isHomogeneous_X ℂ _

theorem isHomogeneous_traces (k : Fin 3) : (traces k).IsHomogeneous (tw k) := by
  unfold traces tw
  exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_pow_entry admY isHomogeneous_Y_entry _ a a

theorem aeval_traces_monomial_one (α : Fin 3 →₀ ℕ) :
    aeval traces (monomial α (1 : ℂ)) = traces 0 ^ α 0 * traces 1 ^ α 1 * traces 2 ^ α 2 := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]

theorem isHomogeneous_aeval_traces_monomial (α : Fin 3 →₀ ℕ) (c : ℂ) :
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

theorem isHomogeneous_aeval_traces_of_isWeightedHomogeneous {G : MvPolynomial (Fin 3) ℂ} {m : ℕ}
    (hG : IsWeightedHomogeneous tw G m) : (aeval traces G).IsHomogeneous m := by
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun α hα => ?_
  have h := isHomogeneous_aeval_traces_monomial α (coeff α G)
  rwa [hG (mem_support_iff.1 hα)] at h

theorem exists_isWeightedHomogeneous_aeval_traces_eq {n : ℕ} {s : admP} (hs : s.IsHomogeneous n)
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

def QF (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ w : List Letter, w.length ≤ n ∧ ∃ f ∈ F, wordOp (letters e) w f = v}

theorem QF_mono {m n : ℕ} (h : m ≤ n) : QF e F m ≤ QF e F n :=
  Submodule.span_mono fun _ ⟨w, hw, hf⟩ => ⟨w, hw.trans h, hf⟩

theorem wordOp_apply_mem_QF {w : List Letter} {n : ℕ} (hw : w.length ≤ n) {f : V} (hf : f ∈ F) :
    wordOp (letters e) w f ∈ QF e F n :=
  Submodule.subset_span ⟨w, hw, f, hf, rfl⟩

theorem apply_mem_QF {n : ℕ} {T : Module.End ℂ V} (hT : T ∈ lengthSpan (letters e) n) {f : V} (hf : f ∈ F) :
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

theorem wordOp_apply_mem_QF_of_inr_mem {w : List Letter} {ij : Fin 3 × Fin 3} (hij : (Sum.inr ij : Letter) ∈ w)
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

theorem op_L_monomial_apply_mem {μ : Letter →₀ ℕ} {ij : Fin 3 × Fin 3} (hμ : μ (Sum.inr ij) ≠ 0) {f : V}
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
theorem proj_monomial_of_inr {μ : Letter →₀ ℕ} {ij : Fin 3 × Fin 3} (hμ : μ (Sum.inr ij) ≠ 0) :
    admproj (monomial μ (1 : ℂ)) = 0 := by
  show aeval _ (monomial μ (1 : ℂ)) = 0
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hμ) ?_
  simp [zero_pow hμ]

omit hg hF in
theorem emb_proj_monomial_of_forall {μ : Letter →₀ ℕ} (hμ : ∀ ij : Fin 3 × Fin 3, μ (Sum.inr ij) = 0) :
    admemb (admproj (monomial μ (1 : ℂ))) = monomial μ 1 := by
  have key : ∀ x ∈ μ.support, admemb (admproj (X x)) = (X x : MvPolynomial Letter ℂ) := by
    intro x hx
    rcases x with v | ij
    · rw [proj_X_inl, emb_X]
    · exact absurd (hμ ij) (Finsupp.mem_support_iff.1 hx)
  rw [monomial_eq, map_one, one_mul, Finsupp.prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [map_pow, map_pow, key x hx]

theorem op_L_sub_op_L_emb_proj_apply_mem {n : ℕ} {u : MvPolynomial Letter ℂ} (hu : u.IsHomogeneous n) {f : V}
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
theorem pow_mem_filt {m : ℕ} {a : FreeAlgebra ℂ Letter} (ha : a ∈ filt m) (j : ℕ) : a ^ j ∈ filt (j * m) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_mul]
    exact one_mem_filt 0
  | succ j ih =>
    rw [pow_succ, add_mul, one_mul]
    exact mul_mem_filt ih ha

def casMon (α : Fin 3 →₀ ℕ) : FreeAlgebra ℂ Letter := cas admfe 1 ^ α 0 * cas admfe 2 ^ α 1 * cas admfe 3 ^ α 2

omit hg hF in
theorem casMon_mem_filt (α : Fin 3 →₀ ℕ) : casMon α ∈ filt (Finsupp.weight tw α) := by
  rw [weight_tw, casMon]
  exact mul_mem_filt (mul_mem_filt (pow_mem_filt (cas_mem_filt 1) _) (pow_mem_filt (cas_mem_filt 2) _))
    (pow_mem_filt (cas_mem_filt 3) _)

omit hg hF in
theorem isHomogeneous_sym_casMon (α : Fin 3 →₀ ℕ) : (sym (casMon α)).IsHomogeneous (Finsupp.weight tw α) := by
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, weight_tw]
  have h := (((isHomogeneous_sym_cas 1).pow (α 0)).mul ((isHomogeneous_sym_cas 2).pow (α 1))).mul
    ((isHomogeneous_sym_cas 3).pow (α 2))
  convert h using 1
  ring

omit hg hF in
theorem proj_sym_casMon (α : Fin 3 →₀ ℕ) : admproj (sym (casMon α)) = aeval traces (monomial α (1 : ℂ)) := by
  change psym (casMon α) = _
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, psym_cas, psym_cas, psym_cas, aeval_traces_monomial_one]
  simp [traces]

omit hg hF in
theorem op_casMon (α : Fin 3 →₀ ℕ) :
    admop (letters e) (casMon α) = cas e 1 ^ α 0 * cas e 2 ^ α 1 * cas e 3 ^ α 2 := by
  rw [casMon, map_mul, map_mul, map_pow, map_pow, map_pow, op_cas, op_cas, op_cas]

omit hg hF in
theorem admpow_apply_mem {Z : Submodule ℂ V} {T : Module.End ℂ V} (hT : ∀ z ∈ Z, T z ∈ Z) (j : ℕ) {z : V}
    (hz : z ∈ Z) : (T ^ j) z ∈ Z := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hT _ ih

omit hg hF in

theorem op_casMon_apply_mem {Z : Submodule ℂ V} (hFZ : F ≤ Z) (hZ₁ : ∀ z ∈ Z, cas e 1 z ∈ Z)
    (hZ₂ : ∀ z ∈ Z, cas e 2 z ∈ Z) (hZ₃ : ∀ z ∈ Z, cas e 3 z ∈ Z)
    (α : Fin 3 →₀ ℕ) {f : V} (hf : f ∈ F) : admop (letters e) (casMon α) f ∈ Z := by
  rw [op_casMon, Module.End.mul_apply, Module.End.mul_apply]
  exact admpow_apply_mem hZ₁ _ (admpow_apply_mem hZ₂ _ (admpow_apply_mem hZ₃ _ (hFZ hf)))

theorem op_L_emb_aeval_traces_monomial_apply_mem {Z : Submodule ℂ V} (hFZ : F ≤ Z)
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

theorem op_L_emb_apply_mem_of_invariant {Z : Submodule ℂ V} (hFZ : F ≤ Z)
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

example : ∃ G : MvPolynomial (Fin 3) ℂ, IsWeightedHomogeneous tw G 2 ∧ aeval traces G = (admY ^ 2).trace :=
  exists_isWeightedHomogeneous_aeval_traces_eq
    (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_pow_entry admY isHomogeneous_Y_entry 2 a a)
    (fun i j => D_trace_Y_pow i j 2)

example (e : Fin 3 → Fin 3 → Module.End ℂ V) :
    admop (letters e) (casMon (Finsupp.single 0 1 + Finsupp.single 2 1)) = cas e 1 * cas e 3 := by
  rw [op_casMon]
  simp

example (i j : Fin 3) : psym (admfe i j) = psym (admfe j i) := by
  rw [psym_fe, psym_fe, Y_symm]

end Adm0

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def admcm (a b : Module.End ℂ V) : Module.End ℂ V := a * b - b * a

theorem cm_add_left (a a' b : Module.End ℂ V) : admcm (a + a') b = admcm a b + admcm a' b := by
  simp only [admcm, add_mul, mul_add]
  abel

theorem cm_add_right (a b b' : Module.End ℂ V) : admcm a (b + b') = admcm a b + admcm a b' := by
  simp only [admcm, add_mul, mul_add]
  abel

theorem cm_sub_left (a a' b : Module.End ℂ V) : admcm (a - a') b = admcm a b - admcm a' b := by
  simp only [admcm, sub_mul, mul_sub]
  abel

theorem cm_sub_right (a b b' : Module.End ℂ V) : admcm a (b - b') = admcm a b - admcm a b' := by
  simp only [admcm, sub_mul, mul_sub]
  abel

theorem cm_smul_left (z : ℂ) (a b : Module.End ℂ V) : admcm (z • a) b = z • admcm a b := by
  simp only [admcm, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem cm_smul_right (z : ℂ) (a b : Module.End ℂ V) : admcm a (z • b) = z • admcm a b := by
  simp only [admcm, smul_mul_assoc, mul_smul_comm, smul_sub]

def LS (e : Fin 3 → Fin 3 → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ (Set.range (letters e))

theorem e_mem_LS (e : Fin 3 → Fin 3 → Module.End ℂ V) (i j : Fin 3) : e i j ∈ LS e := by
  have h : e i j = letters e (Sum.inl (pIdx i j)) + (2⁻¹ : ℂ) • letters e (Sum.inr (i, j)) := by
    rw [letters_inl_pIdx, letters_inr]
    module
  rw [h]
  exact add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

section Table

variable {e : Fin 3 → Fin 3 → Module.End ℂ V} (he : admRel e)
include he

theorem cm_e_mem_LS (a b c d : Fin 3) : admcm (e a b) (e c d) ∈ LS e := by
  rw [admcm, he]
  split_ifs
  · exact sub_mem (e_mem_LS e _ _) (e_mem_LS e _ _)
  · rw [sub_zero]
    exact e_mem_LS e _ _
  · rw [zero_sub]
    exact neg_mem (e_mem_LS e _ _)
  · rw [sub_self]
    exact zero_mem _

theorem closure_letters (x y : Letter) :
    letters e x * letters e y - letters e y * letters e x ∈ Submodule.span ℂ (Set.range (letters e)) := by
  change admcm (letters e x) (letters e y) ∈ LS e
  rcases x with v | ⟨i, j⟩ <;> rcases y with w | ⟨k, l⟩ <;>
    simp only [letters, cm_add_left, cm_add_right, cm_sub_left, cm_sub_right, cm_smul_left, cm_smul_right] <;>
    repeat' first | exact cm_e_mem_LS he _ _ _ _ | apply add_mem | apply sub_mem | apply Submodule.smul_mem

end Table

def ktab (i j : Fin 3) (kl : Fin 3 × Fin 3) : MvPolynomial Letter ℂ :=
  ((if j = kl.1 then X (Sum.inr (i, kl.2) : Letter) else 0) +
      (if i = kl.2 then X (Sum.inr (j, kl.1) : Letter) else 0)) -
    ((if j = kl.2 then X (Sum.inr (i, kl.1) : Letter) else 0) +
      (if i = kl.1 then X (Sum.inr (j, kl.2) : Letter) else 0))

def rot (i j : Fin 3) : Derivation ℂ (MvPolynomial Letter ℂ) (MvPolynomial Letter ℂ) :=
  mkDerivation ℂ (Sum.elim (fun v : admIdx => admemb (-(admD i j (X v : admP)))) (ktab i j))

theorem rot_X_inl (i j : Fin 3) (v : admIdx) : rot i j (X (Sum.inl v : Letter)) = admemb (-(admD i j (X v :
    admP))) := by
  rw [rot, mkDerivation_X]
  rfl

theorem rot_X_inr (i j : Fin 3) (kl : Fin 3 × Fin 3) : rot i j (X (Sum.inr kl : Letter)) = ktab i j kl := by
  rw [rot, mkDerivation_X]
  rfl

theorem pIdx_idx (v : admIdx) : pIdx v.1.1 v.1.2 = v := by
  unfold pIdx
  rw [dif_pos v.2]

theorem X_idx_eq_Y (v : admIdx) : (X v : admP) = admY v.1.1 v.1.2 := by
  rw [Y_eq_X_pIdx, pIdx_idx]

theorem emb_Y (c d : Fin 3) : admemb (admY c d) = X (Sum.inl (pIdx c d) : Letter) := by
  rw [Y_eq_X_pIdx, emb_X]

theorem isHomogeneous_ite' {σ : Type*} (p : Prop) [Decidable p] {q : MvPolynomial σ ℂ}
    (hq : q.IsHomogeneous 1) : (if p then q else 0).IsHomogeneous 1 := by
  split_ifs
  · exact hq
  · exact isHomogeneous_zero σ ℂ 1

theorem isHomogeneous_rot_X (i j : Fin 3) (x : Letter) : (rot i j (X x)).IsHomogeneous 1 := by
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

theorem rot_emb (i j : Fin 3) (s : admP) : rot i j (admemb s) = admemb (-(admD i j s)) := by
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

theorem bracket_inl (i j a b : Fin 3) :
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

theorem bracket_inr (i j k l : Fin 3) :
    letters e (Sum.inr (i, j)) * letters e (Sum.inr (k, l)) - letters e (Sum.inr (k, l)) * letters e (Sum.inr (i, j)) =
      admop (letters e) (admL (rot i j (X (Sum.inr (k, l) : Letter)))) := by
  have he' : ∀ i j k l : Fin 3,
      e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0) := he
  change admcm _ _ = _
  rw [rot_X_inr, ktab, letters_inr, letters_inr, cm_sub_left, cm_sub_right, cm_sub_right]
  simp only [admcm, he', map_add, map_sub, apply_ite admL, apply_ite (admop (letters e)), map_zero, L_X, op_ι,
      letters_inr]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp <;> module

theorem bracket_letter (i j : Fin 3) (x : Letter) :
    letters e (Sum.inr (i, j)) * letters e x - letters e x * letters e (Sum.inr (i, j)) =
      admop (letters e) (admL (rot i j (X x))) := by
  rcases x with v | ⟨k, l⟩
  · have h := bracket_inl he i j v.1.1 v.1.2
    rwa [pIdx_idx] at h
  · exact bracket_inr he i j k l

theorem rot_bracket_mem (i j : Fin 3) {n : ℕ} {t : admP} (ht : t.IsHomogeneous n) :
    letters e (Sum.inr (i, j)) * admop (letters e) (admL (admemb t)) - admop (letters e) (admL (admemb t)) * letters e
        (Sum.inr (i, j)) +
        admop (letters e) (admL (admemb (admD i j t))) ∈ lengthSpan (letters e) (n - 1) := by
  have hemb : (admemb t).IsHomogeneous n := ht.rename_isHomogeneous (f := Sum.inl)
  have h := bracket_op_L_sub_mem (letters e) (rot i j) (letters e (Sum.inr (i, j))) (closure_letters he)
    (bracket_letter he i j) (isHomogeneous_rot_X i j) hemb
  rw [rot_emb, map_neg, map_neg, map_neg, sub_neg_eq_add] at h
  exact h

end Brackets

example : rot 0 1 (X (Sum.inl (pIdx 0 0) : Letter)) = -((2 : ℂ) • X (Sum.inl (pIdx 0 1) : Letter)) := by
  rw [rot_X_inl, ← Y_eq_X_pIdx, D_Y_eq]
  simp [emb_Y, Y_symm, two_smul]

example : rot 0 1 (X (Sum.inr (1, 2) : Letter)) = X (Sum.inr (0, 2) : Letter) := by
  rw [rot_X_inr, ktab]
  simp

end Adm0

end CarryC8b

namespace FischerForm

open MvPolynomial Finset

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

theorem wt_pos (α : σ →₀ ℕ) : 0 < wt α := by
  unfold wt Finsupp.prod
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

section Form

variable [DecidableEq σ]

def admform (p q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ p.support ∪ q.support, (wt α : ℂ) * p.coeff α * star (q.coeff α)

theorem form_eq_sum {p q : MvPolynomial σ ℂ} {S : Finset (σ →₀ ℕ)} (hS : p.support ∪ q.support ⊆ S) :
    admform p q = ∑ α ∈ S, (wt α : ℂ) * p.coeff α * star (q.coeff α) := by
  unfold admform
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [Finset.mem_union, not_or] at hα
  rw [notMem_support_iff.1 hα.1]
  simp

theorem form_lin (z : ℂ) (p₁ p₂ q : MvPolynomial σ ℂ) :
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

theorem form_symm (p q : MvPolynomial σ ℂ) : admform q p = star (admform p q) := by
  unfold admform
  rw [star_sum, Finset.union_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [star_mul, star_mul, star_star, star_natCast]
  ring

theorem form_pos {p : MvPolynomial σ ℂ} (hp : p ≠ 0) : 0 < (admform p p).re := by
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

theorem form_zero_left (q : MvPolynomial σ ℂ) : admform (0 : MvPolynomial σ ℂ) q = 0 := by
  unfold admform
  simp

theorem form_add_left (p₁ p₂ q : MvPolynomial σ ℂ) : admform (p₁ + p₂) q = admform p₁ q + admform p₂ q := by
  simpa using form_lin 1 p₁ p₂ q

theorem form_smul_left (z : ℂ) (p q : MvPolynomial σ ℂ) : admform (z • p) q = z * admform p q := by
  simpa [form_zero_left] using form_lin z p 0 q

theorem form_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    admform (∑ i ∈ s, f i) q = ∑ i ∈ s, admform (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih]

theorem form_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ ℂ) (g : ι → MvPolynomial σ ℂ) :
    admform p (∑ i ∈ s, g i) = ∑ i ∈ s, admform p (g i) := by
  rw [form_symm, form_sum_left, star_sum]
  exact Finset.sum_congr rfl fun i _ => (form_symm (g i) p).symm

theorem form_smul_right (z : ℂ) (p q : MvPolynomial σ ℂ) : admform p (z • q) = star z * admform p q := by
  rw [form_symm, form_smul_left, star_mul', ← form_symm]

theorem form_monomial (γ β : σ →₀ ℕ) (c d : ℂ) :
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

theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    homogeneousSubmodule σ ℂ n ≤ restrictTotalDegree σ ℂ n := by
  intro p hp
  rw [mem_restrictTotalDegree]
  by_cases h0 : p = 0
  · simp [h0]
  · exact ((mem_homogeneousSubmodule n p).1 hp).totalDegree h0 |>.le

section Der

variable [Fintype σ]

def admder (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ∑ i : σ, ∑ j : σ, A i j • (LinearMap.mulLeft ℂ (X j : MvPolynomial σ ℂ)).comp (pderiv i).toLinearMap

theorem der_apply (A : σ → σ → ℂ) (p : MvPolynomial σ ℂ) :
    admder A p = ∑ i : σ, ∑ j : σ, A i j • (X j * pderiv i p) := by
  simp [admder]

theorem der_monomial_isHomogeneous (A : σ → σ → ℂ) (α : σ →₀ ℕ) (c : ℂ) :
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

theorem der_mem_homogeneousSubmodule (A : σ → σ → ℂ) {n : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ homogeneousSubmodule σ ℂ n) : admder A p ∈ homogeneousSubmodule σ ℂ n := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : α.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.1 hα)
  rw [mem_homogeneousSubmodule, ← hd]
  exact der_monomial_isHomogeneous A α _

scoped instance finiteDimensional_homogeneousSubmodule (n : ℕ) :
    FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

theorem der_monomial (A : σ → σ → ℂ) (α : σ →₀ ℕ) (c : ℂ) :
    admder A (monomial α c) =
      ∑ i : σ, ∑ j : σ, A i j • monomial (Finsupp.single j 1 + (α - Finsupp.single i 1)) (c * (α i : ℂ)) := by
  rw [der_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end Der

section Skew

variable [Fintype σ] [DecidableEq σ]

theorem wt_add_single (γ : σ →₀ ℕ) (i : σ) : wt (γ + Finsupp.single i 1) = (γ i + 1) * wt γ := by
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

theorem ite_weight_swap (α β : σ →₀ ℕ) (i j : σ) :
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

theorem form_der_monomial {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (α β : σ →₀ ℕ) (c d : ℂ) :
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

theorem form_der_skew {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (p q : MvPolynomial σ ℂ) :
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

theorem form_der_der_symm {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (p q : MvPolynomial σ ℂ) :
    admform (admder A (admder A p)) q = admform p (admder A (admder A q)) := by
  rw [form_der_skew hA, form_der_skew hA, neg_neg]

end Skew

example [DecidableEq σ] (i : σ) : admform (X i ^ 2 : MvPolynomial σ ℂ) (X i ^ 2) = 2 := by
  have hX : (X i ^ 2 : MvPolynomial σ ℂ) = monomial (Finsupp.single i 2) 1 := by
    rw [X_pow_eq_monomial]
  rw [hX]
  unfold admform
  rw [Finset.union_self, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  unfold wt
  rw [Finsupp.prod_single_index (by simp)]
  simp [Nat.factorial]

example [Fintype σ] [DecidableEq σ] (A : σ → σ → ℂ) (k : σ) :
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm"

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem form_zero_left (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    {n : W} (hn : n ∈ M₀) : B 0 n = 0 := by
  have h := hlin (-1) 0 M₀.zero_mem 0 M₀.zero_mem n hn
  rw [smul_zero, add_zero] at h
  linear_combination h

def orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
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

theorem mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (w : W) : w ∈ orthoIn M₀ N B hlin hNM ↔ w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0 := Iff.rfl

theorem orthoIn_mapsTo (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (admD : W → W) (hDM : ∀ w ∈ M₀, admD w ∈ M₀) (hDN : ∀ n ∈ N, admD n ∈ N)
    (hskew : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (admD w) w' = - B w (admD w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, admD w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hDM w hw.1, fun n hn => ?_⟩
  rw [hskew w hw.1 n (hNM hn), hw.2 (admD n) (hDN n hn), neg_zero]

theorem orthoIn_mapsTo_of_isometry (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, ∃ n' ∈ N, T n' = n)
    (hTB : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) (T w') = B w w') :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hTM w hw.1, fun n hn => ?_⟩
  obtain ⟨n', hn', rfl⟩ := hTN n hn
  rw [hTB w hw.1 n' (hNM hn')]
  exact hw.2 n' hn'

theorem eq_zero_of_mem_orthoIn {Z : Type*} [AddCommGroup Z] (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) (Λ : W → Z)
    (hker : ∀ w ∈ M₀, Λ w = 0 → w ∈ N) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, Λ w = 0 → w = 0 := by
  intro w hw hΛ
  by_contra hne
  have h := hpos w hw.1 hne
  rw [hw.2 w (hker w hw.1 hΛ), Complex.zero_re] at h
  exact lt_irrefl _ h

theorem exists_ne_zero_mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
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

theorem eq_zero_of_mem_inf_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) {w : W} (hwN : w ∈ N) (hwP : w ∈ orthoIn M₀ N B hlin hNM) : w = 0 := by
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hwP
  by_contra hne
  have h := hpos w hwM hne
  rw [hperp w hwN, Complex.zero_re] at h
  exact lt_irrefl _ h

theorem sup_orthoIn_eq (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
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

theorem orthoIn_mapsTo_comp (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T₁ T₂ : W → W)
    (h₁ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ w ∈ orthoIn M₀ N B hlin hNM)
    (h₂ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₂ w ∈ orthoIn M₀ N B hlin hNM) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ (T₂ w) ∈ orthoIn M₀ N B hlin hNM :=
  fun w hw => h₁ _ (h₂ w hw)

theorem exists_mem_orthoIn_map_eq_of_killed {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
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

theorem exists_mem_orthoIn_map_eq_of_killed' {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
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

theorem orthoIn_mapsTo_of_symm (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, T n ∈ N)
    (hsym : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) w' = B w (T w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hw
  refine (mem_orthoIn M₀ N B hlin hNM (T w)).2 ⟨hTM w hwM, fun n hn => ?_⟩
  rw [hsym w hwM n (hNM hn)]
  exact hperp (T n) (hTN n hn)

theorem exists_eigen_decomposition :
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm"

namespace S5Split

open Adm0 SymRestriction FischerForm MvPolynomial

abbrev R9 : Type := MvPolynomial (Fin 3 × Fin 3) ℂ

def a9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℤ :=
  (if x.1 = i ∧ y = (j, x.2) then 1 else 0) - (if x.1 = j ∧ y = (i, x.2) then 1 else 0) -
    (if x.2 = j ∧ y = (x.1, i) then 1 else 0) + (if x.2 = i ∧ y = (x.1, j) then 1 else 0)

theorem a9_antisymm (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, a9 i j x y = -a9 i j y x := by
  fin_cases i <;> fin_cases j <;> decide

def A9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℂ := (a9 i j x y : ℂ)

theorem A9_skew (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, star (A9 i j x y) = -A9 i j y x := by
  intro x y
  rw [A9, A9, a9_antisymm i j x y]
  push_cast
  rw [star_neg, Complex.star_def, map_intCast]

def D9 (i j : Fin 3) : R9 →ₗ[ℂ] R9 := FischerForm.admder (A9 i j)

theorem D9_X (i j : Fin 3) (x : Fin 3 × Fin 3) :
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

theorem admder_mul {τ : Type*} [Fintype τ] (A : τ → τ → ℂ) (p q : MvPolynomial τ ℂ) :
    FischerForm.admder A (p * q) = p * FischerForm.admder A q + q * FischerForm.admder A p := by
  simp only [der_apply, Derivation.leibniz, smul_eq_mul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section Nine

variable (n : ℕ)

abbrev M9 : Submodule ℂ R9 := homogeneousSubmodule (Fin 3 × Fin 3) ℂ n

scoped instance : FiniteDimensional ℂ (M9 n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

theorem D9_mem_M9 (i j : Fin 3) {r : R9} (hr : r ∈ M9 n) : D9 i j r ∈ M9 n :=
  der_mem_homogeneousSubmodule (A9 i j) hr

def T9 : (Fin 3 × Fin 3 → M9 n) →ₗ[ℂ] R9 :=
  ∑ ij : Fin 3 × Fin 3, (D9 ij.1 ij.2).comp ((M9 n).subtype.comp (LinearMap.proj ij))

theorem T9_apply (q : Fin 3 × Fin 3 → M9 n) : T9 n q = ∑ ij : Fin 3 × Fin 3, D9 ij.1 ij.2 (q ij : R9) := by
  simp [T9]

abbrev N9 : Submodule ℂ R9 := LinearMap.range (T9 n)

theorem N9_le_M9 : N9 n ≤ M9 n := by
  rintro _ ⟨q, rfl⟩
  rw [T9_apply]
  exact Submodule.sum_mem _ fun ij _ => D9_mem_M9 n ij.1 ij.2 (q ij).2

theorem D9_mem_N9 (i j : Fin 3) {r : R9} (hr : r ∈ M9 n) : D9 i j r ∈ N9 n := by
  refine ⟨Pi.single (i, j) ⟨r, hr⟩, ?_⟩
  rw [T9_apply, Finset.sum_eq_single (i, j)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hlin9 : ∀ (z : ℂ), ∀ w₁ ∈ M9 n, ∀ w₂ ∈ M9 n, ∀ w' ∈ M9 n,
    admform (z • w₁ + w₂) w' = z * admform w₁ w' + admform w₂ w' := by
  intro z w₁ _ w₂ _ w' _
  rw [form_add_left, form_smul_left]

theorem hsymm9 : ∀ w ∈ M9 n, ∀ w' ∈ M9 n, admform w' w = (starRingEnd ℂ) (admform w w') := by
  intro w _ w' _
  rw [form_symm]
  rfl

theorem hpos9 : ∀ w ∈ M9 n, w ≠ 0 → 0 < (admform w w).re := fun _ _ hw => form_pos hw

theorem D9_eq_zero_of_mem_orthoIn {x : R9} (hx : x ∈ orthoIn (M9 n) (N9 n) admform (hlin9 n) (N9_le_M9 n))
    (i j : Fin 3) : D9 i j x = 0 := by
  obtain ⟨hxM, hperp⟩ := (mem_orthoIn _ _ _ _ _ x).1 hx
  by_contra hne
  have h1 : admform (D9 i j x) (D9 i j x) = -admform x (D9 i j (D9 i j x)) := form_der_skew (A9_skew i j) x (D9 i j x)
  have h2 : admform x (D9 i j (D9 i j x)) = 0 := hperp _ (D9_mem_N9 n i j (D9_mem_M9 n i j hxM))
  have h3 := form_pos hne
  rw [h1, h2, neg_zero] at h3
  simp at h3

theorem exists_split9 {r : R9} (hr : r ∈ M9 n) :
    ∃ s ∈ M9 n, (∀ i j : Fin 3, D9 i j s = 0) ∧
      ∃ q : Fin 3 × Fin 3 → M9 n, r = s + ∑ ij : Fin 3 × Fin 3, D9 ij.1 ij.2 (q ij : R9) := by
  have hdec := sup_orthoIn_eq (M9 n) (N9 n) admform (hlin9 n) (hsymm9 n) (hpos9 n) (N9_le_M9 n)
  rw [← hdec] at hr
  obtain ⟨m, hm, s, hs, rfl⟩ := Submodule.mem_sup.1 hr
  obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hm
  refine ⟨s, ((mem_orthoIn _ _ _ _ _ s).1 hs).1, fun i j => D9_eq_zero_of_mem_orthoIn n hs i j, q, ?_⟩
  rw [T9_apply, add_comm]

end Nine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm"

section Six

def toP : R9 →ₐ[ℂ] admP := rename fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2

def ofP : admP →ₐ[ℂ] R9 := rename fun v : admIdx => v.1

theorem toP_ofP (p : admP) : toP (ofP p) = p := by
  rw [toP, ofP, rename_rename]
  have h : ((fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2) ∘ fun v : admIdx => v.1) = id := funext fun v => pIdx_idx v
  rw [h, rename_id]
  rfl

theorem toP_X (ab : Fin 3 × Fin 3) : toP (X ab) = admY ab.1 ab.2 := by
  rw [toP, rename_X, Y_eq_X_pIdx]

theorem toP_isHomogeneous {n : ℕ} {r : R9} (hr : r ∈ M9 n) : (toP r).IsHomogeneous n :=
  ((mem_homogeneousSubmodule n r).1 hr).rename_isHomogeneous

theorem toP_D9_X (i j : Fin 3) (ab : Fin 3 × Fin 3) : toP (D9 i j (X ab)) = admD i j (toP (X ab)) := by
  rw [D9_X, map_sum, toP_X, D_Y_eq]
  simp only [map_smul, toP_X]
  obtain ⟨a, b⟩ := ab
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [A9, a9, Fintype.sum_prod_type, Fin.sum_univ_three] <;> module

theorem toP_D9 (i j : Fin 3) (r : R9) : toP (D9 i j r) = admD i j (toP r) := by
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

theorem exists_splitting {n : ℕ} {p : admP} (hp : p.IsHomogeneous n) :
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm"

example : a9 0 1 (0, 0) (1, 0) = 1 ∧ a9 0 1 (0, 0) (0, 1) = 1 ∧ a9 0 1 (0, 0) (0, 0) = 0 := by decide

example : toP (X (0, 1)) = toP (X (1, 0)) := by
  rw [toP_X, toP_X, Y_symm]

example (v : admIdx) : toP (ofP (X v)) = X v := toP_ofP _

end S5Split
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

set_option autoImplicit false

noncomputable section

namespace WsB
namespace TF

open Adm0 SymRestriction FischerForm S5Split MvPolynomial

def symE : admP →ₐ[ℂ] R9 :=
  aeval fun v : admIdx => C (1 / 2 : ℂ) * ((X v.1 : R9) + X (v.1.2, v.1.1))

theorem symE_X (v : admIdx) : symE (X v) = C (1 / 2 : ℂ) * ((X v.1 : R9) + X (v.1.2, v.1.1)) := by
  rw [symE, aeval_X]

theorem symE_Y (a b : Fin 3) : symE (admY a b) = C (1 / 2 : ℂ) * ((X (a, b) : R9) + X (b, a)) := by
  rw [Y_eq_X_pIdx, symE_X]
  unfold pIdx
  split_ifs with h
  · rfl
  · simp only
    rw [add_comm]

theorem toP_symE_X (v : admIdx) : toP (symE (X v)) = X v := by
  obtain ⟨⟨a, b⟩, hab⟩ := v
  rw [symE_X, ← smul_eq_C_mul, map_smul, map_add]
  simp only
  rw [toP_X, toP_X]
  simp only
  rw [Y_symm b a, ← two_smul ℂ (admY a b), smul_smul, X_idx_eq_Y]
  norm_num

theorem toP_symE (p : admP) : toP (symE p) = p := by
  have h : toP.comp symE = AlgHom.id ℂ admP := MvPolynomial.algHom_ext fun v => by
    rw [AlgHom.comp_apply, AlgHom.id_apply, toP_symE_X]
  exact congrArg (fun φ : admP →ₐ[ℂ] admP => φ p) h

theorem symE_injective : Function.Injective symE := fun p q h => by
  rw [← toP_symE p, ← toP_symE q, h]

def symP : R9 →ₐ[ℂ] R9 := symE.comp toP

theorem symP_X (x : Fin 3 × Fin 3) : symP (X x) = C (1 / 2 : ℂ) * ((X x : R9) + X (x.2, x.1)) := by
  rw [symP, AlgHom.comp_apply, toP_X, symE_Y]

theorem a9_swap (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, a9 i j (x.2, x.1) y = a9 i j x (y.2, y.1) := by
  fin_cases i <;> fin_cases j <;> decide

theorem A9_swap (i j : Fin 3) (x y : Fin 3 × Fin 3) : A9 i j (x.2, x.1) y = A9 i j x (y.2, y.1) := by
  rw [A9, A9, a9_swap]

theorem D9_symP_X (i j : Fin 3) (x : Fin 3 × Fin 3) : D9 i j (symP (X x)) = symP (D9 i j (X x)) := by

  have hsw : (∑ y : Fin 3 × Fin 3, A9 i j (x.2, x.1) y • (X y : R9)) =
      ∑ y : Fin 3 × Fin 3, A9 i j x y • (X (y.2, y.1) : R9) := by
    rw [← Fintype.sum_equiv (Equiv.prodComm (Fin 3) (Fin 3)) (fun y => A9 i j x (y.2, y.1) • (X y : R9))
      (fun y => A9 i j x y • (X (y.2, y.1) : R9)) (fun y => rfl)]
    exact Finset.sum_congr rfl (fun y _ => by rw [A9_swap])
  calc D9 i j (symP (X x)) = D9 i j ((1 / 2 : ℂ) • ((X x : R9) + X (x.2, x.1))) := by rw [symP_X, smul_eq_C_mul]
    _ = (1 / 2 : ℂ) • (∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) +
          ∑ y : Fin 3 × Fin 3, A9 i j (x.2, x.1) y • (X y : R9)) := by rw [map_smul, map_add, D9_X, D9_X]
    _ = (1 / 2 : ℂ) • (∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) +
          ∑ y : Fin 3 × Fin 3, A9 i j x y • (X (y.2, y.1) : R9)) := by rw [hsw]
    _ = ∑ y : Fin 3 × Fin 3, A9 i j x y • ((1 / 2 : ℂ) • ((X y : R9) + X (y.2, y.1))) := by
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← smul_add, smul_comm]
    _ = symP (D9 i j (X x)) := by
          rw [D9_X, map_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [map_smul, symP_X, ← smul_eq_C_mul]

theorem D9_symP (i j : Fin 3) (r : R9) : D9 i j (symP r) = symP (D9 i j r) := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    have h9 : ∀ c : ℂ, D9 i j (C c : R9) = 0 := by
      intro c; rw [D9, der_apply]; simp
    have hs : symP (C c) = C c := by rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [hs, h9, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    simp only [D9] at hp ⊢
    rw [map_mul, admder_mul, admder_mul, map_add, map_mul, map_mul, hp]
    have hX := D9_symP_X i j x
    simp only [D9] at hX
    rw [hX]

theorem symE_admD (i j : Fin 3) (p : admP) : symE (admD i j p) = D9 i j (symE p) := by
  have h1 : symE p = symP (ofP p) := by rw [symP, AlgHom.comp_apply, toP_ofP]
  rw [h1, D9_symP, symP, AlgHom.comp_apply, toP_D9, toP_ofP]

def FP (p q : admP) : ℂ := FischerForm.admform (symE p) (symE q)

theorem FP_lin (z : ℂ) (p₁ p₂ q : admP) : FP (z • p₁ + p₂) q = z * FP p₁ q + FP p₂ q := by
  simp only [FP, map_add, map_smul, form_lin]

theorem FP_symm (p q : admP) : FP q p = (starRingEnd ℂ) (FP p q) := by
  rw [FP, FP, form_symm, starRingEnd_apply]

theorem FP_pos (p : admP) (hp : p ≠ 0) : 0 < (FP p p).re :=
  form_pos fun h => hp (symE_injective (by rw [h, map_zero]))

theorem FP_add_left (p₁ p₂ q : admP) : FP (p₁ + p₂) q = FP p₁ q + FP p₂ q := by
  simp only [FP, map_add, form_add_left]

theorem FP_smul_left (z : ℂ) (p q : admP) : FP (z • p) q = z * FP p q := by
  simp only [FP, map_smul, form_smul_left]

theorem FP_zero_left (q : admP) : FP 0 q = 0 := by
  simp only [FP, map_zero, FischerForm.form_zero_left]

theorem FP_D_skew (i j : Fin 3) (p q : admP) : FP (admD i j p) q = -FP p (admD i j q) := by
  simp only [FP, symE_admD, D9]
  exact form_der_skew (A9_skew i j) _ _

theorem admD_isHomogeneous (i j : Fin 3) {N : ℕ} {p : admP} (hp : p.IsHomogeneous N) :
    (admD i j p).IsHomogeneous N := by
  have hr : ofP p ∈ M9 N := (mem_homogeneousSubmodule N _).2 (hp.rename_isHomogeneous (f := fun v : admIdx => v.1))
  have h := toP_isHomogeneous (D9_mem_M9 N i j hr)
  rwa [toP_D9, toP_ofP] at h

end WsB.TF
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace WsB
namespace TFT

variable {P : Type*} [AddCommGroup P] [Module ℂ P]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {r : ℕ}

def coord (e : Module.Basis (Fin r) ℂ W) : P ⊗[ℂ] W ≃ₗ[ℂ] (Fin r → P) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ P) e.equivFun).trans (TensorProduct.piScalarRight ℂ ℂ P (Fin r))

theorem coord_tmul (e : Module.Basis (Fin r) ℂ W) (p : P) (w : W) (k : Fin r) :
    coord e (p ⊗ₜ[ℂ] w) k = e.repr w k • p := by
  simp [coord, TensorProduct.congr_tmul, TensorProduct.piScalarRightHom_tmul, Module.Basis.equivFun_apply]

theorem coord_map_left (e : Module.Basis (Fin r) ℂ W) (f : P →ₗ[ℂ] P) (x : P ⊗[ℂ] W) (k : Fin r) :
    coord e (TensorProduct.map f LinearMap.id x) k = f (coord e x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w => rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul, coord_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem coord_map_right (e : Module.Basis (Fin r) ℂ W) (g : W →ₗ[ℂ] W) (x : P ⊗[ℂ] W) (k : Fin r) :
    coord e (TensorProduct.map LinearMap.id g x) k = ∑ l : Fin r, e.repr (g (e l)) k • coord e x l := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul]
    simp only [coord_tmul, smul_smul, ← Finset.sum_smul]
    congr 1

    have hgw : g w = ∑ x : Fin r, e.repr w x • g (e x) := by
      conv_lhs => rw [← e.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun x _ => map_smul _ _ _)
    rw [hgw, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]

section Form

variable (FP : P → P → ℂ)
  (hFlin : ∀ (z : ℂ) (p₁ p₂ q : P), FP (z • p₁ + p₂) q = z * FP p₁ q + FP p₂ q)
  (hFsymm : ∀ p q : P, FP q p = (starRingEnd ℂ) (FP p q))
  (hFpos : ∀ p : P, p ≠ 0 → 0 < (FP p p).re)

include hFlin in
theorem F_zero_left (q : P) : FP 0 q = 0 := by
  have h := hFlin (-1) 0 0 q; rw [smul_zero, add_zero] at h; linear_combination h

include hFlin in
theorem F_add_left (p₁ p₂ q : P) : FP (p₁ + p₂) q = FP p₁ q + FP p₂ q := by
  have h := hFlin 1 p₁ p₂ q; rw [one_smul, one_mul] at h; exact h

include hFlin in
theorem F_smul_left (z : ℂ) (p q : P) : FP (z • p) q = z * FP p q := by
  have h := hFlin z p 0 q; rw [add_zero, F_zero_left FP hFlin, add_zero] at h; exact h

include hFlin hFsymm in
theorem F_add_right (p q₁ q₂ : P) : FP p (q₁ + q₂) = FP p q₁ + FP p q₂ := by
  rw [hFsymm (q₁ + q₂) p, hFsymm q₁ p, hFsymm q₂ p, F_add_left FP hFlin, map_add]

include hFlin hFsymm in
theorem F_smul_right (z : ℂ) (p q : P) : FP p (z • q) = (starRingEnd ℂ) z * FP p q := by
  rw [hFsymm (z • q) p, F_smul_left FP hFlin, map_mul, ← hFsymm q p]

include hFlin in
theorem F_sum_left {ι : Type*} (s : Finset ι) (f : ι → P) (q : P) : FP (∑ i ∈ s, f i) q = ∑ i ∈ s, FP (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [F_zero_left FP hFlin]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, F_add_left FP hFlin, ih]

include hFlin hFsymm in
theorem F_sum_right {ι : Type*} (s : Finset ι) (p : P) (f : ι → P) : FP p (∑ i ∈ s, f i) = ∑ i ∈ s, FP p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [hFsymm 0 p, F_zero_left FP hFlin, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, F_add_right FP hFlin hFsymm, ih]

include hFlin hFpos in
theorem F_re_nonneg (p : P) : 0 ≤ (FP p p).re := by
  by_cases hp : p = 0
  · rw [hp, F_zero_left FP hFlin]; simp
  · exact (hFpos p hp).le

def BT (e : Module.Basis (Fin r) ℂ W) (x y : P ⊗[ℂ] W) : ℂ := ∑ k : Fin r, FP (coord e x k) (coord e y k)

include hFlin in
theorem BT_lin (e : Module.Basis (Fin r) ℂ W) (z : ℂ) (x₁ x₂ y : P ⊗[ℂ] W) :
    BT FP e (z • x₁ + x₂) y = z * BT FP e x₁ y + BT FP e x₂ y := by
  simp only [BT, map_add, map_smul, Pi.add_apply, Pi.smul_apply, hFlin, Finset.sum_add_distrib, Finset.mul_sum]

include hFsymm in
theorem BT_symm (e : Module.Basis (Fin r) ℂ W) (x y : P ⊗[ℂ] W) : BT FP e y x = (starRingEnd ℂ) (BT FP e x y) := by
  simp only [BT, map_sum]
  exact Finset.sum_congr rfl (fun k _ => hFsymm _ _)

include hFlin hFpos in
theorem BT_pos (e : Module.Basis (Fin r) ℂ W) (x : P ⊗[ℂ] W) (hx : x ≠ 0) : 0 < (BT FP e x x).re := by
  have hne : coord e x ≠ 0 := fun h => hx ((coord e).map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ : ∃ k, coord e x k ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  simp only [BT, Complex.re_sum]
  refine lt_of_lt_of_le (hFpos _ hk) ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have : 0 ≤ ∑ i ∈ Finset.univ.erase k, (FP (coord e x i) (coord e x i)).re :=
    Finset.sum_nonneg (fun i _ => F_re_nonneg FP hFlin hFpos _)
  linarith

include hFlin hFsymm in

theorem BT_skew_left (e : Module.Basis (Fin r) ℂ W) (f : P →ₗ[ℂ] P) (hf : ∀ p q : P, FP (f p) q = -FP p (f q))
    (x y : P ⊗[ℂ] W) :
    BT FP e (TensorProduct.map f LinearMap.id x) y = -BT FP e x (TensorProduct.map f LinearMap.id y) := by
  simp only [BT, coord_map_left, hf, Finset.sum_neg_distrib]

include hFlin hFsymm in

theorem BT_skew_right (e : Module.Basis (Fin r) ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (horth : ∀ i j : Fin r, B (e i) (e j) = if i = j then 1 else 0)
    (g : W →ₗ[ℂ] W) (hg : ∀ x y : W, B (g x) y = -B x (g y)) (x y : P ⊗[ℂ] W) :
    BT FP e (TensorProduct.map LinearMap.id g x) y = -BT FP e x (TensorProduct.map LinearMap.id g y) := by

  have hB0 : ∀ w' : W, B 0 w' = 0 := by
    intro w'; have h := hlin (-1) 0 0 w'; rw [smul_zero, add_zero] at h; linear_combination h
  have hBadd : ∀ x y w' : W, B (x + y) w' = B x w' + B y w' := by
    intro x y w'; have h := hlin 1 x y w'; rw [one_smul, one_mul] at h; exact h
  have hBsmul : ∀ (z : ℂ) (x w' : W), B (z • x) w' = z * B x w' := by
    intro z x w'; have h := hlin z x 0 w'; rw [add_zero, hB0, add_zero] at h; exact h
  have hrepr : ∀ (w : W) (j : Fin r), e.repr w j = B w (e j) := by
    intro w j
    conv_rhs => rw [← e.sum_repr w]
    have : ∀ s : Finset (Fin r), B (∑ i ∈ s, e.repr w i • e i) (e j) = ∑ i ∈ s, e.repr w i * B (e i) (e j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hB0]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBadd, hBsmul, ih]
    rw [this]
    simp [horth, Finset.sum_ite_eq']
  have hc : ∀ k l : Fin r, (starRingEnd ℂ) (e.repr (g (e k)) l) = -e.repr (g (e l)) k := by
    intro k l
    rw [hrepr, hrepr, ← hsymm, hg, neg_neg]
  simp only [BT, coord_map_right, F_sum_left FP hFlin, F_sum_right FP hFlin hFsymm, F_smul_left FP hFlin,
    F_smul_right FP hFlin hFsymm, hc, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm, neg_neg]

end Form
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

end WsB.TFT
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

set_option autoImplicit false

open scoped TensorProduct

namespace WsB
namespace TFC

open MvPolynomial

noncomputable section

abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
abbrev P : Type := MvPolynomial admIdx ℂ

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def S (N : ℕ) : Submodule ℂ (P ⊗[ℂ] W) :=
  Submodule.span ℂ {x : P ⊗[ℂ] W | ∃ (q : P) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}

theorem tmul_mem_S {N : ℕ} {q : P} (hq : q.IsHomogeneous N) (w : W) : q ⊗ₜ[ℂ] w ∈ S (W := W) N :=
  Submodule.subset_span ⟨q, w, hq, rfl⟩

theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    homogeneousSubmodule admIdx ℂ n ≤ restrictTotalDegree admIdx ℂ n := by
  intro p hp
  rw [mem_restrictTotalDegree]
  by_cases h0 : p = 0
  · simp [h0]
  · exact ((mem_homogeneousSubmodule n p).1 hp).totalDegree h0 |>.le

scoped instance finite_homogeneousSubmodule (n : ℕ) : Module.Finite ℂ (homogeneousSubmodule admIdx ℂ n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

theorem S_le_range (N : ℕ) :
    S (W := W) N ≤ LinearMap.range (TensorProduct.map (homogeneousSubmodule admIdx ℂ N).subtype
      (LinearMap.id : W →ₗ[ℂ] W)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨q, w, hq, rfl⟩
  exact ⟨(⟨q, (mem_homogeneousSubmodule N q).2 hq⟩ : homogeneousSubmodule admIdx ℂ N) ⊗ₜ[ℂ] w,
    by rw [TensorProduct.map_tmul]; rfl⟩

theorem finite_S [Module.Finite ℂ W] (N : ℕ) : Module.Finite ℂ (S (W := W) N) := by
  haveI : Module.Finite ℂ (LinearMap.range (TensorProduct.map (homogeneousSubmodule admIdx ℂ N).subtype
      (LinearMap.id : W →ₗ[ℂ] W))) := inferInstance
  exact Submodule.finiteDimensional_of_le (S_le_range N)

variable (D : Fin 3 → Fin 3 → Derivation ℂ P P) (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))

def θ (i j : Fin 3) : P ⊗[ℂ] W →ₗ[ℂ] P ⊗[ℂ] W :=
  TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id

theorem θ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ D ρ i j (q ⊗ₜ[ℂ] w) = q ⊗ₜ[ℂ] (ρ i j w) - (D i j q) ⊗ₜ[ℂ] w := by
  simp only [θ, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem theta_mapsTo (hD : ∀ (i j : Fin 3) (N : ℕ) (q : P), q.IsHomogeneous N → (D i j q).IsHomogeneous N)
    (i j : Fin 3) (N : ℕ) : ∀ x ∈ S (W := W) N, θ D ρ i j x ∈ S (W := W) N := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, w, hq, rfl⟩ := hy
    rw [θ_tmul]
    exact sub_mem (tmul_mem_S hq _) (tmul_mem_S (hD i j N q hq) _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul z a _ ha => rw [map_smul]; exact Submodule.smul_mem _ z ha

def Y : Matrix (Fin 3) (Fin 3) P :=
  Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
def K (i j : Fin 3) : Matrix (Fin 3) (Fin 3) P := Matrix.single i j 1 - Matrix.single j i 1
def Dc (i j : Fin 3) : Derivation ℂ P P := MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2

theorem isHomogeneous_derivation_monomial {σ : Type*}
    (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hδ : ∀ x : σ, (δ (X x)).IsHomogeneous 1) (μ : σ →₀ ℕ) :
    (δ (monomial μ (1 : ℂ))).IsHomogeneous (μ.degree) := by
  classical
  induction μ using Finsupp.induction with
  | zero =>
    rw [monomial_zero', C_1, Derivation.map_one_eq_zero]
    exact isHomogeneous_zero σ ℂ _
  | single_add a b f ha hb ih =>
    rw [monomial_single_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul,
      (map_add Finsupp.degree), Finsupp.degree_single]
    refine IsHomogeneous.add ?_ ?_
    · exact (isHomogeneous_X_pow a b).mul ih
    · rw [add_comm b (Finsupp.degree f)]
      refine (isHomogeneous_monomial _ rfl).mul ?_
      rw [nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
      have h2 : ((b : MvPolynomial σ ℂ) * X a ^ (b - 1)).IsHomogeneous (b - 1) := by
        have := (isHomogeneous_X_pow (R := ℂ) a (b - 1)).C_mul (b : ℂ)
        simpa using this
      have h3 := h2.mul (hδ a)
      rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hb)] at h3

theorem isHomogeneous_derivation {σ : Type*} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hδ : ∀ x : σ, (δ (X x)).IsHomogeneous 1) {n : ℕ} {p : MvPolynomial σ ℂ} (hp : p.IsHomogeneous n) :
    (δ p).IsHomogeneous n := by
  classical
  rw [p.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun μ hμ => ?_
  have hdeg : μ.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 hμ)
  have hc : (monomial μ) (coeff μ p) = C (coeff μ p) * (monomial μ (1 : ℂ) : MvPolynomial σ ℂ) := by
    rw [C_mul_monomial, mul_one]
  rw [hc, C_mul', δ.map_smul, smul_eq_C_mul, ← hdeg]
  exact (isHomogeneous_derivation_monomial δ hδ μ).C_mul _

theorem isHomogeneous_Y (a b : Fin 3) : (Y a b).IsHomogeneous 1 := by
  unfold Y
  simp only [Matrix.of_apply]
  split_ifs <;> exact isHomogeneous_X ℂ _

theorem isHomogeneous_KY_sub_YK (i j a b : Fin 3) : ((K i j * Y - Y * K i j) a b).IsHomogeneous 1 := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, K, Matrix.sub_apply, Fin.sum_univ_three, Matrix.single_apply]

  refine IsHomogeneous.sub ?_ ?_ <;>
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_ <;>
    first
      | (refine (zero_add 1) ▸ IsHomogeneous.mul ?_ (isHomogeneous_Y _ _); split_ifs <;> simp <;>
          first | exact isHomogeneous_one admIdx ℂ | exact isHomogeneous_zero admIdx ℂ 0
                | exact (isHomogeneous_one admIdx ℂ).neg | exact ((isHomogeneous_one admIdx ℂ).sub (isHomogeneous_one admIdx ℂ)) )
      | (refine (add_zero 1) ▸ IsHomogeneous.mul (isHomogeneous_Y _ _) ?_; split_ifs <;> simp <;>
          first | exact isHomogeneous_one admIdx ℂ | exact isHomogeneous_zero admIdx ℂ 0
                | exact (isHomogeneous_one admIdx ℂ).neg | exact ((isHomogeneous_one admIdx ℂ).sub (isHomogeneous_one admIdx ℂ)) )

theorem Dc_isHomogeneous (i j : Fin 3) (N : ℕ) (q : P) (hq : q.IsHomogeneous N) : (Dc i j q).IsHomogeneous N := by
  refine isHomogeneous_derivation (Dc i j) (fun v => ?_) hq
  rw [Dc, mkDerivation_X]
  exact isHomogeneous_KY_sub_YK i j _ _

theorem θθ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ D ρ i j (θ D ρ i j (q ⊗ₜ[ℂ] w)) =
      q ⊗ₜ[ℂ] (ρ i j (ρ i j w)) - ((D i j q) ⊗ₜ[ℂ] (ρ i j w) + (D i j q) ⊗ₜ[ℂ] (ρ i j w)) +
        (D i j (D i j q)) ⊗ₜ[ℂ] w := by
  rw [θ_tmul, map_sub, θ_tmul, θ_tmul]
  abel

theorem Omega_add_two_tmul
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x)) (q : P) (w : W) :
    (θ D ρ 0 1 ∘ₗ θ D ρ 0 1 + θ D ρ 0 2 ∘ₗ θ D ρ 0 2 + θ D ρ 1 2 ∘ₗ θ D ρ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
      ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
      ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
      ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w))) := by
  have hsum : q ⊗ₜ[ℂ] (ρ 0 1 (ρ 0 1 w)) + q ⊗ₜ[ℂ] (ρ 0 2 (ρ 0 2 w)) + q ⊗ₜ[ℂ] (ρ 1 2 (ρ 1 2 w)) +
      (2 : ℂ) • (q ⊗ₜ[ℂ] w) = 0 := by
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add,
      hcas, neg_add_cancel, TensorProduct.tmul_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, θθ_tmul]
  rw [← sub_eq_zero, ← hsum]
  abel

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split"

end WsB.TFC
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB.TFC"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace WsB
namespace TFmain

open SymRestriction FischerForm S5Split WsB.TF WsB.TFT

theorem exists_orthonormal_basis (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ W), ∀ i j : Fin n, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  have hB0 : ∀ w' : W, B 0 w' = 0 := by
    intro w'; have h := hlin (-1) 0 0 w'; rw [smul_zero, add_zero] at h; linear_combination h
  have hadd : ∀ x y w' : W, B (x + y) w' = B x w' + B y w' := by
    intro x y w'; have h := hlin 1 x y w'; rw [one_smul, one_mul] at h; exact h
  have hsmul : ∀ (z : ℂ) (x w' : W), B (z • x) w' = z * B x w' := by
    intro z x w'; have h := hlin z x 0 w'; rw [add_zero, hB0, add_zero] at h; exact h
  let core : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B x y) = B y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ (B x x).re
        by_cases hx : x = 0
        · rw [hx, hB0]; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show B z (x + y) = B z x + B z y
        rw [hsymm (x + y) z, hsymm x z, hsymm y z, hadd, map_add]
      smul_left := fun x y r => by
        show B y (r • x) = (starRingEnd ℂ) r * B y x
        rw [hsymm (r • x) y, hsmul, map_mul, ← hsymm x y]
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        have hx' : B x x = 0 := hx
        rw [hx', Complex.zero_re] at this
        exact lt_irrefl _ this }
  letI ipc : InnerProductSpace.Core ℂ W := core
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := W)
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore (𝕜 := ℂ) (F := W) ipc.toCore
  let ob := stdOrthonormalBasis ℂ W
  refine ⟨Module.finrank ℂ W, ob.toBasis, fun i j => ?_⟩
  have h := ob.orthonormal
  rw [orthonormal_iff_ite] at h
  have hij := h i j
  change B (ob j) (ob i) = _ at hij
  rw [OrthonormalBasis.coe_toBasis]
  rw [hsymm (ob j) (ob i), hij]
  split_ifs <;> simp

theorem form_part (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y)) :
    ∃ B' : admP ⊗[ℂ] W → admP ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ) (w₁ w₂ w' : admP ⊗[ℂ] W), B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w w' : admP ⊗[ℂ] W, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w : admP ⊗[ℂ] W, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ (i j : Fin 3) (w w' : admP ⊗[ℂ] W),
        B' ((TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (admD i j).toLinearMap LinearMap.id :
            admP ⊗[ℂ] W →ₗ[ℂ] admP ⊗[ℂ] W) w) w' =
          -B' w ((TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (admD i j).toLinearMap LinearMap.id :
            admP ⊗[ℂ] W →ₗ[ℂ] admP ⊗[ℂ] W) w')) := by
  obtain ⟨r, e, horth⟩ := exists_orthonormal_basis W B hlin hsymm hpos
  refine ⟨BT FP e, BT_lin FP FP_lin e, BT_symm FP FP_symm e, BT_pos FP FP_lin FP_pos e, ?_⟩
  intro i j w w'
  have hsubL : ∀ x₁ x₂ y : admP ⊗[ℂ] W, BT FP e (x₁ - x₂) y = BT FP e x₁ y - BT FP e x₂ y := by
    intro x₁ x₂ y
    rw [sub_eq_add_neg, add_comm, ← neg_one_smul ℂ x₂, BT_lin FP FP_lin e]; ring
  have hsubR : ∀ x y₁ y₂ : admP ⊗[ℂ] W, BT FP e x (y₁ - y₂) = BT FP e x y₁ - BT FP e x y₂ := by
    intro x y₁ y₂
    rw [BT_symm FP FP_symm e (y₁ - y₂) x, hsubL, map_sub, ← BT_symm FP FP_symm e y₁ x, ← BT_symm FP FP_symm e y₂ x]
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hsubL, hsubR,
    BT_skew_right FP FP_lin FP_symm e B hlin hsymm horth (ρ i j) (hskew i j),
    BT_skew_left FP FP_lin FP_symm e (admD i j).toLinearMap (fun p q => FP_D_skew i j p q)]
  ring

end WsB.TFmain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB.TFC"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB.TFC"

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (N : ℕ) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    let θ : Fin 3 → Fin 3 → (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W →ₗ[ℂ] MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      fun i j => TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id
    let S : Submodule ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W | ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}
    Module.Finite ℂ S ∧
    (∀ i j : Fin 3, ∀ x ∈ S, θ i j x ∈ S) ∧
    (∃ B' : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ), ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ w' ∈ S, B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w ∈ S, ∀ w' ∈ S, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w ∈ S, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ i j : Fin 3, ∀ w ∈ S, ∀ w' ∈ S, B' (θ i j w) w' = -B' w (θ i j w'))) ∧
    (∀ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
      (θ 0 1 ∘ₗ θ 0 1 + θ 0 2 ∘ₗ θ 0 2 + θ 1 2 ∘ₗ θ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
        ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
        ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
        ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))) := by
  intro Y K D θ S
  obtain ⟨B', h1, h2, h3, h4⟩ := WsB.TFmain.form_part W ρ B hlin hsymm hpos hskew
  refine ⟨?_, ?_, ⟨B', fun z w₁ _ w₂ _ w' _ => h1 z w₁ w₂ w', fun w _ w' _ => h2 w w', fun w _ hw => h3 w hw,
    fun i j w _ w' _ => h4 i j w w'⟩, ?_⟩
  · exact WsB.TFC.finite_S N
  · intro i j x hx
    exact WsB.TFC.theta_mapsTo D ρ (fun i j N q hq => WsB.TFC.Dc_isHomogeneous i j N q hq) i j N x hx
  · intro q w
    exact WsB.TFC.Omega_add_two_tmul D ρ hcas q w

end
end
end
end S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul (solution)
