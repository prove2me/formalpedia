-- Prove2me | solution 1 for MagicSquares.semi_magic_polynomial_exists
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-20T14:43:44.11898+00:00
-- url     : https://prove2.me/submissions/36575948-2773-4c3f-b3c4-6e899aa4271f

import Mathlib
import Definitions.Def_MagicSquares

/-!
# Semi-magic counting polynomial at every nonnegative line sum

Standalone platform bundle.  It follows Spencer's positive-line-sum support
recursion and extends it at line sum zero through closed support fibres and
inclusion-exclusion.  It proves polynomiality and exact degree only; it makes
no claim about Ehrhart-Macdonald reciprocity or the negative-value vanishing
list.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset
open MagicSquares
open scoped BigOperators


-- ==========================================================================
-- from spencer/Spencer.lean
-- ==========================================================================

/-
# The Spencer (1980) machinery, part 1 of 2: from a triangular recurrence to a polynomial

Spencer's elementary proof that the number `H_n(t)` of `n × n` semi-magic squares of line sum
`t` is a polynomial in `t` has two analytic-looking ingredients that are in fact purely
discrete:

* the **discrete antiderivative**: `P ↦ (n ↦ ∑_{m<n} P m)` raises the degree by exactly one;
  Mathlib supplies Bernoulli-polynomial Faulhaber (`Polynomial.bernoulli_succ_eval`), so this is
  `(B_{d+1}(X) - B_{d+1}) / (d+1)` for the monomial `X ^ d`;
* the **Spencer step**: a strictly triangular system of recurrences with polynomial coefficients
  of degree `≤ K` produces a polynomial of degree `≤ K + 1`.

What is *not* here yet — and what the combinatorics still has to supply — is the support-set
poset, the Hall/Birkhoff–von Neumann choice of a permutation inside a support set, and the
degree count.  See `missions/magic-squares-v/SPENCER-ROUTE.md` for the plan and for the two
subtleties (the value at line sum `0`, and the exact degree bound) that this note records.

Scratch file, compiled with `lake env lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

open Polynomial

/-- The Bernoulli polynomial of index `n` has degree at most `n`. -/
theorem natDegree_bernoulli_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [Polynomial.coeff_bernoulli, if_neg (by omega)]

/-- Subtracting a constant never increases the degree. -/
theorem natDegree_sub_C_le (p : Polynomial ℚ) (c : ℚ) : (p - C c).natDegree ≤ p.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hN

/-- The Bernoulli antiderivative of the monomial `X ^ d`: a polynomial of degree at most
`d + 1` whose value at `n : ℕ` is `∑_{m < n} m ^ d`. -/
noncomputable def bernoulliAntideriv (d : ℕ) : Polynomial ℚ :=
  C (((d : ℚ) + 1)⁻¹) * (Polynomial.bernoulli d.succ - C (_root_.bernoulli d.succ))

theorem bernoulliAntideriv_natDegree (d : ℕ) : (bernoulliAntideriv d).natDegree ≤ d + 1 := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_sub_C_le (Polynomial.bernoulli d.succ) _).trans
    ((natDegree_bernoulli_le d.succ).trans (by omega))

theorem bernoulliAntideriv_eval (d n : ℕ) :
    (bernoulliAntideriv d).eval (n : ℚ) = ∑ m ∈ range n, (m : ℚ) ^ d := by
  have h := Polynomial.bernoulli_succ_eval n d
  have hne : ((d : ℚ) + 1) ≠ 0 := by positivity
  simp only [bernoulliAntideriv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
  rw [h]
  field_simp
  ring

/-- The antiderivative of a polynomial, built from the Bernoulli antiderivatives of its
monomials. -/
noncomputable def antideriv (P : Polynomial ℚ) : Polynomial ℚ :=
  ∑ p ∈ range (P.natDegree + 1), C (P.coeff p) * bernoulliAntideriv p

theorem antideriv_natDegree (P : Polynomial ℚ) : (antideriv P).natDegree ≤ P.natDegree + 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le (s := range (P.natDegree + 1))
    (fun p => C (P.coeff p) * bernoulliAntideriv p) fun p hp => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  have hp' : p ≤ P.natDegree := by simpa using hp
  exact (bernoulliAntideriv_natDegree p).trans (by omega)

theorem antideriv_eval (P : Polynomial ℚ) (n : ℕ) :
    (antideriv P).eval (n : ℚ) = ∑ m ∈ range n, P.eval (m : ℚ) := by
  rw [antideriv, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [bernoulliAntideriv_eval]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

/-- **The discrete antiderivative.** For every polynomial `P` there is a polynomial `Q` of
degree at most `natDegree P + 1` with `Q n = ∑_{m < n} P m` for every `n : ℕ`. -/
theorem exists_antideriv (P : Polynomial ℚ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ P.natDegree + 1 ∧
      ∀ n : ℕ, Q.eval (n : ℚ) = ∑ m ∈ range n, P.eval (m : ℚ) :=
  ⟨antideriv P, antideriv_natDegree P, antideriv_eval P⟩

/-! ## Brick 2: the Spencer step, and its summing form -/

/-- `b` agrees with a polynomial of degree at most `K` on all of `ℕ`. -/
def IsPolyDegLe (K : ℕ) (b : ℕ → ℚ) : Prop :=
  ∃ p : Polynomial ℚ, p.natDegree ≤ K ∧ ∀ n : ℕ, p.eval (n : ℚ) = b n

theorem isPolyDegLe_const (c : ℚ) (K : ℕ) : IsPolyDegLe K (fun _ => c) :=
  ⟨C c, by simp, by intro n; simp⟩

/-- Degree bounds are inherited by weaker ones. -/
theorem isPolyDegLe_mono {K K' : ℕ} {b : ℕ → ℚ} (h : IsPolyDegLe K b) (hKK : K ≤ K') :
    IsPolyDegLe K' b := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp.trans hKK, hv⟩

theorem isPolyDegLe_sum {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ} {K : ℕ}
    (hc : ∀ i ∈ s, IsPolyDegLe K (c i)) :
    IsPolyDegLe K (fun n => ∑ i ∈ s, c i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp, by intro n; simp⟩
  | insert a s ha ih =>
      obtain ⟨p₁, hp₁, hv₁⟩ := hc a (Finset.mem_insert_self a s)
      obtain ⟨p₂, hp₂, hv₂⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
      refine ⟨p₁ + p₂, ?_, fun n => ?_⟩
      · exact (Polynomial.natDegree_add_le_iff_left p₁ p₂ hp₂).mpr hp₁
      · simp only [Polynomial.eval_add, hv₁ n, hv₂ n, Finset.sum_insert ha]

/-- **The Spencer step.** A sequence satisfying a triangular recurrence whose coefficients are
polynomial of degree at most `K` is itself polynomial of degree at most `K + 1`. -/
theorem isPolyDegLe_of_recurrence {b : ℕ → ℚ} {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ} {K : ℕ}
    (hc : ∀ i ∈ s, IsPolyDegLe K (c i))
    (hrec : ∀ r : ℕ, 1 ≤ r → b r = b (r - 1) + ∑ i ∈ s, c i (r - 1)) :
    IsPolyDegLe (K + 1) b := by
  -- Step 1: telescoping.
  have htel : ∀ r : ℕ, b r = b 0 + ∑ t ∈ range r, ∑ i ∈ s, c i t := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [hrec (r + 1) (by omega), Nat.add_sub_cancel, ih, Finset.sum_range_succ]
        ring
  -- Step 2: the coefficient sequence, and its antiderivative.
  obtain ⟨R, hRdeg, hRval⟩ := isPolyDegLe_sum s hc
  obtain ⟨Q, hQdeg, hQval⟩ := exists_antideriv R
  have hC : (Polynomial.C (b 0)).natDegree ≤ K + 1 := by
    rw [Polynomial.natDegree_C]
    omega
  refine ⟨C (b 0) + Q, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le_iff_right (Polynomial.C (b 0)) Q hC).mpr
      (hQdeg.trans (by omega))
  · intro n
    rw [htel n, Polynomial.eval_add, Polynomial.eval_C, hQval n]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hRval t

/-- The same step, in the *shifted* indexing that the fibre recurrence naturally produces.

The counting sequences of the support-set recursion are indexed so that the level-`(r+1)` count
satisfies `b (r+1) = b r + Σ …`; writing the recurrence with `r - 1` on the right costs a
case split that this form avoids.  Telescoping from `r = 0` is identical to the proof above. -/
theorem isPolyDegLe_of_recurrence_succ {b : ℕ → ℚ} {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ}
    {K : ℕ} (hc : ∀ i ∈ s, IsPolyDegLe K (c i))
    (hrec : ∀ r : ℕ, b (r + 1) = b r + ∑ i ∈ s, c i r) :
    IsPolyDegLe (K + 1) b := by
  have htel : ∀ r : ℕ, b r = b 0 + ∑ t ∈ range r, ∑ i ∈ s, c i t := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [hrec r, ih, Finset.sum_range_succ]
        ring
  obtain ⟨R, hRdeg, hRval⟩ := isPolyDegLe_sum s hc
  obtain ⟨Q, hQdeg, hQval⟩ := exists_antideriv R
  have hC : (Polynomial.C (b 0)).natDegree ≤ K + 1 := by
    rw [Polynomial.natDegree_C]
    omega
  refine ⟨C (b 0) + Q, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le_iff_right (Polynomial.C (b 0)) Q hC).mpr
      (hQdeg.trans (by omega))
  · intro n
    rw [htel n, Polynomial.eval_add, Polynomial.eval_C, hQval n]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hRval t

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/PolynomialRecurrence.lean
-- ==========================================================================

set_option autoImplicit false

namespace MagicSquaresSpencer

open Polynomial Finset

/-- A polynomial forward difference determines a polynomial sequence, including its
initial value. The difference is evaluated at the new level. -/
theorem exists_poly_of_forward_difference (b : ℕ → ℚ) (P : Polynomial ℚ)
    (h : ∀ t : ℕ, b (t + 1) = b t + P.eval ((t + 1 : ℕ) : ℚ)) :
    ∃ Q : Polynomial ℚ, ∀ t : ℕ, Q.eval (t : ℚ) = b t := by
  let R := P.comp (X + 1)
  refine ⟨C (b 0) + antideriv R, ?_⟩
  intro t
  rw [Polynomial.eval_add, Polynomial.eval_C, antideriv_eval]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, h]
    simp [R, Polynomial.eval_comp, Nat.cast_add, Nat.cast_one]

/-- Induction for closed-support counts. Bad boards need only vanish at positive
levels, so their exceptional zero matrix never enters the forward difference. -/
theorem exists_poly_of_board_recurrence {α : Type*} [DecidableEq α]
    (b : Finset α → ℕ → ℚ) (good : Finset α → Prop)
    (terms : Finset α → Finset (Finset α))
    (child : Finset α → Finset α → Finset α)
    (weight : Finset α → Finset α → ℚ)
    (smaller : ∀ B C, C ∈ terms B → child B C ⊂ B)
    (bad : ∀ B, ¬ good B → ∀ t : ℕ, b B (t + 1) = 0)
    (recurrence : ∀ B, good B → ∀ t : ℕ,
      b B (t + 1) = b B t + ∑ C ∈ terms B, weight B C * b (child B C) (t + 1)) :
    ∀ B, good B → ∃ Q : Polynomial ℚ, ∀ t : ℕ, Q.eval (t : ℚ) = b B t := by
  classical
  intro B
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    intro hB
    have hp : ∀ C ∈ terms B, ∃ P : Polynomial ℚ,
        ∀ t : ℕ, P.eval ((t + 1 : ℕ) : ℚ) = b (child B C) (t + 1) := by
      intro C hC
      by_cases hg : good (child B C)
      · obtain ⟨P, hP⟩ := ih (child B C) (smaller B C hC) hg
        exact ⟨P, fun t => hP (t + 1)⟩
      · exact ⟨0, fun t => by simp [bad (child B C) hg t]⟩
    choose P hP using hp
    let R : Polynomial ℚ := ∑ C ∈ (terms B).attach,
      Polynomial.C (weight B C.val) * P C.val C.property
    apply exists_poly_of_forward_difference (b B) R
    intro t
    rw [recurrence B hB t]
    congr 1
    simp only [R, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    simp_rw [hP]
    exact (Finset.sum_attach _ _).symm

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/HallSupport.lean
-- ==========================================================================

/-
# Brick 3: the support of a semi-magic square contains a permutation

Spencer's proof of polynomiality runs a recursion over the *support sets*
`B(T) = {(i,j) : T(i,j) ≥ 1}` of semi-magic squares, ordered by inclusion.  The recursion
step removes from such a square the 0/1 matrix of a permutation contained in its support, and
for that to be possible every support set must contain one.  That is exactly Hall's marriage
theorem, and the zbMATH review of Spencer's note lists "marriage theorem" among its keywords.

This brick proves the input in the form the recursion needs it:

  if `M` is an `n × n` matrix of nonnegative integers whose rows and columns all sum to the
  same *positive* `t`, then there is a permutation `σ` with `0 < M i (σ i)` for all `i`.

Positivity of `t` is essential: the zero matrix has the empty support and no permutation in it,
which is the source of the boundary subtlety recorded in `SPENCER-ROUTE.md` §4.1.

Scratch file, compiled with `lake env lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

/-- **The Birkhoff–von Neumann/marriage input for Spencer's proof.**  The support of a
nonnegative integer matrix with all rows and columns summing to the same positive `t` contains
the support of a permutation matrix. -/
theorem exists_perm_pos_of_line_sums {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) (ht : 0 < t)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, M i j = t)
    (hcol : ∀ j : Fin n, ∑ i : Fin n, M i j = t) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 0 < M i (σ i) := by
  classical
  set supp : Fin n → Finset (Fin n) := fun i => Finset.univ.filter fun j => 0 < M i j with hsupp
  have hmem : ∀ i j : Fin n, j ∈ supp i ↔ 0 < M i j := by
    intro i j
    rw [hsupp]
    simp
  have hhall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion supp).card := by
    intro s
    have key : s.card * t ≤ (s.biUnion supp).card * t := by
      calc s.card * t = ∑ i ∈ s, ∑ j : Fin n, M i j := by
            rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, smul_eq_mul]
        _ = ∑ i ∈ s, ∑ j ∈ s.biUnion supp, M i j := by
            refine (Finset.sum_congr rfl fun i hi => ?_).symm
            refine Finset.sum_subset (fun j _ => Finset.mem_univ j) fun j _ hj => ?_
            by_contra hne
            exact hj (Finset.mem_biUnion.mpr ⟨i, hi, (hmem i j).mpr (Nat.pos_of_ne_zero hne)⟩)
        _ = ∑ j ∈ s.biUnion supp, ∑ i ∈ s, M i j := Finset.sum_comm
        _ ≤ ∑ j ∈ s.biUnion supp, ∑ i : Fin n, M i j := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (fun i _ => Finset.mem_univ i)
              fun i _ _ => Nat.zero_le _
        _ = ∑ j ∈ s.biUnion supp, t := by
            exact Finset.sum_congr rfl fun j _ => hcol j
        _ = (s.biUnion supp).card * t := by
            rw [Finset.sum_const, smul_eq_mul]
    exact Nat.le_of_mul_le_mul_right key ht
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective supp).mp hhall
  refine ⟨Equiv.ofBijective f ?_, fun i => (hmem i (f i)).mp (hf i)⟩
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hfinj, rfl⟩

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/SupportSplit.lean
-- ==========================================================================

/-
# Brick 4: splitting a semi-magic square along a permutation in its support

This is the technical heart of step 3 of Spencer's proof.  Given a semi-magic square `T` of
line sum `r` and a permutation `σ` whose support `φ = {(i, σ i)}` lies inside the support of `T`,
the matrix `S := T - P` (where `P` is the 0/1 matrix of `σ`) is again semi-magic, now of line
sum `r - 1`, and its support is obtained from that of `T` by deleting exactly those cells of `φ`
where `T` takes the value `1`:

  `supp S ∪ φ = supp T`,   `(i, σ i) ∈ supp S ↔ 1 < T i (σ i)`.

Equivalently, `supp S` runs over the support sets `C` with `supp T \ φ ⊆ C ⊆ supp T`, and
`C = supp T` exactly when `T ≥ 2` on `φ`.  Since `S ↦ S + P` inverts `T ↦ T - P`, this is a
bijection and produces the recurrence consumed by `isPolyDegLe_of_recurrence`:

  `h_B(r) = h_B(r-1) + Σ_{C : B \ φ ⊆ C ⊊ B} h_C(r-1)`   for `r ≥ 2`.

`0 < T i (σ i)` (i.e. `φ ⊆ supp T`) is what makes `T - P` a genuine subtraction; positivity of
the line sum is what makes `φ` exist at all (see `HallSupport.lean`).

Scratch file, compiled with `lake env lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

variable {n : ℕ}

/-- The `0/1` matrix of a permutation. -/
def permMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if σ i = j then 1 else 0

/-- The support of a matrix, as a finset of positions. -/
def matSupport (M : Matrix (Fin n) (Fin n) ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => 0 < M p.1 p.2

theorem permMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permMatrix σ i j = if σ i = j then 1 else 0 := rfl

/-- `P ≤ T` entrywise as soon as `T` is positive on the support of `σ`. -/
theorem permMatrix_le_of_pos (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : ∀ i j, permMatrix σ i j ≤ T i j := by
  intro i j
  by_cases h : σ i = j
  · rw [permMatrix_apply, if_pos h, ← h]
    exact hσ i
  · rw [permMatrix_apply, if_neg h]
    exact Nat.zero_le _

theorem permMatrix_row (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ j : Fin n, permMatrix σ i j = 1 := by
  have h : ∀ j : Fin n, permMatrix σ i j = if σ i = j then (1 : ℕ) else 0 := fun j => rfl
  simp only [h]
  rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) (σ i) fun _ => (1 : ℕ)]
  simp

/-- The permutation matrix is transposed by passing to the inverse permutation. -/
theorem permMatrix_comm (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permMatrix σ i j = permMatrix σ.symm j i := by
  rw [permMatrix_apply, permMatrix_apply]
  by_cases h : σ i = j
  · rw [if_pos h, if_pos (by rw [← h, σ.symm_apply_apply])]
  · rw [if_neg h, if_neg fun h' => h (by rw [← h', σ.apply_symm_apply])]

theorem permMatrix_col (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    ∑ i : Fin n, permMatrix σ i j = 1 := by
  rw [Finset.sum_congr rfl fun i _ => permMatrix_comm σ i j]
  exact permMatrix_row σ.symm j

theorem matSupport_add (A B : Matrix (Fin n) (Fin n) ℕ) :
    matSupport (A + B) = matSupport A ∪ matSupport B := by
  ext p
  obtain ⟨i, j⟩ := p
  have h : (A + B) i j = A i j + B i j := Matrix.add_apply A B i j
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, h]
  omega

theorem matSupport_permMatrix (σ : Equiv.Perm (Fin n)) :
    matSupport (permMatrix σ) = Finset.univ.image fun i => (i, σ i) := by
  ext p
  obtain ⟨i, j⟩ := p
  rw [Finset.mem_image]
  constructor
  · intro h
    simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have h' : σ i = j := by
      by_contra hne
      rw [permMatrix_apply, if_neg hne] at h
      exact absurd h (by norm_num)
    exact ⟨i, Finset.mem_univ i, by rw [h']⟩
  · rintro ⟨k, -, hk⟩
    simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    have hki : k = i := (Prod.ext_iff.mp hk).1
    subst hki
    have hkj : σ k = j := (Prod.ext_iff.mp hk).2
    rw [permMatrix_apply, if_pos hkj]
    norm_num

/-- **The split.**  Removing the permutation matrix from a square that is positive on its support
yields a square whose support is that of the original, minus the cells of the permutation where
the original entry is exactly `1`. -/
theorem matSupport_sub_permMatrix_union (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) :
    matSupport (T - permMatrix σ) ∪ matSupport (permMatrix σ) = matSupport T := by
  ext p
  obtain ⟨i, j⟩ := p
  have hsub : (T - permMatrix σ) i j = T i j - permMatrix σ i j := Matrix.sub_apply T _ i j
  have hpm : permMatrix σ i j = if σ i = j then 1 else 0 := rfl
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    hsub, hpm]
  by_cases h : σ i = j
  · rw [if_pos h]
    constructor
    · intro _
      rw [← h]
      exact hσ i
    · intro _
      exact Or.inr (by norm_num)
  · rw [if_neg h]
    constructor
    · rintro (h1 | h2)
      · rwa [Nat.sub_zero] at h1
      · exact absurd h2 (by norm_num)
    · intro hT
      exact Or.inl (by rwa [Nat.sub_zero])

theorem matSupport_sub_permMatrix_subset (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : matSupport (T - permMatrix σ) ⊆ matSupport T := by
  intro p hp
  rw [← matSupport_sub_permMatrix_union T σ hσ]
  exact Finset.mem_union_left _ hp

/-- A cell of the permutation survives the split exactly when the original entry exceeds `1`. -/
theorem mem_matSupport_sub_permMatrix_perm (T : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (i, σ i) ∈ matSupport (T - permMatrix σ) ↔ 1 < T i (σ i) := by
  have hsub : (T - permMatrix σ) i (σ i) = T i (σ i) - permMatrix σ i (σ i) :=
    Matrix.sub_apply T _ i (σ i)
  have hpm : permMatrix σ i (σ i) = 1 := by rw [permMatrix_apply, if_pos rfl]
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, hsub, hpm]
  omega

theorem sub_add_permMatrix (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : T - permMatrix σ + permMatrix σ = T := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have := permMatrix_le_of_pos T σ hσ i j
  omega

theorem add_sub_permMatrix (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n)) :
    S + permMatrix σ - permMatrix σ = S := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  exact Nat.add_sub_cancel _ _

theorem sum_sub_permMatrix (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) (i : Fin n) :
    ∑ j : Fin n, (T - permMatrix σ) i j = (∑ j : Fin n, T i j) - 1 := by
  have key : ∑ j : Fin n, T i j = (∑ j : Fin n, (T - permMatrix σ) i j) + 1 := by
    have h : ∀ j : Fin n, T i j = (T - permMatrix σ) i j + permMatrix σ i j := by
      intro j
      rw [Matrix.sub_apply, Nat.sub_add_cancel (permMatrix_le_of_pos T σ hσ i j)]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, permMatrix_row σ i]
  omega

theorem sum_sub_permMatrix_col (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) (j : Fin n) :
    ∑ i : Fin n, (T - permMatrix σ) i j = (∑ i : Fin n, T i j) - 1 := by
  have key : ∑ i : Fin n, T i j = (∑ i : Fin n, (T - permMatrix σ) i j) + 1 := by
    have h : ∀ i : Fin n, T i j = (T - permMatrix σ) i j + permMatrix σ i j := by
      intro i
      rw [Matrix.sub_apply, Nat.sub_add_cancel (permMatrix_le_of_pos T σ hσ i j)]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, permMatrix_col σ j]
  omega

/-! ## Bricks 5-6: boxes, fibres, and the fibres of the split

The counting functions of the Spencer recursion live on matrices **with entries bounded by the
line sum**, and the bound drops by one when the permutation is removed.  It is therefore
convenient to describe a fibre as a finset of `ℕ`-valued matrices cut out by an explicit bound
condition, rather than as a finset of the platform's `Fin (t+1)`-valued matrices: the level-`s`
and level-`(s-1)` fibres then live in the *same* type, which is what makes the bijection
`T ↦ T - P` statable at all.  (With `Fin`-valued entries the two levels are different types, and
`Fin` subtraction moreover wraps around.)

The bridge back to the platform's `semiMagicCount` is a single cardinality lemma, deferred.
-/

/-- All `n × n` matrices of natural numbers with entries at most `s`. -/
def matBox (n s : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ) :=
  Finset.map
    ⟨fun M : Matrix (Fin n) (Fin n) (Fin (s + 1)) => fun i j => (M i j : ℕ),
      fun A B h => by funext i j; exact Fin.ext (congrFun (congrFun h i) j)⟩
    Finset.univ

theorem mem_matBox {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℕ} :
    M ∈ matBox n s ↔ ∀ i j, M i j ≤ s := by
  constructor
  · intro h
    rw [matBox, Finset.mem_map] at h
    obtain ⟨M', -, hM'⟩ := h
    intro i j
    rw [← congrFun (congrFun hM' i) j]
    exact Nat.le_of_lt_succ (M' i j).isLt
  · intro h
    rw [matBox, Finset.mem_map]
    refine ⟨fun i j => ⟨M i j, Nat.lt_succ_of_le (h i j)⟩, Finset.mem_univ _, ?_⟩
    funext i j
    rfl

theorem matBox_mono {n s t : ℕ} (h : s ≤ t) : matBox n s ⊆ matBox n t := by
  intro M hM
  rw [mem_matBox] at hM ⊢
  exact fun i j => (hM i j).trans h

/-- A matrix all of whose rows and columns sum to `s`. -/
def LineSums (M : Matrix (Fin n) (Fin n) ℕ) (s : ℕ) : Prop :=
  (∀ i, ∑ j, M i j = s) ∧ ∀ j, ∑ i, M i j = s

/-- The matrices with entries at most `m`, line sums `s` and support exactly `B`. -/
noncomputable def matFiber (n m s : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBox n m).filter fun M => LineSums M s ∧ matSupport M = B

/-- In a matrix whose rows all sum to `s`, every entry is at most `s`. -/
theorem le_of_rowSum {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℕ} (h : ∀ i, ∑ j, M i j = s)
    (i j : Fin n) : M i j ≤ s := by
  have := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n))) (f := fun j => M i j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [h i] at this
  exact this

/-- Removing a permutation matrix from a square keeps the entries within the bound `s`, and the
line sums drop by one; in fact the entries drop to at most `s - 1`. -/
theorem matBox_sub_permMatrix {n s : ℕ} {T : Matrix (Fin n) (Fin n) ℕ}
    (σ : Equiv.Perm (Fin n)) (hrow : ∀ i, ∑ j, (T - permMatrix σ) i j = s - 1) :
    T - permMatrix σ ∈ matBox n (s - 1) := by
  rw [mem_matBox]
  intro i j
  exact le_of_rowSum hrow i j

theorem sum_add_permMatrix (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ j : Fin n, (S + permMatrix σ) i j = (∑ j : Fin n, S i j) + 1 := by
  have h : ∀ j : Fin n, (S + permMatrix σ) i j = S i j + permMatrix σ i j :=
    fun j => Matrix.add_apply S _ i j
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, permMatrix_row σ i]

theorem sum_add_permMatrix_col (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) :
    ∑ i : Fin n, (S + permMatrix σ) i j = (∑ i : Fin n, S i j) + 1 := by
  have h : ∀ i : Fin n, (S + permMatrix σ) i j = S i j + permMatrix σ i j :=
    fun i => Matrix.add_apply S _ i j
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, permMatrix_col σ j]

theorem permMatrix_le_one (σ : Equiv.Perm (Fin n)) (i j : Fin n) : permMatrix σ i j ≤ 1 := by
  rw [permMatrix_apply]
  split_ifs <;> omega

/-- Adding the permutation matrix back keeps the entries within the bound `s`. -/
theorem mem_matBox_add_permMatrix {n s : ℕ} (hs : 1 ≤ s) {S : Matrix (Fin n) (Fin n) ℕ}
    (hrow : ∀ i, ∑ j, S i j = s - 1) (σ : Equiv.Perm (Fin n)) :
    S + permMatrix σ ∈ matBox n s := by
  rw [mem_matBox]
  intro i j
  have h1 : S i j ≤ s - 1 := le_of_rowSum hrow i j
  have h2 : permMatrix σ i j ≤ 1 := permMatrix_le_one σ i j
  rw [Matrix.add_apply]
  omega

/-- If `A ⊆ B`, `C ⊆ B` and `B \ A ⊆ C`, then `C ∪ A = B`. -/
theorem union_eq_of_subset {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hCB : C ⊆ B) (hAB : A ⊆ B) (hB : B \ A ⊆ C) : C ∪ A = B := by
  ext x
  rw [Finset.mem_union]
  constructor
  · rintro (hx | hx)
    · exact hCB hx
    · exact hAB hx
  · intro hx
    by_cases hxA : x ∈ A
    · exact Or.inr hxA
    · exact Or.inl (hB (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))

theorem mem_matSupport_permMatrix_self (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (i, σ i) ∈ matSupport (permMatrix σ) := by
  rw [matSupport_permMatrix]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The candidate supports for the split of a square supported on `B` along a permutation with
support `φ`: the `C` with `B \ φ ⊆ C ⊆ B`. -/
noncomputable def fiberCandidates (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact B.powerset.filter fun C => B \ φ ⊆ C

theorem mem_fiberCandidates {B φ C : Finset (Fin n × Fin n)} :
    C ∈ fiberCandidates B φ ↔ C ⊆ B ∧ B \ φ ⊆ C := by
  classical
  simp [fiberCandidates]

/-- **The heart of Spencer's step 3.**  Subtracting the permutation matrix spreads the squares of
line sum `s` whose support is `B` bijectively over the squares of line sum `s - 1` whose support
`C` satisfies `B \ φ ⊆ C ⊆ B`. -/
theorem card_matFiber_split {n s : ℕ} (hs : 1 ≤ s) {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n s s B).card
      = ∑ C ∈ fiberCandidates B (matSupport (permMatrix σ)), (matFiber n s (s - 1) C).card := by
  classical
  have hbij : (matFiber n s s B).card
      = ((fiberCandidates B (matSupport (permMatrix σ))).sigma
          fun C => matFiber n s (s - 1) C).card := by
    refine Finset.card_bij (fun T _ => ⟨matSupport (T - permMatrix σ), T - permMatrix σ⟩) ?_ ?_ ?_
    · rintro T hT
      simp only [matFiber, Finset.mem_filter] at hT
      obtain ⟨hbox, hls, hsup⟩ := hT
      have hσ : ∀ i, 0 < T i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T := by
          rw [hsup]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have hunion := matSupport_sub_permMatrix_union T σ hσ
      have hsub : matSupport (T - permMatrix σ) ⊆ B := by
        intro x hx
        rw [← hsup, ← hunion]
        exact Finset.mem_union_left _ hx
      have hsdiff : B \ matSupport (permMatrix σ) ⊆ matSupport (T - permMatrix σ) := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        have hone : x ∈ matSupport (T - permMatrix σ) ∪ matSupport (permMatrix σ) := by
          rw [hunion, hsup]
          exact hx.1
        rcases Finset.mem_union.mp hone with h | h
        · exact h
        · exact absurd h hx.2
      rw [Finset.mem_sigma, mem_fiberCandidates]
      refine ⟨⟨hsub, hsdiff⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_, rfl⟩
      · rw [mem_matBox] at hbox ⊢
        intro i j
        show (T - permMatrix σ) i j ≤ s
        rw [Matrix.sub_apply]
        have hTij : T i j ≤ s := hbox i j
        have hle := permMatrix_le_of_pos T σ hσ i j
        omega
      · exact ⟨fun i => by rw [sum_sub_permMatrix T σ hσ i, hls.1 i],
               fun j => by rw [sum_sub_permMatrix_col T σ hσ j, hls.2 j]⟩
    · rintro T₁ hT₁ T₂ hT₂ heq
      simp only [matFiber, Finset.mem_filter] at hT₁ hT₂
      have hσ₁ : ∀ i, 0 < T₁ i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T₁ := by
          rw [hT₁.2.2]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have hσ₂ : ∀ i, 0 < T₂ i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T₂ := by
          rw [hT₂.2.2]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have h : T₁ - permMatrix σ = T₂ - permMatrix σ := congrArg Sigma.snd heq
      rw [← sub_add_permMatrix T₁ σ hσ₁, ← sub_add_permMatrix T₂ σ hσ₂, h]
    · rintro ⟨C, S⟩ hmem
      rw [Finset.mem_sigma, mem_fiberCandidates] at hmem
      obtain ⟨⟨hCB, hsdiff⟩, hS⟩ := hmem
      simp only [matFiber, Finset.mem_filter] at hS
      obtain ⟨hSbox, hSls, hSsup⟩ := hS
      refine ⟨S + permMatrix σ, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · exact mem_matBox_add_permMatrix hs hSls.1 σ
        · exact ⟨fun i => by rw [sum_add_permMatrix S σ i, hSls.1 i]; omega,
                 fun j => by rw [sum_add_permMatrix_col S σ j, hSls.2 j]; omega⟩
        · rw [matSupport_add, hSsup, union_eq_of_subset hCB hφB hsdiff]
      · rw [add_sub_permMatrix S σ, hSsup]
  rw [hbij, Finset.card_sigma]

/-- **The recurrence.**  For `s ≥ 1` the number of squares of line sum `s` with support `B`
equals the number of line sum `s - 1` still supported on `B`, plus the sum over the strictly
smaller candidates `C`. -/
theorem card_matFiber_recurrence {n s : ℕ} (hs : 1 ≤ s) {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n s s B).card
      = (matFiber n s (s - 1) B).card
        + ∑ C ∈ (fiberCandidates B (matSupport (permMatrix σ))).erase B,
            (matFiber n s (s - 1) C).card := by
  classical
  have hBmem : B ∈ fiberCandidates B (matSupport (permMatrix σ)) := by
    rw [mem_fiberCandidates]
    exact ⟨Finset.Subset.refl B, Finset.sdiff_subset⟩
  rw [card_matFiber_split hs σ hφB]
  rw [← Finset.sum_erase_add (s := fiberCandidates B (matSupport (permMatrix σ)))
    (f := fun C => (matFiber n s (s - 1) C).card) hBmem, add_comm]

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/Recursion.lean
-- ==========================================================================

/-
# Brick 7: the support-set recursion, and polynomiality of the level counts

This is the last piece of Spencer's step 3 (`SPENCER-ROUTE.md` §5, rung **S2d**).  `SupportSplit.lean`
produced the recurrence one level at a time,

  `#(fibre of line sum s at B) = #(fibre of line sum s-1 at B) + Σ_{C ∈ nb B φ} #(fibre of line sum s-1 at C)`,

but with the *ambient* bound (the box the entries live in) still written as `s` on both sides, and
with the permutation `σ` left free.  Three things are done here:

1. **Cancelling the ambient bound.**  A fibre of line sum `s` already has all entries `≤ s`, so the
   ambient bound is redundant as soon as it dominates the line sum (`matFiber_eq_of_le`).  This is
   what lets the two sides live in the same type at all.
2. **Choosing the permutation.**  Hall (`HallSupport.lean`) gives a permutation inside the support of
   any square of *positive* line sum (`exists_perm_support_subset_of_lineSums`).  Note that once
   `φ(σ) ⊆ B = supp T`, the split applies to `T` for free: the hypothesis `0 < T i (σ i)` needed by
   `SupportSplit.lean` is automatic.  So a single `σ` per support set serves *every* line sum, which
   is exactly what a recurrence with constant coefficients requires.
3. **The induction.**  Shifting once (`gB n B r := #(fibre of line sum r+1 at B)`) turns the
   recurrence into `gB (r+1) = gB r + Σ_C gB C r`, the shifted Spencer step, and strong induction on
   `B.card` — legitimate because every `C ∈ nb B φ` is a *strict* subset of `B` — closes it.

The conclusion is

  `IsPolyDegLe B.card (gB n B)`  for every support `B`,

i.e. the count of squares of line sum `t ≥ 1` with support exactly `B` is a polynomial in `t` of
degree at most `#B`.  Summing over the supports (rung S4) is deliberately *not* attempted here.

Scratch file, built with `lake build examples.«magic-squares».spencer.Recursion`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial

/-! ## Step 1: the ambient bound is redundant

`matFiber n m s B` carries both the ambient bound `m` and the line sum `s`.  As soon as `s ≤ m` the
bound `m` is implied by the line sum, so the fibre does not depend on it.  This is the cancellation
promised in `card_matFiber_recurrence`: with it, both sides of the recurrence can be written with the
ambient bound equal to the line sum, which is the form the shift wants. -/

theorem matFiber_eq_of_le {n m s : ℕ} (h : s ≤ m) (B : Finset (Fin n × Fin n)) :
    matFiber n m s B = matFiber n s s B := by
  classical
  ext M
  simp only [matFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hls, hsup⟩
    rw [mem_matBox] at hbox ⊢
    exact ⟨fun i j => le_of_rowSum hls.1 i j, hls, hsup⟩
  · rintro ⟨hbox, hls, hsup⟩
    rw [mem_matBox] at hbox ⊢
    exact ⟨fun i j => (hbox i j).trans h, hls, hsup⟩

/-! ## Step 2: Hall, in the shape the recursion consumes -/

/-- **The permutation inside a support.**  A square of positive line sum has a permutation inside
its support.  This is `exists_perm_pos_of_line_sums` rewritten in terms of `matSupport`, and it is
all the freedom the recursion needs: a permutation supported on `B` splits *every* square supported
on `B`, at every line sum. -/
theorem exists_perm_support_subset_of_lineSums {n s : ℕ} (hs : 1 ≤ s)
    {T : Matrix (Fin n) (Fin n) ℕ} (hls : LineSums T s) :
    ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ matSupport T := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_pos_of_line_sums T (by omega) hls.1 hls.2
  refine ⟨σ, ?_⟩
  rw [matSupport_permMatrix]
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hσ i

/-! ## Step 3: the recurrence with the bound cancelled, and the induction -/

/-- The supports strictly below `B` that the split along a permutation with support `φ` can produce:
the `C` with `B \ φ ⊆ C ⊆ B`, `C ≠ B`. -/
noncomputable def nbSupp {n : ℕ} (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  (fiberCandidates B φ).erase B

/-- **The recurrence, ready for the Spencer step.**  For a square of line sum `s + 1` supported on
`B` and a permutation supported inside `B`, the level-`(s+1)` fibre at `B` splits into the level-`s`
fibre at `B` and the level-`s` fibres at the strictly smaller supports of `nbSupp B φ`. -/
theorem card_matFiber_recurrence_succ {n s : ℕ} {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n (s + 1) (s + 1) B).card
      = (matFiber n s s B).card
        + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), (matFiber n s s C).card := by
  classical
  have h := card_matFiber_recurrence (n := n) (s := s + 1) (B := B) (by omega) σ hφB
  have hsub : s + 1 - 1 = s := by omega
  rw [hsub] at h
  rw [matFiber_eq_of_le (m := s + 1) (Nat.le_succ s) B] at h
  rw [Finset.sum_congr rfl
    (fun C _ => congrArg Finset.card (matFiber_eq_of_le (m := s + 1) (Nat.le_succ s) C))] at h
  simpa only [nbSupp] using h

/-- The number of squares of line sum `r + 1` with support exactly `B`, as a sequence in `r`.

The `+ 1` is the shift of `SPENCER-ROUTE.md` §4.1: the support recursion only sees *positive* line
sums, and after shifting away from line sum `0` it is homogeneous with the constants as its base
case, so the Spencer step applies with no exceptional first coefficient.  The price is that the
resulting polynomial agrees with the true count only for `t ≥ 1`; the value at `t = 0` is the
reciprocity statement (rung S5) and is not claimed here. -/
noncomputable def gB (n : ℕ) (B : Finset (Fin n × Fin n)) : ℕ → ℚ :=
  fun r => ((matFiber n (r + 1) (r + 1) B).card : ℚ)

/-- In dimension `0` there is exactly one matrix, and it lies in the fibre over the empty support at
every level: the line-sum equations are vacuous, so nothing forces it out. -/
theorem card_matFiber_zero (m s : ℕ) : (matFiber 0 m s (∅ : Finset (Fin 0 × Fin 0))).card = 1 := by
  classical
  let M0 : Matrix (Fin 0) (Fin 0) ℕ := fun i => i.elim0
  have huniq : ∀ M : Matrix (Fin 0) (Fin 0) ℕ, M = M0 := fun M => funext fun i => i.elim0
  have hmem : ∀ M : Matrix (Fin 0) (Fin 0) ℕ, M ∈ matFiber 0 m s ∅ := by
    intro M
    rw [huniq M, matFiber, Finset.mem_filter]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · rw [mem_matBox]
      intro i
      exact i.elim0
    · exact ⟨fun i => i.elim0, fun j => j.elim0⟩
    · exact Finset.eq_empty_iff_forall_notMem.mpr fun p _ => p.1.elim0
  refine Finset.card_eq_one.mpr ⟨M0, ?_⟩
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem M0, fun M _ => huniq M⟩

/-- The empty support contributes a *constant*: the level-`(r+1)` fibre over `∅` is empty for
`n ≥ 1` (a matrix of support `∅` is zero, and its line sums are `0`), and a single point for
`n = 0`, where the line-sum equations are vacuous. -/
theorem isPolyDegLe_gB_empty (n : ℕ) : IsPolyDegLe 0 (gB n (∅ : Finset (Fin n × Fin n))) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    refine ⟨Polynomial.C 1, by simp, fun r => ?_⟩
    show (Polynomial.C (1 : ℚ)).eval (r : ℚ) = ((matFiber 0 (r + 1) (r + 1) ∅).card : ℚ)
    rw [Polynomial.eval_C, card_matFiber_zero]
    norm_num
  · refine ⟨Polynomial.C 0, by simp, fun r => ?_⟩
    rw [Polynomial.eval_C]
    have hcard : (matFiber n (r + 1) (r + 1) (∅ : Finset (Fin n × Fin n))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro M hM
      rw [matFiber, Finset.mem_filter] at hM
      obtain ⟨-, hls, hsup⟩ := hM
      have hM0 : ∀ j : Fin n, M ⟨0, hn1⟩ j = 0 := by
        intro j
        by_contra hne
        have hmem : (⟨0, hn1⟩, j) ∈ matSupport M := by
          simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.pos_of_ne_zero hne
        rw [hsup] at hmem
        simp at hmem
      have hpos : (0 : ℕ) = r + 1 := by
        rw [← hls.1 ⟨0, hn1⟩]
        exact (Finset.sum_eq_zero fun j _ => hM0 j).symm
      omega
    show (0 : ℚ) = ((matFiber n (r + 1) (r + 1) (∅ : Finset (Fin n × Fin n))).card : ℚ)
    rw [hcard, Nat.cast_zero]

/-- **Spencer's theorem at a fixed support.**  The number of `n × n` semi-magic squares of line sum
`r + 1` whose support is exactly `B` is a polynomial in `r` of degree at most `#B`.

The proof is strong induction on `#B`.  If no permutation fits inside `B`, the fibre is *empty* at
every level (Hall), so the sequence is zero.  Otherwise fix one such permutation `σ` — it serves
every level — and apply the shifted Spencer step to `card_matFiber_recurrence_succ`; the sum runs
over strict subsets, which is what makes the induction legitimate. -/
theorem isPolyDegLe_gB (n : ℕ) (B : Finset (Fin n × Fin n)) :
    IsPolyDegLe B.card (gB n B) := by
  classical
  have key : ∀ k, ∀ B : Finset (Fin n × Fin n), B.card = k → IsPolyDegLe B.card (gB n B) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hBk
      by_cases hB0 : B = ∅
      · subst hB0
        rw [Finset.card_empty]
        exact isPolyDegLe_gB_empty n
      · have hBpos : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
        by_cases hno : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
        · obtain ⟨σ, hφB⟩ := hno
          have hbelow : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), C ⊂ B := by
            intro C hC
            rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
            obtain ⟨hne, hCB, -⟩ := hC
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hCB, hne⟩
          have hih : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
              IsPolyDegLe (B.card - 1) (gB n C) := by
            intro C hC
            have hlt := hbelow C hC
            have hcard : C.card ≤ B.card - 1 := by
              have := Finset.card_lt_card hlt
              omega
            have hltk : C.card < k := by
              rw [← hBk]
              exact Finset.card_lt_card hlt
            exact isPolyDegLe_mono (ih C.card hltk C rfl) hcard
          have hrec : ∀ r : ℕ, gB n B (r + 1)
              = gB n B r + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), gB n C r := by
            intro r
            have hstep := card_matFiber_recurrence_succ (n := n) (s := r + 1) (B := B) σ hφB
            change ((matFiber n (r + 1 + 1) (r + 1 + 1) B).card : ℚ)
                = ((matFiber n (r + 1) (r + 1) B).card : ℚ)
                  + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
                      ((matFiber n (r + 1) (r + 1) C).card : ℚ)
            rw [hstep]
            push_cast
            rfl
          have hgoal : IsPolyDegLe ((B.card - 1) + 1) (gB n B) :=
            isPolyDegLe_of_recurrence_succ (b := gB n B) (c := fun C => gB n C)
              (K := B.card - 1) (nbSupp B (matSupport (permMatrix σ))) hih hrec
          rw [Nat.sub_add_cancel hBpos] at hgoal
          exact hgoal
        · -- no permutation fits inside `B`: Hall says the fibre is empty at every positive level
          have hzero : gB n B = fun _ => (0 : ℚ) := by
            funext r
            have hcard : (matFiber n (r + 1) (r + 1) B).card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro M hM
              rw [matFiber, Finset.mem_filter] at hM
              obtain ⟨-, hls, hsup⟩ := hM
              obtain ⟨σ, hσ⟩ :=
                exists_perm_support_subset_of_lineSums (n := n) (s := r + 1) (by omega) hls
              exact hno ⟨σ, by rw [← hsup]; exact hσ⟩
            show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
            rw [hcard, Nat.cast_zero]
          rw [hzero]
          exact isPolyDegLe_const 0 B.card
  exact key B.card B rfl

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/Aggregate.lean
-- ==========================================================================

/-
# Brick 8: summing the support fibres back up — the bridge to the platform's `semiMagicCount`

`Recursion.lean` proves that each support contributes a polynomial in the line sum (`isPolyDegLe_gB`).
What is still missing to say anything about the platform's `H_n(t) = semiMagicCount n t` is that the
support fibres *partition* the semi-magic squares.  That is this file (rung **S4a**), together with
the shift that turns "polynomial in `r` at line sum `r + 1`" into "polynomial in `t` at line sum
`t`" (rung **S4b**).

Two things to keep in mind, both from `SPENCER-ROUTE.md`:

* the platform's `semiMagicSquares n t` is a *filter of `Finset.univ`* on `Square n (Fin (t+1))`,
  while `matBox n t` is the image of that same `univ` under the entry coercion `Fin (t+1) → ℕ`.
  The bridge is a bijection along the coercion (and the coercion is injective);
* the conclusion is the **`t ≥ 1`** statement.  Agreement at `t = 0` is *not* claimed — it is the
  reciprocity content (rung S5, §4.1 of the route notes) — and the degree bound here is `n ^ 2`,
  not the sharp `(n-1) ^ 2` (that is rung S3, the face-rank count).

Scratch file, built with `lake build examples.«magic-squares».spencer.Aggregate`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-! ## S4a: the fibres partition the semi-magic squares -/

/-- The platform's `IsSemiMagic` is verbatim the row-and-column condition that `LineSums` names:
`rowSum`/`colSum` are the very same `∑ j`/`∑ i`. -/
theorem isSemiMagic_iff_lineSums {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    IsSemiMagic M t ↔ LineSums M t :=
  ⟨fun h => h, fun h => h⟩

/-- The line-sum-`t` part of the box, as a *named* finset.  This has to be a def rather than a
literal `Finset.filter` in a statement: a raw `filter` in a theorem's *type* needs a
`DecidablePred` instance, and the `classical` inside the proof body cannot supply one (the
statement is elaborated first).  `matFiber` and the platform's own `semiMagicSquares` are written
the same way, for the same reason. -/
noncomputable def matBoxLine (n t : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBox n t).filter fun M => LineSums M t

/-- **The bridge, at the level of the box.**  `matBox n t` is `Finset.univ` transported along the
entry coercion, so counting the line-sum-`t` members of the box is the same as counting the
platform's semi-magic squares of line sum `t`. -/
theorem card_matBoxLine (n t : ℕ) : (matBoxLine n t).card = semiMagicCount n t := by
  classical
  have hset : (Finset.univ.filter fun M : Square n (Fin (t + 1)) =>
        LineSums (fun i j => (M i j : ℕ)) t) = semiMagicSquares n t := by
    rw [semiMagicSquares]
    exact Finset.filter_congr fun M _ => (isSemiMagic_iff_lineSums _).symm
  rw [matBoxLine, semiMagicCount, ← hset, matBox, Finset.filter_map, Finset.card_map]
  refine congrArg Finset.card (Finset.filter_congr fun M _ => ?_)
  exact ⟨fun h => h, fun h => h⟩

/-- The fibre over `B` is exactly the `matSupport`-fibre of the line-sum-`t` part of the box. -/
theorem matFiber_eq_filter_matBoxLine {n t : ℕ} (B : Finset (Fin n × Fin n)) :
    matFiber n t t B = (matBoxLine n t).filter (fun M => matSupport M = B) := by
  classical
  rw [matBoxLine, matFiber, Finset.filter_filter]

/-- **The fibres sum to the count.**  Every semi-magic square has exactly one support, so the fibres
`matFiber n t t B` (over all supports `B`, i.e. over the whole powerset — the non-supports
contribute nothing) partition the set counted by `semiMagicCount`. -/
theorem semiMagicCount_eq_sum_matFiber (n t : ℕ) :
    semiMagicCount n t
      = ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, (matFiber n t t B).card := by
  classical
  rw [← card_matBoxLine n t]
  rw [Finset.card_eq_sum_card_fiberwise (f := matSupport) (s := matBoxLine n t)
    (t := (Finset.univ : Finset (Fin n × Fin n)).powerset)
    (fun M _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [matFiber_eq_filter_matBoxLine B]

/-! ## S4b: shifting down by one, and the aggregate -/

/-- **Shifting a polynomial sequence down.**  If `b` agrees with a polynomial of degree `≤ K`, so
does `t ↦ b (t - 1)` — for `t ≥ 1`, by substituting `X - 1` (the identity `↑(t-1) = ↑t - 1` is what
fails at `t = 0`, and nothing is claimed there). -/
theorem exists_poly_comp_X_sub_one {K : ℕ} {b : ℕ → ℚ} (h : IsPolyDegLe K b) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ K ∧ ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = b (t - 1) := by
  obtain ⟨P, hPdeg, hPval⟩ := h
  refine ⟨P.comp (Polynomial.X - Polynomial.C 1), ?_, fun t ht => ?_⟩
  · refine (Polynomial.natDegree_comp_le (p := P) (q := Polynomial.X - Polynomial.C 1)).trans ?_
    have hq : (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree ≤ 1 := by
      calc (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree
          ≤ max (Polynomial.X : ℚ[X]).natDegree (Polynomial.C (1 : ℚ)).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max 1 0 := max_le_max (le_of_eq Polynomial.natDegree_X)
            (le_of_eq (Polynomial.natDegree_C (1 : ℚ)))
        _ = 1 := by norm_num
    calc P.natDegree * (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree
        ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hq
      _ = P.natDegree := Nat.mul_one _
      _ ≤ K := hPdeg
  · have hval : ((t : ℚ) - 1) = ((t - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub ht, Nat.cast_one]
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hval,
      hPval (t - 1)]

/-- **Spencer (1980), aggregated.**  For every `t ≥ 1` the number of `n × n` semi-magic squares of
line sum `t` is the value of one fixed polynomial of degree at most `n ^ 2`.

Both restrictions are deliberate and are *not* oversights:

* `t ≥ 1`: the support recursion only sees positive line sums, and `p(0) = 1` is the
  Ehrhart–Macdonald reciprocity statement at `-1` (rung S5);
* degree `n ^ 2` rather than `(n-1) ^ 2`: that is the crude count that the recursion bounds alone
  give; the sharp bound needs the face rank `ρ(B) = |B| - v(B) + c(B)` (rung S3). -/
theorem exists_polynomial_semiMagicCount_pos (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ n * n ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  have hcard : ∀ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, B.card ≤ n * n := by
    intro B hB
    calc B.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_le_card (Finset.mem_powerset.mp hB)
      _ = n * n := by simp
  have hsum : IsPolyDegLe (n * n)
      (fun r => ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, gB n B r) :=
    isPolyDegLe_sum _ fun B hB => isPolyDegLe_mono (isPolyDegLe_gB n B) (hcard B hB)
  obtain ⟨p, hpdeg, hpval⟩ := exists_poly_comp_X_sub_one hsum
  refine ⟨p, hpdeg, fun t ht => ?_⟩
  rw [hpval t ht, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  show ((matFiber n ((t - 1) + 1) ((t - 1) + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/ClosedSupport.lean
-- ==========================================================================

/-!
# Closed support fibres

These are semi-magic squares whose support is contained in a fixed board.  Subtracting a fixed
permutation matrix is a bijection between the next-level squares positive on that permutation and
the entire current-level closed fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open MagicSquares

variable {n : ℕ}

/-- Semi-magic squares of line sum `t` whose support is contained in `B`. -/
noncomputable def closedFiber (n t : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBoxLine n t).filter fun M => matSupport M ⊆ B

theorem mem_closedFiber {n t : ℕ} {B : Finset (Fin n × Fin n)}
    {M : Matrix (Fin n) (Fin n) ℕ} :
    M ∈ closedFiber n t B ↔ M ∈ matBoxLine n t ∧ matSupport M ⊆ B := by
  classical
  simp [closedFiber]

/-- Containing the support of a permutation is exactly positivity on its selected cells. -/
theorem permSupport_subset_matSupport_iff (M : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) :
    matSupport (permMatrix σ) ⊆ matSupport M ↔ ∀ i, 0 < M i (σ i) := by
  constructor
  · intro h i
    have := h (mem_matSupport_permMatrix_self σ i)
    simpa [matSupport] using this
  · intro h
    rw [matSupport_permMatrix]
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    simpa [matSupport] using h i

/-- Subtracting `Pσ` bijects closed-support squares at level `t+1` which are positive on `σ`
with all closed-support squares at level `t`. -/
theorem card_closedFiber_filter_permSupport (n t : ℕ)
    (B : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (hφB : matSupport (permMatrix σ) ⊆ B) :
    ((closedFiber n (t + 1) B).filter
        (fun M => matSupport (permMatrix σ) ⊆ matSupport M)).card
      = (closedFiber n t B).card := by
  classical
  refine Finset.card_bij (fun T _ => T - permMatrix σ) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hclosed, hφT⟩ := hT
    rw [mem_closedFiber] at hclosed ⊢
    obtain ⟨hline, hTB⟩ := hclosed
    rw [matBoxLine, Finset.mem_filter] at hline ⊢
    obtain ⟨hbox, hls⟩ := hline
    have hpos : ∀ i, 0 < T i (σ i) :=
      (permSupport_subset_matSupport_iff T σ).mp hφT
    refine ⟨?_, matSupport_sub_permMatrix_subset T σ hpos |>.trans hTB⟩
    refine ⟨?_, ?_⟩
    · rw [mem_matBox]
      exact fun i j => le_of_rowSum (fun i => by
        rw [sum_sub_permMatrix T σ hpos i, hls.1 i]
        omega) i j
    · exact ⟨fun i => by rw [sum_sub_permMatrix T σ hpos i, hls.1 i]; omega,
        fun j => by rw [sum_sub_permMatrix_col T σ hpos j, hls.2 j]; omega⟩
  · intro T₁ hT₁ T₂ hT₂ heq
    rw [Finset.mem_filter] at hT₁ hT₂
    have hpos₁ := (permSupport_subset_matSupport_iff T₁ σ).mp hT₁.2
    have hpos₂ := (permSupport_subset_matSupport_iff T₂ σ).mp hT₂.2
    rw [← sub_add_permMatrix T₁ σ hpos₁, ← sub_add_permMatrix T₂ σ hpos₂, heq]
  · intro S hS
    refine ⟨S + permMatrix σ, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_closedFiber]
      rw [mem_closedFiber] at hS
      obtain ⟨hline, hSB⟩ := hS
      rw [matBoxLine, Finset.mem_filter] at hline
      obtain ⟨hbox, hls⟩ := hline
      have hline' : S + permMatrix σ ∈ matBoxLine n (t + 1) := by
        rw [matBoxLine, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [mem_matBox]
          exact fun i j => le_of_rowSum (fun i => by
            rw [sum_add_permMatrix S σ i, hls.1 i]) i j
        · exact ⟨fun i => by rw [sum_add_permMatrix S σ i, hls.1 i],
            fun j => by rw [sum_add_permMatrix_col S σ j, hls.2 j]⟩
      refine ⟨⟨hline', ?_⟩, ?_⟩
      · rw [matSupport_add]
        exact Finset.union_subset hSB hφB
      · rw [matSupport_add]
        exact Finset.subset_union_right
    · exact add_sub_permMatrix S σ

/-- If `B` contains no permutation support, its positive closed fibres are empty. -/
theorem closedFiber_eq_empty_of_no_perm {n t : ℕ} (ht : 1 ≤ t)
    {B : Finset (Fin n × Fin n)}
    (hno : ∀ σ : Equiv.Perm (Fin n), ¬ matSupport (permMatrix σ) ⊆ B) :
    closedFiber n t B = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [mem_closedFiber] at hM
  rw [matBoxLine, Finset.mem_filter] at hM
  obtain ⟨σ, hσ⟩ := exists_perm_support_subset_of_lineSums ht hM.1.2
  exact hno σ (hσ.trans hM.2)

/-- The full board imposes no support restriction. -/
theorem closedFiber_univ (n t : ℕ) :
    closedFiber n t (Finset.univ : Finset (Fin n × Fin n)) = matBoxLine n t := by
  classical
  ext M
  simp [closedFiber]

theorem card_closedFiber_univ (n t : ℕ) :
    (closedFiber n t (Finset.univ : Finset (Fin n × Fin n))).card =
      MagicSquares.semiMagicCount n t := by
  rw [closedFiber_univ, card_matBoxLine]

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/Rank.lean
-- ==========================================================================

/-
# Brick 9: the sharp degree bound — rung S3, via the zero-line-sum space

Spencer's recursion (`Recursion.lean`) bounds the degree of the level counts by `#B`, which
aggregated gives degree `≤ n²` — one full order too high.  The sharp bound `(n-1)²` is usually
read off the face rank `ρ(B) = |B| - v(B) + c(B)` of the Birkhoff polytope, which needs the
connectivity of the support graph.  This file avoids graph theory altogether, by measuring the
rank of a support `B` as the dimension of the *zero-line-sum space*

  `zeroLineSubmodule B = {M : Fin n → Fin n → ℚ | every line sum of M is 0, supp M ⊆ B}`,

whose dimension is exactly `|B| - v(B) + c(B)` (the constraint rank `v(B) - c(B)` is never
computed, so neither are the vertices or the components).  What is needed instead:

* `rankB_univ` — `dim zeroLineSubmodule(univ) = (n-1)²`, by rank–nullity on the line-sum map
  (its range is the `Σrow = Σcol` hyperplane, of dimension `2n - 1`; surjectivity is the
  explicit transportation matrix `M i j = (a (inl i) + a (inr j) - d / n) / n`);
* the **escape lemma** — if `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` and `e ∈ B \ C`, then some
  zero-line-sum matrix on `B` is nonzero at `e`.  Proof by duality: were `e` forced to zero,
  the evaluation functional at `e` would factor through the line-sum map
  (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), yielding coefficients `u` (rows) and
  `v` (columns) with `u i + v j = [ij = e]` on `B`.  Summing over the `τ`-cells `(i, τ i) ∈ C`
  gives `Σu + Σv = 0`, while summing over the `σ`-cells `(i, σ i) ∈ B` — exactly one of which
  is `e`, since `e ∈ B \ C ⊆ φ(σ)` — gives `Σu + Σv = 1`.  Contradiction;
* `rankB_lt_of_candidate` — consequently `rankB C < rankB B` for every candidate `C ⊂ B`
  that contains a permutation support (a proper subspace of equal dimension is impossible).

The payoff (rung S3b, later in this file) is `isPolyDegLe_gB_sharp` (degree `≤ rankB B` at
every support) and `exists_polynomial_semiMagicCount_sharp` (degree `≤ (n-1)²`, still for
`t ≥ 1`; the value at `t = 0` is rung S5 and is *not* claimed).  Both are **new** declarations —
the published `isPolyDegLe_gB` / `exists_polynomial_semiMagicCount_pos` are left untouched.

Scratch file, built with `lake build examples.«magic-squares».spencer.Rank`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-! ## The line-sum functional on `ℚ`-valued matrices -/

/-- The line sums of a `ℚ`-valued matrix, as one function on `Fin n ⊕ Fin n`. -/
def lsumQ (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) : ℚ :=
  Sum.elim (fun i => ∑ j, M i j) (fun j => ∑ i, M i j) a

@[simp] theorem lsumQ_inl (M : Fin n → Fin n → ℚ) (i : Fin n) :
    lsumQ M (Sum.inl i) = ∑ j, M i j := rfl

@[simp] theorem lsumQ_inr (M : Fin n → Fin n → ℚ) (j : Fin n) :
    lsumQ M (Sum.inr j) = ∑ i, M i j := rfl

@[simp] theorem lsumQ_zero (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) : lsumQ 0 a = 0 := by
  cases a <;> simp

@[simp] theorem lsumQ_add (M N : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (M + N) a = lsumQ M a + lsumQ N a := by
  cases a <;> simp [Pi.add_apply, Finset.sum_add_distrib]

@[simp] theorem lsumQ_smul (c : ℚ) (M : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (c • M) a = c * lsumQ M a := by
  cases a <;> simp [Pi.smul_apply, Finset.mul_sum, smul_eq_mul]

@[simp] theorem lsumQ_sub (M N : Fin n → Fin n → ℚ) (a : Fin n ⊕ Fin n) :
    lsumQ (M - N) a = lsumQ M a - lsumQ N a := by
  cases a <;> simp [Pi.sub_apply, Finset.sum_sub_distrib]

/-- Line sums of a `ℚ`-coerced `ℕ`-matrix are the coercion of its line sum. -/
theorem lsumQ_cast {M : Matrix (Fin n) (Fin n) ℕ} {s : ℕ} (h : LineSums M s)
    (a : Fin n ⊕ Fin n) : lsumQ (fun i j => (M i j : ℚ)) a = (s : ℚ) := by
  cases a with
  | inl i => rw [lsumQ_inl, ← Nat.cast_sum, h.1 i]
  | inr j => rw [lsumQ_inr, ← Nat.cast_sum, h.2 j]

/-- The line-sum map `M ↦ (row sums, col sums)`, linear. -/
noncomputable def lineSumMap (n : ℕ) : (Fin n → Fin n → ℚ) →ₗ[ℚ] (Fin n ⊕ Fin n → ℚ) where
  toFun := lsumQ
  map_add' := by
    intro x y
    funext a
    simp [lsumQ_add, Pi.add_apply]
  map_smul' := by
    intro m x
    funext a
    simp [lsumQ_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- The imbalance functional `a ↦ Σrow a - Σcol a`, linear. -/
noncomputable def imbalanceMap (n : ℕ) : (Fin n ⊕ Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun a := ∑ i, a (Sum.inl i) - ∑ j, a (Sum.inr j)
  map_add' := by
    intro x y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro m x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_sub]

/-- The `Σrow = Σcol` hyperplane. -/
noncomputable def balanceSpace (n : ℕ) : Submodule ℚ (Fin n ⊕ Fin n → ℚ) where
  carrier := {a | ∑ i, a (Sum.inl i) = ∑ j, a (Sum.inr j)}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha hb ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [ha, hb]
  zero_mem' := by rw [Set.mem_setOf_eq]; simp
  smul_mem' := by
    intro c a ha
    rw [Set.mem_setOf_eq] at ha ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ha]

theorem mem_balanceSpace (a : Fin n ⊕ Fin n → ℚ) :
    a ∈ balanceSpace n ↔ ∑ i, a (Sum.inl i) = ∑ j, a (Sum.inr j) := Iff.rfl

theorem mem_balanceSpace_iff (x : Fin n ⊕ Fin n → ℚ) :
    x ∈ balanceSpace n ↔ imbalanceMap n x = 0 := by
  constructor
  · intro h
    have hx : ∑ i, x (Sum.inl i) = ∑ j, x (Sum.inr j) := (mem_balanceSpace x).mp h
    show ∑ i, x (Sum.inl i) - ∑ j, x (Sum.inr j) = 0
    rw [hx]
    ring
  · intro h
    have hx : ∑ i, x (Sum.inl i) - ∑ j, x (Sum.inr j) = 0 := h
    exact (mem_balanceSpace x).mpr (by linarith)

theorem range_lineSumMap_le_balance (n : ℕ) :
    LinearMap.range (lineSumMap n) ≤ balanceSpace n := by
  intro a ha
  obtain ⟨M, rfl⟩ := ha
  have heq : ∑ i, lsumQ M (Sum.inl i) = ∑ j, lsumQ M (Sum.inr j) := by
    simp only [lsumQ_inl, lsumQ_inr]
    rw [Finset.sum_comm]
  exact heq

/-- **Surjectivity onto the balance hyperplane**, by the explicit transportation matrix
`M i j = (a (inl i) + a (inr j) - d / n) / n` with `d = Σcol a`. -/
theorem balance_le_range_lineSumMap {n : ℕ} (hn : 1 ≤ n) :
    balanceSpace n ≤ LinearMap.range (lineSumMap n) := by
  intro a ha
  have hd : ∑ i, a (Sum.inl i) = ∑ k, a (Sum.inr k) := (mem_balanceSpace a).mp ha
  have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsumconst : ∀ x : ℚ, (∑ _j : Fin n, x) = n * x := by intro x; simp
  have hq : ∀ z : ℚ, (n : ℚ) * (z / (n : ℚ)) = z := fun z => by
    rw [mul_comm, div_mul_cancel₀ _ hne]
  have hrow : ∀ i : Fin n,
      (∑ j : Fin n, ((a (Sum.inl i) + a (Sum.inr j)
        - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))) = a (Sum.inl i) := by
    intro i
    have key : ∀ j : Fin n,
        ((a (Sum.inl i) + a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))
          = ((a (Sum.inl i) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ)
              + a (Sum.inr j) / (n : ℚ)) := fun _ => by ring
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, hsumconst,
      ← Finset.sum_div, mul_div_cancel₀ _ hne, sub_add_cancel]
  have hcol : ∀ j : Fin n,
      (∑ i : Fin n, ((a (Sum.inl i) + a (Sum.inr j)
        - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))) = a (Sum.inr j) := by
    intro j
    have key : ∀ i : Fin n,
        ((a (Sum.inl i) + a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ))
          = ((a (Sum.inr j) - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ)
              + a (Sum.inl i) / (n : ℚ)) := fun _ => by ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, hsumconst,
      ← Finset.sum_div, hd, mul_div_cancel₀ _ hne, sub_add_cancel]
  refine LinearMap.mem_range.mpr
    ⟨fun i j => (a (Sum.inl i) + a (Sum.inr j)
      - (∑ k : Fin n, a (Sum.inr k)) / (n : ℚ)) / (n : ℚ), ?_⟩
  funext a'
  cases a' with
  | inl i => exact hrow i
  | inr j => exact hcol j

theorem range_lineSumMap_eq_balance {n : ℕ} (hn : 1 ≤ n) :
    LinearMap.range (lineSumMap n) = balanceSpace n :=
  le_antisymm (range_lineSumMap_le_balance n) (balance_le_range_lineSumMap hn)

/-! ## The zero-line-sum space, the equal-line-sum space, and the rank -/

/-- `M` has zero line sums and is supported inside `B`. -/
def IsZeroLine (B : Finset (Fin n × Fin n)) (M : Fin n → Fin n → ℚ) : Prop :=
  (∀ a, lsumQ M a = 0) ∧ ∀ i j, (i, j) ∉ B → M i j = 0

/-- `M` has all line sums equal to each other and is supported inside `B`. -/
def IsEqLine (B : Finset (Fin n × Fin n)) (M : Fin n → Fin n → ℚ) : Prop :=
  (∀ a b, lsumQ M a = lsumQ M b) ∧ ∀ i j, (i, j) ∉ B → M i j = 0

theorem IsZeroLine.eqLine {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ}
    (h : IsZeroLine B M) : IsEqLine B M :=
  ⟨fun a b => (h.1 a).trans (h.1 b).symm, h.2⟩

/-- The zero-line-sum space of a support. -/
def zeroLineSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | IsZeroLine B M}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun c => by rw [lsumQ_add, ha.1 c, hb.1 c, add_zero], fun i j hij => ?_⟩
    simp only [Pi.add_apply]
    rw [ha.2 i j hij, hb.2 i j hij, add_zero]
  zero_mem' := ⟨fun a => lsumQ_zero 0 a, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun b => by rw [lsumQ_smul, ha.1 b, mul_zero], fun i j hij => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha.2 i j hij, mul_zero]

/-- The equal-line-sum space of a support. -/
def eqLineSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | IsEqLine B M}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun c d => by rw [lsumQ_add, lsumQ_add, ha.1 c d, hb.1 c d], fun i j hij => ?_⟩
    simp only [Pi.add_apply]
    rw [ha.2 i j hij, hb.2 i j hij, add_zero]
  zero_mem' := ⟨fun a b => (lsumQ_zero 0 a).trans (lsumQ_zero 0 b).symm, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun d e => by rw [lsumQ_smul, lsumQ_smul, ha.1 d e], fun i j hij => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha.2 i j hij, mul_zero]

/-- **The rank of a support**: the dimension of its zero-line-sum space.  This is the face
rank `ρ(B) = |B| - v(B) + c(B)` in disguise; the graph never appears. -/
noncomputable def rankB (B : Finset (Fin n × Fin n)) : ℕ :=
  Module.finrank ℚ (zeroLineSubmodule B)

theorem mem_zeroLineSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ zeroLineSubmodule B ↔ IsZeroLine B M := ⟨fun h => h, fun h => h⟩

theorem mem_eqLineSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ eqLineSubmodule B ↔ IsEqLine B M := ⟨fun h => h, fun h => h⟩
theorem ker_lineSumMap (n : ℕ) :
    LinearMap.ker (lineSumMap n) = zeroLineSubmodule (Finset.univ : Finset (Fin n × Fin n)) := by
  ext M
  constructor
  · intro h
    rw [mem_zeroLineSubmodule]
    refine ⟨fun a => congrFun h a, fun i j hij => absurd (Finset.mem_univ (i, j)) hij⟩
  · intro h
    rw [LinearMap.mem_ker]
    funext a
    show lsumQ M a = 0
    exact (mem_zeroLineSubmodule.mp h).1 a

/-! ### two finrank helpers -/

theorem finrank_le_finrank_of_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {p q : Submodule ℚ V} (h : p ≤ q) :
    Module.finrank ℚ ↥p ≤ Module.finrank ℚ ↥q := by
  have hinj : Function.Injective (Submodule.inclusion h) := Submodule.inclusion_injective h
  have hr : Module.finrank ℚ (LinearMap.range (Submodule.inclusion h))
      = Module.finrank ℚ ↥p := LinearMap.finrank_range_of_inj hinj
  calc Module.finrank ℚ ↥p
      = Module.finrank ℚ (LinearMap.range (Submodule.inclusion h)) := hr.symm
    _ ≤ Module.finrank ℚ ↥q := Submodule.finrank_le _

theorem finrank_lt_of_proper_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {p q : Submodule ℚ V} (hpq : p ≤ q) (hne : p ≠ q) :
    Module.finrank ℚ ↥p < Module.finrank ℚ ↥q := by
  have hinj : Function.Injective (Submodule.inclusion hpq) := Submodule.inclusion_injective hpq
  have hr : Module.finrank ℚ (LinearMap.range (Submodule.inclusion hpq))
      = Module.finrank ℚ ↥p := LinearMap.finrank_range_of_inj hinj
  have hne2 : LinearMap.range (Submodule.inclusion hpq) ≠ ⊤ := by
    intro heq
    have hnotle : ¬ (q ≤ p) := fun h => hne (le_antisymm hpq h)
    obtain ⟨x, hxq, hxp⟩ : ∃ x : V, x ∈ q ∧ x ∉ p := by
      by_contra hall
      push_neg at hall
      exact hnotle fun y hy => hall y hy
    have hxq' : (⟨x, hxq⟩ : ↥q) ∈ LinearMap.range (Submodule.inclusion hpq) := by
      rw [heq]; exact Submodule.mem_top
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hxq'
    have hy2 : (y : V) = x := congrArg Subtype.val hy
    refine hxp ?_
    rw [← hy2]
    exact y.2
  calc Module.finrank ℚ ↥p
      = Module.finrank ℚ (LinearMap.range (Submodule.inclusion hpq)) := hr.symm
    _ < Module.finrank ℚ ↥q := Submodule.finrank_lt hne2

/-! ### rank monotonicity -/

theorem zeroLineSubmodule_mono {B C : Finset (Fin n × Fin n)} (h : B ⊆ C) :
    zeroLineSubmodule B ≤ zeroLineSubmodule C := by
  intro M hM
  exact ⟨hM.1, fun i j hij => hM.2 i j fun hc => hij (h hc)⟩

theorem rankB_mono {B C : Finset (Fin n × Fin n)} (h : B ⊆ C) : rankB B ≤ rankB C :=
  finrank_le_finrank_of_le (zeroLineSubmodule_mono h)

/-- **The rank of the full support is `(n-1)²`.**  Rank–nullity on the line-sum map: the domain
has dimension `n²`, the range is the `(2n-1)`-dimensional `Σrow = Σcol` hyperplane. -/
theorem rankB_univ (n : ℕ) :
    rankB (Finset.univ : Finset (Fin n × Fin n)) = (n - 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have hV : Module.finrank ℚ (Fin 0 → Fin 0 → ℚ) = 0 := by
      rw [Module.finrank_pi_fintype]; simp
    have hle := Submodule.finrank_le (zeroLineSubmodule (Finset.univ : Finset (Fin 0 × Fin 0)))
    simp only [rankB] at hle ⊢
    have hz : ((0 : ℕ) - 1) ^ 2 = 0 := by norm_num
    omega
  · -- finrank of the domain
    have hV : Module.finrank ℚ (Fin n → Fin n → ℚ) = n * n := by
      rw [Module.finrank_pi_fintype]
      have hint : ∀ _i : Fin n, Module.finrank ℚ (Fin n → ℚ) = n := fun _ => by
        rw [Module.finrank_pi]; simp
      simp [hint]
    -- finrank of the range: the balance hyperplane, dimension 2n - 1
    have hfr := LinearMap.finrank_range_add_finrank_ker (f := lineSumMap n)
    rw [range_lineSumMap_eq_balance hn1, hV] at hfr
    have hbal : Module.finrank ℚ (balanceSpace n) = 2 * n - 1 := by
      -- the balance hyperplane is a codimension-one subspace: ⊤ = balance ⊔ ℚ∙δ
      set δ : Fin n ⊕ Fin n → ℚ :=
        Sum.elim (fun i : Fin n => if i.val = 0 then (1 : ℚ) else 0) (fun _ => (0 : ℚ))
        with hδdef
      have hδrow : ∑ i : Fin n, δ (Sum.inl i) = 1 := by
        rw [Finset.sum_eq_single (⟨0, hn1⟩ : Fin n)]
        · simp [hδdef]
        · intro b _ hb
          simp only [hδdef, Sum.elim_inl]
          rw [if_neg (fun h : b.val = 0 => hb (Fin.ext h))]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hδf : imbalanceMap n δ = 1 := by
        show ∑ i : Fin n, δ (Sum.inl i) - ∑ j : Fin n, δ (Sum.inr j) = 1
        rw [hδrow]
        have hδcol : ∑ j : Fin n, δ (Sum.inr j) = 0 := by
          simp [hδdef]
        rw [hδcol]
        norm_num
      have hδne : δ ≠ 0 := by
        intro h
        have h0 : δ (Sum.inl (⟨0, hn1⟩ : Fin n)) = 0 := congrFun h _
        simp [hδdef] at h0
      have hsup : balanceSpace n ⊔ Submodule.span ℚ {δ} = ⊤ := by
        refine le_antisymm le_top ?_
        intro a ha
        refine Submodule.mem_sup.mpr ⟨a - imbalanceMap n a • δ, ?_, imbalanceMap n a • δ, ?_, ?_⟩
        · have hc : imbalanceMap n (a - imbalanceMap n a • δ) = 0 := by
            rw [map_sub, map_smul, hδf, smul_eq_mul, mul_one, sub_self]
          exact (mem_balanceSpace_iff _).mpr hc
        · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self δ)
        · exact sub_add_cancel _ _
      have hinf : balanceSpace n ⊓ Submodule.span ℚ {δ} = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx.2
        have himm : imbalanceMap n x = 0 := by
          have hxeq : ∑ i : Fin n, x (Sum.inl i) = ∑ j : Fin n, x (Sum.inr j) :=
            (mem_balanceSpace x).mp hx.1
          show ∑ i : Fin n, x (Sum.inl i) - ∑ j : Fin n, x (Sum.inr j) = 0
          rw [hxeq]
          ring
        rw [← hc] at himm
        rw [map_smul, hδf, smul_eq_mul, mul_one] at himm
        rw [← hc, himm, zero_smul]
      have hcard := Submodule.finrank_sup_add_finrank_inf_eq (balanceSpace n)
        (Submodule.span ℚ {δ})
      rw [hsup, hinf, finrank_top ℚ (Fin n ⊕ Fin n → ℚ), finrank_bot ℚ (Fin n ⊕ Fin n → ℚ),
        finrank_span_singleton hδne] at hcard
      have hV2 : Module.finrank ℚ (Fin n ⊕ Fin n → ℚ) = 2 * n := by
        rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [hV2] at hcard
      omega
    rw [hbal] at hfr
    rw [ker_lineSumMap] at hfr
    simp only [rankB]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hnm : m + 1 - 1 = m := by omega
    rw [hnm]
    have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e1] at hfr
    have key : 2 * m + 1 + m ^ 2 = (m + 1) * (m + 1) := by ring
    omega

/-! ## The escape lemma: cells outside a permutation-containing candidate are not forced

This is the strictness input for rung S3b.  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` (the shape every
candidate of the support recursion has) and `e ∈ B \ C`, then some zero-line-sum matrix on `B`
is nonzero at `e`; hence `rankB C < rankB B` for every candidate that contains a permutation. -/

/-- The free space on a support: all matrices supported inside `B`, no line-sum condition. -/
def suppSubmodule (B : Finset (Fin n × Fin n)) : Submodule ℚ (Fin n → Fin n → ℚ) where
  carrier := {M | ∀ i j, (i, j) ∉ B → M i j = 0}
  add_mem' := by
    intro a b ha hb i j hij
    have ha' : a i j = 0 := ha i j hij
    have hb' : b i j = 0 := hb i j hij
    show a i j + b i j = 0
    rw [ha', hb']
    norm_num
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := by
    intro c a ha i j hij
    have ha' : a i j = 0 := ha i j hij
    show c * a i j = 0
    rw [ha', mul_zero]

theorem mem_suppSubmodule {B : Finset (Fin n × Fin n)} {M : Fin n → Fin n → ℚ} :
    M ∈ suppSubmodule B ↔ ∀ i j, (i, j) ∉ B → M i j = 0 := ⟨fun h => h, fun h => h⟩

/-- The evaluation functional at a cell. -/
noncomputable def evalCell (e : Fin n × Fin n) : (Fin n → Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun M := M e.1 e.2
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The line-sum map restricted to the free space of `B`. -/
noncomputable def lineSumMapOn (B : Finset (Fin n × Fin n)) :
    ↥(suppSubmodule B) →ₗ[ℚ] (Fin n ⊕ Fin n → ℚ) :=
  (lineSumMap n).comp (suppSubmodule B).subtype

/-- The evaluation functional at a cell, restricted to the free space of `B`. -/
noncomputable def evalCellOn (B : Finset (Fin n × Fin n)) (e : Fin n × Fin n) :
    ↥(suppSubmodule B) →ₗ[ℚ] ℚ :=
  (evalCell e).comp (suppSubmodule B).subtype

/-- The unit matrix at a cell. -/
def unitMat (f : Fin n × Fin n) : Fin n → Fin n → ℚ :=
  fun p q => if (p, q) = f then (1 : ℚ) else 0

theorem unitMat_mem_supp (f : Fin n × Fin n) (B : Finset (Fin n × Fin n)) (hf : f ∈ B) :
    unitMat f ∈ suppSubmodule B := by
  intro p q hpq
  show (if (p, q) = f then (1 : ℚ) else 0) = 0
  by_cases hc : (p, q) = f
  · exact absurd (by rw [hc]; exact hf) hpq
  · rw [if_neg hc]

theorem unitMat_row (i j k : Fin n) :
    ∑ l, unitMat (i, j) k l = if k = i then (1 : ℚ) else 0 := by
  by_cases h : k = i
  · rw [h]
    have hR : (if i = i then (1 : ℚ) else 0) = 1 := if_pos rfl
    rw [hR]
    refine Eq.trans (Finset.sum_eq_single j (fun b _ hb => ?_) (fun hcon => ?_)) ?_
    · show (if (i, b) = (i, j) then (1 : ℚ) else 0) = 0
      rw [if_neg (fun hc => hb (congrArg Prod.snd hc))]
    · exact absurd (Finset.mem_univ j) hcon
    · show (if (i, j) = (i, j) then (1 : ℚ) else 0) = 1
      rw [if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    show (if (k, q) = (i, j) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun hc => h (congrArg Prod.fst hc))]

theorem unitMat_col (i j k : Fin n) :
    ∑ l, unitMat (i, j) l k = if k = j then (1 : ℚ) else 0 := by
  by_cases h : k = j
  · rw [h]
    have hR : (if j = j then (1 : ℚ) else 0) = 1 := if_pos rfl
    rw [hR]
    refine Eq.trans (Finset.sum_eq_single i (fun b _ hb => ?_) (fun hcon => ?_)) ?_
    · show (if (b, j) = (i, j) then (1 : ℚ) else 0) = 0
      rw [if_neg (fun hc => hb (congrArg Prod.fst hc))]
    · exact absurd (Finset.mem_univ i) hcon
    · show (if (i, j) = (i, j) then (1 : ℚ) else 0) = 1
      rw [if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p _ => ?_
    show (if (p, k) = (i, j) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun hc => h (congrArg Prod.snd hc))]

theorem unitMat_eval (i j : Fin n) (p : Fin n × Fin n) :
    unitMat (i, j) p.1 p.2 = if p = (i, j) then (1 : ℚ) else 0 := by
  unfold unitMat
  by_cases h : p = (i, j)
  · simp [h]
  · simp [h]

/-- **The dual certificate.**  If every zero-line-sum matrix supported on `B` vanishes at `e`,
then on `B` the indicator of `e` is of the form `u i + v j` — one coefficient per row and per
column.  This is the duality step: the evaluation functional at `e` factors through the
line-sum map (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), and a functional on the
line-sum target is a combination of row and column coordinates. -/
theorem exists_dual_of_forced {B : Finset (Fin n × Fin n)} {e : Fin n × Fin n}
    (hall : ∀ M ∈ zeroLineSubmodule B, M e.1 e.2 = 0) :
    ∃ u v : Fin n → ℚ, ∀ i j : Fin n, (i, j) ∈ B →
      u i + v j = if (i, j) = e then (1 : ℚ) else 0 := by
  classical
  have hker : LinearMap.ker (lineSumMapOn B) ≤ LinearMap.ker (evalCellOn B e) := by
    intro M hM
    simp only [LinearMap.mem_ker] at hM ⊢
    have hMl : ∀ a, lsumQ (M : Fin n → Fin n → ℚ) a = 0 := fun a => congrFun hM a
    show (M : Fin n → Fin n → ℚ) e.1 e.2 = 0
    exact hall (M : Fin n → Fin n → ℚ) ⟨hMl, mem_suppSubmodule.mp M.2⟩
  have hmem : evalCellOn B e ∈ LinearMap.range (lineSumMapOn B).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact (Submodule.mem_dualAnnihilator _).2 hker
  obtain ⟨g, hg⟩ := LinearMap.mem_range.mp hmem
  have hval : ∀ M : ↥(suppSubmodule B), g (lineSumMapOn B M) = evalCellOn B e M := by
    intro M
    rw [← hg, LinearMap.dualMap_apply]
  have hgsum : ∀ a : Fin n ⊕ Fin n → ℚ, g a
      = ∑ p, a (Sum.inl p) * g (Pi.single (Sum.inl p) (1 : ℚ))
        + ∑ q, a (Sum.inr q) * g (Pi.single (Sum.inr q) (1 : ℚ)) := by
    intro a
    have hdecomp : a = ∑ x : Fin n ⊕ Fin n, a x • Pi.single x (1 : ℚ) := by
      funext y
      rw [Finset.sum_apply]
      simp [Pi.smul_apply, Pi.single_apply]
    calc g a = g (∑ x : Fin n ⊕ Fin n, a x • Pi.single x (1 : ℚ)) := by
          conv_lhs => rw [hdecomp]
      _ = ∑ x : Fin n ⊕ Fin n, a x * g (Pi.single x (1 : ℚ)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul]
      _ = (∑ p, a (Sum.inl p) * g (Pi.single (Sum.inl p) (1 : ℚ))
            + ∑ q, a (Sum.inr q) * g (Pi.single (Sum.inr q) (1 : ℚ))) :=
            Fintype.sum_sum_type
              (fun x => a x * g (Pi.single x (1 : ℚ)))
  refine ⟨fun i => g (Pi.single (Sum.inl i) (1 : ℚ)), fun j => g (Pi.single (Sum.inr j) (1 : ℚ)),
    fun i j hij => ?_⟩
  have hδmem : unitMat (i, j) ∈ suppSubmodule B := unitMat_mem_supp (i, j) B hij
  have h1 : g (lsumQ (unitMat (i, j)))
      = ∑ p, (if p = i then (1 : ℚ) else 0) * g (Pi.single (Sum.inl p) (1 : ℚ))
        + ∑ q, (if q = j then (1 : ℚ) else 0) * g (Pi.single (Sum.inr q) (1 : ℚ)) := by
    rw [hgsum (lsumQ (unitMat (i, j)))]
    simp only [lsumQ_inl, lsumQ_inr, unitMat_row, unitMat_col]
  have hL : ∑ p, (if p = i then (1 : ℚ) else 0) * g (Pi.single (Sum.inl p) (1 : ℚ))
      = g (Pi.single (Sum.inl i) (1 : ℚ)) := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  have hR : ∑ q, (if q = j then (1 : ℚ) else 0) * g (Pi.single (Sum.inr q) (1 : ℚ))
      = g (Pi.single (Sum.inr j) (1 : ℚ)) := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  have hval2 := hval ⟨unitMat (i, j), hδmem⟩
  rw [show lineSumMapOn B ⟨unitMat (i, j), hδmem⟩ = lsumQ (unitMat (i, j)) from rfl, h1, hL,
    hR, show evalCellOn B e ⟨unitMat (i, j), hδmem⟩
      = if (i, j) = e then (1 : ℚ) else 0 from by
        show unitMat (i, j) e.1 e.2 = _
        rw [unitMat_eval]
        by_cases hc : (i, j) = e
        · rw [if_pos hc, if_pos (by rw [hc])]
        · rw [if_neg hc, if_neg (fun hc' => hc hc'.symm)]] at hval2
  exact hval2

/-- **The escape lemma.**  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊆ B` (the shape of every candidate of
the support recursion), `φ(τ) ⊆ C`, and `e ∈ B \ C`, then some zero-line-sum matrix supported
on `B` is nonzero at `e`: the cell `e` is not forced to zero. -/
theorem exists_zeroLine_touching {B C : Finset (Fin n × Fin n)}
    (σ τ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B)
    (hφC : matSupport (permMatrix τ) ⊆ C)
    (hC : B \ matSupport (permMatrix σ) ⊆ C) (hCB : C ⊆ B)
    (e : Fin n × Fin n) (heB : e ∈ B) (heC : e ∉ C) :
    ∃ M : Fin n → Fin n → ℚ, M ∈ zeroLineSubmodule B ∧ M e.1 e.2 ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  obtain ⟨u, v, hcert⟩ := exists_dual_of_forced hall
  -- `e` lies on `σ`'s permutation
  have heφ : e ∈ matSupport (permMatrix σ) := by
    by_contra hne
    exact heC (hC (Finset.mem_sdiff.mpr ⟨heB, hne⟩))
  rw [matSupport_permMatrix] at heφ
  obtain ⟨i₀, -, he⟩ := Finset.mem_image.mp heφ
  -- he : (i₀, σ i₀) = e
  have hi₀ : ∀ i : Fin n, ((i, σ i) = e ↔ i = i₀) := by
    intro i
    constructor
    · intro hc
      exact (congrArg Prod.fst hc).trans (congrArg Prod.fst he).symm
    · intro hc
      rw [hc]
      exact he
  -- summing the certificate over the `τ`-cells (all in `C`, none equal to `e`) gives `Σu + Σv = 0`
  have hτ0 : ∑ i : Fin n, (u i + v (τ i)) = 0 := by
    have h2 : ∀ i : Fin n, u i + v (τ i) = (0 : ℚ) := by
      intro i
      have h := hcert i (τ i) (hCB (hφC (mem_matSupport_permMatrix_self τ i)))
      rw [if_neg (fun hc => heC (by rw [← hc]; exact hφC (mem_matSupport_permMatrix_self τ i)))]
        at h
      exact h
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    simp
  -- summing over the `σ`-cells (all in `B`, exactly one equal to `e`) gives `Σu + Σv = 1`
  have hσ1 : ∑ i : Fin n, (u i + v (σ i)) = 1 := by
    have h2 : ∀ i : Fin n, u i + v (σ i) = if i = i₀ then (1 : ℚ) else 0 := by
      intro i
      have h := hcert i (σ i) (hφB (mem_matSupport_permMatrix_self σ i))
      simp only [hi₀ i] at h
      exact h
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    simp
  -- both sums equal `Σu + Σv`
  have hreindex : ∑ i : Fin n, (u i + v (σ i)) = ∑ i : Fin n, (u i + v (τ i)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ v, ← Equiv.sum_comp τ v]
  rw [hreindex, hτ0] at hσ1
  norm_num at hσ1

/-- **Strict monotonicity on candidates.**  If `φ(σ) ⊆ B`, `B \ φ(σ) ⊆ C ⊂ B` and `C` contains
a permutation support, then `rankB C < rankB B`. -/
theorem rankB_lt_of_candidate {B C : Finset (Fin n × Fin n)}
    (σ τ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B)
    (hφC : matSupport (permMatrix τ) ⊆ C)
    (hC : B \ matSupport (permMatrix σ) ⊆ C) (hCB : C ⊂ B) :
    rankB C < rankB B := by
  classical
  obtain ⟨e, heB, heC⟩ : ∃ e, e ∈ B ∧ e ∉ C := by
    by_contra hall
    push_neg at hall
    exact hCB.2 fun x hx => hall x hx
  obtain ⟨M, hM, hMne⟩ :=
    exists_zeroLine_touching σ τ hφB hφC hC hCB.1 e heB heC
  have hprop : zeroLineSubmodule C ≠ zeroLineSubmodule B := by
    intro heq
    apply hMne
    have hMC : M ∈ zeroLineSubmodule C := by rw [heq]; exact hM
    exact hMC.2 e.1 e.2 heC
  exact finrank_lt_of_proper_le (zeroLineSubmodule_mono hCB.1) hprop

theorem rankB_empty (n : ℕ) : rankB (∅ : Finset (Fin n × Fin n)) = 0 := by
  refine Submodule.finrank_eq_zero.mpr ?_
  rw [Submodule.eq_bot_iff]
  intro M hM
  refine Submodule.mem_bot ℚ |>.mpr ?_
  ext i j
  exact hM.2 i j (by simp)

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/Sharp.lean
-- ==========================================================================

/-
# Brick 10: the sharp degree bound — rung S3b

`Recursion.lean` bounds the degree of the level counts by `#B`; aggregating gives degree `≤ n²`.
The sharp bound is `rankB B` — the dimension of the zero-line-sum space of `B` (`Rank.lean`), the
face rank `ρ(B) = |B| - v(B) + c(B)` in disguise — whose maximum over all supports is
`(n - 1)²` (`rankB_univ`).

The induction mirrors `isPolyDegLe_gB` (strong induction on `#B`, the shifted Spencer step), but
the candidates `C ∈ nbSupp B φ` need the degree bound `rankB B - 1`, and `rankB` is **not**
monotone on arbitrary candidates (degenerate candidates can have `rankB C = rankB B`).  Two
facts save it, both provable with the escape lemma `exists_zeroLine_touching`:

* if `C` contains a permutation support, then `rankB C < rankB B` (`rankB_lt_of_candidate`):
  the escape lemma produces a zero-line-sum matrix on `B` that is nonzero on `B \ C`, so
  `zeroLineSubmodule C` is a *proper* subspace of `zeroLineSubmodule B`;
* if `C` contains no permutation, the level counts of `C` vanish identically (Hall), so any
  degree bound holds.

In particular the case `rankB B = 0` (permutation supports and their forced-zero enlargements)
is automatically covered: no candidate contains a permutation (else `rankB C < 0`), so the
recurrence is homogeneous and the counts are constant.

The payoff is `exists_polynomial_semiMagicCount_sharp` — Spencer's theorem with the sharp degree
`(n - 1)²`, still for `t ≥ 1` (the value at `t = 0` is reciprocity, rung S5, not claimed).
Both theorems here are **new** declarations; the published
`isPolyDegLe_gB` / `exists_polynomial_semiMagicCount_pos` are untouched.

Scratch file, built with `lake build examples.«magic-squares».spencer.Sharp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-- A sequence that never changes is constant. -/
theorem isPolyDegLe_const_of_succ_eq {b : ℕ → ℚ} (h : ∀ r, b (r + 1) = b r) :
    IsPolyDegLe 0 b := by
  have hb : ∀ r, b r = b 0 := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [h r, ih]
  refine ⟨Polynomial.C (b 0), by simp, fun r => ?_⟩
  rw [Polynomial.eval_C, hb r]

/-- If no permutation fits inside `B`, the level counts of `B` vanish identically (Hall). -/
theorem gB_eq_zero_of_no_perm (B : Finset (Fin n × Fin n))
    (hno : ∀ σ : Equiv.Perm (Fin n), ¬ matSupport (permMatrix σ) ⊆ B) :
    gB n B = fun _ => (0 : ℚ) := by
  classical
  funext r
  have hcard : (matFiber n (r + 1) (r + 1) B).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro M hM
    rw [matFiber, Finset.mem_filter] at hM
    obtain ⟨-, hls, hsup⟩ := hM
    obtain ⟨σ, hσ⟩ :=
      exists_perm_support_subset_of_lineSums (n := n) (s := r + 1) (by omega) hls
    exact hno σ (by rw [← hsup]; exact hσ)
  show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
  rw [hcard, Nat.cast_zero]

/-- **Spencer's theorem at a fixed support, with the sharp degree.**  The number of `n × n`
squares of line sum `r + 1` whose support is exactly `B` agrees with a polynomial of degree at
most `rankB B` — the zero-line-sum dimension of `B` — at every `r`. -/
theorem isPolyDegLe_gB_sharp (n : ℕ) (B : Finset (Fin n × Fin n)) :
    IsPolyDegLe (rankB B) (gB n B) := by
  classical
  have key : ∀ k, ∀ B : Finset (Fin n × Fin n), B.card = k → IsPolyDegLe (rankB B) (gB n B) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hBk
      by_cases hpermB : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
      · obtain ⟨σ, hφB⟩ := hpermB
        have hbelow : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), C ⊂ B := by
          intro C hC
          rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
          obtain ⟨hne, hCB, -⟩ := hC
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hCB, hne⟩
        have hCsup : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
            B \ matSupport (permMatrix σ) ⊆ C := by
          intro C hC
          rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
          obtain ⟨-, -, hBC⟩ := hC
          exact hBC
        have hrec : ∀ r : ℕ, gB n B (r + 1)
            = gB n B r + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), gB n C r := by
          intro r
          have hstep := card_matFiber_recurrence_succ (n := n) (s := r + 1) (B := B) σ hφB
          change ((matFiber n (r + 1 + 1) (r + 1 + 1) B).card : ℚ)
              = ((matFiber n (r + 1) (r + 1) B).card : ℚ)
                + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
                    ((matFiber n (r + 1) (r + 1) C).card : ℚ)
          rw [hstep]
          push_cast
          rfl
        by_cases hr0 : rankB B = 0
        · -- `rankB B = 0`: no candidate contains a permutation (else `rankB C < 0`), so the
          -- recurrence is homogeneous and the counts are constant.
          have hz : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), gB n C = fun _ => (0 : ℚ) := by
            intro C hC
            by_cases hpC : ∃ τ : Equiv.Perm (Fin n), matSupport (permMatrix τ) ⊆ C
            · exfalso
              obtain ⟨τ, hφC⟩ := hpC
              have hlt : rankB C < rankB B :=
                rankB_lt_of_candidate σ τ hφB hφC (hCsup C hC) (hbelow C hC)
              rw [hr0] at hlt
              exact absurd hlt (by norm_num)
            · exact gB_eq_zero_of_no_perm C fun τ h => hpC ⟨τ, h⟩
          rw [hr0]
          refine isPolyDegLe_const_of_succ_eq fun r => ?_
          rw [hrec r, Finset.sum_congr rfl fun C hC => by rw [hz C hC]]
          simp
        · -- `rankB B ≥ 1`: candidates with a permutation get the strict bound, the rest vanish.
          have hpos : 1 ≤ rankB B := Nat.pos_of_ne_zero hr0
          have hih : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
              IsPolyDegLe (rankB B - 1) (gB n C) := by
            intro C hC
            by_cases hpC : ∃ τ : Equiv.Perm (Fin n), matSupport (permMatrix τ) ⊆ C
            · obtain ⟨τ, hφC⟩ := hpC
              have hlt : rankB C < rankB B :=
                rankB_lt_of_candidate σ τ hφB hφC (hCsup C hC) (hbelow C hC)
              have hltk : C.card < k := by
                rw [← hBk]
                exact Finset.card_lt_card (hbelow C hC)
              exact isPolyDegLe_mono (ih C.card hltk C rfl) (by omega)
            · rw [gB_eq_zero_of_no_perm C fun τ h => hpC ⟨τ, h⟩]
              exact isPolyDegLe_const 0 (rankB B - 1)
          have hgoal : IsPolyDegLe ((rankB B - 1) + 1) (gB n B) :=
            isPolyDegLe_of_recurrence_succ (b := gB n B) (c := fun C => gB n C)
              (K := rankB B - 1) (nbSupp B (matSupport (permMatrix σ))) hih hrec
          rw [Nat.sub_add_cancel hpos] at hgoal
          exact hgoal
      · -- no permutation fits inside `B`: the counts vanish identically
        rw [gB_eq_zero_of_no_perm B fun σ h => hpermB ⟨σ, h⟩]
        exact isPolyDegLe_const 0 (rankB B)
  exact key B.card B rfl

/-- **Spencer's theorem, sharp.**  For every `t ≥ 1` the number of `n × n` semi-magic squares of
line sum `t` is the value of one fixed polynomial of degree at most `(n - 1) ^ 2`.

Agreement at `t = 0` is *not* claimed — that is the Ehrhart–Macdonald reciprocity statement at
`-1` (rung S5).  This is a **new** declaration; the published
`exists_polynomial_semiMagicCount_pos` (degree `≤ n * n`) is left untouched. -/
theorem exists_polynomial_semiMagicCount_sharp (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  have hbound : ∀ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset,
      rankB B ≤ (n - 1) ^ 2 := by
    intro B hB
    calc rankB B ≤ rankB (Finset.univ : Finset (Fin n × Fin n)) :=
          rankB_mono (Finset.mem_powerset.mp hB)
      _ = (n - 1) ^ 2 := rankB_univ n
  have hsum : IsPolyDegLe ((n - 1) ^ 2)
      (fun r => ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, gB n B r) :=
    isPolyDegLe_sum _ fun B hB => isPolyDegLe_mono (isPolyDegLe_gB_sharp n B) (hbound B hB)
  obtain ⟨p, hpdeg, hpval⟩ := exists_poly_comp_X_sub_one hsum
  refine ⟨p, hpdeg, fun t ht => ?_⟩
  rw [hpval t ht, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  show ((matFiber n ((t - 1) + 1) ((t - 1) + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/Degree.lean
-- ==========================================================================

/-
# Brick 11: the exact degree — the matching lower bound

`Sharp.lean` gives the upper bound `natDegree ≤ (n-1)^2` on the polynomial that counts semi-magic
squares of line sum `t ≥ 1`.  This brick supplies the matching **lower** bound, by exhibiting an
explicit family with `(n-1)^2` free parameters.

For a square of order `n + 1` and a line sum `(n + 1) * s`, take any

  `c : Fin n → Fin n → Fin (s / n + 1)`

and build the `(n + 1) × (n + 1)` matrix

* `M p q = s + c p q` on the top-left `n × n` block,
* `M p last = s - Σ_q c p q` in the last column,
* `M last q = s - Σ_p c p q` in the last row,
* `M last last = s + Σ_{p,q} c p q` at the corner.

Each line sums to `n * s + Σ c + (s - Σ c) = (n + 1) * s`, and the bound `c p q ≤ s / n` guarantees
`Σ_q c p q ≤ n * (s / n) ≤ s`, so every entry is a natural number.  The block is recovered from `M`
by `c p q = M p q - s`, so the family is injective and has `(s / n + 1) ^ (n * n)` elements:

  `semiMagicCount (n + 1) ((n + 1) * s) ≥ (s / n + 1) ^ (n * n)`.

That is a lower bound growing like `s ^ ((n+1) - 1) ^ 2`, so the counting polynomial (which agrees
with `semiMagicCount` for `t ≥ 1`) cannot have smaller degree.  Combined with `Sharp.lean` this
gives the **exact** degree `(n - 1) ^ 2` for `t ≥ 1`
(`exists_polynomial_semiMagicCount_degree_eq`).

Agreement at `t = 0` is *not* claimed here — that is the reciprocity statement (rung S5), and it is
the reason the platform's `semi_magic_polynomial_exists` is still open.  The theorems in this file
are **new** declarations; nothing published is edited.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

/-! ## 1. The explicit family -/

/-- The block index of an index of `Fin (n+1)`: the identity on the first `n` indices, and the junk
value `0` on the last one.  The junk value is never used: `blockIdx` is only ever evaluated in
branches whose index is known to be one of the first `n`. -/
def blockIdx {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1)) : Fin n :=
  ⟨min (j : ℕ) (n - 1), by have := j.isLt; omega⟩

theorem blockIdx_castSucc {n : ℕ} (hn : 1 ≤ n) (j : Fin n) :
    blockIdx hn (Fin.castSucc j) = j := by
  refine Fin.ext ?_
  show min ((Fin.castSucc j : Fin (n + 1)) : ℕ) (n - 1) = (j : ℕ)
  rw [Fin.val_castSucc, Nat.min_eq_left (by have := j.isLt; omega)]

/-- **The linear family.**  The free block `c` on the first `n` rows/columns, and the last row and
column filled in by the line-sum conditions: every line sums to `(n + 1) * s`. -/
def lowerBlock (n s : ℕ) (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ :=
  fun i j =>
    if (i : ℕ) = n then
      (if (j : ℕ) = n then s + ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ)
       else s - ∑ p : Fin n, (c p (blockIdx hn j) : ℕ))
    else
      (if (j : ℕ) = n then s - ∑ q : Fin n, (c (blockIdx hn i) q : ℕ)
       else s + (c (blockIdx hn i) (blockIdx hn j) : ℕ))

/-- The block entries of the family. -/
theorem lowerBlock_castSucc_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p q : Fin n) :
    lowerBlock n s hn c (Fin.castSucc p) (Fin.castSucc q) = s + (c p q : ℕ) := by
  have hi : ¬(((Fin.castSucc p : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt p.isLt
  have hj : ¬(((Fin.castSucc q : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt q.isLt
  simp only [lowerBlock]
  rw [if_neg hi, if_neg hj, blockIdx_castSucc hn p, blockIdx_castSucc hn q]

/-- The last column of the family. -/
theorem lowerBlock_castSucc_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    lowerBlock n s hn c (Fin.castSucc p) (Fin.last n) = s - ∑ q : Fin n, (c p q : ℕ) := by
  have hi : ¬(((Fin.castSucc p : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt p.isLt
  simp only [lowerBlock]
  rw [if_neg hi, if_pos (Fin.val_last n), blockIdx_castSucc hn p]

/-- The last row of the family. -/
theorem lowerBlock_last_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    lowerBlock n s hn c (Fin.last n) (Fin.castSucc q) = s - ∑ p : Fin n, (c p q : ℕ) := by
  have hj : ¬(((Fin.castSucc q : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt q.isLt
  simp only [lowerBlock]
  rw [if_pos (Fin.val_last n), if_neg hj, blockIdx_castSucc hn q]

/-- The corner of the family. -/
theorem lowerBlock_last_last {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    lowerBlock n s hn c (Fin.last n) (Fin.last n)
      = s + ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) := by
  simp only [lowerBlock]
  rw [if_pos (Fin.val_last n), if_pos (Fin.val_last n)]

/-! ## 2. Natural subtraction, and the size of a block line -/

/-- Natural subtraction does not distribute over a sum, so this needs the pointwise bound. -/
theorem sum_sub_const {α : Type*} (u : Finset α) (X : α → ℕ) (a : ℕ) (h : ∀ i ∈ u, X i ≤ a) :
    ∑ i ∈ u, (a - X i) = u.card * a - ∑ i ∈ u, X i := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert x u hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
      have hx' : X x ≤ a := h x (Finset.mem_insert_self x u)
      have hb : ∑ i ∈ u, X i ≤ u.card * a :=
        calc ∑ i ∈ u, X i ≤ ∑ _i ∈ u, a :=
              Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi)
          _ = u.card * a := by simp
      rw [ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
      have h1 : (a - X x) + (u.card * a - ∑ i ∈ u, X i)
          = (u.card * a + a) - (X x + ∑ i ∈ u, X i) := by omega
      have h2 : u.card * a + a = (u.card + 1) * a := by ring
      rw [h1, h2]

/-- The `univ` form of `sum_sub_const`. -/
theorem sum_univ_sub_const {n : ℕ} (X : Fin n → ℕ) (a : ℕ) (h : ∀ i, X i ≤ a) :
    ∑ i : Fin n, (a - X i) = n * a - ∑ i : Fin n, X i := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    sum_sub_const (Finset.univ : Finset (Fin n)) X a fun i _ => h i

/-- A row of the block sums to at most `n * (s / n) ≤ s`. -/
theorem sum_lowerC_le {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    ∑ q : Fin n, (c p q : ℕ) ≤ s := by
  calc ∑ q : Fin n, (c p q : ℕ) ≤ ∑ _q : Fin n, s / n :=
        Finset.sum_le_sum fun q _ => by have := (c p q).isLt; omega
    _ = n * (s / n) := by simp
    _ ≤ s := Nat.mul_div_le s n

/-- A column of the block sums to at most `n * (s / n) ≤ s`. -/
theorem sum_lowerC_le_col {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    ∑ p : Fin n, (c p q : ℕ) ≤ s := by
  calc ∑ p : Fin n, (c p q : ℕ) ≤ ∑ _p : Fin n, s / n :=
        Finset.sum_le_sum fun p _ => by have := (c p q).isLt; omega
    _ = n * (s / n) := by simp
    _ ≤ s := Nat.mul_div_le s n

/-! ## 3. All four kinds of line sum to `(n + 1) * s` -/

/-- The "block line" pattern: `(Σ (s + Y i)) + (s - Σ Y i) = (n + 1) * s`. -/
theorem sum_add_sub_sum {n s : ℕ} (Y : Fin n → ℕ) (h : ∑ i : Fin n, Y i ≤ s) :
    (∑ i : Fin n, (s + Y i)) + (s - ∑ i : Fin n, Y i) = (n + 1) * s := by
  rw [Finset.sum_add_distrib, Finset.sum_const_nat fun i _ => rfl, Finset.card_univ,
    Fintype.card_fin, Nat.add_assoc, Nat.add_sub_of_le h]
  ring

/-- The "last line" pattern: `(Σ (s - Y i)) + (s + Σ Y i) = (n + 1) * s`. -/
theorem sum_sub_add_sum {n s : ℕ} (Y : Fin n → ℕ) (h : ∀ i, Y i ≤ s)
    (hT : ∑ i : Fin n, Y i ≤ n * s) :
    (∑ i : Fin n, (s - Y i)) + (s + ∑ i : Fin n, Y i) = (n + 1) * s := by
  rw [sum_univ_sub_const Y s h, Nat.add_comm s (∑ i : Fin n, Y i), ← Nat.add_assoc,
    Nat.sub_add_cancel hT]
  ring

theorem lowerBlock_rowSum_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    ∑ j : Fin (n + 1), lowerBlock n s hn c (Fin.castSucc p) j = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun q _ => lowerBlock_castSucc_castSucc hn c p q,
    lowerBlock_castSucc_last hn c p]
  exact sum_add_sub_sum (fun q : Fin n => (c p q : ℕ)) (sum_lowerC_le c p)

theorem lowerBlock_colSum_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    ∑ i : Fin (n + 1), lowerBlock n s hn c i (Fin.castSucc q) = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun p _ => lowerBlock_castSucc_castSucc hn c p q,
    lowerBlock_last_castSucc hn c q]
  exact sum_add_sub_sum (fun p : Fin n => (c p q : ℕ)) (sum_lowerC_le_col c q)

/-- The total of the block. -/
theorem sum_lowerC_total_le {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) ≤ n * s :=
  calc ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) ≤ ∑ _p : Fin n, s :=
        Finset.sum_le_sum fun p _ => sum_lowerC_le c p
    _ = n * s := by simp

theorem lowerBlock_rowSum_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ j : Fin (n + 1), lowerBlock n s hn c (Fin.last n) j = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun q _ => lowerBlock_last_castSucc hn c q, lowerBlock_last_last hn c]
  rw [← Finset.sum_comm]
  refine sum_sub_add_sum (fun q : Fin n => ∑ p : Fin n, (c p q : ℕ))
    (fun q => sum_lowerC_le_col c q) ?_
  rw [Finset.sum_comm]
  exact sum_lowerC_total_le c

theorem lowerBlock_colSum_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ i : Fin (n + 1), lowerBlock n s hn c i (Fin.last n) = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun p _ => lowerBlock_castSucc_last hn c p, lowerBlock_last_last hn c]
  exact sum_sub_add_sum (fun p : Fin n => ∑ q : Fin n, (c p q : ℕ))
    (fun p => sum_lowerC_le c p) (sum_lowerC_total_le c)

/-- **Every line of the family sums to the same value.** -/
theorem lowerBlock_lineSums {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    LineSums (lowerBlock n s hn c) ((n + 1) * s) :=
  ⟨fun i => Fin.lastCases (motive := fun i =>
        ∑ j : Fin (n + 1), lowerBlock n s hn c i j = (n + 1) * s)
      (lowerBlock_rowSum_last hn c) (fun p => lowerBlock_rowSum_castSucc hn c p) i,
   fun j => Fin.lastCases (motive := fun j =>
        ∑ i : Fin (n + 1), lowerBlock n s hn c i j = (n + 1) * s)
      (lowerBlock_colSum_last hn c) (fun q => lowerBlock_colSum_castSucc hn c q) j⟩

/-- The family lies in the box of line sum `(n + 1) * s`. -/
theorem lowerBlock_mem {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    lowerBlock n s hn c ∈ matBoxLine (n + 1) ((n + 1) * s) := by
  classical
  have hls := lowerBlock_lineSums hn c
  rw [matBoxLine, Finset.mem_filter, mem_matBox]
  exact ⟨fun i j => le_of_rowSum hls.1 i j, hls⟩

/-- **The family is injective**: the block is recovered from the matrix by `c p q = M p q - s`. -/
theorem lowerBlock_injective {n s : ℕ} (hn : 1 ≤ n) :
    Function.Injective (lowerBlock (n := n) (s := s) hn) := by
  intro c c' h
  funext p q
  have hpq := congrFun (congrFun h (Fin.castSucc p)) (Fin.castSucc q)
  rw [lowerBlock_castSucc_castSucc hn c p q, lowerBlock_castSucc_castSucc hn c' p q] at hpq
  exact Fin.ext (Nat.add_left_cancel hpq)

/-! ## 4. The counting lower bound -/

/-- **The explicit lower bound for the semi-magic count.**  For squares of order `n + 1` and line
sum `(n + 1) * s` there are at least `(s / n + 1) ^ (n * n)` of them. -/
theorem semiMagicCount_ge_family (n s : ℕ) (hn : 1 ≤ n) :
    (s / n + 1) ^ (n * n) ≤ semiMagicCount (n + 1) ((n + 1) * s) := by
  classical
  have hcard : (Finset.univ.image (lowerBlock (n := n) (s := s) hn)).card
      = (s / n + 1) ^ (n * n) := by
    rw [Finset.card_image_of_injective _ (lowerBlock_injective hn), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rw [← hcard, ← card_matBoxLine (n + 1) ((n + 1) * s)]
  refine Finset.card_le_card fun M hM => ?_
  rw [Finset.mem_image] at hM
  obtain ⟨c, -, rfl⟩ := hM
  exact lowerBlock_mem hn c

/-! ## 5. A polynomial growing faster than `x ^ d` has degree at least `d` -/

/-- A polynomial evaluated at `x ≥ 1` is bounded by a constant times `x ^ natDegree`. -/
theorem eval_le_mul_pow {p : Polynomial ℚ} {x : ℚ} (hx : 1 ≤ x) :
    p.eval x ≤ (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) * x ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ p.natDegree := by
    have := Finset.mem_range.mp hk
    omega
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx
  calc p.coeff k * x ^ k ≤ |p.coeff k| * x ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hx0 k)
    _ ≤ |p.coeff k| * x ^ p.natDegree :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hk') (abs_nonneg _)

/-- **Growth forces the degree.**  If a rational polynomial dominates `x ^ d` at the integer
argument `A * s` for every `s ≥ 1`, where `1 ≤ A`, then its degree is at least `d`.

The proof is the elementary one: `p.eval x ≤ B * x ^ e` for `x ≥ 1` (`B` = sum of the absolute
values of the coefficients, `e = p.natDegree`), while at a large `s` the hypothesis together with
`s ^ d = s ^ (d - e) * s ^ e` and `s ^ (d - e) ≥ s` forces `s ≤ B * A ^ e < s` when `e < d`. -/
theorem le_natDegree_of_lowerBound {p : Polynomial ℚ} {d : ℕ} {A : ℚ} (hA : 1 ≤ A)
    (h : ∀ s : ℕ, 1 ≤ s → (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ))) : d ≤ p.natDegree := by
  by_contra hcon
  push Not at hcon
  set e : ℕ := p.natDegree with he
  set B : ℚ := ∑ k ∈ Finset.range (e + 1), |p.coeff k| with hB
  obtain ⟨s, hs1, hlarge⟩ : ∃ s : ℕ, 1 ≤ s ∧ B * A ^ e < (s : ℚ) := by
    obtain ⟨t, ht⟩ := exists_nat_gt (B * A ^ e)
    refine ⟨max t 1, le_max_right _ _, ?_⟩
    exact lt_of_lt_of_le ht (by exact_mod_cast le_max_left t 1)
  have hs1' : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs1
  have hse : (0 : ℚ) < (s : ℚ) ^ e := pow_pos (by linarith) e
  have hub : p.eval (A * (s : ℚ)) ≤ B * A ^ e * (s : ℚ) ^ e := by
    calc p.eval (A * (s : ℚ))
        ≤ B * (A * (s : ℚ)) ^ e := by
          rw [he, hB]
          exact eval_le_mul_pow (by nlinarith [hA, hs1'])
      _ = B * A ^ e * (s : ℚ) ^ e := by rw [mul_pow]; ring
  have hlow : (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ)) := h s hs1
  have hpow : (s : ℚ) ^ d = (s : ℚ) ^ (d - e) * (s : ℚ) ^ e := by
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt hcon)]
  have hge : (s : ℚ) ≤ (s : ℚ) ^ (d - e) := by
    calc (s : ℚ) = (s : ℚ) ^ 1 := (pow_one _).symm
      _ ≤ (s : ℚ) ^ (d - e) := pow_le_pow_right₀ hs1' (by omega)
  have hsme : (s : ℚ) * (s : ℚ) ^ e ≤ B * A ^ e * (s : ℚ) ^ e := by
    calc (s : ℚ) * (s : ℚ) ^ e ≤ (s : ℚ) ^ (d - e) * (s : ℚ) ^ e :=
          mul_le_mul_of_nonneg_right hge (le_of_lt hse)
      _ = (s : ℚ) ^ d := hpow.symm
      _ ≤ p.eval (A * (s : ℚ)) := hlow
      _ ≤ B * A ^ e * (s : ℚ) ^ e := hub
  have hcancel : (s : ℚ) ≤ B * A ^ e := le_of_mul_le_mul_right hsme hse
  linarith

/-! ## 6. The exact degree for `t ≥ 1` -/

/-- **Spencer's theorem with the exact degree.**  For `n ≥ 1` there is one polynomial of degree
exactly `(n - 1) ^ 2` that counts the `n × n` semi-magic squares of line sum `t` for every `t ≥ 1`.

Upper bound: `Sharp.lean`.  Lower bound: the explicit family of `§1`–`§4`, via the growth lemma
above.  This is a **new** declaration; `exists_polynomial_semiMagicCount_pos` and
`exists_polynomial_semiMagicCount_sharp` are untouched.  Agreement at `t = 0` is *not* claimed —
that is the reciprocity statement (rung S5). -/
theorem exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨p, hpdeg, hpval⟩ := exists_polynomial_semiMagicCount_sharp n
  by_cases hn2 : 1 < n
  · have hnn : 1 ≤ n - 1 := by omega
    have hbound : ∀ u : ℕ, 1 ≤ u →
        (u : ℚ) ^ ((n - 1) * (n - 1)) ≤ p.eval (((n - 1) * n : ℕ) * (u : ℚ)) := by
      intro u hu
      have hfam := semiMagicCount_ge_family (n - 1) ((n - 1) * u) hnn
      rw [Nat.mul_div_cancel_left u (by omega), Nat.sub_add_cancel hn] at hfam
      have hval := hpval (n * ((n - 1) * u))
        (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      have hkey : ((u : ℚ) + 1) ^ ((n - 1) * (n - 1))
          ≤ p.eval ((n * ((n - 1) * u) : ℕ) : ℚ) := by
        have hcast : ((u : ℚ) + 1) ^ ((n - 1) * (n - 1))
            = (((u + 1) ^ ((n - 1) * (n - 1)) : ℕ) : ℚ) := by
          push_cast
          ring
        rw [hval, hcast]
        exact Nat.cast_le.mpr hfam
      calc (u : ℚ) ^ ((n - 1) * (n - 1))
          ≤ ((u : ℚ) + 1) ^ ((n - 1) * (n - 1)) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            have : (1 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
            linarith
        _ ≤ p.eval ((n * ((n - 1) * u) : ℕ) : ℚ) := hkey
        _ = p.eval (((n - 1) * n : ℕ) * (u : ℚ)) := by
            congr 1
            push_cast
            ring
    have hge : (n - 1) * (n - 1) ≤ p.natDegree :=
      le_natDegree_of_lowerBound (A := (((n - 1) * n : ℕ) : ℚ)) (by
        have h2 : (1 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
          exact_mod_cast (show 1 ≤ n - 1 by omega)
        have h3 : (1 : ℚ) ≤ ((n : ℕ) : ℚ) := by
          exact_mod_cast (show 1 ≤ n by omega)
        push_cast
        nlinarith) hbound
    refine ⟨p, le_antisymm hpdeg ?_, hpval⟩
    rw [pow_two]
    exact hge
  · -- `n ≤ 1`: then `(n - 1) ^ 2 = 0`, so there is no lower bound to prove
    have hn1 : n ≤ 1 := by omega
    have h0 : (n - 1) ^ 2 = 0 := by
      have : n - 1 = 0 := by omega
      rw [this]; norm_num
    refine ⟨p, ?_, hpval⟩
    rw [h0] at hpdeg ⊢
    exact le_antisymm hpdeg (Nat.zero_le _)

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/S5.lean
-- ==========================================================================

/-
# Brick 12 (rung S5): the value at line sum `0`, reduced to a finite identity

`Recursion.lean` produces a polynomial for every support, but only for line sums `t ≥ 1`; the
missing point is `t = 0`.  This brick makes the obstruction exact and *polynomial-free*.

Write

* `qB n B` for the polynomial with `qB n B r = #(squares of line sum r + 1 with support exactly B)`
  (degree at most `#B`, from `isPolyDegLe_gB`),
* `sB n B := qB n B (-1)` for its value one step below line sum `0`.

Two facts are proved here, entirely inside `ℚ[X]` and `ℕ`:

* the **difference equation**  `qB (X + 1) - qB = Σ_{C ∈ nbOf n B} qB C`,  where `nbOf n B` is the
  neighbour set of the split (`empty` when no permutation fits inside `B`, so that the identity
  holds at *every* `B`, support or not);
* evaluating it at `X = -1` gives the **recursion**  `sB n B = #(level-1 fibre at B) - Σ_C sB n C`,
  in which no polynomial occurs any more.

Consequently rung S5 (`p(0) = 1`, i.e. the count is polynomial at `t = 0` too) is equivalent to the
single numerical statement

  `Σ_{B a support} sB n B = 1`,

and *that* follows from the two inputs isolated at the end of the file:

* **(A)** `sB n B = (-1) ^ rankB B` for every support — Ehrhart–Macdonald reciprocity at `-1`;
* **(B)** `Σ_{B a support} (-1) ^ rankB B = 1` — Euler's formula for the face lattice of the
  Birkhoff polytope, which contains no Ehrhart theory at all.

Both are numerical facts about finitely many supports of a fixed `n`; neither is proved here.  What
*is* proved here is that they are exactly what is missing: `exists_polynomial_semiMagicCount_…`
below turns either statement into the mission's goal.  See `missions/magic-squares-v/S5-NOTES.md`
for the analysis and the (exact-arithmetic) verification for `n ≤ 4`.

Built with `lake build SpencerRoute`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

/-! ## Step 0: polynomials that vanish on `ℕ` (or on the positive integers) -/

/-- A polynomial over `ℚ` which vanishes at every natural number vanishes identically.  This is the
only place where the route needs a fact about `ℚ[X]` rather than about sequences, and it is what
converts a recurrence in `t : ℕ` into an identity of polynomials. -/
theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial ℚ} (h : ∀ r : ℕ, p.eval (r : ℚ) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : ℕ => (r : ℚ))
    Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

/-- The same, for a polynomial vanishing only on the *positive* integers: it vanishes identically.
Multiplying by `X` (which is not a zero divisor) shifts the positive integers down to `ℕ`. -/
theorem poly_eq_zero_of_pos_eval_eq_zero {p : Polynomial ℚ}
    (h : ∀ r : ℕ, 1 ≤ r → p.eval (r : ℚ) = 0) : p = 0 := by
  have hX : X * p = 0 := by
    refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_X]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [Nat.cast_zero, zero_mul]
    · rw [h r hr, mul_zero]
  rcases mul_eq_zero.mp hX with h' | h'
  · exact absurd h' Polynomial.X_ne_zero
  · exact h'

/-! ## Step 1: the empty support, and the count at line sum `0` -/

/-- For `n ≥ 1` there is no matrix of positive line sum with empty support: every entry vanishes, so
every row sums to `0`.  This is the *reason* the support recursion stops at line sum `1`, and the
reason the empty support is excluded from `IsSupport` below. -/
theorem card_matFiber_empty {n m s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (matFiber n m s (∅ : Finset (Fin n × Fin n))).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [matFiber, Finset.mem_filter] at hM
  obtain ⟨-, hls, hsup⟩ := hM
  have hzero : ∀ j : Fin n, M ⟨0, hn⟩ j = 0 := by
    intro j
    by_contra hne
    have hmem : (⟨0, hn⟩, j) ∈ matSupport M := by
      simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.pos_of_ne_zero hne
    rw [hsup] at hmem
    simp at hmem
  have hrow := hls.1 ⟨0, hn⟩
  rw [Finset.sum_eq_zero fun j _ => hzero j] at hrow
  omega

/-- Line sum `0` has exactly one semi-magic square: the zero matrix. -/
theorem semiMagicCount_zero (n : ℕ) : semiMagicCount n 0 = 1 := by
  classical
  rw [← card_matBoxLine n 0]
  have hset : matBoxLine n 0 = {(0 : Matrix (Fin n) (Fin n) ℕ)} := by
    ext M
    rw [matBoxLine, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hbox, -⟩
      rw [mem_matBox] at hbox
      funext i j
      exact Nat.eq_zero_of_le_zero (hbox i j)
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [mem_matBox]
        intro i j
        simp
      · exact ⟨fun i => by simp, fun j => by simp⟩
  rw [hset, Finset.card_singleton]

/-! ## Step 2: supports -/

/-- `B` is a **support** when it is the exact support of some semi-magic square of *positive* line
sum.  The empty set is deliberately not a support here: its only square is the zero matrix, of line
sum `0`. -/
def IsSupport (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ (matFiber n s s B).Nonempty

/-- The supports of `n × n` semi-magic squares, as a finset. -/
noncomputable def supportSet (n : ℕ) : Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).powerset.filter (IsSupport n)

/-! ## Step 3: one polynomial per support, and one neighbour set per support -/

/-- The polynomial of `isPolyDegLe_gB`, chosen once and for all: its value at `r : ℕ` is the number
of squares of line sum `r + 1` with support exactly `B`. -/
noncomputable def qB (n : ℕ) (B : Finset (Fin n × Fin n)) : Polynomial ℚ :=
  Classical.choose (isPolyDegLe_gB n B)

theorem qB_natDegree (n : ℕ) (B : Finset (Fin n × Fin n)) : (qB n B).natDegree ≤ B.card :=
  (Classical.choose_spec (isPolyDegLe_gB n B)).1

theorem qB_eval (n : ℕ) (B : Finset (Fin n × Fin n)) (r : ℕ) :
    (qB n B).eval (r : ℚ) = gB n B r :=
  (Classical.choose_spec (isPolyDegLe_gB n B)).2 r

/-- **The value attached to a support**: `qB` read one step below line sum `0`.  Rung S5 is the
statement that these numbers sum to `1`. -/
noncomputable def sB (n : ℕ) (B : Finset (Fin n × Fin n)) : ℚ := (qB n B).eval (-1)

theorem sB_eq (n : ℕ) (B : Finset (Fin n × Fin n)) : sB n B = (qB n B).eval (-1) := rfl

/-- The neighbour set of `B`, with the choice of the permutation built in.  If some permutation fits
inside `B`, the split of `SupportSplit.lean` applies and the neighbours are `nbSupp B φ`; otherwise
the fibre is empty at every positive level, so the empty set is the honest coefficient set.  This is
what makes the recurrence below hold at *every* `B`. -/
noncomputable def nbOf (n : ℕ) (B : Finset (Fin n × Fin n)) : Finset (Finset (Fin n × Fin n)) :=
  if h : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B then
    nbSupp B (matSupport (permMatrix (Classical.choose h)))
  else ∅

/-- **The shifted Spencer recursion, at every support set.**  One level step of the line sum adds
the neighbours and keeps the support. -/
theorem gB_succ (n : ℕ) (B : Finset (Fin n × Fin n)) (r : ℕ) :
    gB n B (r + 1) = gB n B r + ∑ C ∈ nbOf n B, gB n C r := by
  classical
  by_cases h : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
  · rw [nbOf, dif_pos h]
    have hstep := card_matFiber_recurrence_succ (n := n) (s := r + 1) (B := B)
      (Classical.choose h) (Classical.choose_spec h)
    change ((matFiber n (r + 1 + 1) (r + 1 + 1) B).card : ℚ)
        = ((matFiber n (r + 1) (r + 1) B).card : ℚ)
          + ∑ C ∈ nbSupp B (matSupport (permMatrix (Classical.choose h))),
              ((matFiber n (r + 1) (r + 1) C).card : ℚ)
    rw [hstep]
    push_cast
    rfl
  · rw [nbOf, dif_neg h, gB_eq_zero_of_no_perm B fun σ hσ => h ⟨σ, hσ⟩]
    simp

/-- **The difference equation.**  The recurrence of `gB_succ`, lifted to the polynomials.  This is
the identity whose value at `X = -1` is the recursion for the numbers `sB`. -/
theorem qB_rec (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (qB n B).comp (X + 1) - qB n B = ∑ C ∈ nbOf n B, qB n C := by
  classical
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
  have hcast : (r : ℚ) + 1 = ((r + 1 : ℕ) : ℚ) := by push_cast; ring
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_finsetSum, hcast]
  rw [qB_eval n B (r + 1), qB_eval n B r, gB_succ n B r]
  simp_rw [qB_eval]
  ring

/-- **The recursion the numbers `sB` satisfy** — `qB_rec` evaluated at `X = -1`, with no polynomial
left.  The constant is the level-`1` fibre at `B`: it is `1` exactly for the permutation supports,
because a semi-magic square of line sum `1` *is* a permutation matrix. -/
theorem sB_rec (n : ℕ) (B : Finset (Fin n × Fin n)) :
    sB n B = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, sB n C := by
  classical
  have h := congrArg (fun p : Polynomial ℚ => p.eval (-1)) (qB_rec n B)
  have hX : (X + 1 : Polynomial ℚ).eval (-1) = 0 := by simp
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_finsetSum, hX] at h
  -- h : (qB n B).eval 0 - (qB n B).eval (-1) = ∑ C, (qB n C).eval (-1)
  have h0 : (qB n B).eval 0 = ((matFiber n 1 1 B).card : ℚ) := by
    have hc : (0 : ℚ) = ((0 : ℕ) : ℚ) := by norm_num
    rw [hc, qB_eval n B 0]
    show ((matFiber n (0 + 1) (0 + 1) B).card : ℚ) = ((matFiber n 1 1 B).card : ℚ)
    norm_num
  have h' : (qB n B).eval (-1) = ((matFiber n 1 1 B).card : ℚ)
      - ∑ C ∈ nbOf n B, (qB n C).eval (-1) := by
    linarith [h, h0]
  calc sB n B = (qB n B).eval (-1) := sB_eq n B
    _ = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, (qB n C).eval (-1) := h'
    _ = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, sB n C := by
          rw [Finset.sum_congr rfl fun C _ => (sB_eq n C).symm]

/-- Non-supports contribute nothing: if `B` is not the support of any square of positive line sum,
the sequence `gB n B` is zero, so `qB n B = 0` and hence `sB n B = 0`. -/
theorem sB_eq_zero_of_not_isSupport {n : ℕ} {B : Finset (Fin n × Fin n)}
    (h : ¬ IsSupport n B) : sB n B = 0 := by
  classical
  have hzero : qB n B = 0 := by
    refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
    have hc : (matFiber n (r + 1) (r + 1) B).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro M hM
      exact h ⟨r + 1, by omega, M, hM⟩
    rw [qB_eval n B r]
    show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
    rw [hc, Nat.cast_zero]
  rw [sB_eq, hzero, Polynomial.eval_zero]

/-! ## Step 4: the single polynomial, read at `t = 0` and at `t ≥ 1` -/

/-- The aggregate: the sum of the support polynomials, shifted down to line sum `t`.  It agrees
with the count `semiMagicCount n t` for every `t ≥ 1`. -/
noncomputable def qAll (n : ℕ) : Polynomial ℚ :=
  (∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)

theorem qAll_eval_pos {n t : ℕ} (ht : 1 ≤ t) :
    (qAll n).eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  show ((∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)).eval (t : ℚ)
    = (semiMagicCount n t : ℚ)
  have hcast : (t : ℚ) - 1 = ((t - 1 : ℕ) : ℚ) := by rw [Nat.cast_sub ht, Nat.cast_one]
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_finsetSum, hcast, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [qB_eval]
  show ((matFiber n (t - 1 + 1) (t - 1 + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

/-- **The whole of rung S5 in one evaluation**: the aggregate at line sum `0` is the sum of the
numbers `sB` over the supports.  No information about `t = 0` is available from the recursion, so
this value is unconstrained by `Degree.lean` — it is exactly what S5 asks for. -/
theorem qAll_eval_zero (n : ℕ) :
    (qAll n).eval ((0 : ℕ) : ℚ) = ∑ B ∈ supportSet n, sB n B := by
  classical
  have hsub : supportSet n ⊆ (Finset.univ : Finset (Fin n × Fin n)).powerset := by
    intro B hB
    rw [supportSet, Finset.mem_filter] at hB
    exact hB.1
  show ((∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)).eval
      ((0 : ℕ) : ℚ) = ∑ B ∈ supportSet n, sB n B
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_finsetSum]
  norm_num
  rw [Finset.sum_congr rfl fun B _ => (sB_eq n B).symm]
  exact (Finset.sum_subset hsub fun B hB hBnot =>
    sB_eq_zero_of_not_isSupport fun hs => hBnot (by
      rw [supportSet, Finset.mem_filter]
      exact ⟨hB, hs⟩)).symm

/-! ## Step 5: the two inputs, and what they give -/

/-- **(A)** — Ehrhart–Macdonald reciprocity at `-1`, one support at a time: the value of the
support polynomial at `-1` has the sign `(-1) ^ rankB B`.  Equivalently, the face `F_B` of the
Birkhoff polytope has no interior lattice point at scale `1`.  Mathlib has no Ehrhart theory; this
is the first of the two inputs. -/
def ReciprocityAtNegOne (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), IsSupport n B → sB n B = (-1 : ℚ) ^ rankB B

/-- **(B)** — Euler's formula for the face lattice of the Birkhoff polytope: over the supports the
signs `(-1) ^ dim F` cancel to `1`.  Supports of `B_n` are the non-empty faces of `B_n` and `rankB`
is the face dimension, so this is the polytope-general `Σ_{F} (-1) ^ dim F = 1` and nothing about
Ehrhart.  This is the second input. -/
def FaceLatticeEuler (n : ℕ) : Prop :=
  ∑ B ∈ supportSet n, (-1 : ℚ) ^ rankB B = 1

/-- **(A) and (B) together give rung S5.** -/
theorem sum_sB_eq_one_of (n : ℕ) (hA : ReciprocityAtNegOne n) (hB : FaceLatticeEuler n) :
    ∑ B ∈ supportSet n, sB n B = 1 := by
  classical
  rw [← hB]
  refine Finset.sum_congr rfl fun B hB' => ?_
  exact hA B (by
    rw [supportSet, Finset.mem_filter] at hB'
    exact hB'.2)

/-- **S5, in the form the mission needs it.**  If the numbers `sB` sum to `1` over the supports then
the count `semiMagicCount n` agrees with a polynomial on *all* of `ℕ`, including `t = 0`.

The hypothesis is exactly `Σ_B sB n B = 1`, which `ReciprocityAtNegOne` + `FaceLatticeEuler`
supply — so this is the machine-checked statement that (A) and (B) are the only missing inputs. -/
theorem exists_polynomial_semiMagicCount_of_sum_sB (n : ℕ)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  refine ⟨qAll n, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    rw [qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact qAll_eval_pos ht1

/-- The same, with the degree bound of `Sharp.lean` kept: if the numbers `sB` sum to `1` then the
polynomial of `exists_polynomial_semiMagicCount_sharp` — which is forced, being the unique degree
`≤ (n-1)^2` polynomial agreeing with the count in infinitely many points — also has the right value
at `t = 0`.  This is the mission's goal, minus the *exactness* of the degree, which is
`exists_polynomial_semiMagicCount_degree_eq` in `Degree.lean`. -/
theorem exists_polynomial_semiMagicCount_degLe_of_sum_sB (n : ℕ)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  obtain ⟨P, hPdeg, hPval⟩ := exists_polynomial_semiMagicCount_sharp n
  have hagree : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (qAll n).eval (t : ℚ) :=
    fun t ht => by rw [hPval t ht, qAll_eval_pos ht]
  have hPeq : P = qAll n := by
    have hsub : P - qAll n = 0 :=
      poly_eq_zero_of_pos_eval_eq_zero fun r hr => by
        rw [Polynomial.eval_sub, hagree r hr, sub_self]
    exact sub_eq_zero.mp hsub
  refine ⟨P, hPdeg, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    rw [hPeq, qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact hPval t ht1

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/S5Bridge.lean
-- ==========================================================================

/-!
# Bridge from rung S5 to the exact-degree mission statement

`S5.lean` identifies agreement at `t = 0` with the numerical identity
`sum B in supportSet n, sB n B = 1`.  `Degree.lean` independently supplies the unique counting
polynomial on the positive integers with exact degree `(n - 1) ^ 2`.  This file joins the two
statements by polynomial uniqueness.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

/-- The numerical S5 identity is equivalent to polynomiality of `semiMagicCount n` on all
natural line sums.  No degree hypothesis is needed in either direction. -/
theorem sum_sB_eq_one_iff_exists_polynomial_semiMagicCount (n : ℕ) :
    (∑ B ∈ supportSet n, sB n B = 1) ↔
      ∃ p : Polynomial ℚ, ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  constructor
  · exact exists_polynomial_semiMagicCount_of_sum_sB n
  · rintro ⟨p, hp⟩
    have hpq : p = qAll n := by
      have hzero : p - qAll n = 0 :=
        poly_eq_zero_of_pos_eval_eq_zero fun t ht => by
          rw [Polynomial.eval_sub, hp t, qAll_eval_pos ht, sub_self]
      exact sub_eq_zero.mp hzero
    calc
      ∑ B ∈ supportSet n, sB n B = (qAll n).eval ((0 : ℕ) : ℚ) :=
        (qAll_eval_zero n).symm
      _ = p.eval ((0 : ℕ) : ℚ) := by rw [hpq]
      _ = (semiMagicCount n 0 : ℚ) := hp 0
      _ = 1 := by rw [semiMagicCount_zero, Nat.cast_one]

/-- The exact-degree, all-natural-number form of Spencer's theorem, conditional only on the
numerical S5 identity.  This has the shape of the Magic Squares V mission goal. -/
theorem exists_polynomial_semiMagicCount_degree_eq_of_sum_sB (n : ℕ) (hn : 1 ≤ n)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨p, hpdeg, hpval⟩ := exists_polynomial_semiMagicCount_degree_eq n hn
  have hpq : p = qAll n := by
    have hzero : p - qAll n = 0 :=
      poly_eq_zero_of_pos_eval_eq_zero fun t ht => by
        rw [Polynomial.eval_sub, hpval t ht, qAll_eval_pos ht, sub_self]
    exact sub_eq_zero.mp hzero
  refine ⟨p, hpdeg, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [hpq, qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact hpval t ht

end MagicSquaresSpencer

-- ==========================================================================
-- from spencer/ClosedSupportIE.lean
-- ==========================================================================

set_option autoImplicit false
open Finset

theorem card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (A : Finset α) (supp : α → Finset ι) (B φ : Finset ι) :
    ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
      ∑ S ∈ φ.powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (S.card + 1) *
          ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
  classical
  let U : Finset α := A.filter (fun x => supp x ⊆ B)
  let F : ι → Finset α := fun i => U.filter (fun x => i ∉ supp x)
  have hIE := Finset.inclusion_exclusion_card_biUnion φ F
  have hcard : φ.biUnion F = A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x) := by
    ext x
    simp only [mem_biUnion, mem_filter, F, U]
    constructor
    · rintro ⟨i, hi, ⟨hA, hB⟩, hni⟩
      exact ⟨hA, hB, fun h => hni (h hi)⟩
    · rintro ⟨hA, hB, hnot⟩
      obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hnot
      exact ⟨i, hi, ⟨hA, hB⟩, hni⟩
  rw [hcard] at hIE
  have hIEq :
      ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
        ∑ S : φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.1.card + 1) *
            ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) := by
    exact_mod_cast hIE
  calc
    ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
        ∑ S : φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.1.card + 1) *
            ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) := hIEq
    _ = ∑ S ∈ φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) *
            ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
      conv_rhs => rw [← Finset.sum_attach]
      push_cast
      apply Finset.sum_congr rfl
      intro S hS
      rw [show ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) =
          ((A.filter (fun x => supp x ⊆ B \ S.1)).card : ℚ) by
        norm_cast
        apply congrArg Finset.card
        ext x
        simp only [mem_inf', mem_filter, F, U]
        constructor
        · intro hxi
          obtain ⟨i, hi⟩ := (Finset.mem_filter.mp S.2).2
          have hbase := (hxi i hi).1
          refine ⟨hbase.1, ?_⟩
          intro j hj
          exact Finset.mem_sdiff.mpr ⟨hbase.2 hj, fun hjS => (hxi j hjS).2 hj⟩
        · rintro ⟨hxA, hsub⟩
          intro i hi
          refine ⟨⟨hxA, ?_⟩, ?_⟩
          · intro j hj
            exact (Finset.mem_sdiff.mp (hsub hj)).1
          · intro hix
            exact (Finset.mem_sdiff.mp (hsub hix)).2 hi]

-- ==========================================================================
-- from spencer/ClosedPolynomial.lean
-- ==========================================================================

/-!
# Closed-support induction, including line sum zero

Subtract a fixed supported permutation from squares positive on that permutation.
The complement is a union of zero-cell conditions. Inclusion-exclusion expresses
its size using strictly smaller boards at the new, positive level. Boards with
no permutation vanish there, so their exceptional zero matrix causes no problem.
Discrete summation starts at the actual level zero, closing the earlier S5 gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset Polynomial MagicSquares

theorem closedFiber_card_recurrence (n t : ℕ) (B : Finset (Fin n × Fin n))
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    ((closedFiber n (t + 1) B).card : ℚ) = (closedFiber n t B).card +
      ∑ S ∈ (matSupport (permMatrix σ)).powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (S.card + 1) * (closedFiber n (t + 1) (B \ S)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := closedFiber n (t + 1) B) (fun M => matSupport (permMatrix σ) ⊆ matSupport M)
  rw [card_closedFiber_filter_permSupport n t B σ hφB] at hsplit
  have hIE := card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    (matBoxLine n (t + 1)) matSupport B (matSupport (permMatrix σ))
  have hfilter : (closedFiber n (t + 1) B).filter
      (fun M => ¬ matSupport (permMatrix σ) ⊆ matSupport M) =
      (matBoxLine n (t + 1)).filter (fun M => matSupport M ⊆ B ∧
        ¬ matSupport (permMatrix σ) ⊆ matSupport M) := by
    simp [closedFiber, Finset.filter_filter]
  rw [← hfilter] at hIE
  change (((closedFiber n (t + 1) B).filter
    (fun M => ¬ matSupport (permMatrix σ) ⊆ matSupport M)).card : ℚ) = _ at hIE
  have hcast := congrArg (fun k : ℕ => (k : ℚ)) hsplit
  push_cast at hcast
  rw [hIE] at hcast
  exact hcast.symm

def HasPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B

noncomputable def boardPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) := by
  classical
  exact if h : HasPerm n B then Classical.choose h else Equiv.refl _

theorem boardPerm_subset {n : ℕ} {B : Finset (Fin n × Fin n)} (h : HasPerm n B) :
    matSupport (permMatrix (boardPerm n B)) ⊆ B := by
  simp only [boardPerm, dif_pos h]
  exact Classical.choose_spec h

noncomputable def closedTerms (n : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (B ∩ matSupport (permMatrix (boardPerm n B))).powerset.filter (·.Nonempty)

theorem exists_polynomial_closedFiber (n : ℕ) (B : Finset (Fin n × Fin n))
    (hB : HasPerm n B) :
    ∃ P : Polynomial ℚ, ∀ t : ℕ, P.eval (t : ℚ) = (closedFiber n t B).card := by
  classical
  apply exists_poly_of_board_recurrence
    (fun C t => ((closedFiber n t C).card : ℚ)) (HasPerm n) (closedTerms n)
    (fun C S => C \ S) (fun _ S => (-1 : ℚ) ^ (S.card + 1)) ?_ ?_ ?_ B hB
  · intro C S hS
    have h := Finset.mem_filter.mp hS
    have hsub := Finset.mem_powerset.mp h.1
    exact Finset.sdiff_ssubset (hsub.trans Finset.inter_subset_left) h.2
  · intro C hno t
    rw [closedFiber_eq_empty_of_no_perm (by omega)
      (fun σ hσ => hno ⟨σ, hσ⟩), Finset.card_empty, Nat.cast_zero]
  · intro C hC t
    have hperm := boardPerm_subset hC
    have hterms : closedTerms n C =
        (matSupport (permMatrix (boardPerm n C))).powerset.filter (·.Nonempty) := by
      simp only [closedTerms, Finset.inter_eq_right.mpr hperm]
    rw [hterms]
    exact closedFiber_card_recurrence n t C (boardPerm n C) hperm

/-- Polynomiality on every natural line sum, with no unproved zero-point input. -/
theorem exists_polynomial_semiMagicCount_all (n : ℕ) :
    ∃ P : Polynomial ℚ, ∀ t : ℕ, P.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨P, hP⟩ := exists_polynomial_closedFiber n Finset.univ
    ⟨Equiv.refl _, Finset.subset_univ _⟩
  exact ⟨P, fun t => by rw [hP t, card_closedFiber_univ]⟩

theorem sum_sB_eq_one (n : ℕ) : ∑ B ∈ supportSet n, sB n B = 1 :=
  (sum_sB_eq_one_iff_exists_polynomial_semiMagicCount n).mpr
    (exists_polynomial_semiMagicCount_all n)

/-- The polynomial-existence milestone, with the previously proved exact degree. -/
theorem exists_polynomial_semiMagicCount_all_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ P : Polynomial ℚ, P.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, P.eval (t : ℚ) = (semiMagicCount n t : ℚ) :=
  exists_polynomial_semiMagicCount_degree_eq_of_sum_sB n hn (sum_sB_eq_one n)

end MagicSquaresSpencer



/-! ## Platform-facing theorem -/

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) :=
  MagicSquaresSpencer.exists_polynomial_semiMagicCount_all_degree_eq n hn
