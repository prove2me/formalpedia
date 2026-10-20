-- Prove2me | solution 1 for OAI.CirculantHadamard.Barker.even_length_eq_two_or_four
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:18:17.034035+00:00
-- url     : https://prove2.me/submissions/1017048f-fa7b-4883-88a5-1491940e2a12

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Barker/Main.lean:L66-L76
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CirculantHadamard.Barker.even_length_eq_two_or_four.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CirculantHadamard_Barker_even_length_eq_two_or_four) verbatim and is proved by it.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAdjoin__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingTorsion__EvenBarker
import Theorems.Thm_OAI_CirculantHadamard_Barker_periodic_eq_aperiodic_add

-- ---- from OAI.LinearAlgebra.Barker.Parity ----
namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

theorem aperiodic_parity {n : ℕ} (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (k : ℕ) :
    (2 : ℤ) ∣ aperiodic h k - ((n - k : ℕ) : ℤ) := by
  have hp (j : Fin (n - k)) :
      (2 : ℤ) ∣ h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩ - 1 := by
    rcases hs ⟨j.val, by omega⟩ with hx | hx
    all_goals rcases hs ⟨j.val + k, by omega⟩ with hy | hy
    all_goals norm_num [hx, hy]
  have hsum : (2 : ℤ) ∣ ∑ j : Fin (n - k),
      (h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩ - 1) :=
    Finset.dvd_sum (fun j _ => hp j)
  simpa [aperiodic, Finset.sum_sub_distrib] using hsum

theorem aperiodic_bounds {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    -1 ≤ aperiodic h k ∧ aperiodic h k ≤ 1 :=
  abs_le.mp (hb.2 k hk0 hkn)

theorem aperiodic_even_shift_zero {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h)
    (hn : Even n) (k : ℕ) (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ := aperiodic_parity h hb.1 k
  have hbnd := aperiodic_bounds hb k hk0 hkn
  omega

theorem periodic_zero {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) : periodic h 0 = (n : ℤ) := by
  have hp (j : Fin n) : h j * h j = 1 := by
    rcases hs j with hj | hj <;> simp [hj]
  simp [periodic, hp]

end CirculantHadamard.Barker

end OAI

-- ---- from OAI.LinearAlgebra.Barker.PeriodicModFour ----
namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

theorem sign_eq_one_sub_two_bit {n : ℕ} (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (j : Fin n) :
    h j = 1 - 2 * negativeBit h j := by
  rcases hs j with hj | hj <;> norm_num [negativeBit, hj]

theorem sum_negativeBit_shift {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) :
    (∑ j, negativeBit h (j - a)) = ∑ j, negativeBit h j := by
  exact (cyclicSubtractEquiv a).sum_comp (negativeBit h)

theorem periodic_bit_identity {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (a : Fin n) :
    periodic h a = (n : ℤ) + 4 *
      ((∑ j, negativeBit h j * negativeBit h (j - a)) - ∑ j, negativeBit h j) := by
  have hterm (j : Fin n) : h j * h (j - a) =
      1 - 2 * negativeBit h j - 2 * negativeBit h (j - a) +
        4 * (negativeBit h j * negativeBit h (j - a)) := by
    rw [sign_eq_one_sub_two_bit h hs j, sign_eq_one_sub_two_bit h hs (j - a)]
    ring
  calc
    periodic h a = ∑ j : Fin n,
        (1 - 2 * negativeBit h j - 2 * negativeBit h (j - a) +
          4 * (negativeBit h j * negativeBit h (j - a))) := by
      unfold periodic
      exact Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (n : ℤ) - 2 * (∑ j, negativeBit h j) -
        2 * (∑ j, negativeBit h (j - a)) +
        4 * (∑ j, negativeBit h j * negativeBit h (j - a)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by rw [sum_negativeBit_shift]; ring

theorem periodic_mod_four {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (a : Fin n) :
    (4 : ℤ) ∣ periodic h a - (n : ℤ) := by
  refine ⟨(∑ j, negativeBit h j * negativeBit h (j - a)) -
    ∑ j, negativeBit h j, ?_⟩
  rw [periodic_bit_identity h hs a]
  ring

end CirculantHadamard.Barker

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.Basic ----
namespace OAI

universe uR

namespace CirculantHadamard

theorem rowCirculant_isCirculant {n : ℕ} (h : Fin n → ℝ) :
    IsCirculant (rowCirculant h) := ⟨h, fun _ _ => rfl⟩

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.Witnesses ----
namespace OAI

namespace CirculantHadamard

theorem witness_one_eq_rowCirculant : witness_one = rowCirculant firstRow_one := by
  ext i j
  fin_cases i; fin_cases j; rfl

theorem witness_four_eq_rowCirculant : witness_four = rowCirculant firstRow_four := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem witness_one_signs (i j : Fin 1) : IsSign (witness_one i j) := by
  fin_cases i; fin_cases j; norm_num [IsSign, witness_one]

theorem witness_four_signs (i j : Fin 4) : IsSign (witness_four i j) := by
  fin_cases i <;> fin_cases j <;> norm_num [IsSign, witness_four]

theorem witness_one_gram :
    witness_one * witness_one.transpose = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_one, witness_one,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply]

theorem witness_four_gram :
    witness_four * witness_four.transpose = (4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, witness_four,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_one_isCirculant : IsCirculant witness_one := by
  rw [witness_one_eq_rowCirculant]
  exact rowCirculant_isCirculant firstRow_one

theorem witness_four_isCirculant : IsCirculant witness_four := by
  rw [witness_four_eq_rowCirculant]
  exact rowCirculant_isCirculant firstRow_four

theorem witness_one_isSignHadamard : IsSignHadamard witness_one := by
  exact ⟨witness_one_signs, by simpa using witness_one_gram⟩

theorem witness_four_isSignHadamard : IsSignHadamard witness_four := by
  exact ⟨witness_four_signs, by simpa using witness_four_gram⟩

theorem exists_one : ExistsRealCirculantHadamard 1 :=
  ⟨witness_one, witness_one_isCirculant, witness_one_isSignHadamard⟩

theorem exists_four : ExistsRealCirculantHadamard 4 :=
  ⟨witness_four, witness_four_isCirculant, witness_four_isSignHadamard⟩

/-- The explicit matrices of orders one and four establish existence. -/
theorem exists_of_order_one_or_four {n : ℕ} (hn : n = 1 ∨ n = 4) :
    ExistsRealCirculantHadamard n := by
  rcases hn with rfl | rfl
  · exact exists_one
  · exact exists_four

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.MatrixBridge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uR

/-!
# From real sign matrices to integer cyclic autocorrelation

The Gram entry is reindexed using translation in `Fin n`. The real/integer
bridge uses the injective coefficient map `ℤ → ℝ`; it does not assume any
classification or any group-ring norm statement.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- The Gram entry at `(i,a)` is the cyclic autocorrelation at `a-i`. -/
theorem rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := fun j => sub_add_cancel j i
      right_inv := fun j => add_sub_cancel_right j i }
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  apply Fintype.sum_equiv e
  intro j
  change h (j - i) * h (j - a) = h (j - i) * h ((j - i) - (a - i))
  simp only [sub_sub_sub_cancel_right]

/-- The full Gram equation is exactly the cyclic autocorrelation system. -/
theorem gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  classical
  constructor
  · intro hGram a
    have ha := congrArg (fun M : Matrix (Fin n) (Fin n) R => M 0 a) hGram
    rw [rowCirculant_gram_apply] at ha
    simpa [Matrix.smul_apply, Matrix.one_apply, eq_comm] using ha
  · intro hCorr
    ext i a
    rw [rowCirculant_gram_apply, hCorr]
    by_cases hia : i = a
    · subst a
      simp
    · have hai : a - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hia)
      simp [hia, hai, Matrix.smul_apply]

/-- Casting the integer Gram matrix agrees entry by entry with taking the
Gram matrix after casting the row. -/
theorem intCast_gram_apply (h : Fin n → ℤ) (i j : Fin n) :
    ((rowCirculant h * (rowCirculant h).transpose) i j : ℝ) =
      (rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant, Int.cast_sum,
    Int.cast_mul]

private theorem intCast_scaled_identity_apply (i j : Fin n) :
    (((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℝ) =
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- The real coefficient embedding preserves and reflects the entire Gram
identity, including the diagonal value. -/
theorem gram_intCast_iff (h : Fin n → ℤ) :
    rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose =
        (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor
  · intro hGram
    ext i j
    apply Int.cast_injective (α := ℝ)
    rw [intCast_gram_apply, intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram
  · intro hGram
    ext i j
    rw [← intCast_gram_apply, ← intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hGram

/-- Every integer sign row gives the actual real circulant Hadamard matrix. -/
theorem IsIntegerSignRow.exists_real {h : Fin n → ℤ} (hh : IsIntegerSignRow h) :
    ExistsRealCirculantHadamard n := by
  refine ⟨rowCirculant (fun a => (h a : ℝ)), rowCirculant_isCirculant _, ?_,
    (gram_intCast_iff h).mpr hh.2⟩
  intro i j
  rcases hh.1 (j - i) with hpos | hneg
  · left
    simp only [rowCirculant_apply, hpos, Int.cast_one]
  · right
    simp only [rowCirculant_apply, hneg, Int.cast_neg, Int.cast_one]

/-- A real sign matrix determines an integer sign row without approximation. -/
theorem ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  classical
  rcases hH with ⟨H, ⟨h, hrow⟩, hsign, hGram⟩
  have hsignRow : ∀ j, IsSign (h j) := by
    intro j
    simpa only [hrow, sub_zero] using hsign 0 j
  let z : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hzcast : ∀ j, (z j : ℝ) = h j := by
    intro j
    by_cases hj : h j = 1
    · simp [z, hj]
    · have hneg := (hsignRow j).resolve_left hj
      simp only [z, ite_eq_right hj, Int.cast_neg, Int.cast_one, hneg]
  have hzsign : ∀ j, IsSign (z j) := by
    intro j
    dsimp [z, IsSign]
    split_ifs <;> simp
  have hzH : rowCirculant (fun j => (z j : ℝ)) = H := by
    ext i j
    rw [rowCirculant_apply, hzcast, hrow]
  refine ⟨z, hzsign, (gram_intCast_iff z).mp ?_⟩
  simpa only [hzH] using hGram

/-- Equivalence between the public real matrix problem and integer sign rows. -/
theorem integerSignRow_iff_real [NeZero n] :
    (∃ h : Fin n → ℤ, IsIntegerSignRow h) ↔ ExistsRealCirculantHadamard n := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh.exists_real
  · exact ExistsRealCirculantHadamard.exists_integerSignRow

/-- A direct integer autocorrelation presentation of the real matrix problem. -/
theorem existsReal_iff_integer_autocorrelation [NeZero n] :
    ExistsRealCirculantHadamard n ↔
      ∃ h : Fin n → ℤ, (∀ j, IsSign (h j)) ∧
        ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : ℤ) else 0 := by
  rw [← integerSignRow_iff_real]
  simp only [IsIntegerSignRow, gram_eq_iff_autocorrelation]

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicRing ----
namespace OAI

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

end Convolution

theorem mul_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) :=
  group_mul_apply f g a

theorem mul_ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (f * ringStar f).coeff a = ∑ j, f.coeff j * star (f.coeff (j - a)) := by
  simp only [mul_apply, ringStar_apply, neg_sub]

theorem augmentation_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) :
    augmentation n (ringStar f) = star (augmentation n f) := by
  simp only [augmentation_apply, ringStar_apply, star_sum]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun _ => rfl)

theorem augmentation_norm_star {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (r : R)
    (h : f * ringStar f = scalar n r) :
    augmentation n f * star (augmentation n f) = r := by
  have he := congrArg (augmentation n) h
  simpa only [map_mul, augmentation_ringStar, augmentation_scalar] using he

theorem augmentation_norm {n : ℕ} [NeZero n] (f : Elem ℤ n) (r : ℤ)
    (h : f * ringStar f = scalar n r) : (augmentation n f) ^ 2 = r := by
  simpa only [star_trivial, pow_two] using augmentation_norm_star f r h

end CirculantHadamard.CyclicRing

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicNorm ----
namespace OAI

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

section PositiveOrder

variable {n : ℕ} [NeZero n]

theorem cyclicSignRow_cyclicRow_iff (h : Fin n → ℤ) :
    CyclicSignRow (cyclicRow h) ↔ ∀ j, IsSign (h j) := by
  constructor
  · intro hf j
    simpa using hf (ZMod.finEquiv n j)
  · intro hh a
    simpa using hh ((ZMod.finEquiv n).symm a)

/-- The norm coefficient uses the same `j - a` orientation as the row Gram. -/
theorem cyclicRow_norm_apply (h : Fin n → ℤ) (a : Fin n) :
    (cyclicRow h * CyclicRing.ringStar (cyclicRow h)).coeff (ZMod.finEquiv n a) =
      ∑ j : Fin n, h j * h (j - a) := by
  rw [CyclicRing.mul_ringStar_apply]
  simpa only [cyclicRow_apply, map_sub, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply, star_trivial] using
    ((ZMod.finEquiv n).toEquiv.sum_comp
      (fun j : ZMod n =>
        (cyclicRow h).coeff j * star ((cyclicRow h).coeff (j - ZMod.finEquiv n a)))).symm

theorem cyclicRow_norm_iff_autocorrelation (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      ∀ a : Fin n, (∑ j : Fin n, h j * h (j - a)) =
        if a = 0 then (n : ℤ) else 0 := by
  constructor
  · intro hn a
    have ha := congrArg
      (fun f : CyclicRing.Elem ℤ n => f.coeff (ZMod.finEquiv n a)) hn
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using ha
  · intro hh
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro x
    obtain ⟨a, rfl⟩ := (ZMod.finEquiv n).surjective x
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using hh a

theorem cyclicRow_norm_iff_gram (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) :=
  (cyclicRow_norm_iff_autocorrelation h).trans (gram_eq_iff_autocorrelation h).symm

theorem integerSignRow_iff_cyclicSignNorm (h : Fin n → ℤ) :
    IsIntegerSignRow h ↔
      CyclicSignRow (cyclicRow h) ∧
        cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
          CyclicRing.scalar n (n : ℤ) := by
  exact and_congr (cyclicSignRow_cyclicRow_iff h).symm (cyclicRow_norm_iff_gram h).symm

/-- The literal sign norm equation is equivalent to the public real-matrix
existence predicate.  Neither direction assumes a mathematical bridge. -/
theorem exists_cyclicSignRow_iff_real :
    (∃ f : CyclicRing.Elem ℤ n,
      CyclicSignRow f ∧ f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) ↔
      ExistsRealCirculantHadamard n := by
  rw [← integerSignRow_iff_real]
  constructor
  · rintro ⟨f, hf, hn⟩
    refine ⟨integerRow f, (integerSignRow_iff_cyclicSignNorm _).2 ?_⟩
    simpa only [cyclicRow_integerRow] using And.intro hf hn
  · rintro ⟨h, hh⟩
    exact ⟨cyclicRow h, (integerSignRow_iff_cyclicSignNorm h).1 hh⟩

/-- The identity coefficient is the sum of the actual coefficient squares. -/
theorem cyclicNorm_identity_coeff (f : CyclicRing.Elem ℤ n) :
    (f * CyclicRing.ringStar f).coeff 0 = ∑ a : ZMod n, f.coeff a ^ 2 := by
  simp [CyclicRing.mul_ringStar_apply, pow_two]

end PositiveOrder

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderSquareEven ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIota

/-!
# Square and even order from actual circulant sign rows

Augmentation of the cyclic norm identity gives an integer square. A
nonidentity correlation is a zero sum of signs; reduction modulo two makes
its number of summands even. Both conclusions follow from the actual real
circulant Hadamard matrix predicate.
-/

namespace CirculantHadamard

open scoped BigOperators

private theorem positive_nat_square_of_int_square {n : ℕ} (hn : 0 < n)
    (z : ℤ) (hz : z ^ 2 = (n : ℤ)) :
    ∃ m : ℕ, 0 < m ∧ n = m ^ 2 := by
  have hsq : z.natAbs ^ 2 = n := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hz
  have hm : z.natAbs ≠ 0 := by
    intro hm
    have hzero : n = 0 := by simpa only [hm, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsq.symm
    exact (Nat.ne_of_gt hn) hzero
  exact ⟨z.natAbs, Nat.pos_of_ne_zero hm, hsq.symm⟩

private theorem even_card_of_sign_sum_zero {ι : Type uIota} [Fintype ι]
    (f : ι → ℤ) (hsign : ∀ i, IsSign (f i)) (hsum : ∑ i, f i = 0) :
    Even (Fintype.card ι) := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hcast (i : ι) : φ (f i) = 1 := by
    rcases hsign i with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
      exact ZMod.neg_eq_self_mod_two (1 : ZMod 2)
  have hcard : (Fintype.card ι : ZMod 2) = 0 := by
    have h := congrArg φ hsum
    simpa only [map_sum, hcast, map_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hcard)

/-- A nonidentity norm coefficient is a zero sum of exactly `n` signs. -/
theorem order_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by
  classical
  let : Fact (1 < n) := ⟨hn⟩
  have hcorr : (∑ a : ZMod n, f.coeff a * f.coeff (a - 1)) = 0 := by
    have h := congrArg (fun g : CyclicRing.Elem ℤ n => g.coeff 1) hnorm
    simpa only [CyclicRing.mul_ringStar_apply, star_trivial, CyclicRing.scalar_apply,
      ite_eq_right (one_ne_zero : (1 : ZMod n) ≠ 0)] using h
  have heven := even_card_of_sign_sum_zero (fun a : ZMod n => f.coeff a * f.coeff (a - 1))
    (fun a => by
      rcases hsign a with ha | ha <;> rcases hsign (a - 1) with hb | hb <;>
        simp [IsSign, ha, hb]) hcorr
  simpa only [ZMod.card] using heven

/-- Square and even order from the actual integer sign norm equation. -/
theorem order_square_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  constructor
  · exact positive_nat_square_of_int_square (lt_trans Nat.zero_lt_one hn)
      (CyclicRing.augmentation n f) (CyclicRing.augmentation_norm f (n : ℤ) hnorm)
  · exact order_even_of_sign_norm hn f hsign hnorm

/-- A nontrivial actual real circulant sign Hadamard matrix has positive
square order and even order. The integer row and its norm identity are
obtained from the proved matrix correspondence. -/
theorem order_square_even {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  let : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  obtain ⟨f, hsign, hnorm⟩ := exists_cyclicSignRow_iff_real.mpr h
  exact order_square_even_of_sign_norm hn f hsign hnorm

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.TwoAdicDecomposition ----
namespace OAI

/-!
# The two-adic form of a positive even square

Extract the power of two from an actual positive square root. Evenness of the
square forces a positive exponent in that root, so squaring gives the precise
form used at the start of the circulant Hadamard order reduction.
-/

namespace CirculantHadamard

/-- Extract the two-adic part from a specified positive square root. -/
theorem exists_two_adic_square_decomposition_of_eq_sq {n m : ℕ}
    (hm : 0 < m) (hnm : n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨s, u, hu, hroot⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hmEven : Even m := (Nat.even_pow.mp (hnm ▸ heven)).1
  have hs : s ≠ 0 := by
    intro hs0
    have hmu : m = u := by simpa only [hs0, pow_zero, one_mul] using hroot
    exact (Nat.not_even_iff_odd.mpr hu) (hmu ▸ hmEven)
  have huPos : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hu0
    have hm0 : m = 0 := by simpa only [hu0, mul_zero] using hroot
    exact hm.ne' hm0
  refine ⟨s, u, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs), huPos, hu, ?_⟩
  rw [hnm, hroot, mul_pow, ← pow_mul, Nat.mul_comm s 2]

/-- Interface for an order theorem that already supplies its positive root. -/
theorem exists_two_adic_square_decomposition_of_positive_square {n : ℕ}
    (hsquare : ∃ m : ℕ, 0 < m ∧ n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨m, hm, hnm⟩ := hsquare
  exact exists_two_adic_square_decomposition_of_eq_sq hm hnm heven

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicProjection ----
namespace OAI

universe uR uS

/-!
# Quotients of actual cyclic group rings

For `m ∣ n`, reduction of indices defines the quotient map from the cyclic
group ring of order `n` to that of order `m`. In particular it sends the
distinguished generator to the distinguished generator and fixes scalars.
The definition is the convolution ring homomorphism induced by `ZMod.castHom`.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [Semiring R] {m n l : ℕ}

variable {R}

section Star

variable [StarRing R] [NeZero m] [NeZero n]

/-- A scalar convolution norm descends to the quotient cyclic group. -/
theorem cyclicProjection_norm (h : m ∣ n) {F : Elem R n} {r : R}
    (hnorm : F * ringStar F = scalar n r) :
    cyclicProjection R h F * ringStar (cyclicProjection R h F) = scalar m r := by
  have hq := congrArg (cyclicProjection R h) hnorm
  simpa only [map_mul, cyclicProjection_ringStar, cyclicProjection_scalar] using hq

end Star

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ProjectionPairFiber ----
namespace OAI

/-!
# The two fibers of reduction modulo half the order

Reduction from `ZMod (2 * m)` to `ZMod m` has exactly the two usual lifts
of each element when `m` is positive.
-/

namespace CirculantHadamard

/-- The fiber of reduction modulo `m` consists of its two canonical lifts. -/
theorem zmod_double_cast_eq_iff {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero (2 * m) := ⟨by omega⟩
  have hxlt : x.val < 2 * m := ZMod.val_lt x
  have hjlt : j.val < m := ZMod.val_lt j
  constructor
  · intro hx
    have hmod : x.val % m = j.val := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] using
        congrArg ZMod.val hx
    by_cases hsmall : x.val < m
    · left
      have hval : x.val = j.val := by
        simpa only [Nat.mod_eq_of_lt hsmall] using hmod
      rw [← hval, ZMod.natCast_zmod_val]
    · right
      have hmle : m ≤ x.val := by omega
      have hsub : x.val - m < m := by omega
      rw [Nat.mod_eq_sub_mod hmle, Nat.mod_eq_of_lt hsub] at hmod
      have hval : x.val = j.val + m := by omega
      rw [← hval, ZMod.natCast_zmod_val]
  · rintro (rfl | rfl)
    · simp only [map_natCast, ZMod.natCast_zmod_val]
    · rw [map_natCast]
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

/-- The two canonical lifts into the group of twice the order are distinct. -/
theorem zmod_double_lifts_ne {m : ℕ} (hm : 0 < m) (j : ZMod m) :
    (j.val : ZMod (2 * m)) ≠ ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  have hjlt : j.val < m := ZMod.val_lt j
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show j.val < 2 * m by omega),
    Nat.mod_eq_of_lt (show j.val + m < 2 * m by omega)] at hv
  omega

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ProjectionCoefficients ----
namespace OAI

universe uA uB uR

/-!
# Coefficients of cyclic quotient maps

The coefficient at an element of the quotient is the sum over its entire
fiber. For the quotient of order `2 * m` onto order `m`, the fiber consists
of the two representatives `j.val` and `j.val + m`.
-/

namespace CirculantHadamard

open scoped BigOperators

section Fiber

variable {A : Type uA} {B : Type uB} {R : Type uR} [Fintype A] [DecidableEq B] [AddCommMonoid R]

/-- Mapping the domain adds precisely the coefficients in a quotient fiber. -/
theorem mapDomain_apply_sum (q : A → B) (f : A →₀ R) (b : B) :
    Finsupp.mapDomain q f b = ∑ a ∈ Finset.univ.filter (fun a => q a = b), f a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply, Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hzero : f a = 0 := Finsupp.notMem_support_iff.mp ha
  simp [hzero]

/-- The same coefficient formula, indexed by the subtype of the fiber. -/
theorem mapDomain_apply_fiber (q : A → B) (f : A →₀ R) (b : B) :
    Finsupp.mapDomain q f b = ∑ a : {a : A // q a = b}, f a.val := by
  classical
  rw [mapDomain_apply_sum]
  exact Finset.sum_subtype _ (by intro a; simp) _

end Fiber

section Cyclic

variable {R : Type uR} [Semiring R]

/-- Coefficients of the actual cyclic group-ring quotient as a finite filter sum. -/
theorem cyclicProjection_apply_sum {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod n =>
        ZMod.castHom h (ZMod m) x = a), f.coeff x := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_sum _ _ _

/-- Coefficients of the actual cyclic group-ring quotient as a fiber subtype sum. -/
theorem cyclicProjection_apply_fiber {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x : {x : ZMod n // ZMod.castHom h (ZMod m) x = a}, f.coeff x.val := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_fiber _ _ _

/-- A quotient by the subgroup of order two adds opposite coefficients. -/
theorem cyclicProjection_double_apply {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (f : CyclicRing.Elem R (2 * m)) (j : ZMod m) :
    (cyclicProjection R h f).coeff j =
      f.coeff (j.val : ZMod (2 * m)) + f.coeff ((j.val + m : ℕ) : ZMod (2 * m)) := by
  classical
  let : NeZero (2 * m) := ⟨(Nat.mul_pos (by decide) hm).ne'⟩
  rw [cyclicProjection_apply_sum]
  refine Finset.sum_eq_add_of_mem _ _ ?_ ?_ (zmod_double_lifts_ne hm j) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inl rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inr rfl)
  · intro x hx hne
    have hx' := (Finset.mem_filter.mp hx).2
    rcases (zmod_double_cast_eq_iff hm h x j).mp hx' with hxj | hxj
    · exact (hne.1 hxj).elim
    · exact (hne.2 hxj).elim

end Cyclic

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderProjection ----
namespace OAI

universe uα

/-!
# The first order projection

The quotient sends the original cyclic generator to the cyclic generator of
the smaller order. Its coefficients are the sums over the actual reduction
fibers. When `n = m * d`, every fiber contains exactly `d` original indices;
an odd number of signs therefore produces an odd integer coefficient.

The norm scalar is preserved by the quotient map. In particular, projecting
from `2^(2*s) * u^2` to `2^(2*s)` does not divide the original norm scalar.
-/

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every fiber of reduction modulo a divisor has the exact quotient size. -/
theorem cyclic_reduction_fiber_card {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by
  classical
  let q : ZMod n →+ ZMod m := (ZMod.castHom hdiv (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective q := by
    intro b
    refine ⟨(b.val : ZMod n), ?_⟩
    change ZMod.castHom hdiv (ZMod m) (b.val : ZMod n) = b
    simp only [map_natCast, ZMod.natCast_zmod_val]
  have hcards (b : ZMod m) :
      (Finset.univ.filter (fun x : ZMod n => q x = b)).card =
        (Finset.univ.filter (fun x : ZMod n => q x = a)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range q (hsurj b) (hsurj a)
  have htotal : n = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
    calc
      n = (Finset.univ : Finset (ZMod n)).card := by simp
      _ = ∑ b : ZMod m, (Finset.univ.filter (fun x : ZMod n => q x = b)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
        simp only [hcards, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [Fintype.card_subtype]
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos m) (htotal.symm.trans hn)

/-- An odd finite family of actual integer signs has odd sum. -/
theorem odd_sum_of_signs {α : Type uα} [Fintype α] (f : α → ℤ)
    (hf : ∀ x, IsSign (f x)) (hcard : Odd (Fintype.card α)) :
    Odd (∑ x, f x) := by
  classical
  apply Int.odd_iff.mpr
  have hmod (x : α) : f x % 2 = 1 := by
    rcases hf x with hx | hx <;> norm_num [hx]
  calc
    (∑ x, f x) % 2 = (∑ _x : α, (1 : ℤ)) % 2 := by
      rw [Finset.sum_int_mod]
      simp only [hmod]
    _ = (Fintype.card α : ℤ) % 2 := by simp
    _ = 1 := Int.odd_iff.mp ((Int.odd_coe_nat _).mpr hcard)

/-- The actual quotient coefficient is odd because its fiber consists of
exactly the specified odd number of original signs. -/
theorem cyclicProjection_odd_coefficients {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (hd : Odd d)
    (f : CyclicRing.Elem ℤ n) (hf : CyclicSignRow f) (a : ZMod m) :
    Odd ((cyclicProjection ℤ hdiv f).coeff a) := by
  classical
  rw [cyclicProjection_apply_fiber]
  apply odd_sum_of_signs
    (α := {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a})
    (fun x => f.coeff x.val) (fun x => hf x.val)
  rw [cyclic_reduction_fiber_card hdiv hn a]
  exact hd

/-- First projection in the order reduction: every coefficient is odd and
the scalar on the right of the norm equation remains the original order. -/
theorem exists_odd_cyclic_projection {n s u : ℕ} [NeZero n]
    (hu : Odd u) (heq : n = 2 ^ (2 * s) * u ^ 2)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    ∃ T : CyclicRing.Elem ℤ (2 ^ (2 * s)),
      (∀ a, Odd (T.coeff a)) ∧
        T * CyclicRing.ringStar T =
          CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by
  let : NeZero (2 ^ (2 * s)) := ⟨pow_ne_zero _ (by decide)⟩
  have hdiv : 2 ^ (2 * s) ∣ n := ⟨u ^ 2, heq⟩
  refine ⟨cyclicProjection ℤ hdiv f, ?_, ?_⟩
  · exact cyclicProjection_odd_coefficients hdiv heq hu.pow f hsign
  · calc
      _ = CyclicRing.scalar _ (n : ℤ) := cyclicProjection_norm hdiv hnorm
      _ = CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by rw [heq]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.IntegerLocalDivisibility ----
namespace OAI

universe uA

/-!
# Reflecting prime-power divisibility from the localized integers

A denominator inverted in the localization at `(p)` is not divisible by `p`.
Clearing that denominator and using primality therefore reflects divisibility
by every power of `p` back to the integers. The argument includes the zeroth
power and the zero numerator, without any nonzero numerator hypothesis.
-/

namespace CirculantHadamard

/-- Divisibility by a rational prime power in its actual integer localization
implies the same divisibility in the integers. -/
theorem integer_prime_pow_dvd_of_localization
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl y
  have hinj : Function.Injective (algebraMap ℤ A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hclear : x * (s : ℤ) = (p : ℤ) ^ t * a := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_natCast, hy, mul_assoc, hs]
  have hsprime : ¬ (p : ℤ) ∣ (s : ℤ) := by
    intro hdiv
    have hmem : (s : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      Ideal.mem_span_singleton.mpr hdiv
    exact s.property (hP.symm ▸ hmem)
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right t hsprime
    ⟨a, hclear⟩

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalDVR ----
namespace OAI

universe uR

/-!
# Principal maximal ideals and local factor divisibility

A nonzero principal maximal ideal in a Noetherian local domain gives a DVR
and uniformizer factorizations. Its canonical additive valuation, valued in
`ℕ∞`, splits a product of a prime power and a unit.
-/

noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Normalize the additive valuation using the concrete uniformizer relation. -/
theorem addVal_eq_of_unit_mul_uniformizer_pow {π p : R} {u : Rˣ} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hp : p = (u : R) * π ^ D) :
    addVal R p = (D : ℕ∞) :=
  addVal_def p u ((irreducible_iff_uniformizer π).mpr hspan) D hp

private theorem finite_add_eq {a b : ℕ∞} {N : ℕ} (h : a + b = (N : ℕ∞)) :
    ∃ m n : ℕ, a = (m : ℕ∞) ∧ b = (n : ℕ∞) ∧ m + n = N := by
  have ha : a ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_right zero_le
  have hb : b ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_left zero_le
  obtain ⟨m, hm, _⟩ := ENat.le_natCast_iff.mp ha
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp hb
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- If the valuation of a product is at least twice that of `p`, one factor
is divisible by `p`. The value of `p` is allowed to be ramified. -/
theorem dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, addVal_pow, hpval,
    addVal_eq_zero_iff.mpr hb, add_zero] at hv
  have hv' : addVal R x + addVal R y = ((e * D : ℕ) : ℕ∞) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq hv'
  have heD : 2 * D ≤ e * D := Nat.mul_le_mul_right D he
  have hsplit : D ≤ m ∨ D ≤ n := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_le_iff_dvd.mp
    rw [hpval, hm]
    exact_mod_cast hx
  · right
    apply addVal_le_iff_dvd.mp
    rw [hpval, hn]
    exact_mod_cast hy

end Valuation

end CirculantHadamard.LocalDVR

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.IntegerTwoLocal ----
namespace OAI

/-!
# The integers localized at the prime two

The ring is the actual localization of `ℤ` at the complement of `(2)`. Its
maximal ideal is generated by the image of two, and its nonzero generator makes
it a discrete valuation ring. The characteristic-zero and odd-unit interfaces
refer to this concrete localization, without assuming any valuation facts.
-/

noncomputable section

namespace CirculantHadamard.IntegerTwoLocal

/-- Exactly the odd integers become units. -/
theorem isUnit_algebraMap_iff_odd (z : ℤ) :
    IsUnit (algebraMap ℤ Ring z) ↔ Odd z := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff Ring ideal z]
  change z ∉ ideal ↔ Odd z
  rw [mem_ideal_iff_even, Int.not_even_iff_odd]

theorem isUnit_intCast_of_odd (z : ℤ) (hz : Odd z) : IsUnit (z : Ring) := by
  simpa using (isUnit_algebraMap_iff_odd z).mpr hz

theorem isUnit_natCast_of_odd (u : ℕ) (hu : Odd u) : IsUnit (u : Ring) := by
  simpa only [Int.cast_natCast] using
    isUnit_intCast_of_odd (u : ℤ) ((Int.odd_coe_nat u).mpr hu)

end CirculantHadamard.IntegerTwoLocal

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedConjugation ----
namespace OAI

universe uR uA

/-!
# Cyclotomic conjugation and norm divisibility in a DVR

The conjugation fixes the coefficient ring and sends the actual
adjoined root to its multiplicative inverse. In a DVR every ring
automorphism preserves the canonical additive valuation, because it sends
units to units and uniformizers to uniformizers. Consequently a norm equal
to a unit times an even scalar power forces the corresponding half-power
to divide the element.
-/

noncomputable section

namespace CirculantHadamard.RamifiedConjugation

open Polynomial IsDiscreteValuationRing

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem enat_add_self_injective {a b : ℕ∞} (h : a + a = b + b) : a = b := by
  cases a using ENat.recTopCoe with
  | top =>
      cases b using ENat.recTopCoe with
      | top => rfl
      | coe b => simp only [← ENat.natCast_add, top_add, ENat.top_ne_natCast] at h
  | coe a =>
      cases b using ENat.recTopCoe with
      | top => simp only [← ENat.natCast_add, top_add, ENat.natCast_ne_top] at h
      | coe b =>
          have hab : a + a = b + b := ENat.natCast_inj.mp h
          have : a = b := by omega
          exact congrArg (fun n : ℕ => (n : ℕ∞)) this

/-- A norm with an even scalar exponent gives divisibility by half that
power. The statement includes zero and needs no normalization assumption
on the scalar's valuation. -/
theorem pow_dvd_of_norm_eq (e : R ≃+* R) (a x b : R) (t : ℕ)
    (hb : IsUnit b) (h : x * e x = a ^ (2 * t) * b) : a ^ t ∣ x := by
  have hsq : x * e x = (a ^ t * a ^ t) * b := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm t 2]
    exact h
  have hv := congrArg (addVal R) hsq
  have hbval : addVal R b = 0 := addVal_eq_zero_iff.mpr hb
  simp only [addVal_mul, addVal_ringEquiv, hbval, add_zero] at hv
  exact addVal_le_iff_dvd.mp (enat_add_self_injective hv).symm.le

end Valuation

section Cyclotomic

variable (A : Type uA) [CommRing A] (n : ℕ)

variable (hn : 0 < n)
variable [domain : IsDomain (CyclotomicRing A n)] [charZero : CharZero (CyclotomicRing A n)]

include hn

variable [IsDiscreteValuationRing (CyclotomicRing A n)]

theorem cyclotomic_pow_dvd_of_norm_eq (a x b : CyclotomicRing A n) (t : ℕ)
    (hb : IsUnit b)
    (h : x * cyclotomicConjugation A n hn x = a ^ (2 * t) * b) : a ^ t ∣ x :=
  pow_dvd_of_norm_eq (cyclotomicConjugation A n hn).toRingEquiv a x b t hb h

end Cyclotomic

end CirculantHadamard.RamifiedConjugation

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicIntegerEvaluation ----
namespace OAI

universe uA

/-!
# Integer cyclic evaluation and actual cyclotomic conjugation

The coefficient map is the integer cast into the cyclotomic quotient. The
character sends the cyclic generator to its adjoined root. The root-inverting
automorphism therefore carries evaluation to evaluation of the actual cyclic
group-ring involution.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

theorem integerCyclotomicEvaluation_apply (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      ∑ a : ZMod n, (T.coeff a : AdjoinRoot (cyclotomic n A)) *
        AdjoinRoot.root (cyclotomic n A) ^ a.val := by
  rw [integerCyclotomicEvaluation, CyclicRing.evaluate_apply]
  rfl

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

/-- The actual character intertwines negation of its index and the proved
cyclotomic conjugation. -/
theorem cyclotomicPowerCharacter_neg (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by
  let χ := CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
    (RamifiedConjugation.root_pow_order A n)
  have hnonzero : χ (Multiplicative.ofAdd a) ≠ 0 :=
    pow_ne_zero a.val
      ((RamifiedConjugation.root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ hnonzero
  have hleft : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  change χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) =
    RamifiedConjugation.cyclotomicConjugation A n hn
      (χ (Multiplicative.ofAdd a)) * χ (Multiplicative.ofAdd a)
  rw [hleft]
  symm
  change RamifiedConjugation.cyclotomicConjugation A n hn
      (AdjoinRoot.root (cyclotomic n A) ^ a.val) *
    AdjoinRoot.root (cyclotomic n A) ^ a.val = 1
  rw [map_pow, RamifiedConjugation.cyclotomicConjugation_root, ← mul_pow,
    RamifiedConjugation.root_pow_pred_mul_root A n hn, one_pow]

/-- Evaluating the integer cyclic involution is exactly the cyclotomic
conjugate of the evaluated element. -/
theorem integerCyclotomicEvaluation_ringStar (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n (CyclicRing.ringStar T) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) := by
  apply CyclicRing.evaluate_ringStar_intertwining
    (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))
    (RamifiedConjugation.cyclotomicConjugation A n hn).toRingHom
  · intro r
    simp
  · exact cyclotomicPowerCharacter_neg A n hn

/-- A proved scalar norm equation in the integer group ring transfers to
the actual cyclotomic norm equation. -/
theorem integerCyclotomicEvaluation_norm (T : CyclicRing.Elem ℤ n) (a : ℤ)
    (hT : T * CyclicRing.ringStar T = CyclicRing.scalar n a) :
    integerCyclotomicEvaluation A n T *
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) =
      (a : AdjoinRoot (cyclotomic n A)) := by
  rw [← integerCyclotomicEvaluation_ringStar A n hn, ← map_mul, hT,
    integerCyclotomicEvaluation_scalar]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder ----
namespace OAI

universe uR uS

/-!
# Scalar divisibility and monic remainders

The canonical remainder map for a monic root extension is linear over the
coefficient ring. Consequently, divisibility by a scalar in the extension is
equivalent to divisibility of every coefficient of the monic remainder.

The actual polynomial quotient `AdjoinRoot f` is such an extension;
no additional representation hypothesis is required.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicRemainder

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

/-- Scalar divisibility in a monic root extension gives a constant-polynomial
factor of the canonical remainder. -/
theorem C_dvd_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) :
    C a ∣ F %ₘ f := by
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨h.modByMonicHom x, ?_⟩
  calc
    F %ₘ f = h.modByMonicHom (h.map F) := (h.modByMonicHom_map F).symm
    _ = h.modByMonicHom (a • x) := by rw [hx, Algebra.smul_def]
    _ = a • h.modByMonicHom x := h.modByMonicHom.map_smul a x
    _ = C a * h.modByMonicHom x := Polynomial.smul_eq_C_mul a

/-- A constant factor of the canonical remainder gives scalar divisibility
after passing to the monic root extension. -/
theorem dvd_map_of_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : C a ∣ F %ₘ f) :
    algebraMap R S a ∣ h.map F := by
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨h.map G, ?_⟩
  calc
    h.map F = h.map (F %ₘ f) := (h.map_modByMonic F).symm
    _ = h.map (C a * G) := congrArg h.map hG
    _ = algebraMap R S a * h.map G := by rw [map_mul, ← h.algebraMap_apply]

/-- Exact divisibility equivalence for a monic root extension. -/
theorem map_dvd_iff_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ C a ∣ F %ₘ f :=
  ⟨C_dvd_modByMonic_of_dvd_map h a F, dvd_map_of_C_dvd_modByMonic h a F⟩

/-- The actual quotient by a monic polynomial satisfies the constant-factor
criterion, using its concrete `IsAdjoinRootMonic` constructor. -/
theorem adjoinRoot_dvd_iff_C_dvd_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔ C a ∣ F %ₘ f := by
  simpa only [AdjoinRoot.isAdjoinRootMonic_toAdjoinRoot,
    AdjoinRoot.isAdjoinRoot_map_eq_mkₐ, AdjoinRoot.coe_mkₐ] using
    map_dvd_iff_C_dvd_modByMonic (AdjoinRoot.isAdjoinRootMonic f hf) a F

/-- The concrete monic quotient has scalar divisibility exactly when all
coefficients of the monic remainder have that scalar factor. -/
theorem adjoinRoot_dvd_iff_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔
      ∀ i, a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_C_dvd_modByMonic f hf a F).trans
    (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Scalar divisibility in a monic quotient implies coefficientwise
divisibility of the remainder. -/
theorem adjoinRoot_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X])
    (hdiv : algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_dvd_coeff_modByMonic f hf a F).mp hdiv i

end CirculantHadamard.CyclotomicRemainder

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.DyadicRemainder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR

/-!
# Paired coefficients in a dyadic cyclotomic remainder

Reducing a polynomial of length `2 * m` modulo `X ^ m + 1` subtracts
the upper block of coefficients from the lower block. The construction
and the coefficient formulas work over every commutative ring.
-/

noncomputable section

namespace CirculantHadamard.DyadicRemainder

open Polynomial Finset

variable {R : Type uR} [CommRing R]

theorem degree_coefficientPolynomial_lt (n : ℕ) (c : ℕ → R) :
    (coefficientPolynomial n c).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  simp only [coefficientPolynomial_coeff, ite_eq_right (not_lt.mpr hj)]

theorem degree_remainder_lt (m : ℕ) (c : ℕ → R) :
    (remainder m c).degree < (m : WithBot ℕ) :=
  degree_coefficientPolynomial_lt m _

theorem remainder_eq_sub (m : ℕ) (c : ℕ → R) :
    remainder m c = coefficientPolynomial m c -
      coefficientPolynomial m (fun i => c (i + m)) := by
  simp only [remainder, coefficientPolynomial, monomial_sub, sum_sub_distrib]

/-- Split the coefficient polynomial into its lower and upper blocks. -/
theorem coefficientPolynomial_two_mul (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
  classical
  calc
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
        ∑ i ∈ range m, monomial (m + i) (c (m + i)) := by
      rw [two_mul]
      exact sum_range_add (fun i => monomial i (c i)) m m
    _ = coefficientPolynomial m c +
        X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
      congr 1
      simp only [coefficientPolynomial, mul_sum, X_pow_mul_monomial]
      apply sum_congr rfl
      intro i _
      rw [Nat.add_comm m i]

/-- The explicit quotient/remainder equation before applying monic division. -/
theorem remainder_add_mul (m : ℕ) (c : ℕ → R) :
    remainder m c + (X ^ m + 1) *
      coefficientPolynomial m (fun i => c (i + m)) = coefficientPolynomial (2 * m) c := by
  rw [remainder_eq_sub, add_mul, one_mul,
    add_comm (X ^ m * coefficientPolynomial m (fun i => c (i + m)))
      (coefficientPolynomial m (fun i => c (i + m))),
    ← add_assoc, sub_add_cancel]
  exact (coefficientPolynomial_two_mul m c).symm

/-- The canonical monic remainder is exactly the paired coefficient difference. -/
theorem coefficientPolynomial_modByMonic {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c %ₘ (X ^ m + 1) = remainder m c := by
  nontriviality R
  have hmonic : (X ^ m + (1 : R[X])).Monic := by
    simpa only [C_1] using (monic_X_pow_add_C (1 : R) hm.ne')
  apply (div_modByMonic_unique
    (coefficientPolynomial m (fun i => c (i + m))) (remainder m c) hmonic ?_).2
  refine ⟨remainder_add_mul m c, ?_⟩
  have hdegree : (X ^ m + (1 : R[X])).degree = (m : WithBot ℕ) := by
    simpa only [C_1] using (degree_X_pow_add_C hm (1 : R))
  rw [hdegree]
  exact degree_remainder_lt m c

/-- The dyadic cyclotomic polynomial has the expected two terms. -/
theorem cyclotomic_two_pow_succ (R : Type uR) [CommRing R] (k : ℕ) :
    cyclotomic (2 ^ (k + 1)) R = (X : R[X]) ^ (2 ^ k) + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, geom_sum_two]

/-- The remainder statement specialized to the dyadic cyclotomic polynomial. -/
theorem coefficientPolynomial_modByMonic_cyclotomic (k : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 ^ (k + 1)) c %ₘ cyclotomic (2 ^ (k + 1)) R =
      remainder (2 ^ k) c := by
  rw [cyclotomic_two_pow_succ, pow_succ, Nat.mul_comm (2 ^ k) 2]
  exact coefficientPolynomial_modByMonic (pow_pos (by decide : 0 < (2 : ℕ)) k) c

end CirculantHadamard.DyadicRemainder

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedEisenstein ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uA uB

/-!
# Eisenstein polynomials for the ramified cyclotomic extension

The maximal ideal is generated by the actual natural prime `p`.  We transport
the integer coefficient divisibilities and prove separately that the constant
term `p` is outside the square of the maximal ideal.  This yields irreducibility
over the local base, and hence the minimal polynomial of an actual primitive
root in any faithful domain extension.
-/

noncomputable section

namespace CirculantHadamard.RamifiedEisenstein

open Polynomial

theorem shifted_monic (A : Type uA) [CommRing A] (p k : ℕ) :
    (shifted A p k).Monic := by
  simpa only [shifted, C_1] using
    (cyclotomic.monic (p ^ (k + 1)) A).comp_X_add_C (1 : A)

theorem shifted_natDegree (A : Type uA) [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).natDegree = (p - 1) * p ^ k := by
  rw [shifted, natDegree_comp, show (X + 1 : A[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem cyclotomic_natDegree (A : Type uA) [CommRing A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (cyclotomic (p ^ (k + 1)) A).natDegree = (p - 1) * p ^ k := by
  rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem shifted_coeff_zero (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).coeff 0 = (p : A) := by
  rw [shifted, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime_pow_eq_geom_sum hp, eval_add, eval_X, eval_one, zero_add,
    eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    Nat.smul_one_eq_cast]

theorem shifted_isWeaklyEisensteinAt (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).IsWeaklyEisensteinAt (Ideal.span {(p : A)}) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k).isWeaklyEisensteinAt.map
    (Int.castRingHom A)
  simpa [shifted, Ideal.submodule_span_eq, Ideal.map_span, Polynomial.map_comp] using h

section Local

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A] [IsLocalRing A]
  {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem shifted_isEisensteinAt :
    (shifted A p k).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpu : ¬ IsUnit (p : A) :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : A) hp0 hmax).not_isUnit
  apply (shifted_monic A p k).isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top inferInstance)
  · intro i hi
    rw [hmax]
    exact (shifted_isWeaklyEisensteinAt A hp k).mem hi
  · rw [shifted_coeff_zero A hp k, hmax, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro h
    have h21 : (2 : ℕ) ≤ 1 := (pow_dvd_pow_iff hp0 hpu).mp (by simpa using h)
    exact (by decide : ¬ (2 : ℕ) ≤ 1) h21

theorem shifted_irreducible : Irreducible (shifted A p k) := by
  apply (shifted_isEisensteinAt A hp k hmax).irreducible inferInstance
    (shifted_monic A p k).isPrimitive
  rw [shifted_natDegree A hp k]
  exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)

theorem cyclotomic_irreducible : Irreducible (cyclotomic (p ^ (k + 1)) A) := by
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : A))).mp
  change Irreducible ((cyclotomic (p ^ (k + 1)) A).comp (X + C (1 : A)))
  simpa only [shifted, C_1] using shifted_irreducible A hp k hmax

end Local

section DVR

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem cyclotomic_prime : Prime (cyclotomic (p ^ (k + 1)) A) :=
  irreducible_iff_prime.mp (cyclotomic_irreducible A hp k hmax)

theorem cyclotomic_adjoinRoot_isDomain :
    IsDomain (AdjoinRoot (cyclotomic (p ^ (k + 1)) A)) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic_prime A hp k hmax)

end DVR

end CirculantHadamard.RamifiedEisenstein

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedUnit ----
namespace OAI

universe uR uS

/-!
# The unit factor in a ramified polynomial relation

The exact constant coefficient, together with divisibility of the other
nonleading coefficients, gives a factor with constant coefficient one.
At a root in the maximal ideal this factor is a unit.
-/

noncomputable section

namespace CirculantHadamard.RamifiedUnit

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

/-- The polynomial form of the unit factor in an Eisenstein relation. -/
theorem exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f.eraseLead := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    by_cases hi : i = f.natDegree
    · simp [eraseLead_coeff, hi]
    · rw [eraseLead_coeff_of_ne _ hi]
      by_cases hilt : i < f.natDegree
      · exact hcoeff i hilt
      · rw [coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt hilt) (Ne.symm hi))]
        exact dvd_zero a
  obtain ⟨q, hq⟩ := hdvd
  have hqzero : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ ha
    have hh := congrArg (fun g : R[X] => g.coeff 0) hq
    simpa [eraseLead_coeff_of_ne _ (Nat.ne_of_lt hdeg), hzero] using hh.symm
  have hqrepr : 1 + X * q.divX = q := by
    simpa [hqzero, add_comm] using X_mul_divX_add q
  refine ⟨q.divX, ?_⟩
  calc
    f = f.eraseLead + X ^ f.natDegree := by
      simpa [hf] using (eraseLead_add_C_mul_X_pow f).symm
    _ = X ^ f.natDegree + C a * (1 + X * q.divX) := by
      rw [hq, hqrepr]
      exact add_comm _ _

variable [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A root in the maximal ideal turns the normalized polynomial factor into
a unit, and therefore expresses the constant coefficient as a unit times
the ramified power. -/
theorem exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := exists_polynomial_unit_factor f a ha hf hdeg hzero hcoeff
  have hrel : z ^ f.natDegree + algebraMap R S a * (1 + z * aeval z q) = 0 := by
    rw [hq] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] using hroot
  have hn : -(z * aeval z q) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.maximalIdeal S).neg_mem
      ((IsLocalRing.maximalIdeal S).mul_mem_right _ hz)
  have hu : IsUnit (1 + z * aeval z q) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(z * aeval z q)) hn
  obtain ⟨v, hv⟩ := hu
  have hpow : z ^ f.natDegree = -(algebraMap R S a * (v : S)) := by
    rw [← hv] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  refine ⟨-v⁻¹, ?_⟩
  rw [Units.val_neg, hpow, neg_mul_neg]
  calc
    algebraMap R S a = algebraMap R S a * ((v : S) * ↑v⁻¹) := by simp
    _ = ↑v⁻¹ * (algebraMap R S a * (v : S)) := by ac_rfl

end CirculantHadamard.RamifiedUnit

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedLocal ----
namespace OAI

universe uA

/-!
# The actual ramified cyclotomic local ring

We adjoin a root of the prime-power cyclotomic polynomial to the given
characteristic-zero DVR. Every maximal ideal of this finite integral extension
is shown to be generated by the actual element `root - 1`.
-/

noncomputable section

namespace CirculantHadamard.RamifiedLocal

open Polynomial

theorem uniformizer_aeval_shifted (A : Type uA) [CommRing A] (p k : ℕ) :
    aeval (uniformizer A p k) (RamifiedEisenstein.shifted A p k) = 0 := by
  simp only [RamifiedEisenstein.shifted, aeval_comp, map_add, aeval_X, map_one,
    uniformizer, sub_add_cancel, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- Every element is a scalar modulo the actual root-minus-one parameter. -/
theorem exists_scalar_add_uniformizer_mul (A : Type uA) [CommRing A] (p k : ℕ)
    (x : Extension A p k) :
    ∃ a : A, ∃ b : Extension A p k,
      x = algebraMap A (Extension A p k) a + uniformizer A p k * b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  have hroot : (q.map (algebraMap A (Extension A p k))).eval
      (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) =
      AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A) q := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq]
  have hone : (q.map (algebraMap A (Extension A p k))).eval 1 =
      algebraMap A (Extension A p k) (q.eval 1) := by
    rw [eval_map, eval₂_at_one]
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    (q.map (algebraMap A (Extension A p k)))
  rw [hroot, hone] at hdiv
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨q.eval 1, b, ?_⟩
  change _ = _ + (AdjoinRoot.root _ - 1) * b
  rw [← hb]
  simp

theorem prime_mem_span_uniformizer (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p : Extension A p k) ∈ Ideal.span {uniformizer A p k} := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    ((cyclotomic (p ^ (k + 1)) A).map (algebraMap A (Extension A p k)))
  have hdiv' : uniformizer A p k ∣ -(p : Extension A p k) := by
    simpa only [uniformizer, eval_map, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, eval₂_one_cyclotomic_prime_pow, zero_sub] using hdiv
  exact (Ideal.neg_mem_iff (Ideal.span {uniformizer A p k})).mp
    (Ideal.mem_span_singleton.mpr hdiv')

section LocalBase

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem isDomain : IsDomain (Extension A p k) :=
  RamifiedEisenstein.cyclotomic_adjoinRoot_isDomain A hp k hmax

omit [CharZero A] in
/-- Every maximal ideal of the genuine quotient is the same principal ideal. -/
theorem maximal_eq_span_uniformizer [CharZero A] (M : Ideal (Extension A p k)) [M.IsMaximal] :
    M = Ideal.span {uniformizer A p k} := by
  have hcomap : M.comap (algebraMap A (Extension A p k)) = Ideal.span {(p : A)} :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M)).trans hmax
  have hmap : (Ideal.span {(p : A)}).map (algebraMap A (Extension A p k)) ≤ M := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [hcomap]
  have hpow := Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      (RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k)
      (uniformizer_aeval_shifted A p k) (RamifiedEisenstein.shifted_monic A p k)
      _ (le_refl _)
  have hpi : uniformizer A p k ∈ M :=
    (inferInstance : M.IsPrime).mem_of_pow_mem _ (hmap hpow)
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, hxform⟩ := exists_scalar_add_uniformizer_mul A p k x
    have haM : algebraMap A (Extension A p k) a ∈ M := by
      have hh := M.sub_mem hx (Ideal.mul_mem_right b M hpi)
      simpa [hxform] using hh
    have ha : a ∈ Ideal.span {(p : A)} := by
      rw [← hcomap]
      exact haM
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    have hap : algebraMap A (Extension A p k) a ∈
        Ideal.span {uniformizer A p k} := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ (prime_mem_span_uniformizer A hp k)
    rw [hxform]
    exact (Ideal.span {uniformizer A p k}).add_mem hap
      (Ideal.mul_mem_right b _ (Ideal.subset_span (Set.mem_singleton _)))
  · exact (Ideal.span_singleton_le_iff_mem M).mpr hpi

theorem isLocalRing : IsLocalRing (Extension A p k) := by
  let : IsDomain (Extension A p k) := isDomain A hp k hmax
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Extension A p k)
  let : M.IsMaximal := hM
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  let : N.IsMaximal := hN
  exact (maximal_eq_span_uniformizer A hp k hmax N).trans
    (maximal_eq_span_uniformizer A hp k hmax M).symm

variable [IsLocalRing (Extension A p k)]

theorem maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (Extension A p k) = Ideal.span {uniformizer A p k} :=
  maximal_eq_span_uniformizer A hp k hmax _

theorem exists_unit_mul_uniformizer_pow :
    ∃ u : (Extension A p k)ˣ,
      (p : Extension A p k) = (u : Extension A p k) *
        uniformizer A p k ^ ((p - 1) * p ^ k) := by
  have hd : 0 < (RamifiedEisenstein.shifted A p k).natDegree := by
    rw [RamifiedEisenstein.shifted_natDegree A hp k]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)
  have hcoeff : ∀ i < (RamifiedEisenstein.shifted A p k).natDegree,
      (p : A) ∣ (RamifiedEisenstein.shifted A p k).coeff i := by
    intro i hi
    exact Ideal.mem_span_singleton.mp
      ((RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k).mem hi)
  have hpi : uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k) := by
    rw [maximalIdeal_eq_span A hp k hmax]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨u, hu⟩ := RamifiedUnit.exists_unit_mul_root_pow
    (RamifiedEisenstein.shifted A p k) (p : A) (Nat.cast_ne_zero.mpr hp.ne_zero)
    (RamifiedEisenstein.shifted_monic A p k) hd
    (RamifiedEisenstein.shifted_coeff_zero A hp k) hcoeff
    (uniformizer A p k) hpi (uniformizer_aeval_shifted A p k)
  exact ⟨u, by simpa only [map_natCast, RamifiedEisenstein.shifted_natDegree A hp k] using hu⟩

omit hmax [CharZero A] [IsLocalRing (Extension A p k)] in
theorem algebraMap_injective [CharZero A] [IsLocalRing (Extension A p k)] : Function.Injective (algebraMap A (Extension A p k)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  apply Polynomial.degree_ne_of_natDegree_ne
  rw [RamifiedEisenstein.cyclotomic_natDegree A hp k]
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))

theorem uniformizer_ne_zero : uniformizer A p k ≠ 0 := by
  intro hzero
  have hpS : (p : Extension A p k) ≠ 0 := by
    intro hpzero
    have : algebraMap A (Extension A p k) (p : A) =
        algebraMap A (Extension A p k) 0 := by simpa using hpzero
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : A) ≠ 0)
      (algebraMap_injective A hp k this)
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  have hd : (p - 1) * p ^ k ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))
  exact hpS (by simpa only [hzero, zero_pow hd, mul_zero] using hu)

variable [IsDomain (Extension A p k)]

theorem isDiscreteValuationRing : IsDiscreteValuationRing (Extension A p k) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (uniformizer_ne_zero A hp k hmax) (maximalIdeal_eq_span A hp k hmax)

omit [IsLocalRing (Extension A p k)] in
theorem addVal_prime [IsDiscreteValuationRing (Extension A p k)] :
    IsDiscreteValuationRing.addVal (Extension A p k) (p : Extension A p k) =
      (((p - 1) * p ^ k : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  exact LocalDVR.addVal_eq_of_unit_mul_uniformizer_pow
    (maximalIdeal_eq_span A hp k hmax) hu

end LocalBase

end CirculantHadamard.RamifiedLocal

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderCyclotomicDivisibility ----
namespace OAI

universe uA

/-!
# Dyadic divisibility of opposite coefficient differences

We evaluate the actual integer cyclic group ring in the cyclotomic extension
of the integers localized at two. The norm identity forces divisibility in
that DVR. Its free monic presentation then transfers this divisibility to the
paired coefficient differences, and localization reflects it to the integers.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

/-- The canonical polynomial with the literal integer coefficients of a cyclic
element evaluates to the same element in the cyclotomic quotient. -/
theorem integerCyclotomicEvaluation_coefficientPolynomial
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by
  classical
  rw [integerCyclotomicEvaluation_apply]
  simp only [DyadicRemainder.coefficientPolynomial, map_sum,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
    algebraMap_int_eq, Int.coe_castRingHom, map_intCast]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ a : Fin (n + 1), (T.coeff a : AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val) =
        ∑ a : Fin (n + 1), (T.coeff (Fin.ofNat (n + 1) a.val) :
          AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val
      simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

/-- A scalar norm of the stated dyadic size forces each opposite coefficient
difference to be divisible by its square-root dyadic factor. No condition on
the parity of the coefficients, or separate positivity of `u`, is required. -/
theorem dyadic_difference_dvd (k t u : ℕ)
    (T : CyclicRing.Elem ℤ (2 ^ (k + 1))) (hu : Odd u)
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 ^ (k + 1))) -
        T.coeff ((j.val + 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  let A := IntegerTwoLocal.Ring
  let S := RamifiedLocal.Extension A 2 k
  let : IsDomain S := RamifiedLocal.isDomain A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsLocalRing S := RamifiedLocal.isLocalRing A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsDiscreteValuationRing S := RamifiedLocal.isDiscreteValuationRing A
    Nat.prime_two k IntegerTwoLocal.maximalIdeal_eq_span
  let : CharZero S := charZero_of_injective_algebraMap
    (RamifiedLocal.algebraMap_injective A Nat.prime_two k)
  have hn : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
  let : NeZero (2 ^ (k + 1)) := ⟨hn.ne'⟩
  let x : S := integerCyclotomicEvaluation A (2 ^ (k + 1)) T
  have huS : IsUnit ((u : S) ^ 2) := by
    have hunit := (IntegerTwoLocal.isUnit_natCast_of_odd u hu).map
      (algebraMap A S)
    have huS' : IsUnit (u : S) := by simpa only [map_natCast] using hunit
    exact huS'.pow 2
  have hnormS : x * RamifiedConjugation.cyclotomicConjugation A (2 ^ (k + 1)) hn x =
      (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
    have hcast : (((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) : S) =
        (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
      exact (Int.cast_natCast (R := S) (2 ^ (2 * t) * u ^ 2)).trans
        (show ((2 ^ (2 * t) * u ^ 2 : ℕ) : S) =
            (2 : S) ^ (2 * t) * (u : S) ^ 2 by
          exact (Nat.cast_mul (α := S) (2 ^ (2 * t)) (u ^ 2)).trans
            (congrArg₂ (fun a b : S => a * b)
              ((Nat.cast_pow (α := S) 2 (2 * t)).trans
                (congrArg (fun a : S => a ^ (2 * t)) (Nat.cast_two (R := S))))
              (Nat.cast_pow (α := S) u 2)))
    exact (integerCyclotomicEvaluation_norm A (2 ^ (k + 1)) hn T
      ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) hnorm).trans hcast
  have hdiv : (2 : S) ^ t ∣ x :=
    RamifiedConjugation.cyclotomic_pow_dvd_of_norm_eq A (2 ^ (k + 1)) hn
      2 x ((u : S) ^ 2) t huS hnormS
  let c : ℕ → A := fun i => algebraMap ℤ A (T.coeff (i : ZMod (2 ^ (k + 1))))
  have hpoly : algebraMap A S ((2 : A) ^ t) ∣
      AdjoinRoot.mk (cyclotomic (2 ^ (k + 1)) A)
        (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) := by
    simpa only [x, map_pow, map_ofNat,
      integerCyclotomicEvaluation_coefficientPolynomial, c,
      eq_intCast] using hdiv
  intro j
  have hcoeff := CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (2 ^ (k + 1)) A) (cyclotomic.monic _ _) ((2 : A) ^ t)
    (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) hpoly j.val
  rw [DyadicRemainder.coefficientPolynomial_modByMonic_cyclotomic,
    DyadicRemainder.remainder_coeff _ _ _ j.val_lt] at hcoeff
  apply integer_prime_pow_dvd_of_localization (A := A) (P := IntegerTwoLocal.ideal)
    Nat.prime_two rfl t
  simpa only [c, map_sub, Nat.cast_ofNat] using hcoeff

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderHalving ----
namespace OAI

/-!
# Halving an odd-coefficient dyadic group-ring element

The integer averaging lemmas retain the original paired coefficients.
The group-ring step uses their actual quotient fiber sums and the concrete
cyclotomic divisibility theorem; the ring is not assumed to be a domain.
-/

namespace CirculantHadamard

open CyclicRing

theorem two_mul_pairAverage {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    2 * pairAverage a b = a + b := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  dsimp [pairAverage]
  omega

/-- Congruent odd coefficients modulo four have an odd integral average. -/
theorem odd_pairAverage {a b : ℤ} (hb : Odd b) (hab : (4 : ℤ) ∣ a - b) :
    Odd (pairAverage a b) := by
  obtain ⟨r, hr⟩ := hb
  obtain ⟨s, hs⟩ := hab
  refine ⟨r + s, ?_⟩
  dsimp [pairAverage]
  omega

theorem odd_pairAverage_of_two_pow_dvd {a b : ℤ} {t : ℕ}
    (hb : Odd b) (ht : 2 ≤ t) (hab : (2 : ℤ) ^ t ∣ a - b) :
    Odd (pairAverage a b) := by
  apply odd_pairAverage hb
  have hpow : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ t := pow_dvd_pow 2 ht
  exact (show (4 : ℤ) ∣ (2 : ℤ) ^ t from hpow).trans hab

theorem normScalar_halving (u : ℤ) {t : ℕ} (ht : 1 ≤ t) :
    (2 : ℤ) ^ (2 * t) * u ^ 2 =
      4 * ((2 : ℤ) ^ (2 * (t - 1)) * u ^ 2) := by
  have hexp : 2 * t = 2 * (t - 1) + 2 := by omega
  rw [hexp, pow_add]
  ring

/-- Cancellation takes place in each integer coefficient. A cyclic group
ring has zero divisors, which are irrelevant to this scalar cancellation. -/
theorem four_smul_cancel {m : ℕ} {S T : Elem ℤ m}
    (h : (4 : ℤ) • S = (4 : ℤ) • T) : S = T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  have hj := congrArg (fun f : Elem ℤ m => f.coeff j) h
  change 4 * S.coeff j = 4 * T.coeff j at hj
  omega

theorem norm_of_double_norm {m : ℕ} [NeZero m] (T : Elem ℤ m) (c : ℤ)
    (h : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) = scalar m (4 * c)) :
    T * ringStar T = scalar m c := by
  have hstar : ringStar ((2 : ℤ) • T) = (2 : ℤ) • ringStar T := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change star ((2 : ℤ) * T.coeff (-j)) = (2 : ℤ) * star (T.coeff (-j))
    simp only [star_trivial]
  have hfour : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) =
      (4 : ℤ) • (T * ringStar T) := by
    rw [hstar, smul_mul_assoc, mul_smul_comm, smul_smul]
    rfl
  have hscalar : scalar m (4 * c) = (4 : ℤ) • scalar m c := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change (scalar m (4 * c)).coeff j = (4 : ℤ) * (scalar m c).coeff j
    by_cases hj : j = 0 <;> simp [scalar_apply, hj]
  apply four_smul_cancel
  rw [← hfour, h, hscalar]

/-- Odd coefficients make the literal projected fiber sums exactly twice the
integer averages. This is an identity for the actual cyclic quotient map. -/
theorem cyclicProjection_eq_two_smul_halvePairs {m : ℕ} [NeZero m]
    (h : m ∣ 2 * m) (T : Elem ℤ (2 * m)) (hodd : ∀ j, Odd (T.coeff j)) :
    cyclicProjection ℤ h T = (2 : ℤ) • halvePairs T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  rw [cyclicProjection_double_apply (NeZero.pos m) h]
  change _ = 2 * pairAverage _ _
  exact (two_mul_pairAverage (hodd _) (hodd _)).symm

/-- Projecting and dividing by two divides the scalar norm by four. All
coefficient and star identities are consequences of the actual quotient. -/
theorem halvePairs_norm {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (T : Elem ℤ (2 * m)) (c : ℤ) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) (4 * c)) :
    halvePairs T * ringStar (halvePairs T) = scalar m c := by
  have hdiv : m ∣ 2 * m := ⟨2, Nat.mul_comm 2 m⟩
  have hproj := cyclicProjection_norm hdiv hnorm
  rw [cyclicProjection_eq_two_smul_halvePairs hdiv T hodd] at hproj
  exact norm_of_double_norm (halvePairs T) c hproj

/-- Algebraic halving with paired divisibility. In the dyadic case, cyclotomic
evaluation supplies this divisibility from the norm equation. -/
theorem halvePairs_odd_norm_of_pair_divisibility {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (t u : ℕ) (T : Elem ℤ (2 * m)) (ht : 2 ≤ t)
    (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
    (hpair : ∀ j : ZMod m, (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 * m)) - T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) :
    (∀ j, Odd ((halvePairs T).coeff j)) ∧
      halvePairs T * ringStar (halvePairs T) =
        scalar m ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  constructor
  · intro j
    exact odd_pairAverage_of_two_pow_dvd (hodd _) ht (hpair j)
  · apply halvePairs_norm T _ hodd
    have hs : ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) =
        4 * ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        normScalar_halving (u : ℤ) (show 1 ≤ t by omega)
    rw [← hs]
    exact hnorm

/-- The actual dyadic order-halving step. The paired divisibility is supplied
by cyclotomic evaluation and localization, not assumed in this statement.
The constructed witness is the literal paired average `halvePairs`. -/
theorem exists_odd_halving (k t u : ℕ) (T : Elem ℤ (2 ^ (k + 1)))
    (ht : 2 ≤ t) (hu : Odd u) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T =
      scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
      U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  have hstep (n : ℕ) [NeZero n] (hn : n = 2 * 2 ^ k) (S : Elem ℤ n)
      (hS : ∀ j, Odd (S.coeff j))
      (hnormS : S * ringStar S = scalar n ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
      (hpair : ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
        S.coeff (j.val : ZMod n) - S.coeff ((j.val + 2 ^ k : ℕ) : ZMod n)) :
      ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
        U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
    subst n
    exact ⟨halvePairs S,
      halvePairs_odd_norm_of_pair_divisibility t u S ht hS hnormS hpair⟩
  exact hstep (2 ^ (k + 1)) (pow_succ' 2 k) T hodd hnorm
    (dyadic_difference_dvd k t u T hu hnorm)

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ModEight ----
namespace OAI

universe uIota

/-!
# The odd-coefficient obstruction modulo eight

The identity coefficient of an integer cyclic norm is the sum of the actual
coefficient squares. Every odd square is one modulo eight. Consequently an
odd-coefficient element in a cyclic group of order divisible by eight cannot
have norm scalar `4 * u^2` with `u` odd. The divisibility hypothesis excludes
order four, so the explicit order-four example is not ruled out.
-/

namespace CirculantHadamard

open scoped BigOperators

/-- Every odd integer square is congruent to one modulo eight. -/
theorem odd_sq_mod_eight {a : ℤ} (ha : Odd a) :
    Int.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  nlinarith [hm]

/-- A finite sum of odd integer squares is congruent to the number of terms. -/
theorem sum_odd_sq_mod_eight {ι : Type uIota} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by
  classical
  revert ha
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Int.ModEq]
  · intro i s hi ih ha
    have hiOdd : Odd (a i) := ha i (Finset.mem_insert_self i s)
    have hsOdd : ∀ j ∈ s, Odd (a j) :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, add_comm (s.card : ℤ) 1] using
      (odd_sq_mod_eight hiOdd).add (ih hsOdd)

/-- The same congruence for all members of a finite type. -/
theorem sum_univ_odd_sq_mod_eight {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) :
    Int.ModEq 8 (∑ i, a i ^ 2) (Fintype.card ι : ℤ) := by
  simpa using sum_odd_sq_mod_eight Finset.univ a (fun i _ => ha i)

/-- A multiple of eight odd squares cannot sum to four times an odd square. -/
theorem odd_sq_sum_ne_four_mul_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℤ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ 4 * u ^ 2 := by
  have hc : (8 : ℤ) ∣ (Fintype.card ι : ℤ) :=
    Int.natCast_dvd_natCast.mpr hcard
  have hzero : Int.ModEq 8 (∑ i, a i ^ 2) 0 :=
    (sum_univ_odd_sq_mod_eight a ha).trans (Int.modEq_zero_iff_dvd.mpr hc)
  have hfour : Int.ModEq 8 (4 * u ^ 2) 4 := by
    simpa using (odd_sq_mod_eight hu).mul_left 4
  intro hsum
  rw [hsum] at hzero
  have hbad : Int.ModEq 8 (0 : ℤ) 4 := hzero.symm.trans hfour
  norm_num [Int.ModEq] at hbad

/-- Natural norm parameters are cast only after forming the literal scalar. -/
theorem odd_sq_sum_ne_four_mul_nat_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℕ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ ((4 * u ^ 2 : ℕ) : ℤ) := by
  simpa using odd_sq_sum_ne_four_mul_sq a ha hcard ((Int.odd_coe_nat u).mpr hu)

/-- The actual cyclic norm equation is impossible for an all-odd row when
the cyclic order is divisible by eight and the norm parameter is odd. -/
theorem odd_norm_four_impossible {n u : ℕ} [NeZero n]
    (hcard : 8 ∣ n) (hu : Odd u) (T : CyclicRing.Elem ℤ n)
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar n ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  have hsum : (∑ a : ZMod n, T.coeff a ^ 2) = ((4 * u ^ 2 : ℕ) : ℤ) := by
    rw [← cyclicNorm_identity_coeff T, hnorm]
    simp
  exact odd_sq_sum_ne_four_mul_nat_sq (fun a : ZMod n => T.coeff a) hodd
    (by simpa using hcard) hu hsum

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderDescent ----
namespace OAI

/-!
# Finite descent of an odd dyadic cyclic norm

The invariant `1 ≤ t` and `t + 2 ≤ k` records exactly the range needed to
halve an odd row until its norm is `4*u^2` while retaining a group order
divisible by eight. Every step invokes the concrete cyclotomic halving
theorem. The final step is the coefficient-square contradiction modulo eight.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

/-- An odd-coefficient dyadic cyclic norm cannot have two more group
exponents than norm half-exponents. No halving is performed when `t = 1`. -/
theorem odd_norm_impossible {k t u : ℕ}
    (ht : 1 ≤ t) (hkt : t + 2 ≤ k) (hu : Odd u)
    (T : Elem ℤ (2 ^ k)) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    False := by
  suffices main : ∀ t k : ℕ, 1 ≤ t → t + 2 ≤ k →
      ∀ T : Elem ℤ (2 ^ k), (∀ a, Odd (T.coeff a)) →
        T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) →
          False by
    exact main t k ht hkt T hodd hnorm
  intro t
  induction t with
  | zero =>
      intro k ht
      omega
  | succ t ih =>
      intro k ht hkt T hodd hnorm
      cases t with
      | zero =>
          have hcard : 8 ∣ 2 ^ k := by
            have hpow : (2 : ℕ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
            norm_num at hpow
            exact hpow
          apply odd_norm_four_impossible hcard hu T hodd
          simpa only [Nat.zero_add, Nat.mul_one, Nat.reducePow] using hnorm
      | succ t =>
          cases k with
          | zero => omega
          | succ k =>
              obtain ⟨U, hUodd, hUnorm⟩ := exists_odd_halving
                k (t + 1 + 1) u T (by omega) hu hodd hnorm
              apply ih k (by omega) (by omega) U hUodd
              simpa only [Nat.add_sub_cancel] using hUnorm

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderReduction ----
namespace OAI

/-!
# The order of an actual circulant sign Hadamard matrix

The matrix supplies its literal integer sign row. Its positive even square
order has a two-adic decomposition. Projecting the actual row gives odd
coefficients, and the proved cyclotomic halving descent excludes every
two-adic exponent except two, without any coefficient-divisibility or descent
assumption.
-/

namespace CirculantHadamard

/-- Every nontrivial actual real circulant sign Hadamard matrix has order
`4 * u^2` for a positive odd natural number `u`. -/
theorem order_reduction {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨hsquare, heven⟩ := order_square_even hn h
  obtain ⟨s, u, hs, huPos, hu, horder⟩ :=
    exists_two_adic_square_decomposition_of_positive_square hsquare heven
  obtain ⟨f, hf, hnorm⟩ := (exists_cyclicSignRow_iff_real (n := n)).2 h
  have hsOne : s = 1 := by
    by_contra hsOne
    have hsTwo : 2 ≤ s := by omega
    obtain ⟨T, hodd, hTnorm⟩ :=
      exists_odd_cyclic_projection hu horder f hf hnorm
    exact odd_norm_impossible (by omega : 1 ≤ s) (by omega : s + 2 ≤ 2 * s)
      hu T hodd hTnorm
  refine ⟨u, huPos, hu, ?_⟩
  simpa [hsOne] using horder

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryBlocks ----
namespace OAI

universe uR uS

/-!
# The actual four-block decomposition and partial evaluations

The Chinese remainder equivalence transports the actual cyclic group ring,
not just a coefficient count. Coefficients of its four slices are the original
signs. Partial evaluation is a ring homomorphism defined on the product group
algebra and intertwines coefficient conjugation with index reversal.
-/

noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

theorem crt_ringStar {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) :
    crt R u hu (ringStar f) = groupStar (crt R u hu f) := by
  ext a
  simp only [crt_apply, ringStar_apply, groupStar_apply, map_neg]

theorem crt_norm {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) (N : ℕ)
    (hnorm : f * ringStar f = (N : Elem R (4 * u ^ 2))) :
    crt R u hu f * groupStar (crt R u hu f) = (N : ProductElem R (u ^ 2)) := by
  rw [← crt_ringStar hu, ← map_mul, hnorm, map_natCast]

theorem blocks_signs {m : ℕ} [NeZero m] (f : ProductElem ℤ m)
    (hf : ∀ a, IsSign (f.coeff a)) : ∀ j b, IsSign ((blocks f j).coeff b) :=
  fun j b => hf (j, b)

theorem crt_blocks_signs {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hf : ∀ a, IsSign (f.coeff a)) :
    ∀ j b, IsSign ((blocks (crt ℤ u hu f) j).coeff b) := by
  intro j b
  rw [blocks_apply, crt_apply]
  exact hf ((crtIndex u hu).symm (j, b))

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

variable [NeZero m]

/-- The four coefficients are summed, with no loss of the second coordinate. -/
theorem partialEval_apply (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by
  classical
  have hexp : f = ∑ a : ZMod 4 × ZMod m, AddMonoidAlgebra.single a (f.coeff a) := by
    simpa only [AddMonoidAlgebra.sum_coeff_single] using
      (Finsupp.sum_fintype f.coeff AddMonoidAlgebra.single
        (fun a => AddMonoidAlgebra.single_zero a))
  calc
    (partialEval m φ z hz f).coeff b =
        (partialEval m φ z hz (∑ a : ZMod 4 × ZMod m,
          AddMonoidAlgebra.single a (f.coeff a))).coeff b :=
            congrArg (fun g => (partialEval m φ z hz g).coeff b) hexp
    _ = ∑ a : ZMod 4 × ZMod m,
        (AddMonoidAlgebra.single a.2 (φ (f.coeff a) * z ^ a.1.val)).coeff b := by
      rw [map_sum]
      simp only [partialEval_single, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem partialEval_four (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) :
    partialEval m φ z hz f = mappedBlock m φ f 0 + z • mappedBlock m φ f 1 +
      z ^ 2 • mappedBlock m φ f 2 + z ^ 3 • mappedBlock m φ f 3 := by
  ext b
  rw [partialEval_apply]
  change (∑ j : Fin 4, φ (f.coeff (j, b)) * z ^ j.val) =
    φ (f.coeff (0, b)) + z * φ (f.coeff (1, b)) +
      z ^ 2 * φ (f.coeff (2, b)) + z ^ 3 * φ (f.coeff (3, b))
  rw [Fin.sum_univ_four]
  change φ (f.coeff (0, b)) * z ^ 0 + φ (f.coeff (1, b)) * z ^ 1 +
    φ (f.coeff (2, b)) * z ^ 2 + φ (f.coeff (3, b)) * z ^ 3 = _
  simp only [pow_zero, pow_one, one_mul, mul_comm]

theorem partialEval_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ 1 (by simp) f = mappedBlock m φ f 0 + mappedBlock m φ f 1 +
      mappedBlock m φ f 2 + mappedBlock m φ f 3 := by
  simpa using partialEval_four m φ 1 (by simp) f

theorem partialEval_neg_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ (-1) (by norm_num) f = mappedBlock m φ f 0 - mappedBlock m φ f 1 +
      mappedBlock m φ f 2 - mappedBlock m φ f 3 := by
  have hn2 : (-1 : S) ^ 2 = 1 := by norm_num
  have hn3 : (-1 : S) ^ 3 = -1 := by norm_num
  simpa only [hn2, hn3, one_smul, neg_one_smul, sub_eq_add_neg]
    using partialEval_four m φ (-1) (by norm_num) f

/-- The Gaussian coefficient ring can use its actual imaginary unit directly. -/
theorem partialEval_fourthRoot (φ : R →+* S) (i : S) (hi : i ^ 2 = -1)
    (f : ProductElem R m) :
    partialEval m φ i (fourthRoot_pow_four i hi) f =
      mappedBlock m φ f 0 + i • mappedBlock m φ f 1 -
        mappedBlock m φ f 2 - i • mappedBlock m φ f 3 := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  simpa only [hi, hi3, neg_one_smul, neg_smul, one_smul, sub_eq_add_neg]
    using partialEval_four m φ i (fourthRoot_pow_four i hi) f

end Evaluation

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

/-- Intertwining is proved on the actual ring maps, with both parts of the star. -/
theorem partialEval_groupStar (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by
  have hs (a : ZMod 4 × ZMod m) (r : R) :
      partialEval m φ z hz (groupStar (AddMonoidAlgebra.single a r)) =
        ringStar (partialEval m φ z hz (AddMonoidAlgebra.single a r)) := by
    rw [groupStar_single, partialEval_single, partialEval_single, ringStar_single]
    change AddMonoidAlgebra.single (-a.2) (φ (star r) * z ^ (-a.1).val) =
      AddMonoidAlgebra.single (-a.2) (star (φ r * z ^ a.1.val))
    rw [hφ, hchar, star_mul, mul_comm]
  have he : (partialEval m φ z hz).comp groupStarRingHom =
      (ringStarRingHom m).comp (partialEval m φ z hz) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      exact hs 0 r
    · intro a
      exact hs a 1
  exact RingHom.congr_fun he f

theorem one_character_star : ∀ a : ZMod 4, (1 : S) ^ (-a).val = star ((1 : S) ^ a.val) := by
  intro a
  simp

theorem neg_one_character_star :
    ∀ a : ZMod 4, (-1 : S) ^ (-a).val = star ((-1 : S) ^ a.val) := by
  intro a
  fin_cases a
  · change (-1 : S) ^ 0 = star ((-1 : S) ^ 0)
    simp
  · change (-1 : S) ^ 3 = star ((-1 : S) ^ 1)
    norm_num
  · change (-1 : S) ^ 2 = star ((-1 : S) ^ 2)
    norm_num
  · change (-1 : S) ^ 1 = star ((-1 : S) ^ 3)
    norm_num

theorem fourthRoot_character_star (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  intro a
  fin_cases a
  · change i ^ 0 = star (i ^ 0)
    simp
  · change i ^ 3 = star (i ^ 1)
    simp [hi3, hstar]
  · change i ^ 2 = star (i ^ 2)
    rw [hi]
    simp
  · change i ^ 1 = star (i ^ 3)
    simp [hi3, hstar]

end Star

end CirculantHadamard.BinaryBlocks

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryCoefficients ----
namespace OAI

universe uG uR

namespace CirculantHadamard
namespace BinaryCoefficients

theorem two_halfSum {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfSum x y = x + y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfSum]

theorem two_halfDiff {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfDiff x y = x - y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfDiff]

theorem halfDiff_eq {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    halfDiff x y = halfSum x y - y := by
  linarith [two_halfSum hx hy, two_halfDiff hx hy]

theorem two_signOffset {x : ℤ} (hx : IsSign x) :
    2 * signOffset x = x - 1 := by
  rcases hx with rfl | rfl <;> norm_num [signOffset]

theorem sign_eq_one_add {x : ℤ} (hx : IsSign x) :
    x = 1 + 2 * signOffset x := by
  linarith [two_signOffset hx]

variable {G : Type uG}

variable [Finite G]

theorem two_a {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • a H = H 0 + H 2 := by
  ext x
  change 2 * halfSum (H 0 x) (H 2 x) = H 0 x + H 2 x
  exact two_halfSum (hH 0 x) (hH 2 x)

theorem two_b {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • b H = H 1 + H 3 := by
  ext x
  change 2 * halfSum (H 1 x) (H 3 x) = H 1 x + H 3 x
  exact two_halfSum (hH 1 x) (hH 3 x)

theorem two_c {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • c H = H 0 + H 1 + H 2 + H 3 := by
  rw [c, smul_add, two_a hH, two_b hH]
  abel

theorem two_d {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • d H = H 0 - H 1 + H 2 - H 3 := by
  rw [d, smul_sub, two_a hH, two_b hH]
  abel

theorem gOver_eq_ab {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    gOver i H = castCoeffs (a H) + i • castCoeffs (b H) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  simp only [gOver, liftPair, gReal, gImag, a, b, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  rw [halfDiff_eq (hH 0 x) (hH 2 x), halfDiff_eq (hH 1 x) (hH 3 x)]
  push_cast
  ring

theorem two_gOver {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : R) • gOver i H = castCoeffs (H 0) + i • castCoeffs (H 1) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  have h0 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 0 x) (hH 2 x))
  have h1 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 1 x) (hH 3 x))
  push_cast at h0 h1
  simp only [gOver, liftPair, gReal, gImag, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  calc
    _ = 2 * (halfDiff (H 0 x) (H 2 x) : R) +
        i * (2 * (halfDiff (H 1 x) (H 3 x) : R)) := by ring
    _ = _ := by rw [h0, h1]; ring

/-- The binary identity with an explicitly constructed integral-pair `U`. -/
theorem binary_identity_over {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    castCoeffs (H 2) + i • castCoeffs (H 3) =
      (1 + i) • (JOver R : G →₀ R) + (2 : R) • UOver i H := by
  ext x
  have h2 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 2 x))
  have h3 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 3 x))
  push_cast at h2 h3
  simp only [UOver, liftPair, UReal, UImag, Finsupp.add_apply, Finsupp.smul_apply,
    castCoeffs_apply, ofCoeffs_apply, JOver_apply, smul_eq_mul]
  rw [h2, h3]
  ring

end BinaryCoefficients
end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings ----
namespace OAI

/-!
# The concrete coefficient rings for the prime comparisons

The chosen roots and all coefficient rings live in `ℂ`. The away ring is
proved to be generated by one actual primitive root of order prime to the
omitted prime. No equality of root-generated rings is an input hypothesis.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicRings

open scoped BigOperators

theorem I_isPrimitiveRoot : IsPrimitiveRoot Complex.I 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) Complex.I_pow_four
  intro j hj0 hj4
  interval_cases j <;>
    norm_num [pow_one, Complex.I_sq, Complex.I_pow_three, Complex.ext_iff]

theorem gaussianI_sq : gaussianI ^ 2 = -1 :=
  Subtype.ext Complex.I_sq

private theorem map_star_of_pow_eq_one (S : Subalgebra ℤ ℂ) [StarRing S]
    (hstar : ∀ x : S, ((star x : S) : ℂ) = star (x : ℂ))
    (σ : S →+* ℂ) (x : S) (n : ℕ) (hn : n ≠ 0) (hx : (x : ℂ) ^ n = 1) :
    σ (star x) = star (σ x) := by
  have hxS : x ^ n = 1 := Subtype.ext hx
  have hsource : star x = x ^ (n - 1) := by
    apply Subtype.ext
    simpa only [hstar, Subalgebra.coe_pow] using star_eq_pow_pred_of_pow_eq_one hn hx
  have htarget : σ x ^ n = 1 := by rw [← map_pow, hxS, map_one]
  rw [hsource, map_pow, star_eq_pow_pred_of_pow_eq_one hn htarget]

private theorem map_star_adjoin (S : Set ℂ) [StarRing (Algebra.adjoin ℤ S)]
    (hstar : ∀ x : Algebra.adjoin ℤ S, ((star x : Algebra.adjoin ℤ S) : ℂ) = star (x : ℂ))
    (hS : ∀ z ∈ S, ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1)
    (σ : Algebra.adjoin ℤ S →+* ℂ) (x : Algebra.adjoin ℤ S) :
    σ (star x) = star (σ x) := by
  rcases x with ⟨x, hx⟩
  refine Algebra.adjoin_induction
    (p := fun z hz => σ (star (⟨z, hz⟩ : Algebra.adjoin ℤ S)) =
      star (σ (⟨z, hz⟩ : Algebra.adjoin ℤ S))) ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨n, hn, hzn⟩ := hS z hz
    exact map_star_of_pow_eq_one _ hstar σ ⟨z, Algebra.subset_adjoin hz⟩ n hn hzn
  · intro a
    change σ (star (a : Algebra.adjoin ℤ S)) = star (σ (a : Algebra.adjoin ℤ S))
    simp
  · intro z w hz hw hzp hwp
    change σ (star ((⟨z, hz⟩ : Algebra.adjoin ℤ S) + ⟨w, hw⟩)) =
      star (σ ((⟨z, hz⟩ : Algebra.adjoin ℤ S) + ⟨w, hw⟩))
    simpa only [star_add, map_add] using congrArg₂ (· + ·) hzp hwp
  · intro z w hz hw hzp hwp
    change σ (star ((⟨z, hz⟩ : Algebra.adjoin ℤ S) * ⟨w, hw⟩)) =
      star (σ ((⟨z, hz⟩ : Algebra.adjoin ℤ S) * ⟨w, hw⟩))
    simpa only [star_mul, map_mul] using congrArg₂ (· * ·) hwp hzp

/-- Every complex-valued ring map respects the actual conjugation. -/
theorem map_star_rootRing (s : Finset ℕ) (σ : rootRing s →+* ℂ) (x : rootRing s) :
    σ (star x) = star (σ x) := by
  apply @map_star_adjoin (({Complex.I} : Set ℂ) ∪ rho '' (s : Set ℕ))
    (rootRingStarRing s) (coe_star_rootRing s) ?_ σ x
  rintro z (hI | ⟨p, _, rfl⟩)
  · rcases hI with rfl
    exact ⟨4, by decide, Complex.I_pow_four⟩
  · exact rho_finite_order p

theorem map_star_B (u : ℕ) (σ : B u →+* ℂ) (x : B u) :
    σ (star x) = star (σ x) := map_star_rootRing _ σ x

private theorem primitive_mul {z w : ℂ} {m n : ℕ}
    (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n) (hcop : m.Coprime n) :
    IsPrimitiveRoot (z * w) (m * n) := by
  have horder := (Commute.all z w).orderOf_mul_eq_mul_orderOf_of_coprime
    (by simpa only [← hz.eq_orderOf, ← hw.eq_orderOf] using hcop)
  rw [← hz.eq_orderOf, ← hw.eq_orderOf] at horder
  rw [← horder]
  exact IsPrimitiveRoot.orderOf _

theorem prime_roots_prod_primitive (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    IsPrimitiveRoot (∏ p ∈ s, rho p) (∏ p ∈ s, p) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert p s hp ih =>
      intro hs
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      apply primitive_mul (rho_isPrimitiveRoot p hpp.ne_zero) (ih hsp)
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hpp (hsp q hq)).mpr
      intro heq
      exact hp (heq.symm ▸ hq)

theorem etaOf_isPrimitiveRoot (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    IsPrimitiveRoot (etaOf s) (orderOfSet s) := by
  apply primitive_mul I_isPrimitiveRoot (prime_roots_prod_primitive s hs)
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  simpa using ((hodd p hp).coprime_two_left.pow_left 2)

theorem orderOfSet_pos (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 < orderOfSet s :=
  Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (hs p hp).pos))

theorem rootRing_eq_singleton (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    rootRing s = Algebra.adjoin ℤ ({etaOf s} : Set ℂ) := by
  classical
  have hη := etaOf_isPrimitiveRoot s hs hodd
  let : NeZero (orderOfSet s) := ⟨(orderOfSet_pos s hs).ne'⟩
  have hηmem : etaOf s ∈ rootRing s :=
    (rootRing s).mul_mem (I_mem_rootRing s)
      ((rootRing s).prod_mem (fun q hq => rho_mem_rootRing s q hq))
  have hpower {z : ℂ} (hz : z ^ orderOfSet s = 1) :
      z ∈ Algebra.adjoin ℤ ({etaOf s} : Set ℂ) := by
    obtain ⟨j, _, hj⟩ := hη.eq_pow_of_pow_eq_one hz
    rw [← hj]
    exact (Algebra.adjoin ℤ ({etaOf s} : Set ℂ)).pow_mem
      (Algebra.subset_adjoin (by simp)) j
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro z (hI | ⟨q, hq, rfl⟩)
    · rcases hI with rfl
      apply hpower
      exact (I_isPrimitiveRoot.pow_eq_one_iff_dvd _).mpr (dvd_mul_right 4 _)
    · apply hpower
      apply ((rho_isPrimitiveRoot q (hs q hq).ne_zero).pow_eq_one_iff_dvd _).mpr
      exact (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq).trans (dvd_mul_left _ 4)
  · apply Algebra.adjoin_le
    simpa using hηmem

theorem eta_isPrimitiveRoot (u p : ℕ) (hu : Odd u) :
    IsPrimitiveRoot (eta u p) (awayOrder u p) := by
  apply etaOf_isPrimitiveRoot
  · intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  · intro q hq
    exact hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))

theorem awayRing_eq_singleton (u p : ℕ) (hu : Odd u) :
    awayRing u p = Algebra.adjoin ℤ ({eta u p} : Set ℂ) := by
  apply rootRing_eq_singleton
  · intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  · intro q hq
    exact hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))

theorem prime_not_dvd_awayOrder (u p : ℕ) (hu : Odd u) (hp : p ∈ u.primeFactors) :
    ¬p ∣ awayOrder u p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  apply hpp.coprime_iff_not_dvd.mp
  change p.Coprime (4 * ∏ q ∈ u.primeFactors.erase p, q)
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · have hodd := hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    simpa using hodd.coprime_two_right.pow_right 2
  · apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes hpp
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))).mpr
    exact (Finset.ne_of_mem_erase hq).symm

end CirculantHadamard.CyclotomicRings

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryNorms ----
namespace OAI

universe uR uA

/-!
# Cancelling the factor four in the binary norm identities

The coefficient ring may be a domain; the finite cyclic group algebra is not
assumed to be a domain. Cancellation is performed separately at every
coefficient. In particular these statements apply both to complex coefficients
and to the actual Gaussian subring of `ℂ`.

`CyclicRing.ringStar` conjugates coefficients as well as reversing exponents.
The evaluation bridge requires compatibility with this full operation,
including at the fourth root `i`; an inversion-only operation would not suffice.
-/

noncomputable section

namespace CirculantHadamard.BinaryNorms

open CyclicRing

section CoefficientCancellation

variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}

/-- Cancel four coefficientwise, without any domain assumption on the group
algebra. -/
theorem four_nsmul_cancel {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  let coeff : Elem R n →+ R :=
    { toFun := fun p => p.coeff a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have ha := congrArg coeff h
  rw [map_nsmul, map_nsmul] at ha
  have hc : (4 : R) * f.coeff a = (4 : R) * g.coeff a := by
    simp only [coeff, nsmul_eq_mul, Nat.cast_ofNat] at ha
    convert ha using 1 <;> rfl
  exact mul_left_cancel₀ (by norm_num : (4 : R) ≠ 0) hc

end CoefficientCancellation

section NormCancellation

variable {R : Type uR} [CommRing R] [StarRing R]
variable {n : ℕ} [NeZero n]

/-- Coefficient conjugation fixes natural scalar multiples. -/
theorem ringStar_nsmul (k : ℕ) (x : Elem R n) :
    ringStar (k • x) = k • ringStar x := by
  exact map_nsmul (ringStarRingHom n) k x

/-- The exact factor four before cancellation; this is valid even when the
coefficient ring itself has zero divisors. -/
theorem two_nsmul_norm (x : Elem R n) :
    ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      (4 : ℕ) • (x * ringStar x) := by
  rw [ringStar_nsmul]
  simp only [nsmul_eq_mul]
  ring

variable [IsDomain R] [CharZero R]

theorem norm_of_two_nsmul (u : ℕ) (x : Elem R n)
    (h : ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      ((4 * u ^ 2 : ℕ) : Elem R n)) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  rw [scalar_natCast]
  apply four_nsmul_cancel
  calc
    (4 : ℕ) • (x * ringStar x) =
        ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) :=
      (two_nsmul_norm x).symm
    _ = ((4 * u ^ 2 : ℕ) : Elem R n) := h
    _ = (4 : ℕ) • ((u ^ 2 : ℕ) : Elem R n) := by
      simp only [Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat]

theorem norm_of_evaluation
    {A : Type uA} [CommRing A] (sigma : A → A)
    (eval : A →+* Elem R n) (u : ℕ) (h : A) (x : Elem R n)
    (hnorm : h * sigma h = ((4 * u ^ 2 : ℕ) : A))
    (hstar : eval (sigma h) = ringStar (eval h))
    (hvalue : eval h = (2 : ℕ) • x) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  apply norm_of_two_nsmul u x
  rw [← hvalue, ← hstar, ← map_mul, hnorm, map_natCast]

end NormCancellation

section ActualBinaryElements

open BinaryBlocks BinaryCoefficients

variable {m : ℕ} [NeZero m]

/-- The partial evaluation uses the same literal coefficient cast as the
constructed Gaussian element. -/
theorem mappedBlock_intCast {R : Type uR} [CommRing R]
    (f : ProductElem ℤ m) (j : ZMod 4) :
    mappedBlock m (Int.castRingHom R) f j =
      AddMonoidAlgebra.ofCoeff (castCoeffs (block f j).coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  rfl

/-- The value at one is twice the actual integral `c`, not a freely chosen
element with a prescribed evaluation. -/
theorem evaluation_one_eq_two_c (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) 1 (by simp) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)) := by
  rw [partialEval_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_c (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, two_smul, mappedBlock, blocks, block,
    RingHom.id_apply] at hv ⊢
  convert hv using 1 <;> rfl

/-- The value at minus one is twice the actual integral `d`. -/
theorem evaluation_neg_one_eq_two_d (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) (-1) (by norm_num) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)) := by
  rw [partialEval_neg_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_d (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    two_smul, mappedBlock, blocks, block, RingHom.id_apply] at hv ⊢
  convert hv using 1 <;> rfl

/-- The fourth-root evaluation is twice the constructed Gaussian pair.
The coefficient ring is arbitrary, including the actual Gaussian ring,
without assuming a group-algebra domain. -/
theorem evaluation_fourthRoot_eq_two_gOver {R : Type uR} [CommRing R]
    (i : R) (hi : i ^ 2 = -1) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)) := by
  rw [partialEval_fourthRoot m (Int.castRingHom R) i hi f]
  simp only [mappedBlock_intCast]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_gOver i (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_smul, two_smul, blocks] at hv ⊢
  convert hv using 1 <;> rfl

theorem c_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) 1 (by simp)) u f (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) 1 (by simp)
      (fun _ => by simp) one_character_star f)
    (evaluation_one_eq_two_c f hsign)

/-- The second norm uses the real fourth root `-1` and its genuine star law. -/
theorem d_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) (-1) (by norm_num)) u f (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) (-1) (by norm_num)
      (fun _ => by simp) neg_one_character_star f)
    (evaluation_neg_one_eq_two_d f hsign)

/-- The third norm uses conjugation of the fourth root, not exponent reversal
alone. Both the square equation and the conjugation equation are explicit. -/
theorem gOver_norm_of_product_norm {R : Type uR} [CommRing R] [StarRing R]
    [IsDomain R] [CharZero R] (i : R) (hi : i ^ 2 = -1) (hstar : star i = -i)
    (u : ℕ) (f : ProductElem ℤ m) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem R m) (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : R) := by
  exact norm_of_evaluation groupStar
    (partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi))
    u f (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (Int.castRingHom R) i (fourthRoot_pow_four i hi)
      (fun _ => by simp) (fourthRoot_character_star i hi hstar) f)
    (evaluation_fourthRoot_eq_two_gOver i hi f hsign)

/-- Conjugation negates the imaginary unit in the actual Gaussian subring. -/
theorem star_gaussianI : star CyclotomicRings.gaussianI = -CyclotomicRings.gaussianI := by
  apply Subtype.ext
  change star Complex.I = -Complex.I
  simp

/-- The integral Gaussian norm, before any character evaluation or localization. -/
theorem gaussian_g_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem CyclotomicRings.GaussianRing m)
        (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) :=
  gOver_norm_of_product_norm CyclotomicRings.gaussianI CyclotomicRings.gaussianI_sq
    star_gaussianI u f hsign hnorm

end ActualBinaryElements

/-- The complete binary norm step starts from the original cyclic sign row.
The CRT transport, block signs, doubled evaluation values, full-star
compatibility, and scalar cancellation are all proved in the construction.
No separate norm premise for `c`, `d`, or `g` is accepted. -/
theorem binary_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem CyclotomicRings.GaussianRing (u ^ 2))
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) := by
  let F := BinaryBlocks.crt ℤ u hu f
  have hs : ∀ a, IsSign (F.coeff a) := by
    intro a
    simpa only [F, BinaryBlocks.crt_apply] using
      hsign ((BinaryBlocks.crtIndex u hu).symm a)
  have hn : F * groupStar F = ((4 * u ^ 2 : ℕ) : BinaryBlocks.ProductElem ℤ (u ^ 2)) :=
    BinaryBlocks.crt_norm hu f (4 * u ^ 2) (by simpa only [scalar_natCast] using hnorm)
  exact ⟨c_norm_of_product_norm u F hs hn, d_norm_of_product_norm u F hs hn,
    gaussian_g_norm_of_product_norm u F hs hn⟩

end CirculantHadamard.BinaryNorms

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.PrimeComponents ----
namespace OAI

/-!
# Actual primary components of the cyclic group of order u²

The prime set is the literal finite set of prime factors of `u`. The exponent
of each component is `(u ^ 2).factorization p`, hence twice the exponent in u.
Factorization and coprimality supply the hypotheses of the finite Chinese
remainder theorem. Its coordinates are the canonical reduction maps.

The generator of each primary component is the inverse image of its unit
coordinate vector. Its additive order is proved to be the full prime power,
and the complementary integer factor of u² is proved prime to p.
-/

noncomputable section

namespace CirculantHadamard.PrimeComponents

open scoped BigOperators

theorem primes_nonempty {u : ℕ} (hu : 1 < u) : (primes u).Nonempty :=
  Nat.nonempty_primeFactors.mpr hu

theorem prime_ne_two_of_odd {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : p ≠ 2 := by
  intro h
  apply hu.not_two_dvd_nat
  simpa only [h] using dvd_of_mem hp

theorem odd_of_mem {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : Odd p :=
  (prime_of_mem hp).odd_of_ne_two (prime_ne_two_of_odd hu hp)

theorem order_dvd_square (u p : ℕ) : order u p ∣ u ^ 2 :=
  Nat.ordProj_dvd (u ^ 2) p

theorem order_mul_cofactor (u p : ℕ) : order u p * cofactor u p = u ^ 2 := by
  exact Nat.mul_div_cancel' (order_dvd_square u p)

theorem cofactor_coprime {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    Nat.Coprime p (cofactor u p) :=
  Nat.coprime_ordCompl (prime_of_mem hp) (pow_ne_zero 2 hu.ne')

end CirculantHadamard.PrimeComponents

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uR uS uT uA

/-!
# Actual prime-component character evaluations

The partial-evaluation homomorphism retains one cyclic coordinate and evaluates
the others. Its multiplication and subsequent evaluation laws follow from its
construction, rather than assumptions attached to the factors of a norm equation.
-/

noncomputable section

namespace CirculantHadamard.PrimeCharacterEvaluations

open scoped BigOperators
open CyclicRing

section WeightedProjection

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n m : ℕ}

/-- Norm preservation is a consequence of the constructed ring homomorphism.
In particular it does not require the residual group algebra to be a domain. -/
theorem weightedProjection_product (φ : R →+* S) (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) (x y : Elem R n) (r : R)
    (hxy : x * y = scalar n r) :
    weightedProjection φ f χ x * weightedProjection φ f χ y = scalar m (φ r) := by
  rw [← map_mul, hxy, weightedProjection_scalar]

end WeightedProjection

open PrimeComponents CyclotomicRings

section RootCharacters
variable {A : Type uA} [CommMonoid A]

theorem rootsCharacter_generator (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    rootsCharacter u hu r hr S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then r p else 1 := by
  classical
  simp only [rootsCharacter, MonoidHom.finsetProd_apply]
  have heq : ∀ q ∈ S, componentCharacter u hu q (r q) (hr q)
      (Multiplicative.ofAdd (primaryGenerator u hu p)) = if q = p then r p else 1 := by
    intro q _
    by_cases h : q = p
    · subst q
      simp only [componentCharacter_generator, ite_true]
    · simp [h, componentCharacter_generator_ne u hu p q h]
  rw [Finset.prod_congr rfl heq]
  simp

end RootCharacters

theorem rhoB_ne_one (u : ℕ) (p : PrimeIndex u) : rhoB u p ≠ 1 := by
  intro h
  exact (rho_isPrimitiveRoot p.val (prime_of_mem p.property).ne_zero).ne_one
    (prime_of_mem p.property).one_lt (congrArg Subtype.val h)

theorem subsetCharacter_generator (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    subsetCharacter u hu S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then rhoB u p else 1 := rootsCharacter_generator _ _ _ _ _ _

theorem subsetCharacter_nonempty (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ a : ZMod (u ^ 2), subsetCharacter u hu S (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨p, hp⟩ := hS
  refine ⟨primaryGenerator u hu p, ?_⟩
  rw [subsetCharacter_generator, ite_eq_left hp]
  exact rhoB_ne_one u p

theorem partialEvaluation_product (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x y : Elem GaussianRing (u ^ 2))
    (hxy : x * y = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    partialEvaluation u hu p S x * partialEvaluation u hu p S y =
      scalar (order u p.val) ((u ^ 2 : ℕ) : awayRing u p.val) := by
  unfold partialEvaluation
  simpa only [map_natCast] using weightedProjection_product
    (gaussianToAway u p.val).toRingHom (coordinate u hu p) (awayCharacter u hu p S)
    x y ((u ^ 2 : ℕ) : GaussianRing) hxy

theorem subsetEvaluation_ne_zero (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    subsetEvaluation u hu S x ≠ 0 := by
  intro h
  have hn := subsetEvaluation_norm u hu S x hx
  rw [h, zero_mul] at hn
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero 2 hu.ne')) hn.symm

/-- Every complex embedding has the required norm. Compatibility with conjugation
is derived from the actual adjoined roots in `map_star_B`. -/
theorem subsetEvaluation_map_norm (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (σ : B u →+* ℂ) : ‖σ (subsetEvaluation u hu S x)‖ = (u : ℝ) := by
  have hn := congrArg (fun z : B u => ‖σ z‖) (subsetEvaluation_norm u hu S x hx)
  simp only [map_mul, map_star_B, norm_mul, norm_star, map_natCast] at hn
  rw [RCLike.norm_natCast, Nat.cast_pow] at hn
  nlinarith [norm_nonneg (σ (subsetEvaluation u hu S x)), (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]

end CirculantHadamard.PrimeCharacterEvaluations

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryEvaluation ----
namespace OAI

universe uR

/-!
# Evaluation of the actual binary coefficient construction

The integral `c,d` are mapped coefficientwise into the Gaussian subring, with
their proved convolution norms preserved. All values are taken by the
constructed prime-subset character map into the actual cyclotomic ring `B u`.
The norm equations follow from the original cyclic sign row.
-/

noncomputable section

namespace CirculantHadamard.BinaryEvaluation

open scoped BigOperators
open CyclicRing BinaryCoefficients CyclotomicRings PrimeComponents
open PrimeCharacterEvaluations

/- Select the canonical multiplication action directly. This avoids searching
through the concrete subalgebra's unrelated inherited scalar actions. -/
attribute [local instance] OAI.CirculantHadamard.BinaryEvaluation.gaussianSelfScalar
attribute [local instance] OAI.CirculantHadamard.BinaryEvaluation.gaussianCoeffScalar
section CoefficientCast

variable {R : Type uR} [CommRing R] {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem castCoeffs_add [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f + g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) +
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x + g.coeff x : ℤ) : R) = (f.coeff x : R) + (g.coeff x : R)
  exact Int.cast_add _ _

omit [NeZero n] in
theorem castCoeffs_sub [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f - g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) -
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x - g.coeff x : ℤ) : R) = (f.coeff x : R) - (g.coeff x : R)
  exact Int.cast_sub _ _

theorem castCoeffs_mul (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f * g).coeff) =
      Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
        (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  calc
    (((f * g).coeff x : ℤ) : R) = ∑ j, (f.coeff j : R) * (g.coeff (x - j) : R) := by
      rw [CyclicRing.mul_apply]
      simp only [Int.cast_sum, Int.cast_mul]
    _ = _ := (CyclicRing.mul_apply (AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) f.coeff))
      (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) x).symm

theorem castCoeffs_ringStar [StarRing R] (f : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (ringStar f).coeff) =
      ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp

omit [NeZero n] in
theorem castCoeffs_scalar [NeZero n] (r : ℤ) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (scalar n r).coeff) =
      scalar n (r : R) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp [scalar_apply]

/-- Coefficient maps preserve the norm equation. -/
theorem castCoeffs_norm [StarRing R] (f : Elem ℤ n) (r : ℕ)
    (hf : f * ringStar f = scalar n (r : ℤ)) :
    Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
      (ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))) = scalar n (r : R) := by
  have h := congrArg (fun z : Elem ℤ n =>
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) z.coeff)) hf
  simpa only [castCoeffs_mul, castCoeffs_ringStar, castCoeffs_scalar,
    Int.cast_natCast] using h

end CoefficientCast

section GaussianBlocks

variable {n : ℕ} [NeZero n]

theorem cG_eq (H : Fin 4 → Elem ℤ n) : cG H = aG H + bG H :=
  castCoeffs_add (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem dG_eq (H : Fin 4 → Elem ℤ n) : dG H = aG H - bG H :=
  castCoeffs_sub (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem gG_eq {H : Fin 4 → Elem ℤ n} (hH : Signs (fun j => (H j).coeff)) :
    gG H = aG H + gaussianScale gaussianI (bG H) -
      (gaussianScale (1 + gaussianI) JG + gaussianScale 2 (UG H)) := by
  calc
    gG H = aG H + gaussianScale gaussianI (bG H) -
        Add.add (α := Elem GaussianRing n)
          (AddMonoidAlgebra.ofCoeff (castCoeffs (H 2).coeff))
          (gaussianScale gaussianI (AddMonoidAlgebra.ofCoeff (castCoeffs (H 3).coeff))) := by
      apply AddMonoidAlgebra.coeff_injective
      have h := gOver_eq_ab gaussianI hH
      rw [sub_sub] at h
      simp only [gG, aG, bG, gaussianScale, AddMonoidAlgebra.coeff_sub,
        AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1; rfl
    _ = _ := by
      apply congrArg
        (fun z : Elem GaussianRing n => aG H + gaussianScale gaussianI (bG H) - z)
      apply AddMonoidAlgebra.coeff_injective
      have h := binary_identity_over gaussianI hH
      simp only [gaussianScale, JG, UG, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1 <;> rfl

theorem cG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hc : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    cG H * ringStar (cG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff))) r hc

theorem dG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hd : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    dG H * ringStar (dG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff))) r hd

end GaussianBlocks

section Values

variable (u : ℕ) [NeZero u] (hu : 0 < u)

theorem subsetEvaluation_smul (S : Finset (PrimeIndex u)) (r : GaussianRing)
    (x : Elem GaussianRing (u ^ 2)) :
    subsetEvaluation u hu S (gaussianScale r x) =
      gaussianToB u r * subsetEvaluation u hu S x := by
  change evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) _ =
    gaussianToB u r * evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) x
  rw [evaluate_apply, evaluate_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change gaussianToB u (r * x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a) =
    gaussianToB u r *
      (gaussianToB u (x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a))
  rw [map_mul, mul_assoc]

theorem cValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    cValue u hu H S = aValue u hu H S + bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (cG_eq H) |>.trans (map_add _ _ _)

theorem dValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    dValue u hu H S = aValue u hu H S - bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (dG_eq H) |>.trans (map_sub _ _ _)

theorem gValue_eq {H : Fin 4 → Elem ℤ (u ^ 2)} (hH : Signs (fun j => (H j).coeff))
    (S : Finset (PrimeIndex u)) :
    gValue u hu H S = aValue u hu H S + iB u * bValue u hu H S -
      ((1 + iB u) * JValue u hu S + 2 * UValue u hu H S) := by
  have h := congrArg (subsetEvaluation u hu S) (gG_eq hH)
  simpa [map_add, map_sub, map_ofNat, subsetEvaluation_smul, iB, gValue, aValue, bValue,
    JValue, UValue] using h

end Values

/-- All three Gaussian norm equations come from the original cyclic sign row. -/
theorem gaussian_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    cG H * ringStar (cG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      dG H * ringStar (dG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      gG H * ringStar (gG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
  obtain ⟨hc, hd, hg⟩ := BinaryNorms.binary_norms_of_cyclic_norm hu f hsign hnorm
  exact ⟨cG_norm _ (u ^ 2) hc, dG_norm _ (u ^ 2) hd, hg⟩

end CirculantHadamard.BinaryEvaluation

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalizationMaps ----
namespace OAI

universe uA uB

/-!
# Maps between coefficient localizations and maximal ideals over primes

The localization map uses the actual contraction of the target prime ideal.
Its denominator condition follows from the definition of contraction; no
integrality is needed for this map. Integrality is used separately to prove
maximality of contractions and existence of maximal ideals over rational primes.
-/

namespace CirculantHadamard

section LocalizationMap

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]

/-- Integral coefficient extensions preserve maximality on contraction. -/
theorem maximal_comap_of_integral (f : A →+* B) (hf : f.IsIntegral)
    (m : Ideal B) [m.IsMaximal] : (m.comap f).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m

end LocalizationMap

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryLocalization ----
namespace OAI

universe uB uO uk uF

/-!
# The characteristic-two local ring for the binary contradiction

The maximal ideal is constructed from an actual finite characteristic-zero
integer algebra.  Unit denominators follow from the odd norm identity, not
from an assumed extension of complex conjugation to a localization.
-/

namespace CirculantHadamard.BinaryLocalization

/-- A square root of minus one reduces to one in a field of characteristic two. -/
theorem map_i_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) : φ i = 1 := by
  have htwo : (2 : k) = 0 := CharTwo.two_eq_zero
  have hsquare : (φ i) ^ 2 = -1 := by
    simpa using congrArg φ hi
  have hsq : (φ i - 1) ^ 2 = 0 := by
    calc
      (φ i - 1) ^ 2 = (φ i) ^ 2 - 2 * φ i + 1 := by ring
      _ = 0 := by rw [hsquare, htwo]; ring
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)

end CirculantHadamard.BinaryLocalization

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryLocalRing ----
namespace OAI

/-!
# One concrete local ring and residue field

For the actual cyclotomic coefficient algebra `B u`, choose a maximal ideal
containing two. Both first-order calculations use the same localization and
the same residue field. The choices depend only on `u`, not on a character or
on which of the three norm elements is being considered.
-/

noncomputable section

namespace CirculantHadamard.BinaryLocalRing

open CyclotomicRings

/- Name the canonical localization algebra directly. This avoids searching
through iterated-localization algebra instances for these concrete carriers. -/
theorem toFraction_injective (u : ℕ) : Function.Injective (toFraction u) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (twoIdeal u).primeCompl (toFraction u).toRingHom).2
  intro a b
  change toLocal u a = toLocal u b ↔
    toFraction u (toLocal u a) = toFraction u (toLocal u b)
  rw [toFraction_toLocal, toFraction_toLocal]
  constructor
  · intro h
    exact congrArg (algebraMap (B u) (FractionRing (B u))) (toLocal_injective u h)
  · intro h
    exact congrArg (toLocal u) (IsFractionRing.injective (B u) (FractionRing (B u)) h)

theorem imaginary_sq (u : ℕ) : imaginary u ^ 2 = -1 := by
  unfold imaginary
  rw [← map_pow, gaussianI_sq, map_neg, map_one]

theorem residue_imaginary (u : ℕ) : residue u (imaginary u) = 1 :=
  BinaryLocalization.map_i_eq_one (residue u) (imaginary u) (imaginary_sq u)

theorem two_ne_zero (u : ℕ) : (2 : O u) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

end CirculantHadamard.BinaryLocalRing

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uG uH

/-!
# Alternating products over literal finite subsets

The exponent is `(-1)^card S`. Pairing subsets along `p` follows from the
powerset decomposition, with the quotient orientation `x S / x (insert p S)`.

The definition and pairing are valid in a division commutative monoid, so they
apply both to actual field values and to units. Cancellation of a constant
family is stated in a commutative group. No local comparison, nonvanishing,
integrality, or torsion statement is assumed or inferred.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

theorem subsetSign_of_even (S : Finset I) (h : Even S.card) : subsetSign S = 1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = 1)

theorem subsetSign_of_odd (S : Finset I) (h : Odd S.card) : subsetSign S = -1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = -1)

theorem subsetSign_insert [DecidableEq I] (p : I) (S : Finset I) (hp : p ∉ S) :
    subsetSign (insert p S) = -subsetSign S := by
  simp only [subsetSign, Finset.card_insert_of_notMem hp, pow_succ, mul_neg_one]

/-- The signed subset count vanishes by pairing along an actual element of `t`. -/
theorem sum_subsetSign_eq_zero (t : Finset I) (ht : t.Nonempty) :
    ∑ S ∈ t.powerset, subsetSign S = 0 := by
  classical
  obtain ⟨p, hp⟩ := ht
  have hpaired :
      (∑ S ∈ (t.erase p).powerset, subsetSign (insert p S)) =
        -(∑ S ∈ (t.erase p).powerset, subsetSign S) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    exact subsetSign_insert p S
      (fun h => (Finset.notMem_erase p t) ((Finset.mem_powerset.mp hS) h))
  calc
    _ = ∑ S ∈ (insert p (t.erase p)).powerset, subsetSign S := by
      rw [Finset.insert_erase hp]
    _ = (∑ S ∈ (t.erase p).powerset, subsetSign S) +
        ∑ S ∈ (t.erase p).powerset, subsetSign (insert p S) :=
      Finset.sum_powerset_insert (Finset.notMem_erase p t) subsetSign
    _ = 0 := by rw [hpaired, add_neg_cancel]

/-- The even-cardinality and odd-cardinality subset filters have equal size. -/
theorem card_even_subsets_eq_card_odd_subsets (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by
  classical
  have heven : (∑ S ∈ t.powerset.filter (fun S => Even S.card), subsetSign S) =
      ((t.powerset.filter (fun S => Even S.card)).card : ℤ) := by
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Even S.card), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_even S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hodd : (∑ S ∈ t.powerset.filter (fun S => ¬ Even S.card), subsetSign S) =
      -((t.powerset.filter (fun S => Odd S.card)).card : ℤ) := by
    have hfilter : t.powerset.filter (fun S => ¬ Even S.card) =
        t.powerset.filter (fun S => Odd S.card) := by
      ext S
      simp only [Finset.mem_filter, Nat.not_even_iff_odd]
    rw [hfilter]
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Odd S.card), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_odd S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hsum := Finset.sum_filter_add_sum_filter_not t.powerset
    (fun S : Finset I => Even S.card) subsetSign
  rw [heven, hodd, sum_subsetSign_eq_zero t ht] at hsum
  exact Int.natCast_inj.mp (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum))

theorem map_evenSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (evenSubsetProduct t x) = evenSubsetProduct t (fun S => f (x S)) := by
  simp only [evenSubsetProduct, map_prod]

theorem map_oddSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (oddSubsetProduct t x) = oddSubsetProduct t (fun S => f (x S)) := by
  simp only [oddSubsetProduct, map_prod]

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

theorem alternatingProduct_congr (t : Finset I) (x y : Finset I → G)
    (h : ∀ S ⊆ t, x S = y S) :
    alternatingProduct t x = alternatingProduct t y := by
  apply Finset.prod_congr rfl
  intro S hS
  rw [h S (Finset.mem_powerset.mp hS)]

theorem alternatingProduct_mul (t : Finset I) (x y : Finset I → G) :
    alternatingProduct t (fun S => x S * y S) =
      alternatingProduct t x * alternatingProduct t y := by
  simp only [alternatingProduct, mul_zpow, Finset.prod_mul_distrib]

theorem alternatingProduct_inv (t : Finset I) (x : Finset I → G) :
    alternatingProduct t (fun S => (x S)⁻¹) = (alternatingProduct t x)⁻¹ := by
  simp only [alternatingProduct, inv_zpow, Finset.prod_inv_distrib]

/-- A single direction pairs each omitted-`p` subset with its insertion.
The exponent at the inserted subset is the negative of the original one. -/
theorem alternatingProduct_insert [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∉ t) :
    alternatingProduct (insert p t) x =
      ∏ S ∈ t.powerset, (x S / x (insert p S)) ^ subsetSign S := by
  unfold alternatingProduct
  rw [Finset.prod_powerset_insert hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
  rw [subsetSign_insert p S hpS, zpow_neg, div_zpow, div_eq_mul_inv]

theorem alternatingProduct_pair [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∈ t) :
    alternatingProduct t x =
      ∏ S ∈ (t.erase p).powerset, (x S / x (insert p S)) ^ subsetSign S := by
  calc
    alternatingProduct t x = alternatingProduct (insert p (t.erase p)) x := by
      rw [Finset.insert_erase hp]
    _ = _ := alternatingProduct_insert (t.erase p) x p (Finset.notMem_erase p t)

/-- Even subsets contribute the value itself; odd subsets contribute its inverse. -/
theorem alternatingProduct_eq_parity (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x =
      ∏ S ∈ t.powerset, if Even S.card then x S else (x S)⁻¹ := by
  classical
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp only [subsetSign_of_even S h, zpow_one, ite_eq_left h]
  · have ho : Odd S.card := Nat.not_even_iff_odd.mp h
    simp only [subsetSign_of_odd S ho, zpow_neg_one, ite_eq_right h]

/-- Collect the signed powers as a quotient of two ordinary products.
Both products themselves make sense before passing to a fraction field. -/
theorem alternatingProduct_eq_even_div_odd (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x = evenSubsetProduct t x / oddSubsetProduct t x := by
  classical
  rw [alternatingProduct_eq_parity, evenSubsetProduct, oddSubsetProduct,
    Finset.prod_filter, Finset.prod_filter, div_eq_mul_inv,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp [h, Nat.not_odd_iff_even.mpr h]
  · simp [h, Nat.not_even_iff_odd.mp h]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

/-- In particular this applies to the homomorphism from local units to the
fraction field, retaining the single fixed alternating product. -/
theorem map_alternatingProduct (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (alternatingProduct t x) = alternatingProduct t (fun S => f (x S)) := by
  simp only [alternatingProduct, map_prod, map_zpow]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

end FiniteUniverse

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryProductTransport ----
namespace OAI

universe uG uI

/-!
# Odd-power products in the concrete binary local ring

The local units are supplied with their actual coefficient-ring values.
Their alternating product maps to the fixed alternating product in the
fraction field. Injectivity transports each exact power identity back to
the local units, with the same exponent.
-/

noncomputable section

namespace CirculantHadamard.BinaryProductTransport

open CyclotomicRings BinaryLocalRing

/-- Odd-power torsion is closed under taking a quotient in a commutative
group. The product of the two supplied exponents is an explicit witness. -/
theorem odd_power_mul_inv {G : Type uG} [CommGroup G] (x y : G)
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧ x ^ m = 1)
    (hy : ∃ n : ℕ, 0 < n ∧ Odd n ∧ y ^ n = 1) :
    ∃ r : ℕ, 0 < r ∧ Odd r ∧ (x * y⁻¹) ^ r = 1 := by
  obtain ⟨m, hm, hmOdd, hxm⟩ := hx
  obtain ⟨n, hn, hnOdd, hyn⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, hmOdd.mul hnOdd, ?_⟩
  have hxmn : x ^ (m * n) = 1 := by rw [pow_mul, hxm, one_pow]
  have hymn : y ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, hyn, one_pow]
  simp only [mul_pow, inv_pow, hxmn, hymn, inv_one, mul_one]

theorem localUnitToFraction_injective (u : ℕ) :
    Function.Injective (localUnitToFraction u) := by
  intro X Y h
  apply Units.ext
  exact toFraction_injective u h

/-- Transport of the literal signed subset product, using the supplied
value equality only for subsets that occur in the product. -/
theorem local_alternatingProduct_toFraction {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) :
    localUnitToFraction u (alternatingProduct t X) =
      alternatingProduct t (fun S => algebraMap (B u) (FractionRing (B u)) (x S)) := by
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change toFraction u (X S : O u) = _
  rw [hX S hS, toFraction_toLocal]

/-- An exact fraction-field power identity holds for the actual local
alternating product with precisely the same exponent. -/
theorem local_alternatingProduct_pow_eq_one {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) (m : ℕ)
    (hpow : (alternatingProduct t
      (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    (alternatingProduct t X) ^ m = 1 := by
  apply localUnitToFraction_injective u
  rw [map_pow, map_one, local_alternatingProduct_toFraction u t x X hX]
  exact hpow

theorem local_alternatingProduct_has_odd_power {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ (alternatingProduct t X) ^ m = 1 := by
  obtain ⟨m, hm, hmOdd, hpow⟩ := hodd
  exact ⟨m, hm, hmOdd, local_alternatingProduct_pow_eq_one u t x X hX m hpow⟩

/-- The two concrete unit families produce an odd-power quotient family.
No torsion of individual factors is assumed or inferred. -/
theorem local_alternatingProduct_ratio_has_odd_power {I : Type uI}
    (u : ℕ) (t : Finset I) (x y : Finset I → B u)
    (X Y : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hY : ∀ S ⊆ t, (Y S : O u) = toLocal u (y S))
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1)
    (hy : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (y S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t (fun S => X S * (Y S)⁻¹)) ^ m = 1 := by
  simpa only [alternatingProduct_mul, alternatingProduct_inv] using
    odd_power_mul_inv (alternatingProduct t X) (alternatingProduct t Y)
      (local_alternatingProduct_has_odd_power u t x X hX hx)
      (local_alternatingProduct_has_odd_power u t y Y hY hy)

end CirculantHadamard.BinaryProductTransport

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryCharacterSum ----
namespace OAI

universe uG uR uA uI uT uK uk uB

/-!
# Finite character sums and the surviving empty subset

Translation of a finite group permutes its elements. Consequently a character
with one value different from `1` has zero total sum in a domain. In a family
indexed by subsets, this removes every nonempty subset once its actual
character has such a witness.

The unit-denominator formulation takes place in the coefficient ring itself,
so it can subsequently be mapped to a residue field of characteristic two.
It does not require a map from a characteristic-zero field to that residue
field. Nontriviality of the actual subset characters is supplied by their
primitive primary components, rather than assumed of all characters.
-/

namespace CirculantHadamard.BinaryCharacterSum

open scoped BigOperators

section CharacterSum

variable {G : Type uG} {R : Type uR} [Group G] [Fintype G] [CommRing R]

/-- A nontrivial value of a character forces its finite sum to vanish.
The proof uses the permutation of `G` given by left translation. -/
theorem character_sum_eq_zero [IsDomain R] (χ : G →* R)
    (hχ : ∃ g : G, χ g ≠ 1) : (∑ g : G, χ g) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hχ
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul] using
    (Group.mulLeft_bijective g).sum_comp (fun h : G => χ h)

end CharacterSum

section ActualGroupRing

variable {A : Type uA} {R : Type uR} [CommRing A] [CommRing R] {n : ℕ} [NeZero n]

/-- Evaluation of the actual all-ones group-ring element is the complete
character sum. `JOver` is not the scalar unit of the group ring. -/
theorem evaluate_J_eq_sum (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) =
      ∑ g : Multiplicative (ZMod n), χ g := by
  rw [CyclicRing.evaluate_apply]
  simp only [BinaryCoefficients.JOver_apply, map_one, one_mul]
  exact (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n)).sum_comp _

/-- A witnessed nontrivial character annihilates the actual group-ring `J`. -/
theorem evaluate_J_eq_zero [IsDomain R] (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R)
    (hχ : ∃ g : Multiplicative (ZMod n), χ g ≠ 1) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = 0 := by
  rw [evaluate_J_eq_sum]
  exact character_sum_eq_zero χ hχ

/-- At the trivial character, the actual group-ring `J` evaluates to `n`. -/
theorem evaluate_J_trivial (φ : A →+* R) :
    CyclicRing.evaluate φ (1 : Multiplicative (ZMod n) →* R)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = (n : R) := by
  rw [CyclicRing.evaluate_apply]
  simp

end ActualGroupRing

/-- First prove the character sum in its domain, then change coefficient
rings. This does not assume nontriviality of the reduced characters and also
allows the coefficients `d S` to lie in a localization of the original ring. -/
theorem subset_map_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
        ε ∅ * ψ (CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : T) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial, map_natCast]

section SubsetSum

variable {I : Type uI} {G : Type uG} {R : Type uR} [Fintype I] [DecidableEq I]
    [Group G] [Fintype G] [CommRing R] [IsDomain R]

end SubsetSum

section Residue

variable {R : Type uR} {k : Type uk} [CommRing R] [CommRing k] [Nontrivial k] [CharP k 2]

/-- An odd cardinal times the inverse of a unit stays nonzero in any
nontrivial characteristic-two residue ring. -/
theorem residue_odd_mul_unit_inv_ne_zero (φ : R →+* k) {n : ℕ}
    (hn : Odd n) (c : Rˣ) : φ ((n : R) * ↑(c⁻¹)) ≠ 0 := by
  rw [map_mul, map_natCast,
    natCast_eq_one_of_odd_of_two_eq_zero hn (CharTwo.two_eq_zero (R := k)), one_mul]
  exact (IsUnit.map φ (c⁻¹).isUnit).ne_zero

end Residue

section ActualSubsetCharacters

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations

/-- The witness is the actual CRT generator of a prime in the nonempty
subset. Its value is the corresponding primitive prime root, hence not one. -/
theorem actual_subsetCharacter_nontrivial (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ g : Multiplicative (ZMod (u ^ 2)), subsetCharacter u hu S g ≠ 1 := by
  obtain ⟨a, ha⟩ := subsetCharacter_nonempty u hu S hS
  exact ⟨Multiplicative.ofAdd a, ha⟩

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)

/-- The actual prime-subset sum, with the literal parity signs. The target
may be a localization: its coefficients need not belong to the original `B`. -/
theorem actual_subset_J_sum
    {T : Type uT} [CommRing T] (ψ : B u →+* T)
    (d : Finset (PrimeIndex u) → T) :
    (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) = ((u ^ 2 : ℕ) : T) * d ∅ := by
  exact subset_map_evaluate_J_mul (gaussianToB u).toRingHom ψ
    (subsetCharacter u hu) (fun S => (subsetSign S : T)) d (by simp)
    (subsetCharacter_empty u hu) (actual_subsetCharacter_nontrivial u hu)

/-- The concrete prime-character sum has nonzero characteristic-two residue.
Oddness comes from the actual `u`; only the surviving denominator must be a
unit. There is no assumption on reduced-character nontriviality. -/
theorem actual_subset_J_residue_ne_zero
    {T : Type uT} {k : Type uk} [CommRing T] [CommRing k] [Nontrivial k] [CharP k 2]
    (ψ : B u →+* T) (residue : T →+* k)
    (d : Finset (PrimeIndex u) → T) (c₀ : Tˣ)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd u) :
    residue (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) ≠ 0 := by
  rw [actual_subset_J_sum u hu ψ d, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd.pow c₀

end ActualSubsetCharacters

end CirculantHadamard.BinaryCharacterSum

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.FirstOrderResidue ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uO uK uIota

/-!
# First-order residues of principal units

For a nonzero element `t` of a domain, a unit of the form `1 + t * a` has a
unique coefficient `a`. A ring homomorphism killing `t` sends the coefficient
of a product to the sum of the coefficients. This constructs the actual
first-order homomorphism without identifying any quotient rings.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

section Domain

variable [IsDomain O]

variable {K : Type uK} [Field K]

theorem actualFirstOrder_apply_of_eq (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) (u : principalUnits t) {a : O}
    (ha : ((u : Oˣ) : O) = 1 + t * a) :
    (actualFirstOrder φ t ht hφt u).toAdd = φ a := by
  change φ (principalUnitCoeff t u) = φ a
  rw [principalUnitCoeff_eq t ht u ha]

/-- An exact signed product identity among principal units gives a vanishing
sum of their first-order residues. Representations are required only on `s`. -/
theorem first_order_sum_eq_zero_of_prod_eq_one {ι : Type uIota}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by
  classical
  let v : ι → principalUnits t := fun i =>
    if hi : i ∈ s then ⟨u i, ⟨L i, hrep i hi⟩⟩ else 1
  have hv (i : ι) (hi : i ∈ s) : (v i : Oˣ) = u i := by
    simp only [v, dite_eq_left hi]
  have hp : (∏ i ∈ s, (v i) ^ (ε i)) = 1 := by
    apply Subtype.ext
    change (principalUnits t).subtype (∏ i ∈ s, (v i) ^ (ε i)) =
      (principalUnits t).subtype 1
    rw [map_prod, map_one]
    calc
      (∏ i ∈ s, (principalUnits t).subtype ((v i) ^ (ε i))) =
          ∏ i ∈ s, (u i) ^ (ε i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [map_zpow]
        change (v i : Oˣ) ^ (ε i) = (u i) ^ (ε i)
        rw [hv i hi]
      _ = 1 := hprod
  have hmap := congrArg
    (fun z : principalUnits t => (actualFirstOrder φ t ht hφt z).toAdd) hp
  have hsum :
      (∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd) = 0 := by
    simpa only [map_prod, map_zpow, toAdd_prod,
      toAdd_zpow, map_one, toAdd_one] using hmap
  calc
    (∑ i ∈ s, (ε i : K) * φ (L i)) =
        ∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvi : ((v i : Oˣ) : O) = 1 + t * L i := by
        rw [hv i hi]
        exact hrep i hi
      rw [actualFirstOrder_apply_of_eq φ t ht hφt (v i) hvi, zsmul_eq_mul]
    _ = 0 := hsum

end Domain

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ResidueTorsion ----
namespace OAI

universe uR uK

/-!
# Torsion in the kernel of a residue map

The geometric-sum argument works for any ring homomorphism from a domain
to a field of characteristic `p`. In a local-ring application the map is
the residue homomorphism; the domain itself need not have characteristic `p`.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]

/-- A root whose image is one is trivial if one of its torsion exponents
is not divisible by the target characteristic. -/
theorem eq_one_of_residue_one_of_not_dvd {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hmap : f z = 1) (hpow : z ^ m = 1)
    (hm : ¬ p ∣ m) : z = 1 := by
  by_contra hne
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hsum : (∑ i ∈ Finset.range m, z ^ i) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hcast : (m : K) = 0 := by
    have h := congrArg f hsum
    simpa only [map_sum, map_pow, hmap, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  exact hm ((CharP.cast_eq_zero_iff K p m).mp hcast)

/-- Coprime-order torsion in the residue-one subgroup is trivial. The
exponent need not be the exact order. -/
theorem eq_one_of_residue_one_of_coprime {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hpow : z ^ m = 1) (hcop : m.Coprime p) : z = 1 := by
  exact eq_one_of_residue_one_of_not_dvd f z hmap hpow
    (hp.coprime_iff_not_dvd.mp hcop.symm)

theorem exists_prime_power_of_residue_one {p : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hfinite : ∃ N : ℕ, 0 < N ∧ z ^ N = 1) :
    ∃ a : ℕ, z ^ (p ^ a) = 1 := by
  obtain ⟨N, hN, hpow⟩ := hfinite
  obtain ⟨a, m, hm, hNm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  refine ⟨a, eq_one_of_residue_one_of_not_dvd f (z ^ (p ^ a)) ?_ ?_ hm⟩
  · rw [map_pow, hmap, one_pow]
  · rw [← pow_mul, ← hNm]
    exact hpow

/-- The characteristic-two consequence needed for the two alternating
products: a unit of odd torsion exponent and residue one equals one. -/
theorem units_eq_one_of_residue_one_of_odd [CharP K 2]
    (f : R →+* K) (u : Rˣ) (hmap : f (u : R) = 1)
    (hfinite : ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1) : u = 1 := by
  obtain ⟨m, _, hm, hu⟩ := hfinite
  have hpow : (u : R) ^ m = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v : Rˣ => (v : R)) hu
  apply Units.ext
  exact eq_one_of_residue_one_of_coprime f (u : R) Nat.prime_two hmap hpow
    hm.coprime_two_right

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryResidue ----
namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

theorem binary_ratio_r (c d : Oˣ) (a b : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b) :
    ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr c b := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  calc
    ((d * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + 2 * (-b * (↑(c⁻¹) : O)) := by
      change (d : O) * (↑(c⁻¹) : O) = _
      rw [hd]
      ring
    _ = 1 + (2 : O) * binaryLr c b := by rw [hc']; rfl

theorem binary_ratio_w (c g : Oˣ) (a b J U i : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) :
    ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * binaryLw c i b J U := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  calc
    ((g * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + (1 + i) * binaryLw c i b J U -
          (i * i + 1) * (b + U) * (↑(c⁻¹) : O) := by
      change (g : O) * (↑(c⁻¹) : O) = _
      rw [hg]
      unfold binaryLw
      ring
    _ = 1 + (1 + i) * binaryLw c i b J U := by rw [hc', hi']; ring

/-- This identity is exact before applying the residue map. -/
theorem binaryLr_add_binaryLw (c : Oˣ) (i b J U : O) :
    binaryLr c b + binaryLw c i b J U =
      -J * (↑(c⁻¹) : O) - (1 - i) * (b + U) * (↑(c⁻¹) : O) := by
  unfold binaryLr binaryLw
  ring

/-- Nonvanishing of `2` also makes the second first-order parameter nonzero. -/
theorem binary_one_add_i_ne_zero (i : O) (hi : i ^ 2 = -1)
    (h2 : (2 : O) ≠ 0) : 1 + i ≠ 0 := by
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  have hfactor : (1 + i) * (1 - i) = (2 : O) := by
    calc
      (1 + i) * (1 - i) = 1 - i * i := by ring
      _ = 2 := by rw [hi']; ring
  intro hzero
  apply h2
  rw [← hfactor, hzero, zero_mul]

section Domain

variable [IsDomain O]

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

/-- The two coefficients have residues summing to the residue of `J / c`. -/
theorem binary_residue_sum (φ : O →+* k) (c : Oˣ) (i b J U : O)
    (hi : φ i = 1) :
    φ (binaryLr c b) + φ (binaryLw c i b J U) =
      φ (J * (↑(c⁻¹) : O)) := by
  rw [← map_add, binaryLr_add_binaryLw]
  simp [hi, CharTwo.neg_eq]

omit charTwo in
/-- A signed product of units with residue one again has residue one.
The powers are formed in the unit group, including for negative exponents. -/
theorem binary_signed_product_residue_one [CharP k 2] {ι : Type uIota}
    (φ : O →+* k) (s : Finset ι) (u : ι → Oˣ) (ε : ι → ℤ)
    (hu : ∀ j ∈ s, φ (u j : O) = 1) :
    φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 := by
  let f : Oˣ →* kˣ := Units.map φ.toMonoidHom
  have hf (j : ι) (hj : j ∈ s) : f (u j) = 1 := by
    apply Units.ext
    change φ (u j : O) = 1
    exact hu j hj
  have hp : f (∏ j ∈ s, (u j) ^ (ε j)) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro j hj
    rw [map_zpow, hf j hj, one_zpow]
  have hval := congrArg (fun z : kˣ => (z : k)) hp
  change φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 at hval
  exact hval

variable [IsDomain O]

/-- The same-residue-field contradiction for a finite signed family of
binary decompositions. All arithmetic input to the concrete application is
explicit: unit decompositions, a square root of `-1`, odd torsion of both
signed products, and a nonzero signed `J / c` residue sum. -/
theorem binary_residue_contradiction {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by
  have hφ2 : φ (2 : O) = 0 := by
    calc
      φ (2 : O) = φ (1 + 1) := by congr 1; ring
      _ = (1 : k) + 1 := by simp only [map_add, map_one]
      _ = 0 := CharTwo.add_self_eq_zero 1
  have hφpi : φ (1 + i) = 0 := by
    rw [map_add, map_one, hφi]
    exact CharTwo.add_self_eq_zero 1
  have hr (j : ι) (hj : j ∈ s) :
      ((d j * (c j)⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr (c j) (b j) :=
    binary_ratio_r (c j) (d j) (a j) (b j) (hc j hj) (hd j hj)
  have hw (j : ι) (hj : j ∈ s) :
      ((g j * (c j)⁻¹ : Oˣ) : O) =
        1 + (1 + i) * binaryLw (c j) i (b j) (J j) (U j) :=
    binary_ratio_w (c j) (g j) (a j) (b j) (J j) (U j) i (hc j hj) (hg j hj) hi
  have hrMap (j : ι) (hj : j ∈ s) : φ ((d j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hr j hj, map_add, map_one, map_mul, hφ2, zero_mul, add_zero]
  have hwMap (j : ι) (hj : j ∈ s) : φ ((g j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hw j hj, map_add, map_one, map_mul, hφpi, zero_mul, add_zero]
  have hrOne : (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => d j * (c j)⁻¹) ε hrMap) hrOdd
  have hwOne : (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => g j * (c j)⁻¹) ε hwMap) hwOdd
  have hrSum := first_order_sum_eq_zero_of_prod_eq_one φ (2 : O) h2 hφ2 s
    (fun j => d j * (c j)⁻¹) (fun j => binaryLr (c j) (b j)) ε hr hrOne
  have hwSum := first_order_sum_eq_zero_of_prod_eq_one φ (1 + i)
    (binary_one_add_i_ne_zero i hi h2) hφpi s
    (fun j => g j * (c j)⁻¹) (fun j => binaryLw (c j) i (b j) (J j) (U j)) ε hw hwOne
  apply hnonzero
  calc
    (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) =
        ∑ j ∈ s, ((ε j : k) * φ (binaryLr (c j) (b j)) +
          (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_add, binary_residue_sum φ (c j) i (b j) (J j) (U j) hφi]
    _ = (∑ j ∈ s, (ε j : k) * φ (binaryLr (c j) (b j))) +
        ∑ j ∈ s, (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j)) :=
      Finset.sum_add_distrib
    _ = 0 := by rw [hrSum, hwSum, add_zero]

end Residue

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryLocalFamily ----
namespace OAI

noncomputable section

namespace CirculantHadamard.BinaryLocalFamily

open scoped BigOperators
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing
open BinaryLocalRing BinaryProductTransport

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u) (hodd : Odd u)

include hodd in
/-- The concrete local argument. In particular, neither local units nor a
nonzero residue sum are assumptions of this theorem. -/
theorem contradiction_of_evaluated_data
    (C D G : Elem GaussianRing (u ^ 2))
    (hC : C * ringStar C = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hD : D * ringStar D = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hG : G * ringStar G = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (a b U : Finset (PrimeIndex u) → B u)
    (hc : ∀ S, subsetEvaluation u hu S C = a S + b S)
    (hd : ∀ S, subsetEvaluation u hu S D = a S - b S)
    (hg : ∀ S, subsetEvaluation u hu S G =
      a S + gaussianToB u gaussianI * b S -
        ((1 + gaussianToB u gaussianI) *
          subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing)) + 2 * U S))
    (hCodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S C))) ^ m = 1)
    (hDodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S D))) ^ m = 1)
    (hGodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S G))) ^ m = 1) :
    False := by
  classical
  let c := evaluationUnit u hu hodd C hC
  let d := evaluationUnit u hu hodd D hD
  let g := evaluationUnit u hu hodd G hG
  have cval (S) : (c S : O u) = toLocal u (subsetEvaluation u hu S C) :=
    evaluationUnit_val u hu hodd C hC S
  have dval (S) : (d S : O u) = toLocal u (subsetEvaluation u hu S D) :=
    evaluationUnit_val u hu hodd D hD S
  have gval (S) : (g S : O u) = toLocal u (subsetEvaluation u hu S G) :=
    evaluationUnit_val u hu hodd G hG S
  have hr := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S D) (fun S => subsetEvaluation u hu S C)
    d c (fun S _ => dval S) (fun S _ => cval S) hDodd hCodd
  have hw := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S G) (fun S => subsetEvaluation u hu S C)
    g c (fun S _ => gval S) (fun S _ => cval S) hGodd hCodd
  apply binary_residue_contradiction (residue u) (imaginary u)
    (imaginary_sq u) (residue_imaginary u) (two_ne_zero u)
    (Finset.univ : Finset (Finset (PrimeIndex u))) subsetSign c d g
    (fun S => toLocal u (a S)) (fun S => toLocal u (b S))
    (fun S => toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))))
    (fun S => toLocal u (U S))
  · intro S _
    rw [cval, hc, map_add]
  · intro S _
    rw [dval, hd, map_sub]
  · intro S _
    rw [gval, hg]
    have hi_local : toLocal u (gaussianToB u gaussianI) = imaginary u := by
      change toLocal u ((gaussianToB u).toRingHom gaussianI) =
        ((toLocal u).comp (gaussianToB u).toRingHom) gaussianI
      exact (RingHom.comp_apply _ _ _).symm
    simp only [map_sub, map_add, map_mul, map_one, map_ofNat, hi_local]
  · simpa only [alternatingProduct, Finset.powerset_univ] using hr
  · simpa only [alternatingProduct, Finset.powerset_univ] using hw
  · have hnonzero := BinaryCharacterSum.actual_subset_J_residue_ne_zero u hu
      (toLocal u) (residue u) (fun S => (↑((c S)⁻¹) : O u)) (c ∅) rfl hodd
    have hsum : (residue u)
        (∑ S : Finset (PrimeIndex u), (subsetSign S : O u) *
          toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
            (↑((c S)⁻¹) : O u)) =
        ∑ S : Finset (PrimeIndex u), (residue u)
          ((subsetSign S : O u) *
            toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
              (↑((c S)⁻¹) : O u)) :=
      map_sum (residue u).toAddMonoidHom _ _
    rw [hsum] at hnonzero
    simpa only [map_mul, map_intCast, mul_assoc] using hnonzero

end CirculantHadamard.BinaryLocalFamily

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingNorm ----
namespace OAI

universe uR uIota

/-!
# Complex norms after clearing an alternating-product denominator

The integral alternating product is related to its character values by a
polynomial identity in the coefficient ring. Applying an arbitrary complex
ring homomorphism to that identity is legitimate even before knowing that the
homomorphism extends to the fraction field. Equal numbers of numerator and
denominator factors, all of the same positive norm, then force norm one.
-/

namespace CirculantHadamard.AlternatingNorm

open scoped BigOperators

theorem norm_map_prod_of_const {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (s : Finset ι) (c : ℝ)
    (hx : ∀ i ∈ s, ‖σ (x i)‖ = c) :
    ‖σ (∏ i ∈ s, x i)‖ = c ^ s.card := by
  classical
  rw [map_prod, norm_prod]
  calc
    (∏ i ∈ s, ‖σ (x i)‖) = ∏ _i ∈ s, c := Finset.prod_congr rfl hx
    _ = c ^ s.card := by simp

/-- The numerator and denominator have equally many character factors.
Only a genuine cleared identity in `R` is required; there is no assumed norm
bound on `z`, no injectivity assumption on `σ`, and no fraction-field extension.
-/
theorem norm_eq_one_of_balanced_products {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (numerator denominator : Finset ι)
    (z : R) (c : ℝ) (hc : 0 < c)
    (hcard : numerator.card = denominator.card)
    (hnumerator : ∀ i ∈ numerator, ‖σ (x i)‖ = c)
    (hdenominator : ∀ i ∈ denominator, ‖σ (x i)‖ = c)
    (hclear : z * (∏ i ∈ denominator, x i) = ∏ i ∈ numerator, x i) :
    ‖σ z‖ = 1 := by
  have hmap := congrArg σ hclear
  rw [map_mul] at hmap
  have hnorm := congrArg norm hmap
  rw [norm_mul,
    norm_map_prod_of_const σ x denominator c hdenominator,
    norm_map_prod_of_const σ x numerator c hnumerator,
    hcard] at hnorm
  have hpositive : 0 < c ^ denominator.card := pow_pos hc _
  nlinarith

end CirculantHadamard.AlternatingNorm

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingField ----
namespace OAI

universe uI uK uR

/-!
# Clearing the actual alternating fraction

The field formula for an integral alternating product is first converted to
an identity in its coefficient ring. Arbitrary complex homomorphisms are then
applied to that identity, without extending them to the field of fractions.
The only nonvanishing inputs are the individual character values.
-/

namespace CirculantHadamard

open scoped BigOperators

theorem oddSubsetProduct_ne_zero {I : Type uI} {K : Type uK} [Field K]
    (t : Finset I) (x : Finset I → K)
    (hx : ∀ S ⊆ t, x S ≠ 0) : oddSubsetProduct t x ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro S hS
  exact hx S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

/-- An equality in the fraction field genuinely clears to the coefficient
ring. The field embedding is used only to reflect this polynomial identity. -/
theorem cleared_alternatingProduct_identity {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S))) :
    z * oddSubsetProduct t x = evenSubsetProduct t x := by
  have hodd : f (oddSubsetProduct t x) =
      oddSubsetProduct t (fun S => f (x S)) :=
    map_oddSubsetProduct f.toMonoidHom t x
  have heven : f (evenSubsetProduct t x) =
      evenSubsetProduct t (fun S => f (x S)) :=
    map_evenSubsetProduct f.toMonoidHom t x
  apply hf
  rw [map_mul, hodd, heven, hz, alternatingProduct_eq_even_div_odd]
  exact div_mul_cancel₀ _ (oddSubsetProduct_ne_zero t (fun S => f (x S)) hx)

/-- Once the actual alternating fraction belongs to the coefficient ring,
every complex homomorphism has modulus one if each character value has the
same positive modulus. Subset parity supplies the equal factor counts. -/
theorem norm_hom_integral_alternatingProduct {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (ht : t.Nonempty) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S)))
    (σ : R →+* ℂ) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ S ⊆ t, ‖σ (x S)‖ = c) : ‖σ z‖ = 1 := by
  classical
  apply AlternatingNorm.norm_eq_one_of_balanced_products σ x
    (t.powerset.filter (fun S => Even S.card))
    (t.powerset.filter (fun S => Odd S.card)) z c hc
    (card_even_subsets_eq_card_odd_subsets t ht)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · exact cleared_alternatingProduct_identity f hf t x z hx hz

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalizationIntersection ----
namespace OAI

universe uR uK

/-!
# Recovering a global coefficient from its local representations

The denominator-ideal argument works in any commutative algebra. It identifies
the intersection of maximal localizations inside a fraction field with the
base ring, both as subalgebra membership and through actual local elements.
-/

namespace CirculantHadamard

section FractionField

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Membership in every maximal localization, realized inside a common fraction
field, gives a base-ring representative. -/
theorem exists_base_of_mem_all_maximal_localizations
    {z : K}
    (hz : ∀ m : MaximalSpectrum R,
      z ∈ Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = z := by
  have hzall : z ∈ (⨅ m : MaximalSpectrum R,
      Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :=
    Algebra.mem_iInf.mpr hz
  rw [MaximalSpectrum.iInf_localization_eq_bot R K] at hzall
  exact Algebra.mem_bot.mp hzall

/-- A fraction-field element represented by an actual element of each maximal
local ring is the image of a base-ring element. -/
theorem exists_base_of_localization_images
    {z : K}
    (hz : ∀ m : MaximalSpectrum R, ∃ y : Localization.AtPrime m.asIdeal,
      Localization.mapToFractionRing K m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal)
        m.asIdeal.primeCompl_le_nonZeroDivisors y = z) :
    ∃ r : R, algebraMap R K r = z := by
  apply exists_base_of_mem_all_maximal_localizations
  intro m
  obtain ⟨y, hy⟩ := hz m
  change ∃ (a s : R) (_ : s ∈ m.asIdeal.primeCompl),
    z = algebraMap R K a * (algebraMap R K s)⁻¹
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
    (Localization.AtPrime m.asIdeal) z).mp ⟨y, hy⟩

end FractionField

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ResidueOneAssociation ----
namespace OAI

universe uS uk

/-!
# Association by a unit with residue one

This algebraic relation expresses the local comparison conclusion without
introducing division in the coefficient ring. The scalar-cancellation lemmas
require regularity explicitly; they do not give group rings a domain instance.
For a local ring, the residue map is the quotient by its maximal ideal.
-/

namespace CirculantHadamard.LocalComparison

variable {S : Type uS} {k : Type uk} [CommRing S] [CommRing k]

namespace ResidueOneAssociated

variable {residue : S →+* k} {x y z c x' y' : S}

theorem mul_left (h : ResidueOneAssociated residue x y) (c : S) :
    ResidueOneAssociated residue (c * x) (c * y) := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u, ?_, hu⟩
  rw [hxy]
  ac_rfl

/-- With equal nonzero products, a comparison for one factor gives the inverse
unit as comparison for the other factor. Only regularity of `y` is needed. -/
theorem product_complement_of_regular (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hy : IsLeftRegular y) :
    ResidueOneAssociated residue x' y' := by
  obtain ⟨u, hxy, hu⟩ := h
  have hcancel : (u : S) * x' = y' := by
    apply hy
    calc
      y * ((u : S) * x') = ((u : S) * y) * x' := by ac_rfl
      _ = x * x' := by rw [← hxy]
      _ = y * y' := hprod
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [← hcancel, Units.inv_mul_cancel_left]

/-- The two-factor step used in the character-comparison base case. -/
theorem product_complement [IsDomain S] (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hne : y * y' ≠ 0) :
    ResidueOneAssociated residue x' y' := by
  have hy : y ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
  exact h.product_complement_of_regular hprod (fun _ _ h => mul_left_cancel₀ hy h)

/-- Two units with the same residue differ by a unit with residue one. -/
theorem of_isUnit_of_residue_eq (residue : S →+* k)
    (hx : IsUnit x) (hy : IsUnit y) (hres : residue x = residue y) :
    ResidueOneAssociated residue x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u * v⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [Units.val_mul, map_mul, hres, ← map_mul, Units.mul_inv, map_one]

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

/-- Equality to the residue of a unit forces an element of a local ring to be
a unit. The residue map is the actual quotient by the maximal ideal. -/
theorem isUnit_of_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  rw [hres]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit y).mpr hy

/-- Concrete local-ring base case: an augmentation unit and agreement in the
residue field suffice to construct the comparison unit. -/
theorem residueOneAssociated_of_isUnit_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ResidueOneAssociated (IsLocalRing.residue S) x y :=
  ResidueOneAssociated.of_isUnit_of_residue_eq (IsLocalRing.residue S)
    (isUnit_of_residue_eq hy hres) hy hres

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicLocalBase ----
namespace OAI

universe uK uR uA

/-!
# The unramified cyclotomic coefficient ring

We use the actual subring `ℤ[eta]` of `ℂ`. At a maximal ideal above a
rational prime not dividing the order of `eta`, its localization has maximal
ideal generated by that prime. The central argument proves the vanishing of
the universal derivation by differentiating `eta ^ L = 1`.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicLocalBase

open IsLocalRing

variable {eta : ℂ} {L p : ℕ}

theorem order_pos (hpL : ¬ p ∣ L) : 0 < L := by
  apply Nat.pos_of_ne_zero
  intro h
  apply hpL
  rw [h]
  exact dvd_zero p

theorem order_finite (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    Module.Finite ℤ (Order eta) := (powerBasis hη hL).finite

theorem generator_pow (hη : IsPrimitiveRoot eta L) :
    generator eta ^ L = 1 := by
  apply Subtype.ext
  exact hη.pow_eq_one

theorem order_not_mem (hp : p.Prime) (hpL : ¬ p ∣ L)
    (m : Ideal (Order eta)) [hm : m.IsMaximal] (hpm : (p : Order eta) ∈ m) :
    (L : Order eta) ∉ m := by
  intro hLm
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd.mpr hpL).cast (R := Order eta)
  have hone : (1 : Order eta) ∈ m := by
    rw [← hab]
    exact m.add_mem (m.mul_mem_left a hpm) (m.mul_mem_left b hLm)
  exact hm.ne_top (m.eq_top_iff_one.mpr hone)

theorem order_isUnit (hp : p.Prime) (hpL : ¬ p ∣ L)
    (m : Ideal (Order eta)) [m.IsMaximal] (hpm : (p : Order eta) ∈ m) :
    IsUnit (L : Local eta m) := by
  simpa only [map_natCast] using
    (IsLocalization.AtPrime.isUnit_to_map_iff (Local eta m) m (L : Order eta)).mpr
      (order_not_mem hp hpL m hpm)

private theorem formallyUnramified_of_powerBasis
    {K : Type uK} {R : Type uR} {A : Type uA} [CommRing K] [CommRing R] [CommRing A] [Algebra K R] [Algebra K A]
    [Algebra R A] [IsScalarTower K R A] (M : Submonoid R) [IsLocalization M A]
    (pb : PowerBasis K R) {L : ℕ} (hL : 0 < L) (hroot : pb.gen ^ L = 1)
    (hLu : IsUnit (L : A)) : Algebra.FormallyUnramified K A := by
  let z : A := algebraMap R A pb.gen
  let D : Derivation K A (KaehlerDifferential K A) := KaehlerDifferential.D K A
  have hzpow : z ^ L = 1 := by
    dsimp [z]
    rw [← map_pow, hroot, map_one]
  have hzunit : IsUnit z := by
    apply IsUnit.of_mul_eq_one (z ^ (L - 1))
    rw [← pow_succ', Nat.sub_add_cancel hL, hzpow]
  have hDroot : D z = 0 := by
    have hpow := congrArg D hzpow
    have hzero : (L : A) • (z ^ (L - 1) • D z : KaehlerDifferential K A) =
        (0 : KaehlerDifferential K A) := by
      simpa only [Derivation.leibniz_pow, Derivation.map_one_eq_zero,
        Nat.cast_smul_eq_nsmul A] using hpow
    have hcancel : z ^ (L - 1) • D z = (0 : KaehlerDifferential K A) :=
      hLu.smul_eq_zero.mp hzero
    exact (hzunit.pow (L - 1)).smul_eq_zero.mp hcancel
  have hDorder (a : R) : D (algebraMap R A a) = 0 := by
    obtain ⟨f, hf⟩ := pb.exists_eq_aeval' a
    rw [hf]
    change D ((IsScalarTower.toAlgHom K R A) (Polynomial.aeval pb.gen f)) = 0
    rw [← Polynomial.aeval_algHom_apply, Derivation.map_aeval]
    change Polynomial.aeval z (Polynomial.derivative f) • D z = 0
    rw [hDroot, smul_zero]
  have hD (x : A) : D x = 0 := by
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj M x
    have hd := congrArg D hxs
    rw [Derivation.leibniz, hDorder, hDorder, smul_zero, zero_add] at hd
    exact (IsLocalization.map_units A s).smul_eq_zero.mp hd
  have hspan : Submodule.span A (Set.range D) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro x ⟨y, rfl⟩
    exact hD y
  have htop : (⊤ : Submodule A (KaehlerDifferential K A)) = ⊥ :=
    (KaehlerDifferential.span_range_derivation K A).symm.trans hspan
  have hall (x : KaehlerDifferential K A) : x = 0 := by
    have hx : x ∈ (⊤ : Submodule A (KaehlerDifferential K A)) := trivial
    rw [htop, Submodule.mem_bot] at hx
    exact hx
  exact ⟨⟨fun x y => (hall x).trans (hall y).symm⟩⟩

/-- Every absolute differential vanishes: the root has invertible derivative,
and the same vanishing extends across the localization denominators. -/
theorem formallyUnramified (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : Algebra.FormallyUnramified ℤ (Local eta m) := by
  let : Algebra (Order eta) (Local eta m) :=
    OreLocalization.instAlgebra (R := Order eta) (S := m.primeCompl) (R₀ := Order eta)
  let : SMul (Order eta) (Local eta m) :=
    (inferInstance : Algebra (Order eta) (Local eta m)).toSMul
  let : Module (Order eta) (Local eta m) := Algebra.toModule
  let : IsScalarTower ℤ (Order eta) (Local eta m) :=
    AddCommGroup.intIsScalarTower
  apply formallyUnramified_of_powerBasis m.primeCompl
    (powerBasis hη (order_pos hpL)) (order_pos hpL)
  · simpa only [powerBasis_gen] using generator_pow hη
  · exact order_isUnit hp hpL m hpm

/-- The rational prime ideal lies under the chosen maximal ideal. -/
theorem liesOver_prime (hp : p.Prime) (m : Ideal (Order eta)) [hm : m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : m.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  constructor
  apply hmax.eq_of_le
  · apply (Ideal.ne_top_iff_one _).mpr
    change algebraMap ℤ (Order eta) 1 ∉ m
    simpa only [map_one] using (m.ne_top_iff_one.mp hm.ne_top)
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change algebraMap ℤ (Order eta) (p : ℤ) ∈ m
    simpa only [Ideal.mem_under, map_natCast, map_intCast, Int.cast_natCast] using hpm

/-- The maximal ideal is generated by the actual rational prime. -/
theorem maximalIdeal_eq_span (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) :
    maximalIdeal (Local eta m) = Ideal.span {(p : Local eta m)} := by
  let := order_finite hη (order_pos hpL)
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : P.IsPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  let : m.LiesOver P := liesOver_prime hp m hpm
  let := Localization.AtPrime.algebraOfLiesOver P m
  have hU : Algebra.IsUnramifiedAt ℤ m := formallyUnramified hη hp hpL m hpm
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq ℤ P m).mp hU).2
  simpa only [P, Ideal.map_span, Set.image_singleton, map_natCast, map_intCast,
    Int.cast_natCast] using
    hmap.symm

end CirculantHadamard.CyclotomicLocalBase

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicAwayLocal ----
namespace OAI

universe uR uS

/-!
# The actual away coefficient localization

The prime ideal is the contraction of a maximal ideal of the actual global
root ring. Its maximality follows from integrality of the coefficient
inclusion, and the single-generator theorem identifies its localization
with the unramified cyclotomic construction.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicAwayLocal

open CyclotomicRings IsLocalRing

/-- Integrality follows from the genuine finite integer module structure of
the global root ring, through the coefficient inclusion. -/
theorem awayInclusion_isIntegral (u p : ℕ) :
    (awayInclusion u p).toRingHom.IsIntegral := by
  apply RingHom.IsIntegral.tower_top (algebraMap ℤ (awayRing u p))
    (awayInclusion u p).toRingHom
  rw [show (awayInclusion u p).toRingHom.comp (algebraMap ℤ (awayRing u p)) =
    algebraMap ℤ (B u) from Subsingleton.elim _ _]
  exact Algebra.IsIntegral.isIntegral

theorem awayMaximal (u p : ℕ) (m : Ideal (B u)) [m.IsMaximal] :
    (awayPrime u p m).IsMaximal :=
  maximal_comap_of_integral (awayInclusion u p).toRingHom
    (awayInclusion_isIntegral u p) m

private theorem natCast_mem_comap_of_mem {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal S) (p : ℕ) (h : (p : S) ∈ m) :
    (p : R) ∈ m.comap f := by
  change f (p : R) ∈ m
  simpa only [map_natCast] using h

theorem prime_mem_awayPrime (u p : ℕ) (m : Ideal (B u))
    (hpm : (p : B u) ∈ m) : (p : awayRing u p) ∈ awayPrime u p m :=
  natCast_mem_comap_of_mem (awayInclusion u p).toRingHom m p hpm

private theorem maximalIdeal_eq_span_of_eq (S : Subalgebra ℤ ℂ) {z : ℂ} {L p : ℕ}
    (hS : S = CyclotomicLocalBase.Order z) (hz : IsPrimitiveRoot z L)
    (hp : p.Prime) (hpL : ¬ p ∣ L) (m : Ideal S) [m.IsMaximal]
    (hpm : (p : S) ∈ m) :
    maximalIdeal (Localization.AtPrime m) = Ideal.span {(p : Localization.AtPrime m)} := by
  subst S
  exact CyclotomicLocalBase.maximalIdeal_eq_span hz hp hpL m hpm

/-- The maximal ideal of the exact contracted localization is generated by
the rational prime; no ring-property premise is assumed. -/
theorem awayLocal_maximalIdeal_eq_span (u p : ℕ) (hu : Odd u)
    (hp : p ∈ u.primeFactors) (m : Ideal (B u)) [m.IsMaximal]
    (hpm : (p : B u) ∈ m) :
    maximalIdeal (AwayLocal u p m) = Ideal.span {(p : AwayLocal u p m)} := by
  let := awayMaximal u p m
  exact maximalIdeal_eq_span_of_eq (awayRing u p) (awayRing_eq_singleton u p hu)
    (eta_isPrimitiveRoot u p hu) (Nat.prime_of_mem_primeFactors hp)
    (prime_not_dvd_awayOrder u p hu hp) (awayPrime u p m)
    (prime_mem_awayPrime u p m hpm)

theorem awayLocal_prime_ne_zero (u p : ℕ) (hp : p ∈ u.primeFactors)
    (m : Ideal (B u)) [m.IsPrime] : (p : AwayLocal u p m) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem awayLocal_isDiscreteValuationRing (u p : ℕ) (hu : Odd u)
    (hp : p ∈ u.primeFactors) (m : Ideal (B u)) [m.IsMaximal]
    (hpm : (p : B u) ∈ m) : IsDiscreteValuationRing (AwayLocal u p m) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (awayLocal_prime_ne_zero u p hp m)
    (awayLocal_maximalIdeal_eq_span u p hu hp m hpm)

end CirculantHadamard.CyclotomicAwayLocal

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicScalarDivision ----
namespace OAI

universe uR uG uH

/-!
# Division by regular coefficient scalars in an additive monoid algebra

A finite group algebra usually has zero divisors. A nonzero scalar from a
domain nevertheless acts injectively, as is seen separately at each coefficient.
This is the cancellation needed when the projected norm equation is divided by
one power of the residue characteristic.
-/

noncomputable section

namespace CirculantHadamard

section DivisionExists

variable {R : Type uR} {G : Type uG} [CommRing R] [AddMonoid G] [finiteG : Finite G]

end DivisionExists

section Cancellation

variable {R : Type uR} {G : Type uG} [CommRing R] [IsDomain R] [AddMonoid G]

/-- A scalar is cancellable because its action at each coefficient is
injective. No domain structure is asserted for the group algebra. -/
theorem scalar_mul_left_cancel (p : R) (hp : p ≠ 0)
    {F K : AddMonoidAlgebra R G}
    (h : AddMonoidAlgebra.single (0 : G) p * F =
      AddMonoidAlgebra.single (0 : G) p * K) : F = K := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  apply mul_left_cancel₀ hp
  simpa only [AddMonoidAlgebra.coeff_single_zero_mul] using
    congrArg (fun H : AddMonoidAlgebra R G => H.coeff g) h

/-- Cancelling one regular scalar lowers the exponent of the norm equation
by exactly one. This is valid although the group algebra has zero divisors. -/
theorem scalar_mul_norm_division (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G)
    (h : (AddMonoidAlgebra.single (0 : G) p * F) * K =
      AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) :
    F * K = AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
  apply scalar_mul_left_cancel p hp
  calc
    AddMonoidAlgebra.single (0 : G) p * (F * K) =
        (AddMonoidAlgebra.single (0 : G) p * F) * K := (mul_assoc _ _ _).symm
    _ = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b) := h
    _ = AddMonoidAlgebra.single (0 : G) p *
        AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
      rw [pow_succ', mul_assoc]

end Cancellation

section Quotient

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R] [IsDomain R]
  [AddMonoid G] [AddMonoid H]

/-- Project the norm equation along a genuine ring homomorphism and then
divide the chosen projected factor by one coefficient scalar. -/
theorem quotient_scalar_norm_division
    (q : AddMonoidAlgebra R G →+* AddMonoidAlgebra R H)
    (hscalar : ∀ r : R, q (AddMonoidAlgebra.single (0 : G) r) =
      AddMonoidAlgebra.single (0 : H) r)
    (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G) (F' : AddMonoidAlgebra R H)
    (hFK : F * K = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b))
    (hF : q F = AddMonoidAlgebra.single (0 : H) p * F') :
    F' * q K = AddMonoidAlgebra.single (0 : H) (p ^ e * b) := by
  apply scalar_mul_norm_division p hp e b F' (q K)
  calc
    (AddMonoidAlgebra.single (0 : H) p * F') * q K = q F * q K := by rw [hF]
    _ = q (F * K) := (q.map_mul F K).symm
    _ = q (AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) := congrArg q hFK
    _ = AddMonoidAlgebra.single (0 : H) (p ^ (e + 1) * b) := hscalar _

end Quotient

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction ----
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- If the product has exactly one prime factor up to a unit, at least one
factor is a unit. This elementary base step does not use a valuation. -/
theorem isUnit_or_isUnit_of_mul_prime_unit {p x y : A} (hp : Prime p)
    (b : Aˣ) (hxy : x * y = p * (b : A)) : IsUnit x ∨ IsUnit y := by
  have hdvd : p ∣ x * y := ⟨(b : A), hxy⟩
  rcases hp.dvd_or_dvd hdvd with hx | hy
  · obtain ⟨z, hz⟩ := hx
    have hzy : z * y = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (z * y) = (p * z) * y := (mul_assoc _ _ _).symm
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inr (isUnit_of_mul_isUnit_right (hzy.symm ▸ b.isUnit))
  · obtain ⟨z, hz⟩ := hy
    have hxz : x * z = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (x * z) = x * (p * z) := by ac_rfl
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inl (isUnit_of_mul_isUnit_left (hxz.symm ▸ b.isUnit))

/-- The exponent-one base case, using the actual residue field of `S`. -/
theorem comparison_base (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  have haug : augmentation n F * augmentation n K = (p : A) * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using congrArg (augmentation n) hFK
  have hv : v F * v K = φ ((p : A) * (b : A)) := by
    simpa only [map_mul, vscalar] using congrArg v hFK
  have hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K) := by
    calc
      v F * v K = φ ((p : A) * (b : A)) := hv
      _ = φ (augmentation n F * augmentation n K) := congrArg φ haug.symm
      _ = φ (augmentation n F) * φ (augmentation n K) := φ.map_mul _ _
  have hne : φ (augmentation n F) * φ (augmentation n K) ≠ 0 := by
    rw [← map_mul, haug, map_mul]
    exact mul_ne_zero hpS (b.isUnit.map φ).ne_zero
  rcases isUnit_or_isUnit_of_mul_prime_unit hp b haug with hF | hK
  · have h := residueOneAssociated_of_isUnit_residue_eq (hF.map φ) (vres F)
    exact ⟨h, h.product_complement hprod hne⟩
  · have h := residueOneAssociated_of_isUnit_residue_eq (hK.map φ) (vres K)
    have hprod' : v K * v F = φ (augmentation n K) * φ (augmentation n F) := by
      simpa only [mul_comm] using hprod
    have hne' : φ (augmentation n K) * φ (augmentation n F) ≠ 0 := by
      simpa only [mul_comm] using hne
    exact ⟨h.product_complement hprod' hne', h⟩

omit domainS in
/-- Induction step when the first projected factor is divisible by `p`.
The other factor is left intact. The two output associations are both
transported, so the next step may divide either factor. -/
theorem comparison_step_left [IsDomain S] (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by
  let q := cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1)))
  have hdiv : F' * q K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) :=
    quotient_scalar_norm_division q (fun a => cyclicProjection_single_zero _ a)
      (p : A) hp (e + 1) (b : A) F K F' hFK hF
  obtain ⟨hiF, hiK⟩ := ih F' (q K) hdiv
  have heval : v' F = φ (p : A) * v F' := by
    rw [← vq F, hF, map_mul, vscalar]
  have haug : augmentation (p ^ (e + 2)) F =
      (p : A) * augmentation (p ^ (e + 1)) F' := by
    rw [← augmentation_cyclicProjection (pow_dvd_pow p (Nat.le_succ (e + 1))) F,
      hF, map_mul, augmentation_scalar]
  constructor
  · rw [heval, haug, map_mul]
    exact hiF.mul_left (φ (p : A))
  · simpa only [q, vq, augmentation_cyclicProjection] using hiK

/-- The integral induction with its projection-divisibility input exposed.
The concrete cyclotomic theorem discharges `hdivide`; it is not a definition
of the comparison conclusion. -/
theorem comparison_induction (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by
  intro e
  induction e with
  | zero =>
      intro b F K hFK
      exact comparison_base (p ^ (0 + 1)) p φ hp hpS (v 0) (vscalar 0) vres
        b F K (by simpa only [Nat.zero_add, pow_one] using hFK)
  | succ e ih =>
      intro b F K hFK
      rcases hdivide e b F K hFK with ⟨F', hF⟩ | ⟨K', hK⟩
      · exact comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b F K hFK F' hF (ih b)
      · have hKF : K * F = scalar (p ^ (e + 2))
            ((p : A) ^ (e + 2) * (b : A)) := by
          simpa only [mul_comm] using hFK
        exact (comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b K F hKF K' hK (ih b)).symm

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicProjectionPolynomial ----
namespace OAI

universe uR

/-! Polynomial evaluation commutes with the concrete cyclic quotient map. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [CommRing R] {m n : ℕ}

/-- Polynomial evaluation at the generator commutes with the cyclic quotient. -/
theorem cyclicProjection_aeval (h : m ∣ n) (F : Polynomial R) :
    cyclicProjection R h (Polynomial.aeval (CyclicPolynomial.generator R n) F) =
      Polynomial.aeval (CyclicPolynomial.generator R m) F := by
  change cyclicProjectionAlgHom R h
    (Polynomial.aeval (CyclicPolynomial.generator R n) F) = _
  have hgen : cyclicProjectionAlgHom R h (CyclicPolynomial.generator R n) =
      CyclicPolynomial.generator R m := cyclicProjection_generator (R := R) h
  rw [← Polynomial.aeval_algHom_apply, hgen]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicProjection ----
namespace OAI

universe uR uS

/-!
# Integral division after projection to a smaller cyclic group

At an element of order dividing `p ^ e`, the prime-power cyclotomic polynomial
`cyclotomic (p ^ (e + 1)) R` evaluates to the scalar `p`. Consequently, if all
coefficients of a polynomial's monic remainder are divisible by `p`, its image
in the group algebra of `ZMod (p ^ e)` is divisible by the same scalar.

All divisions are witnessed inside the coefficient ring or group algebra.
No domain instance or cancellation assumption on a finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Every actual cyclic group-ring element has a polynomial representative. -/
theorem exists_cyclic_polynomial (n : ℕ) [NeZero n]
    (F : AddMonoidAlgebra R (ZMod n)) :
    ∃ P : R[X], aeval (CyclicPolynomial.generator R n) P = F := by
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (CyclicPolynomial.cyclicEquiv R n F)
  refine ⟨P, ?_⟩
  apply (CyclicPolynomial.cyclicEquiv R n).injective
  rw [CyclicPolynomial.cyclicEquiv_aeval, hP]

/-- A prime-power cyclotomic polynomial becomes `p` at every element whose
`p ^ e`th power is one. -/
theorem aeval_cyclotomic_prime_pow_of_pow_eq_one {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) :
    aeval x (cyclotomic (p ^ (e + 1)) R) = (p : S) := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp]
  simp [hx]

/-- Evaluating a monic division identity preserves integral divisibility if
both the divisor's evaluation and the remainder have the stated scalar factor. -/
theorem aeval_divisible_of_modByMonic_coeff (x : S) (F Q : R[X]) (a : R)
    (_hQ : Q.Monic) (hQx : aeval x Q = algebraMap R S a)
    (hcoeff : ∀ i, a ∣ (F %ₘ Q).coeff i) :
    ∃ G : S, aeval x F = algebraMap R S a * G := by
  obtain ⟨T, hT⟩ := (C_dvd_iff_dvd_coeff a (F %ₘ Q)).2 hcoeff
  refine ⟨aeval x T + aeval x (F /ₘ Q), ?_⟩
  calc
    aeval x F = aeval x (F %ₘ Q) + aeval x Q * aeval x (F /ₘ Q) := by
      rw [← map_mul, ← map_add, modByMonic_add_div F Q]
    _ = algebraMap R S a * (aeval x T + aeval x (F /ₘ Q)) := by
      rw [hT, map_mul, aeval_C, hQx, mul_add]

/-- Integral divisibility at a `p ^ e`th root follows from coefficientwise
divisibility of the remainder modulo the next cyclotomic polynomial. -/
theorem aeval_divisible_of_cyclotomic_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : S, aeval x F = (p : S) * G := by
  have hQx : aeval x (cyclotomic (p ^ (e + 1)) R) =
      algebraMap R S (p : R) := by
    simpa only [map_natCast] using aeval_cyclotomic_prime_pow_of_pow_eq_one hp x hx
  simpa only [map_natCast] using aeval_divisible_of_modByMonic_coeff x F
    (cyclotomic (p ^ (e + 1)) R) (p : R) (cyclotomic.monic _ _) hQx hcoeff

/-- The concrete `p`-division step in the cyclic group algebra: project from
order `p ^ (e + 1)` to order `p ^ e`, then divide integrally by `p`. -/
theorem cyclicProjection_divisible_of_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e))
          (aeval (CyclicPolynomial.generator R (p ^ (e + 1))) F) =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  rw [cyclicProjection_aeval]
  exact aeval_divisible_of_cyclotomic_remainder_coeff hp
    (CyclicPolynomial.generator R (p ^ e)) (CyclicPolynomial.generator_pow R (p ^ e))
    F hcoeff

/-- Divisibility at the actual primitive-root quotient forces integral
divisibility after projecting the actual cyclic group-ring element.

The concrete monic quotient's linear remainder map supplies coefficientwise
divisibility of the remainder. -/
theorem cyclicProjection_divisible_of_cyclotomicEvaluation {p e : ℕ}
    [NeZero p] (hp : p.Prime) (F : AddMonoidAlgebra R (ZMod (p ^ (e + 1))))
    (hdiv : (p : AdjoinRoot (cyclotomic (p ^ (e + 1)) R)) ∣
      cyclicCyclotomicEvaluation R (p ^ (e + 1)) F) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e)) F =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  obtain ⟨P, rfl⟩ := exists_cyclic_polynomial (p ^ (e + 1)) F
  rw [cyclicCyclotomicEvaluation_aeval] at hdiv
  apply cyclicProjection_divisible_of_remainder_coeff hp P
  intro i
  exact CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (p ^ (e + 1)) R) (cyclotomic.monic _ _) (p : R) P
    (by simpa only [map_natCast] using hdiv) i

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicFactorDivision ----
namespace OAI

universe uA

/-!
# A projected factor is integrally divisible by the residue prime

The primitive-character values live in the actual cyclotomic quotient. Their
product is evaluated from the actual group-ring product. The DVR inequality
chooses a factor, and the monic remainder theorem transfers its divisibility
to the smaller cyclic group ring.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial IsDiscreteValuationRing

variable {A : Type uA} [CommRing A]

/-- The ramified DVR and its value of `p` imply the concrete choice of a
divisible projected factor. These are local-ring properties, independent of
the input factors. The scalar and group exponents are both `e + 2`. -/
theorem projected_factor_divisible {p e D : ℕ} [NeZero p] (hp : p.Prime)
    [IsDomain (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    [IsDiscreteValuationRing (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    (hpS : (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ≠ 0)
    (hD : 0 < D)
    (hpval : addVal (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) = (D : ℕ∞))
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A))) :
    (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F') ∨
    (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
      scalar (p ^ (e + 1)) (p : A) * K') := by
  let v := cyclicCyclotomicEvaluation A (p ^ (e + 2))
  have hscalar : ∀ a : A, v (scalar (p ^ (e + 2)) a) =
      algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) a := by
    intro a
    exact v.commutes a
  have hv : v F * v K =
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ^ (e + 2) *
        algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) (b : A) := by
    have h := congrArg v hFK
    simpa only [map_mul, hscalar, map_pow, map_natCast] using h
  have hb : IsUnit (algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (b : A)) := b.isUnit.map _
  have hchoose := LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
    hpS hD hpval (Nat.le_add_left 2 e) hb hv
  rcases hchoose with hF | hK
  · left
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp F hF
  · right
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp K hK

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationProjection ----
namespace OAI

universe uR uS

/-! Evaluation at a root of smaller order factors through the cyclic quotient. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The actual root evaluation is unchanged after reducing the cyclic index.
Both root equations are stated explicitly to match the two evaluation maps. -/
theorem evaluateAt_cyclicProjection (h : m ∣ n)
    (x : S) (hm : x ^ m = 1) (hn : x ^ n = 1) (F : Elem R n) :
    evaluateAt m x hm (cyclicProjection R h F) = evaluateAt n x hn F := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change evaluateAt m x hm (cyclicProjection R h ((F : Elem R n) + G)) =
      evaluateAt n x hn ((F : Elem R n) + G)
    simp only [map_add, hF, hG]
  · intro a r
    simp only [cyclicProjection_single, evaluateAt_single]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [← pow_eq_pow_mod _ hm]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparison ----
namespace OAI

universe uA

/-!
# Local character comparison in the actual cyclotomic quotient

Starting with a characteristic-zero DVR whose maximal ideal is generated by
the rational prime `p`, all ramified rings needed by the induction are
constructed as the actual cyclotomic quotients. No projection-divisibility,
comparison, or existence-of-valuation premise is taken from the caller.

The conclusion uses membership in the ideal generated by `root - 1` to state
residue one. This is independent of how a local-ring instance is installed and
can be transported directly to a later localization.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial

variable (A : Type uA) [CommRing A]

theorem orderPValue_projection (p e : ℕ) [NeZero p]
    (F : Elem A (p ^ (e + 2))) :
    orderPValue A p e
        (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) =
      orderPValue A p (e + 1) F :=
  evaluateAt_cyclicProjection _ _ _ _ F

section DVR

variable [IsDomain A] [CharZero A] [IsDiscreteValuationRing A]

/-- Character comparison with every ramified extension constructed from the
input DVR. Both factors are compared, with matching group/scalar exponents. -/
theorem local_character_comparison (p : ℕ) [NeZero p] (hp : p.Prime)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    (e : ℕ) (b : Aˣ) (F K : Elem A (p ^ (e + 1)))
    (hFK : F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A))) :
    OrderPCompared A p e F ∧ OrderPCompared A p e K := by
  let : IsDomain (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isDomain A hp 0 hmax
  let : IsLocalRing (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isLocalRing A hp 0 hmax
  have hpA : Prime (p : A) :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer (p : A)).mpr hmax).prime
  have hpS : algebraMap A (RamifiedLocal.Extension A p 0) (p : A) ≠ 0 := by
    intro h
    exact hpA.ne_zero (RamifiedLocal.algebraMap_injective A hp 0
      (by simpa only [map_zero] using h))
  have hroot : IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPRoot A p) = 1 := by
    have hpi : RamifiedLocal.uniformizer A p 0 ∈
        IsLocalRing.maximalIdeal (RamifiedLocal.Extension A p 0) := by
      rw [RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hpi
    simpa only [RamifiedLocal.uniformizer, orderPRoot, map_sub, map_one, sub_eq_zero] using hz
  have hc := comparison_induction p (algebraMap A (RamifiedLocal.Extension A p 0))
    hpA hpS (fun k => (orderPValue A p k).toRingHom)
    (fun k a => orderPValue_scalar A p k a)
    (by
      intro U
      change IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPValue A p 0 U) =
        IsLocalRing.residue (RamifiedLocal.Extension A p 0)
          (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ 1) U))
      simp only [orderPValue, evaluateAt_apply,
        augmentation_apply, map_sum, map_mul, map_pow, hroot, one_pow, mul_one])
    (fun k U => orderPValue_projection A p k U)
    (by
      intro k c U V hUV
      let : IsDomain (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDomain A hp (k + 1) hmax
      let : IsLocalRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isLocalRing A hp (k + 1) hmax
      let : IsDiscreteValuationRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDiscreteValuationRing A hp (k + 1) hmax
      have hpR : (p : RamifiedLocal.Extension A p (k + 1)) ≠ 0 := by
        intro h
        apply hpA.ne_zero
        apply RamifiedLocal.algebraMap_injective A hp (k + 1)
        simpa only [map_natCast, map_zero] using h
      exact projected_factor_divisible hp hpR
        (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos (k + 1)))
        (RamifiedLocal.addVal_prime A hp (k + 1) hmax) c U V hUV)
    e b F K hFK
  have toCompared {U : Elem A (p ^ (e + 1))}
      (hU : ResidueOneAssociated (IsLocalRing.residue (RamifiedLocal.Extension A p 0))
        (orderPValue A p e U)
        (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ (e + 1)) U))) :
      OrderPCompared A p e U := by
    obtain ⟨u, hu, hres⟩ := hU
    refine ⟨u, hu, ?_⟩
    rw [← RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, hres, map_one, sub_self]
  exact ⟨toCompared hc.1, toCompared hc.2⟩

end DVR

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR uK uAZero uS uL uI uk

/-!
# Local representatives of the fixed alternating product

All local rings are actual localizations at maximal ideals. Their maps
into the common fraction field are canonical. The adjoined-root comparison
map is constructed from the actual base-ring inclusion and cyclotomic relation.
Membership in every maximal localization implies membership in the base ring.
-/

noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

theorem toFraction_injective {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : Function.Injective (toFraction K m) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := m.asIdeal.primeCompl) (AtMaximal R m) (toFraction K m).toRingHom
  intro a ha
  change toFraction K m (algebraMap R (AtMaximal R m) a) = 0 at ha
  rw [AlgHom.commutes] at ha
  have ha0 : a = 0 := IsFractionRing.injective R K (by simpa only [map_zero] using ha)
  rw [ha0, map_zero]

/-- The integral representative and a local representative of the same fixed
fraction agree under the actual coefficient localization map. -/
theorem local_representative_eq {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) (b : R) (v : AtMaximal R m)
    (h : algebraMap R K b = toFraction K m v) :
    algebraMap R (AtMaximal R m) b = v := by
  apply toFraction_injective K m
  simpa only [AlgHom.commutes] using h

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Residue characteristic is derived from membership of the rational prime,
not assumed as an independent property of the chosen maximal ideal. -/
theorem residue_charP (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) :
    CharP (IsLocalRing.ResidueField (AtMaximal R m)) p := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  have hpzero : (p : k) = 0 := by
    have hm : algebraMap R (AtMaximal R m) (p : R) ∈
        IsLocalRing.maximalIdeal (AtMaximal R m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (AtMaximal R m) m.asIdeal _).mpr hpm
    simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff _).mpr hm
  exact (CharP.charP_iff_prime_eq_zero hp).mpr hpzero

/-- A p-th root has residue one at every maximal ideal containing p. -/
theorem residue_root_eq_one (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) (rho : R) (hrho : rho ^ p = 1) :
    IsLocalRing.residue (AtMaximal R m) (algebraMap R (AtMaximal R m) rho) = 1 := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  let : Fact p.Prime := ⟨hp⟩
  let : CharP k p := residue_charP m p hp hpm
  let r : k := IsLocalRing.residue (AtMaximal R m)
    (algebraMap R (AtMaximal R m) rho)
  have hpow : r ^ p = 1 := by
    dsimp [r]
    rw [← map_pow, ← map_pow, hrho, map_one, map_one]
  have hnil : (r - 1) ^ p = 0 := by rw [sub_pow_char, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hnil)

theorem residue_unit_eq_one_of_span {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing L] (f : S →+* L) (rho : S) (v : Sˣ)
    (hv : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) :
    IsLocalRing.residue L ((Units.map f.toMonoidHom v : Lˣ) : L) = 1 := by
  let g : S →+* IsLocalRing.ResidueField L := (IsLocalRing.residue L).comp f
  have hspan : Ideal.span ({rho - 1} : Set S) ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = rho - 1 := Set.mem_singleton_iff.mp ha
    subst a
    change g (rho - 1) = 0
    simp only [map_sub, map_one, RingHom.comp_apply, g, hrho, sub_self]
  have hz := hspan hv
  change g ((v : S) - 1) = 0 at hz
  have hval : g (v : S) = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)
  exact hval

end ActualComparisonMap

/-- The local association is converted to the actual fraction-field quotient
only after the augmentation image is known to be nonzero. -/
theorem local_edge_of_associated {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (m : MaximalSpectrum R)
    (a b : R) (hb : algebraMap R K b ≠ 0)
    (h : LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m) a) (algebraMap R (AtMaximal R m) b)) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) = algebraMap R K a / algebraMap R K b ∧
      IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1 := by
  obtain ⟨v, hv, hres⟩ := h
  refine ⟨v, ?_, hres⟩
  apply (eq_div_iff hb).mpr
  have hmap := congrArg (toFraction K m) hv
  simpa only [map_mul, AlgHom.commutes] using hmap.symm

/-- A finite prime factorization supplies the away-from-u unit, including u=1. -/
theorem natCast_isUnit_of_primeFactors {R : Type uR} [CommRing R]
    (u : ℕ) (hu : u ≠ 0) (hprime : ∀ p ∈ u.primeFactors, IsUnit (p : R)) :
    IsUnit (u : R) := by
  rw [← Nat.prod_primeFactorsList hu, Nat.cast_list_prod]
  apply List.prod_isUnit
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact hprime p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)

theorem local_norm_factor_isUnit {R : Type uR} [CommRing R]
    (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal)
    (x y : R) (hnorm : x * y = (u : R) ^ 2) :
    IsUnit (algebraMap R (AtMaximal R m) x) := by
  have huunit : IsUnit (u : AtMaximal R m) :=
    natCast_isUnit_of_primeFactors u hu (fun p hp => by
      have h := (IsLocalization.AtPrime.isUnit_to_map_iff
        (AtMaximal R m) m.asIdeal (p : R)).mpr (havoid p hp)
      simpa only [map_natCast] using h)
  apply isUnit_of_mul_isUnit_left (y := algebraMap R (AtMaximal R m) y)
  rw [← map_mul, hnorm, map_pow, map_natCast]
  exact huunit.pow 2

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

theorem exists_unit_of_edges (f : R →+* K) (res : R →+* k)
    (t : Finset I) (p : I) (hp : p ∈ t) (x : Finset I → K)
    (hedge : ∀ S ∈ (t.erase p).powerset, ∃ v : Rˣ,
      f (v : R) = x (insert p S) / x S ∧ res (v : R) = 1) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t x ∧ res (v : R) = 1 := by
  classical
  let edge : Finset I → Rˣ := fun S =>
    if hS : S ∈ (t.erase p).powerset then Classical.choose (hedge S hS) else 1
  have hedge' : ∀ S ∈ (t.erase p).powerset,
      f (edge S : R) = x (insert p S) / x S ∧ res (edge S : R) = 1 := by
    intro S hS
    simpa only [edge, dite_eq_left hS] using Classical.choose_spec (hedge S hS)
  let v : Rˣ := ∏ S ∈ (t.erase p).powerset, (edge S)⁻¹ ^ subsetSign S
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  let tok : Rˣ →* k := res.toMonoidHom.comp (Units.coeHom R)
  refine ⟨v, ?_, ?_⟩
  · change toK v = alternatingProduct t x
    rw [alternatingProduct_pair t x p hp]
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_congr rfl
    intro S hS
    change (f (edge S : R))⁻¹ ^ subsetSign S = _
    rw [(hedge' S hS).1, inv_div]
  · change tok v = 1
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_eq_one
    intro S hS
    change (res (edge S : R))⁻¹ ^ subsetSign S = 1
    rw [(hedge' S hS).2, inv_one, one_zpow]

/-- Ordinary local units give an actual local unit representative of the fixed
field product. The representatives are not independently chosen field values. -/
theorem exists_unit_of_factor_units (f : R →+* K) (t : Finset I)
    (x : Finset I → R) (hx : ∀ S ⊆ t, IsUnit (x S)) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t (fun S => f (x S)) := by
  classical
  let units : Finset I → Rˣ := fun S => if hS : S ⊆ t then (hx S hS).unit else 1
  have hval : ∀ S ⊆ t, (units S : R) = x S := by
    intro S hS
    simp only [units, dite_eq_left hS, IsUnit.unit_spec]
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  refine ⟨alternatingProduct t units, ?_⟩
  change toK (alternatingProduct t units) = _
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change f (units S : R) = f (x S)
  rw [hval S hS]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The away-from-u case uses only the evaluated norm identity and avoidance
of the actual rational prime factors of u. -/
theorem exists_local_unit_away (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (x y : Finset I → R)
    (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) =
        alternatingProduct t (fun S => algebraMap R K (x S)) := by
  obtain ⟨v, hv⟩ := exists_unit_of_factor_units (toFraction K m).toRingHom t
    (fun S => algebraMap R (AtMaximal R m) (x S))
    (fun S hS => local_norm_factor_isUnit m u hu havoid (x S) (y S) (hnorm S hS))
  refine ⟨v, ?_⟩
  change toFraction K m (v : AtMaximal R m) = alternatingProduct t
    (fun S => toFraction K m (algebraMap R (AtMaximal R m) (x S))) at hv
  simpa only [AlgHom.commutes] using hv

/-- Every maximal ideal is covered either by a genuine prime-direction edge
comparison or by the norm argument. Local character comparison supplies the
edge hypotheses, without assuming that the product belongs to the base ring. -/
theorem exists_base_of_edges_and_norm (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (prime : I → ℕ)
    (hcover : ∀ p ∈ u.primeFactors, ∃ i ∈ t, prime i = p)
    (x y : Finset I → R) (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (hedge : ∀ m : MaximalSpectrum R, ∀ i ∈ t, (prime i : R) ∈ m.asIdeal →
      ∀ S ∈ (t.erase i).powerset, ∃ v : (AtMaximal R m)ˣ,
        toFraction K m (v : AtMaximal R m) =
          algebraMap R K (x (insert i S)) / algebraMap R K (x S) ∧
        IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1) :
    ∃ b : R, algebraMap R K b =
      alternatingProduct t (fun S => algebraMap R K (x S)) := by
  classical
  apply exists_base_of_localization_images
  intro m
  by_cases hm : ∃ p ∈ u.primeFactors, (p : R) ∈ m.asIdeal
  · obtain ⟨p, hp, hpm⟩ := hm
    obtain ⟨i, hi, hpi⟩ := hcover p hp
    have him : (prime i : R) ∈ m.asIdeal := by rw [hpi]; exact hpm
    obtain ⟨v, hv, _⟩ := exists_unit_of_edges (toFraction K m).toRingHom
      (IsLocalRing.residue (AtMaximal R m)) t i hi
      (fun S => algebraMap R K (x S)) (hedge m i hi him)
    exact ⟨v, hv⟩
  · have havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal := by
      intro p hp hpm
      exact hm ⟨p, hp, hpm⟩
    obtain ⟨v, hv⟩ := exists_local_unit_away (K := K) m u hu t x y hnorm havoid
    exact ⟨v, hv⟩

end MaximalCover

section ConcreteComparison

open CyclicRing

/-- Bezout makes the complementary integer factor a unit in the actual
localization at any prime containing `p`. -/
theorem coprime_natCast_isUnit {R : Type uR} [CommRing R]
    (I : Ideal R) [I.IsPrime] (p c : ℕ) (hpc : Nat.Coprime p c)
    (hpI : (p : R) ∈ I) : IsUnit (c : Localization.AtPrime I) := by
  have hcI : (c : R) ∉ I := by
    intro hc
    obtain ⟨a, b, hab⟩ := hpc.cast (R := R)
    have hone : (1 : R) ∈ I := by
      rw [← hab]
      exact I.add_mem (I.mul_mem_left a hpI) (I.mul_mem_left b hc)
    exact (inferInstance : I.IsPrime).ne_top (I.eq_top_iff_one.mpr hone)
  simpa only [map_natCast] using
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime I) I (c : R)).mpr hcI

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Apply the proved DVR comparison after coefficient localization and map its
actual unit through the cyclotomic quotient into the target maximal localization.
The group order and scalar prime exponent are the same `p ^ (e + 1)`. -/
theorem actual_local_character_association
    (f : A₀ →+* R) (m : MaximalSpectrum R)
    [IsDomain (AtComap f m)] [CharZero (AtComap f m)]
    [IsDiscreteValuationRing (AtComap f m)]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpm : (p : R) ∈ m.asIdeal)
    (hmax : IsLocalRing.maximalIdeal (AtComap f m) =
      Ideal.span {(p : AtComap f m)})
    (rho : R) (hrho : rho ^ p = 1)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (n e c : ℕ) [NeZero n] (hn : n = p ^ (e + 1))
    (hrhon : rho ^ n = 1) (hc : IsUnit (c : AtComap f m))
    (F K : Elem A₀ n)
    (hFK : F * K = scalar n ((p : A₀) ^ (e + 1) * (c : A₀))) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m)
        (evaluate f (CyclicPolynomial.powerCharacter n rho hrhon) F))
      (algebraMap R (AtMaximal R m) (evaluate f 1 F)) := by
  subst n
  let A := AtComap f m
  let L := AtMaximal R m
  let φ : A₀ →+* A := algebraMap A₀ A
  let FA := coefficientMap φ (p ^ (e + 1)) F
  let KA := coefficientMap φ (p ^ (e + 1)) K
  have hFA : FA * KA = scalar (p ^ (e + 1))
      ((p : A) ^ (e + 1) * (hc.unit : A)) := by
    dsimp [FA, KA]
    rw [← map_mul, hFK, coefficientMap_scalar, map_mul, map_pow,
      map_natCast, map_natCast]
  obtain ⟨v, hv, hvspan⟩ :=
    (LocalComparison.local_character_comparison A p hp hmax e hc.unit FA KA hFA).1
  let j : RamifiedLocal.Extension A p 0 →+* L :=
    comparisonToLocal f m (p ^ (0 + 1)) rho (by simpa only [Nat.zero_add, pow_one] using hroot)
  have jroot : j (LocalComparison.orderPRoot A p) = algebraMap R L rho := by
    exact comparisonToLocal_root f m _ rho _
  have jcoeff (a : A) : j (algebraMap A (RamifiedLocal.Extension A p 0) a) =
      baseToLocal f m a := by
    exact comparisonToLocal_of f m _ rho _ a
  have evalRoot :
      (j.comp (LocalComparison.orderPValue A p e).toRingHom).comp
          (coefficientMap φ (p ^ (e + 1))) =
        (algebraMap R L).comp
          (evaluate f (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single 0 r))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single 0 r))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ (0 : ZMod (p ^ (e + 1))).val)
        (baseToLocal_algebraMap f m r)
    · intro a
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single a 1))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single a 1))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ a.val)
        (baseToLocal_algebraMap f m (1 : A₀))
  have evalOne : j (algebraMap A (RamifiedLocal.Extension A p 0)
      (augmentation (p ^ (e + 1)) FA)) =
        algebraMap R L (evaluate f 1 F) := by
    rw [jcoeff]
    dsimp [FA]
    rw [augmentation_coefficientMap, baseToLocal_algebraMap,
      evaluate_trivial_eq_augmentation]
  have hres : IsLocalRing.residue L
      ((Units.map j.toMonoidHom v : Lˣ) : L) = 1 := by
    apply residue_unit_eq_one_of_span j (LocalComparison.orderPRoot A p) v
    · exact hvspan
    · rw [jroot]
      exact residue_root_eq_one m p hp hpm rho hrho
  refine ⟨Units.map j.toMonoidHom v, ?_, hres⟩
  have heval := DFunLike.congr_fun evalRoot F
  change j (LocalComparison.orderPValue A p e FA) =
    algebraMap R L (evaluate f
      (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon) F) at heval
  rw [← heval]
  change j (LocalComparison.orderPValue A p e FA) =
    j (v : RamifiedLocal.Extension A p 0) * algebraMap R L (evaluate f 1 F)
  simpa only [map_mul, evalOne, Units.coe_map] using congrArg j hv

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

/-- The selected element of B satisfies the actual cyclotomic relation. -/
theorem rhoB_cyclotomic_root (u : ℕ) (p : PrimeIndex u) :
    (Polynomial.cyclotomic p.val (B u)).eval (rhoB u p) = 0 := by
  have hp := prime_of_mem p.property
  apply Subtype.val_injective
  change (B u).val ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) =
    (B u).val (0 : B u)
  rw [map_zero]
  change (B u).val.toRingHom
    ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) = 0
  rw [← Polynomial.cyclotomic.eval_apply]
  exact (rho_isPrimitiveRoot p.val hp.ne_zero).isRoot_cyclotomic hp.pos

theorem subset_evaluations_local_associated (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal (B u) m))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu (insert p S) x))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu S x)) := by
  let f := (awayInclusion u p.val).toRingHom
  let A := AtComap f m
  let : NeZero p.val := ⟨(prime_of_mem p.property).ne_zero⟩
  let : CharZero A := CyclotomicAwayLocal.awayLocal_charZero u p.val m.asIdeal
  let : IsDiscreteValuationRing A :=
    CyclotomicAwayLocal.awayLocal_isDiscreteValuationRing u p.val huodd p.property m.asIdeal hpm
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p.val : A)} :=
    CyclotomicAwayLocal.awayLocal_maximalIdeal_eq_span u p.val huodd p.property m.asIdeal hpm
  let e := exponent u p.val - 1
  have he : exponent u p.val = e + 1 := by
    dsimp [e]
    have hpos := exponent_pos hu p.property
    omega
  have hn : order u p.val = p.val ^ (e + 1) := by rw [order, he]
  have hc : IsUnit (cofactor u p.val : A) :=
    coprime_natCast_isUnit (m.asIdeal.comap f) p.val (cofactor u p.val)
      (cofactor_coprime hu p.property)
      (CyclotomicAwayLocal.prime_mem_awayPrime u p.val m.asIdeal hpm)
  let F := partialEvaluation u hu p S x
  let K := partialEvaluation u hu p S (ringStar x)
  have hnum : u ^ 2 = p.val ^ (e + 1) * cofactor u p.val := by
    rw [← hn]
    exact (order_mul_cofactor u p.val).symm
  have hFK : F * K = scalar (order u p.val)
      ((p.val : awayRing u p.val) ^ (e + 1) * (cofactor u p.val : awayRing u p.val)) := by
    dsimp [F, K]
    rw [partialEvaluation_product u hu p S x (ringStar x) hx]
    apply congrArg (scalar (order u p.val))
    exact_mod_cast hnum
  have h := actual_local_character_association f m p.val (prime_of_mem p.property)
    hpm hmax (rhoB u p) (rhoB_pow u p) (rhoB_cyclotomic_root u p)
    (order u p.val) e (cofactor u p.val) hn
    (root_order_pow u hu p (rhoB u p) (rhoB_pow u p)) hc F K hFK
  change LocalComparison.ResidueOneAssociated _
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtRoot u hu p F))
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtOne u p F)) at h
  simpa only [F, partialEvaluation_at_root_apply,
    partialEvaluation_at_one_apply u hu p S hpS x] using h

/-- The denominator is nonzero because it is an actual evaluated norm factor. -/
theorem exists_local_edge_unit (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu (insert p S) x) /
          algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  apply local_edge_of_associated m _ _
  · intro hz
    apply subsetEvaluation_ne_zero u hu S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hz
  · exact subset_evaluations_local_associated u hu huodd x hx p m hpm S hpS

/-- At every maximal ideal over p, the one fixed global alternating product
is the image of a unit with residue one. No edge comparison is an input. -/
theorem exists_local_unit_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        alternatingProduct (Finset.univ : Finset (PrimeIndex u))
          (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  classical
  apply exists_unit_of_edges (toFraction (FractionRing (B u)) m).toRingHom
    (IsLocalRing.residue (AtMaximal (B u) m)) Finset.univ p (Finset.mem_univ p)
  intro S hS
  have hpS : p ∉ S := fun hp =>
    (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
  exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

/-- Integrality of the actual subset-character alternating product. The
maximal ideals over prime divisors use the proved local comparison; every
other maximal ideal uses the actual norm identity. -/
theorem exists_integral_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u, algebraMap (B u) (FractionRing (B u)) z =
      alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) := by
  classical
  refine exists_base_of_edges_and_norm u hu.ne' Finset.univ
    (fun p : PrimeIndex u => p.val) ?_
    (fun S => subsetEvaluation u hu S x) (fun S => star (subsetEvaluation u hu S x)) ?_ ?_
  · intro p hp
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    simpa only [Nat.cast_pow] using subsetEvaluation_norm u hu S x hx
  · intro m p _ hpm S hS
    have hpS : p ∉ S := fun hp =>
      (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
    exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicAdjoin ----
namespace OAI

universe uR

/-!
# The integral algebra and number field generated by roots of unity

Both objects are concrete subobjects of `ℂ`. The integer algebra includes
literally into the rationally generated intermediate field. Integrality is
proved from positive power-equals-one witnesses for the generators; finite
generation then supplies the finite-dimensional and number-field structures.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicAdjoin

/-- Each generator's positive power relation is a monic integral relation
over both the integers and the rationals. -/
theorem root_integral (R : Type uR) [CommRing R] [Algebra R ℂ] {ζ : ℂ}
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) : IsIntegral R ζ := by
  obtain ⟨n, hn, hpow⟩ := hζ
  apply IsIntegral.of_pow hn
  rw [hpow]
  exact isIntegral_one

theorem inclusion_injective (s : Set ℂ) : Function.Injective (inclusion s) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : Field s => (z : ℂ)) hxy

/-- Every element of the integer algebra is integral over the integers.
Finiteness of the generator set is not needed for this conclusion. -/
theorem integral {s : Set ℂ}
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Ring s) : IsIntegral ℤ z := by
  have hA : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ s) :=
    Algebra.IsIntegral.adjoin (fun ζ hζ => root_integral ℤ (hroots ζ hζ))
  exact Algebra.isIntegral_def.mp hA z

/-- Integrality of the element after its literal inclusion into the field. -/
theorem inclusion_integral {s : Set ℂ}
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Ring s) : IsIntegral ℤ (inclusion s z) :=
  map_isIntegral_int (inclusion s) (integral hroots z)

/-- A finite set of roots of unity generates a finite-dimensional extension
of `ℚ`. -/
theorem finiteDimensional {s : Set ℂ} (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    FiniteDimensional ℚ (Field s) := by
  classical
  let : Fintype s := hs.fintype
  exact IntermediateField.finiteDimensional_adjoin
    (fun ζ hζ => root_integral ℚ (hroots ζ hζ))

/-- The number-field structure for the concrete rational adjoin follows
from its finite dimension. -/
theorem numberField {s : Set ℂ} (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    NumberField (Field s) := by
  let : FiniteDimensional ℚ (Field s) := finiteDimensional hs hroots
  exact NumberField.of_module_finite ℚ (Field s)

end CirculantHadamard.CyclotomicAdjoin

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.Kronecker ----
namespace OAI

universe uK

/-!
# Kronecker's criterion for the actual finite cyclotomic adjoin

Every embedding of the field generated by the chosen roots restricts to a
unital ring homomorphism of their integral adjoin. This supplies the norm
hypothesis in Kronecker's theorem. The field, its finite dimension, and the
integrality of the selected element are constructed from the generators.
-/

namespace CirculantHadamard

/-- An algebraic integer in a number field with all embedding norms equal to
one is a root of unity, with a positive exponent. -/
theorem root_of_unity_of_norm_embeddings (K : Type uK) [Field K] [NumberField K]
    {z : K} (hzi : IsIntegral ℤ z)
    (hz : ∀ σ : K →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hzi hz
  exact ⟨n, hn, hpow⟩

theorem finite_adjoin_root_of_unity (s : Set ℂ) (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Algebra.adjoin ℤ s)
    (hz : ∀ σ : Algebra.adjoin ℤ s →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  let : NumberField (CyclotomicAdjoin.Field s) :=
    CyclotomicAdjoin.numberField hs hroots
  have hnorm (σ : CyclotomicAdjoin.Field s →+* ℂ) :
      ‖σ (CyclotomicAdjoin.inclusion s z)‖ = 1 :=
    hz (σ.comp (CyclotomicAdjoin.inclusion s))
  obtain ⟨n, hn, hpow⟩ := root_of_unity_of_norm_embeddings
    (CyclotomicAdjoin.Field s) (CyclotomicAdjoin.inclusion_integral hroots z) hnorm
  refine ⟨n, hn, CyclotomicAdjoin.inclusion_injective s ?_⟩
  simpa only [map_pow, map_one] using hpow

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicTorsion ----
namespace OAI

/-!
# Kronecker's criterion in the actual alternating coefficient ring

The finite generator and root-of-unity hypotheses are discharged for the
literal ring `B u = ℤ[i, rho_p : p ∣ u]`. The modulus-one hypothesis follows
for alternating products by clearing the actual product denominator and
evaluating the norm identities.
-/

namespace CirculantHadamard

theorem B_root_of_unity (u : ℕ) (z : CyclotomicRings.B u)
    (hz : ∀ σ : CyclotomicRings.B u →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  apply finite_adjoin_root_of_unity
    (({Complex.I} : Set ℂ) ∪ CyclotomicRings.rho '' (u.primeFactors : Set ℕ))
    ((Set.finite_singleton Complex.I).union
      (u.primeFactors.finite_toSet.image CyclotomicRings.rho)) ?_ z hz
  intro ζ hζ
  rcases hζ with hI | ⟨p, hp, rfl⟩
  · have hζI : ζ = Complex.I := Set.mem_singleton_iff.mp hI
    subst ζ
    exact ⟨4, by decide, CyclotomicRings.I_isPrimitiveRoot.pow_eq_one⟩
  · have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    exact ⟨p, hprime.pos, CyclotomicRings.rho_pow p hprime.ne_zero⟩

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingTorsion ----
namespace OAI

/-!
# The actual alternating character product has odd torsion

The index is the full set of prime divisors of u. The local comparison and
all-maximal-ideal argument are applied to the actual partial evaluations of
the given constant-norm group-ring element. No edge-comparison, integrality,
complex-norm, or torsion conclusion is assumed.
-/

noncomputable section

namespace CirculantHadamard

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations
open AlternatingLocalization

/-- Denominator removal and all complex homomorphisms are discharged for the
actual character values before invoking Kronecker's criterion. -/
theorem exists_integral_alternating_root_of_unity (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u,
      algebraMap (B u) (FractionRing (B u)) z =
        alternatingValue u (lt_trans Nat.zero_lt_one hu) x ∧
      ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz⟩ := exists_integral_alternatingProduct u hu0 huodd x hx
  refine ⟨z, hz, B_root_of_unity u z ?_⟩
  intro σ
  have ht : (Finset.univ : Finset (PrimeIndex u)).Nonempty := by
    obtain ⟨p, hp⟩ := primes_nonempty hu
    exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  have hne : ∀ S ⊆ (Finset.univ : Finset (PrimeIndex u)),
      algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu0 S x) ≠ 0 := by
    intro S _ hS
    apply subsetEvaluation_ne_zero u hu0 S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hS
  exact norm_hom_integral_alternatingProduct
    (algebraMap (B u) (FractionRing (B u)))
    (IsFractionRing.injective (B u) (FractionRing (B u)))
    Finset.univ ht (fun S => subsetEvaluation u hu0 S x) z hne hz σ (u : ℝ)
    (by exact_mod_cast hu0) (fun S _ => subsetEvaluation_map_norm u hu0 S x hx σ)

/-- The same alternating product is killed by a power of every actual prime
dividing u. The maximal ideal and characteristic-p residue field are built
from the concrete integral coefficient ring. -/
theorem alternatingProduct_prime_power_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) :
    ∃ a : ℕ, (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ (p.val ^ a) = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz, hfinite⟩ := exists_integral_alternating_root_of_unity u hu huodd x hx
  have hp : p.val.Prime := prime_of_mem p.property
  obtain ⟨m, hm, _, hpm⟩ := exists_maximal_ideal_over_nat_prime_of_charZero (B u) hp
  let M : MaximalSpectrum (B u) := ⟨m, hm⟩
  let : Algebra (B u) (AtMaximal (B u) M) := B_local_algebra u M
  obtain ⟨v, hv, hvres⟩ :=
    exists_local_unit_alternatingProduct u hu0 huodd x hx p M hpm
  have hlocal : algebraMap (B u) (AtMaximal (B u) M) z =
      (v : AtMaximal (B u) M) :=
    local_representative_eq (FractionRing (B u)) M z v (hz.trans hv.symm)
  let : CharP (IsLocalRing.ResidueField (AtMaximal (B u) M)) p.val :=
    residue_charP M p.val hp hpm
  let f : B u →+* IsLocalRing.ResidueField (AtMaximal (B u) M) :=
    (IsLocalRing.residue (AtMaximal (B u) M)).comp
      (algebraMap (B u) (AtMaximal (B u) M))
  have hres : f z = 1 := by
    change IsLocalRing.residue (AtMaximal (B u) M)
      (algebraMap (B u) (AtMaximal (B u) M) z) = 1
    rw [hlocal]
    exact hvres
  obtain ⟨a, ha⟩ := exists_prime_power_of_residue_one f z hp hres hfinite
  refine ⟨a, ?_⟩
  have h := congrArg (algebraMap (B u) (FractionRing (B u))) ha
  simpa only [map_pow, map_one, hz] using h

/-- The actual subset-character product has a positive odd torsion exponent. -/
theorem alternatingProduct_odd_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u : GaussianRing) ^ 2)) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ m = 1 := by
  classical
  have hx' : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
    simpa only [Nat.cast_pow] using hx
  obtain ⟨p, hp⟩ := primes_nonempty hu
  obtain ⟨a, ha⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx' ⟨p, hp⟩
  exact ⟨p ^ a, pow_pos (prime_of_mem hp).pos _, (odd_of_mem huodd hp).pow, ha⟩

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryContradiction ----
namespace OAI

noncomputable section

namespace CirculantHadamard

open CyclicRing BinaryEvaluation

/-- The binary contradiction starts with the original integer sign row and
its full cyclic norm equation. -/
theorem binary_sign_norm_impossible {u : ℕ} [NeZero u]
    (hu : 1 < u) (hodd : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    False := by
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hodd f)
  have hH : BinaryCoefficients.Signs (fun j => (H j).coeff) :=
    BinaryBlocks.crt_blocks_signs hodd f hsign
  obtain ⟨hc, hd, hg⟩ := gaussian_norms_of_cyclic_norm hodd f hsign hnorm
  apply BinaryLocalFamily.contradiction_of_evaluated_data u hu0 hodd
    (cG H) (dG H) (gG H) hc hd hg
    (aValue u hu0 H) (bValue u hu0 H) (UValue u hu0 H)
  · exact fun S => cValue_eq u hu0 H S
  · exact fun S => dValue_eq u hu0 H S
  · exact fun S => gValue_eq u hu0 hH S
  · exact alternatingProduct_odd_torsion u hu hodd (cG H)
      (by simpa only [Nat.cast_pow] using hc)
  · exact alternatingProduct_odd_torsion u hu hodd (dG H)
      (by simpa only [Nat.cast_pow] using hd)
  · exact alternatingProduct_odd_torsion u hu hodd (gG H)
      (by simpa only [Nat.cast_pow] using hg)

/-- No real circulant sign Hadamard matrix has order `4u²` for odd `u > 1`.
The original real-matrix predicate is converted by the proved integer-row
equivalence; every subsequent construction is made from that actual row. -/
theorem not_exists_four_mul_odd_square {u : ℕ}
    (hu : 1 < u) (hodd : Odd u) :
    ¬ ExistsRealCirculantHadamard (4 * u ^ 2) := by
  let : NeZero u := ⟨(lt_trans Nat.zero_lt_one hu).ne'⟩
  intro hH
  obtain ⟨f, hsign, hnorm⟩ :=
    (exists_cyclicSignRow_iff_real (n := 4 * u ^ 2)).mpr hH
  exact binary_sign_norm_impossible hu hodd f hsign hnorm

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.Main ----
namespace OAI

/-!
# Classification of positive real circulant sign Hadamard orders

The existence predicate retains the actual real matrix, its sign entries,
literal cyclic rows, and full Gram identity. Square-order and two-adic descent
reduce every nontrivial order to `4 * u^2` with `u` positive and odd. The binary
contradiction excludes `u > 1`, while explicit matrices realize orders one and four.
-/

namespace CirculantHadamard

/-- An actual real circulant sign Hadamard matrix of positive order exists
exactly at orders one and four. -/
theorem exists_iff_order_one_or_four (n : ℕ) (hn : 0 < n) :
    ExistsRealCirculantHadamard n ↔ n = 1 ∨ n = 4 := by
  constructor
  · intro hH
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · have hnlarge : 1 < n := by omega
      rcases order_reduction hnlarge hH with ⟨u, hu, hodd, rfl⟩
      by_cases hu1 : u = 1
      · right
        simp [hu1]
      · have hul : 1 < u := by omega
        exact (not_exists_four_mul_odd_square hul hodd hH).elim
  · exact exists_of_order_one_or_four

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.Barker.Main ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace CirculantHadamard.Barker

theorem four_dvd_length {n : ℕ} [NeZero n] {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n) : (4 : ℤ) ∣ (n : ℤ) := by
  let a : Fin n := ⟨2, hnlarge⟩
  have ha : a ≠ 0 := by
    intro heq
    have hv := congrArg Fin.val heq
    change 2 = 0 at hv
    omega
  have ht : aperiodic h 2 = 0 :=
    aperiodic_even_shift_zero hb hn 2 (by decide) (by omega) hnlarge
  have hnsub : Even (n - 2) := by
    obtain ⟨u, hu⟩ := hn
    exact ⟨u - 1, by omega⟩
  have ht' : aperiodic h (n - 2) = 0 :=
    aperiodic_even_shift_zero hb hn (n - 2) hnsub (by omega) (by omega)
  have hpa : periodic h a = 0 := by
    rw [periodic_eq_aperiodic_add h a ha]
    change aperiodic h 2 + aperiodic h (n - 2) = 0
    rw [ht, ht', add_zero]
  have hd := periodic_mod_four h hb.1 a
  rw [hpa, zero_sub] at hd
  exact dvd_neg.mp hd

theorem periodic_offpeak_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n)
    (a : Fin n) (ha : a ≠ 0) : periodic h a = 0 := by
  have ha0 : 0 < a.val := by
    by_contra hnot
    have hz : a.val = 0 := by omega
    apply ha
    apply Fin.ext
    simpa using hz
  have hab := aperiodic_bounds hb a.val ha0 a.isLt
  have hac := aperiodic_bounds hb (n - a.val) (by omega) (by omega)
  have hp := periodic_eq_aperiodic_add h a ha
  obtain ⟨u, hu⟩ := periodic_mod_four h hb.1 a
  obtain ⟨v, hv⟩ := four_dvd_length hb hn hnlarge
  omega

theorem existsRealCirculantHadamard_of_even_barker {n : ℕ} {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n) :
    ExistsRealCirculantHadamard n := by
  let : NeZero n := ⟨by omega⟩
  apply existsReal_iff_integer_autocorrelation.mpr
  refine ⟨h, hb.1, ?_⟩
  intro a
  change periodic h a = if a = 0 then (n : ℤ) else 0
  by_cases ha : a = 0
  · subst a
    simp [periodic_zero h hb.1]
  · rw [ite_eq_right ha]
    exact periodic_offpeak_zero hb hn hnlarge a ha

theorem even_length_eq_two_or_four {n : ℕ} (h : Fin n → ℤ)
    (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  by_cases hsmall : n ≤ 2
  · left
    obtain ⟨u, hu⟩ := hn
    omega
  · have hnlarge : 2 < n := by omega
    have hH := existsRealCirculantHadamard_of_even_barker hb hn hnlarge
    have hc := (exists_iff_order_one_or_four n hnpos).mp hH
    right
    omega

end CirculantHadamard.Barker

end OAI

-- ---- mission target ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.Barker
universe u
open scoped BigOperators

namespace OAI
namespace CirculantHadamard
namespace Barker
theorem _root_.solution {n : ℕ} (h : Fin n → ℤ)
    (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  first
    | exact OAI.CirculantHadamard.Barker.even_length_eq_two_or_four h hnpos hn hb
    | exact OAI.CirculantHadamard.Barker.even_length_eq_two_or_four
    | (apply OAI.CirculantHadamard.Barker.even_length_eq_two_or_four <;> assumption)
    | (intros; apply OAI.CirculantHadamard.Barker.even_length_eq_two_or_four <;> assumption)
end Barker
end CirculantHadamard
end OAI
