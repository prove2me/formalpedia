-- Prove2me | solution 1 for OAI.CirculantHadamard.exists_iff_order_one_or_four
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:18:08.971705+00:00
-- url     : https://prove2.me/submissions/ff3ccfd1-801d-4f1e-a8bf-79fdac6d07b0

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/Main.lean:L19-L34
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CirculantHadamard.exists_iff_order_one_or_four.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CirculantHadamard_exists_iff_order_one_or_four) verbatim and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAdjoin
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingTorsion
import Theorems.Thm_OAI_CirculantHadamard_ExistsRealCirculantHadamard_exists_integerSignRow
import Theorems.Thm_OAI_CirculantHadamard_binary_sign_norm_impossible
import Theorems.Thm_OAI_CirculantHadamard_gram_eq_iff_autocorrelation
import Theorems.Thm_OAI_CirculantHadamard_order_reduction

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

/-- Equivalence between the public real matrix problem and integer sign rows. -/
theorem integerSignRow_iff_real [NeZero n] :
    (∃ h : Fin n → ℤ, IsIntegerSignRow h) ↔ ExistsRealCirculantHadamard n := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh.exists_real
  · exact ExistsRealCirculantHadamard.exists_integerSignRow

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

end PositiveOrder

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryContradiction ----
namespace OAI

noncomputable section

namespace CirculantHadamard

open CyclicRing BinaryEvaluation

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

-- ---- mission target ----
open OAI OAI.CirculantHadamard
universe u

namespace OAI
namespace CirculantHadamard
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    ExistsRealCirculantHadamard n ↔ n = 1 ∨ n = 4 := by
  first
    | exact OAI.CirculantHadamard.exists_iff_order_one_or_four n hn
    | exact OAI.CirculantHadamard.exists_iff_order_one_or_four
    | (apply OAI.CirculantHadamard.exists_iff_order_one_or_four <;> assumption)
    | (intros; apply OAI.CirculantHadamard.exists_iff_order_one_or_four <;> assumption)
end CirculantHadamard
end OAI
