-- Prove2me | solution 1 for OAI.CirculantHadamard.order_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:00:45.982474+00:00
-- url     : https://prove2.me/submissions/e1dbb474-8201-464b-8718-ea4e173f902d

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderReduction.lean:L20-L38
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.order_reduction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_CirculantHadamard_ExistsRealCirculantHadamard_exists_integerSignRow
import Theorems.Thm_OAI_CirculantHadamard_cyclic_reduction_fiber_card
import Theorems.Thm_OAI_CirculantHadamard_exists_two_adic_square_decomposition_of_eq_sq
import Theorems.Thm_OAI_CirculantHadamard_gram_eq_iff_autocorrelation
import Theorems.Thm_OAI_CirculantHadamard_odd_norm_impossible
import Theorems.Thm_OAI_CirculantHadamard_order_even_of_sign_norm

-- ---- from OAI.LinearAlgebra.CirculantHadamard.Basic ----
namespace OAI

universe uR

namespace CirculantHadamard

theorem rowCirculant_isCirculant {n : ℕ} (h : Fin n → ℝ) :
    IsCirculant (rowCirculant h) := ⟨h, fun _ _ => rfl⟩

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

/-- Coefficients of the actual cyclic group-ring quotient as a fiber subtype sum. -/
theorem cyclicProjection_apply_fiber {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x : {x : ZMod n // ZMod.castHom h (ZMod m) x = a}, f.coeff x.val := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_fiber _ _ _

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

-- ---- platform node ----
open OAI OAI.CirculantHadamard


theorem solution : type_of% @_root_.OAI.CirculantHadamard.order_reduction := @_root_.OAI.CirculantHadamard.order_reduction
