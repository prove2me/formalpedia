-- Prove2me | solution 1 for OAI.CirculantHadamard.binary_sign_norm_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:14:57.980412+00:00
-- url     : https://prove2.me/submissions/a102746d-23a7-4890-82eb-3278fd713c47

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryContradiction.lean:L14-L37
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.binary_sign_norm_impossible. The node keeps its source
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
import Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_fourthRoot_character_star
import Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_partialEval_apply
import Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_partialEval_groupStar
import Theorems.Thm_OAI_CirculantHadamard_BinaryLocalFamily_contradiction_of_evaluated_data
import Theorems.Thm_OAI_CirculantHadamard_BinaryNorms_four_nsmul_cancel
import Theorems.Thm_OAI_CirculantHadamard_alternatingProduct_prime_power_torsion

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

end CirculantHadamard.CyclicRing

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

theorem gaussianI_sq : gaussianI ^ 2 = -1 :=
  Subtype.ext Complex.I_sq

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

end CirculantHadamard.PrimeComponents

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

end CirculantHadamard

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open CyclicRing BinaryEvaluation


theorem solution : type_of% @_root_.OAI.CirculantHadamard.binary_sign_norm_impossible := @_root_.OAI.CirculantHadamard.binary_sign_norm_impossible
