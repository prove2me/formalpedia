-- Prove2me | solution 1 for OAI.TwoPointCorrelations.quantitative_centering_assembly
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:59:33.622981+00:00
-- url     : https://prove2.me/submissions/121a0fda-fcad-4197-9b79-d5817b11fa9c

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
import Theorems.Thm_OAI_TwoPointCorrelations_quantitative_partial_tuple_bin

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h




theorem liouville_oneBounded : OneBounded liouville := by
  intro n hn
  have hs : ‖liouville n‖ ^ 2 = 1 := by
    rw [← norm_pow, liouville_sq hn.ne', norm_one]
  nlinarith [norm_nonneg (liouville n)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary
namespace OAI

/-!
# The endpoint error in the rough-shift averaging argument

These are finite identities and bounds from the proof of (q:rough-shifts)
in quantitative/03-analytic.tex. No short-sum or sieve estimate is assumed.
The averages below use the positive integers `1,...,Y` and translations
`1,...,D`; the resulting error is at most `2D/Y` times the total weight.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators




theorem norm_positivePrefix_le (u : ℕ → ℂ) (Y : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) : ‖positivePrefix u Y‖ ≤ Y * B := by
  calc
    _ ≤ ∑ v ∈ Finset.range Y, ‖u (v + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.range Y, B :=
      Finset.sum_le_sum (fun v _ => hu (v + 1) (by omega))
    _ = _ := by simp







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NearbyCutoffs
namespace OAI

/-! A bounded positive-prefix mean changes little when the real cutoff
is moved within one logarithmic bin. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma positivePrefix_sub_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    (N M : ℕ) (hNM : N ≤ M) :
    ‖positivePrefix f M - positivePrefix f N‖ ≤ (M - N : ℕ) := by
  have he : positivePrefix f M = positivePrefix f N +
      positivePrefix (fun n => f (N + n)) (M - N) := by
    unfold positivePrefix
    have hs := sum_range_add (fun n => f (n + 1)) N (M - N)
    rw [Nat.add_sub_of_le hNM] at hs
    simpa only [Nat.add_assoc] using hs
  rw [he, add_sub_cancel_left]
  simpa only [mul_one] using norm_positivePrefix_le (fun n => f (N + n)) (M - N) 1
    (fun n hn => hf _ (by omega))

lemma real_prefix_nearby (f : ℕ → ℂ) (hf : OneBounded f) (X Y : ℝ)
    (hY : 0 < Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * (X - Y) / X + 1 / X := by
  have hX : 0 < X := hY.trans_le hYX
  have hNM : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hYX
  have hN : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le hY.le
  have hM : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX.le
  have hlow := Nat.lt_floor_add_one Y
  have hdiff : ((⌊X⌋₊ - ⌊Y⌋₊ : ℕ) : ℝ) ≤ X - Y + 1 := by
    rw [Nat.cast_sub hNM]
    linarith
  have hnormN : ‖positivePrefix f ⌊Y⌋₊‖ ≤ (⌊Y⌋₊ : ℝ) := by
    simpa only [mul_one] using norm_positivePrefix_le f ⌊Y⌋₊ 1 hf
  have hnorm : ‖positivePrefix f ⌊Y⌋₊‖ ≤ Y := hnormN.trans hN
  have hinv : 0 ≤ 1 / Y - 1 / X := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hY hYX)
  have he : positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ) =
      positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ)) -
        (positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ))‖ +
        ‖(positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ)‖ := norm_sub_le _ _
    _ = ‖positivePrefix f ⌊Y⌋₊‖ * (1 / Y - 1 / X) +
        ‖positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊‖ / X := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hinv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    _ ≤ Y * (1 / Y - 1 / X) + (X - Y + 1) / X := by
      exact add_le_add (mul_le_mul_of_nonneg_right hnorm hinv)
        (div_le_div_of_nonneg_right
          ((positivePrefix_sub_norm_le f hf _ _ hNM).trans hdiff) hX.le)
    _ = _ := by field_simp; ring

lemma real_prefix_log_bin (f : ℕ → ℂ) (hf : OneBounded f) (X Y η : ℝ)
    (hX : 0 < X) (_hη : 0 ≤ η) (hYlow : X * Real.exp (-η) ≤ Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * η + 1 / X := by
  have hY : 0 < Y := (mul_pos hX (Real.exp_pos _)).trans_le hYlow
  apply (real_prefix_nearby f hf X Y hY hYX).trans
  have hexp : 1 - η ≤ Real.exp (-η) := by
    have he := Real.add_one_le_exp (-η)
    linarith
  have hy : X - Y ≤ X * η := by nlinarith
  have hd : (X - Y) / X ≤ η := (div_le_iff₀ hX).mpr (by nlinarith)
  calc
    _ = 2 * ((X - Y) / X) + 1 / X := by ring
    _ ≤ _ := by linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]






@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerLiouville
namespace OAI

/-! The real Liouville test function on ambient integer vertices and
the exact cancellation of the square-root weights on each directed edge. -/

namespace TwoPointCorrelations

open scoped _root_.Classical




lemma integerLiouville_natCast (n : ℕ) : integerLiouville n = liouville n := by
  simp [integerLiouville]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights
namespace OAI

/-! Tuple weights in integer and product residue environments. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
  {P : α → Type*} [∀ i, Fintype (P i)]








omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- With distinct selected primes, the integer family center is exactly the
paper's product over prime divisors of the numerical tuple. -/
lemma familyCenter_zero_eq_centeredTuple (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) (n : ℤ) :
    familyCenter value (fun _ _ => 0) x n = centeredTuple (familyTuple value x).primeFactors n := by
  classical
  rw [familyTuple_primeFactors value hprime x hinj, centeredTuple, prod_image]
  · simp only [familyCenter, zero_add]
  · exact fun i _ j _ hij => hinj hij

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionGateOnEdge
namespace OAI

/-! On a genuine increasing edge, the symmetric gate is precisely the
original progression restriction for that edge's padding divisor. -/

namespace TwoPointCorrelations

lemma progressionEdgeGate_on_edge (h l b d q : ℕ) (hh : 0 < h) (hd : 0 < d)
    (hq : 0 < q) (n : ℤ) :
    progressionEdgeGate h l b d n (n + (h * q * d : ℕ)) ↔
      Int.ModEq (l : ℤ) n (b * q * d : ℕ) := by
  constructor
  · rintro ⟨q', hf | hr⟩
    · have he : h * q * d = h * q' * d := by
        exact_mod_cast add_left_cancel hf.1
      have hq' : q = q' := Nat.eq_of_mul_eq_mul_left hh
        (Nat.eq_of_mul_eq_mul_right hd he)
      simpa only [← hq'] using hf.2
    · have hpos : (0 : ℤ) < (h * q * d : ℕ) := by positivity
      have hnneg : (0 : ℤ) ≤ (h * q' * d : ℕ) := by positivity
      omega
  · intro he
    exact ⟨q, Or.inl ⟨rfl, he⟩⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology









lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]


lemma modFivePrimesUpTo_le {one : Bool} {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : (p : ℝ) ≤ x :=
  (Nat.le_floor_iff hx).mp (mem_Icc.mp (mem_filter.mp hp).1).2



lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

/-- A single constant controls the logarithmic PNT error for both residue
selections and every real endpoint at least two. -/
theorem ModFiveThetaInput.log_error (hP : ModFiveThetaInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFiveTheta one x - modFiveDensity one * x| ≤ K * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨24 * C / c ^ 4, by positivity, fun one x hx => ?_⟩
  apply (h one x hx).trans
  have hh := mul_le_mul_of_nonneg_left (exp_neg_sqrt_log_le c x hc (by linarith))
    (mul_nonneg hC (by linarith : 0 ≤ x))
  convert (preTransparency := .instances) hh using 1
  ring

theorem ModFiveThetaInput.deleted_log_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        K * x / Real.log x ^ 2 := by
  obtain ⟨K, hK, h⟩ := hP.log_error
  let D : ℝ := ∑ p ∈ E, Real.log p
  have hD : 0 ≤ D := sum_nonneg (fun p _ => log_nat_nonneg p)
  refine ⟨K + 2 * D, by positivity, fun one x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hd : D ≤ 2 * D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := mul_le_mul_of_nonneg_left (log_sq_le_two_mul x (by linarith)) hD
    nlinarith [hh]
  calc
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| + D := by
      calc
        _ = |(modFiveTheta one x - modFiveDensity one * x) +
            (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (deletedModFiveTheta_error E one x)
    _ ≤ K * x / Real.log x ^ 2 + 2 * D * x / Real.log x ^ 2 :=
      add_le_add (h one x hx) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring

lemma reciprocalLog_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |reciprocalLog x * E| ≤ K / Real.log x := by
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [abs_mul, abs_of_nonneg (by unfold reciprocalLog; positivity)]
  calc
    _ ≤ reciprocalLog x * (K * x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by unfold reciprocalLog; positivity)
    _ = K / Real.log x ^ 3 := by unfold reciprocalLog; field_simp
    _ ≤ K / Real.log x := by
      apply div_le_div_of_nonneg_left hK hlp
      nlinarith [sq_nonneg (Real.log x - 1)]

lemma reciprocalLog_deriv_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 1 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |deriv reciprocalLog x * E| ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) *
        (K * x / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < x * Real.log x ^ 4)).mp
      field_simp
      nlinarith [sq_nonneg (Real.log x - 1), mul_nonneg hK (sq_nonneg (Real.log x - 1))]

/-- A uniform band error. The upper endpoint is arbitrary, so this applies
simultaneously to all the logarithmically spaced supplies in the manuscript. -/
theorem reciprocal_band_error (c : ℕ → ℝ) (α K a b : ℝ) (hK : 0 ≤ K)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog n * c n) -
      α * (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 4 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hla : 1 ≤ Real.log a := by
    simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ reciprocalLog x :=
    fun x hx => (reciprocalLog_hasDerivAt (hx1 x hx)).differentiableAt
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 :=
    fun x hx => (zero_lt_one.trans (hx1 x hx)).ne'
  have hln : ∀ x ∈ Set.Icc a b, Real.log x ≠ 0 :=
    fun x hx => (Real.log_pos (hx1 x hx)).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hdf : ContinuousOn (deriv reciprocalLog) (Set.Icc a b) := by
    apply ContinuousOn.congr (f := fun x => -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2))
    · exact (hclog.add continuousOn_const).neg.div
        ((continuousOn_id.pow 2).mul (hclog.pow 2))
        (fun x hx => mul_ne_zero (pow_ne_zero 2 (hxn x hx)) (pow_ne_zero 2 (hln x hx)))
    · intro x hx
      exact (reciprocalLog_hasDerivAt (hx1 x hx)).deriv
  have hAbel := centered_partial_summation c α a b ha0.le hab reciprocalLog hf hdf
  rw [show (∫ t in a..b, reciprocalLog t) =
      Real.log (Real.log b) - Real.log (Real.log a) from
    integral_inv_div_log ha1 hb1] at hAbel
  have hg : IntervalIntegrable (fun x : ℝ => 2 * K * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ hxn).div (hclog.pow 2)
      (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (2 * K)
  have hi : |∫ x in a..b, deriv reciprocalLog x * (partialCoefficientSum c x - α * x)| ≤
      2 * K / Real.log a := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact reciprocalLog_deriv_error_le K x _ hK (hx1 x ⟨hx.1.le, hx.2⟩)
          (hlx x ⟨hx.1.le, hx.2⟩) (hE x ⟨hx.1.le, hx.2⟩))) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hbound
    apply hbound.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K) hbnonneg]
  have hA := reciprocalLog_error_le K a _ hK ha0 hla (hE a ⟨le_rfl, hab⟩)
  have hB := reciprocalLog_error_le K b _ hK (zero_lt_one.trans hb1)
    (hlx b ⟨hab, le_rfl⟩) (hE b ⟨hab, le_rfl⟩)
  have hBA : K / Real.log b ≤ K / Real.log a :=
    div_le_div_of_nonneg_left hK hlap (Real.log_le_log ha0 hab)
  rw [hAbel]
  calc
    _ ≤ |reciprocalLog b * (partialCoefficientSum c b - α * b)| +
        |reciprocalLog a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv reciprocalLog t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ K / Real.log a + K / Real.log a + 2 * K / Real.log a :=
      add_le_add (add_le_add (hB.trans hBA) hA) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands
namespace OAI

/-! Concrete modulus-five supplies and their reciprocal masses. We use
half-open bands `(exp A, exp B]`; this harmless endpoint convention makes
adjacent supplies exactly disjoint and matches finite Abel summation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma partialSum_deletedModFive (E : Finset ℕ) (one : Bool) (x : ℝ) :
    partialCoefficientSum (deletedModFiveLogWeight E one) x =
      deletedModFiveTheta E one x := by
  unfold partialCoefficientSum deletedModFiveTheta deletedModFivePrimes
    modFivePrimesUpTo deletedModFiveLogWeight
  rw [sdiff_eq_filter, sum_filter, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ModFivePrime one p <;> by_cases he : p ∈ E <;> simp [h, he]



lemma modFivePrimeBand_sum (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, 1 / (p : ℝ)) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    rw [if_pos hs]
    unfold deletedModFiveLogWeight
    rw [if_pos hs]
    unfold reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

/-- Both selected prime classes have their correct logarithmic-band mass,
uniformly over the upper endpoint and with any fixed finite exclusions. -/
theorem ModFiveThetaInput.band_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (A B : ℝ), 1 ≤ A → A ≤ B →
      |(∑ p ∈ modFivePrimeBand E one (Real.exp A) (Real.exp B), 1 / (p : ℝ)) -
          modFiveDensity one * (Real.log B - Real.log A)| ≤ 4 * K / A := by
  obtain ⟨K, hK, h⟩ := hP.deleted_log_error E
  refine ⟨K, hK, fun one A B hA hAB => ?_⟩
  rw [modFivePrimeBand_sum]
  have hh := reciprocal_band_error (deletedModFiveLogWeight E one) (modFiveDensity one)
    K (Real.exp A) (Real.exp B) hK (Real.exp_le_exp.mpr hA)
      (Real.exp_le_exp.mpr hAB) (fun x hx => by
        rw [partialSum_deletedModFive]
        apply h one x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans ((Real.exp_le_exp.mpr hA).trans hx.1))
  simpa only [Real.log_exp] using hh

/-- The concrete centered-prime supplies have reciprocal mass in `[W,2W]`
once their lower logarithmic endpoint exceeds one fixed threshold. -/
theorem ModFiveThetaInput.centered_band_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      W ≤ (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ∧
      (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨K, hK, h⟩ := hP.band_error E
  refine ⟨max 1 (8 * K / W), le_max_left _ _, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB : A ≤ A * Real.exp (6 * W) := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 6 * W)) hA0.le
    simpa only [mul_one] using hh
  have hmass := h true A (A * Real.exp (6 * W)) hA1 hB
  have he : Real.log (A * Real.exp (6 * W)) - Real.log A = 6 * W := by
    rw [Real.log_mul hA0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [he] at hmass
  have hsmall : 4 * K / A ≤ W / 2 := by
    have hh := (div_le_iff₀ hW).mp ((le_max_right 1 (8 * K / W)).trans hA)
    apply (div_le_iff₀ hA0).mpr
    nlinarith [hh]
  have hh := abs_le.mp hmass
  norm_num [modFiveDensity] at hh
  simp only [one_div]
  constructor <;> linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring





lemma centeredPrimeSupply_global_bounds {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) {J i p : ℕ} (hi : i < J)
    (hL : primeSupplyEndpoint A W J ≤ L) (hp : p ∈ centeredPrimeSupply E A W i) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  have hh := centeredPrimeSupply_mem hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
  have hlo : A < Real.log p := by
    have hmono := primeSupplyEndpoint_mono A W hA hW (Nat.zero_le i)
    rw [primeSupplyEndpoint_zero] at hmono
    exact hmono.trans_lt hh.2.2.2.1
  have hhi : Real.log p ≤ L := hh.2.2.2.2.trans
    ((primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hi)).trans hL)
  constructor
  · simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hlo
  · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hhi

lemma primeSupplyEndpoint_sum_lt (A W : ℝ) (hA : 0 < A) (hW : 1 ≤ W) (J : ℕ) :
    (∑ i ∈ range J, primeSupplyEndpoint A W (i + 1)) < 2 * primeSupplyEndpoint A W J := by
  have hratio : 2 ≤ Real.exp (6 * W) := by
    linarith [Real.add_one_le_exp (6 * W)]
  induction J with
  | zero => simp [primeSupplyEndpoint, hA]
  | succ J ih =>
    have he : 0 ≤ primeSupplyEndpoint A W J := by unfold primeSupplyEndpoint; positivity
    have hstep : 2 * primeSupplyEndpoint A W J ≤ primeSupplyEndpoint A W (J + 1) := by
      rw [primeSupplyEndpoint_succ]
      nlinarith [mul_le_mul_of_nonneg_right hratio he]
    rw [sum_range_succ]
    linarith

lemma centeredPrimeSupply_tuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    (p : Fin J → ℕ) (hp : ∀ i : Fin J, p i ∈ centeredPrimeSupply E A W i.val) :
    Real.log ((∏ i, p i : ℕ) : ℝ) < 2 * L := by
  have hlog : Real.log ((∏ i, p i : ℕ) : ℝ) = ∑ i, Real.log (p i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (centeredPrimeSupply_mem (hp i)).1.ne_zero
  rw [hlog]
  calc
    _ ≤ ∑ i : Fin J, primeSupplyEndpoint A W (i.val + 1) :=
      sum_le_sum (fun i _ => (centeredPrimeSupply_mem (hp i)).2.2.2.2)
    _ = ∑ i ∈ range J, primeSupplyEndpoint A W (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => primeSupplyEndpoint A W (i + 1)) J
    _ < 2 * primeSupplyEndpoint A W J := primeSupplyEndpoint_sum_lt A W hA hW J
    _ ≤ 2 * L := by linarith

/-- Every centered supply is nonempty and has the required reciprocal mass.
The threshold is independent of the number of supplies and their indices. -/
theorem ModFiveThetaInput.centered_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ i : ℕ,
      (centeredPrimeSupply E A W i).Nonempty ∧
      W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hmass⟩ := hP.centered_band_mass E W hW
  refine ⟨A₀, hA₀, fun A hA i => ?_⟩
  have hA0 : 0 ≤ A := (zero_le_one.trans hA₀).trans hA
  have hlower : A₀ ≤ primeSupplyEndpoint A W i := by
    calc
      A₀ ≤ A := hA
      _ = primeSupplyEndpoint A W 0 := (primeSupplyEndpoint_zero A W).symm
      _ ≤ _ := primeSupplyEndpoint_mono A W hA0 hW.le (Nat.zero_le _)
  have hh := hmass (primeSupplyEndpoint A W i) hlower
  rw [← primeSupplyEndpoint_succ] at hh
  change W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W at hh
  refine ⟨?_, hh⟩
  by_contra he
  rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hh
  linarith [hh.1]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeSupplyScale_endpoint (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W) :=
    Nat.floor_le (by positivity)
  have hj' := (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj
  unfold primeSupplyEndpoint
  calc
    _ = Real.exp (Real.log L * (199 / 200 : ℝ) + 6 * W * primeSupplyCount W L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add]
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by nlinarith)
    _ = L := Real.exp_log hLp

lemma eventually_primeSupplyCount_pos (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (1200 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 1200 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : (0 : ℝ) ≤ 1200 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

theorem ModFiveThetaInput.eventually_actual_prime_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ primeSupplyCount W L ∧
      primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L ∧
      ∀ i : ℕ, (centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i).Nonempty ∧
        W ≤ (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ∧
        (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ≤ 2 * W := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨A₀, _, hmass⟩ := hP.centered_supplies E W hWp
  have hlarge := (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop A₀)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_primeSupplyCount_pos W hWp,
    hlarge] with L hL hJ hA
  exact ⟨hJ, primeSupplyScale_endpoint W L hWp hL,
    hmass (L ^ (199 / 200 : ℝ)) hA⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical






lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma primeSubset_product_injective (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) S.powerset := by
  intro U hU V hV heq
  have hU' : U ⊆ S := mem_powerset.mp hU
  have hV' : V ⊆ S := mem_powerset.mp hV
  have hprimeU : ∀ p ∈ U, Nat.Prime p := fun p hp => hS p (hU' hp)
  have hprimeV : ∀ p ∈ V, Nat.Prime p := fun p hp => hS p (hV' hp)
  have hfactors := congrArg Nat.primeFactors heq
  simpa only [Nat.primeFactors_prod hprimeU, Nat.primeFactors_prod hprimeV] using hfactors

lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)



theorem retainedPrimeDivisors_weighted_mass (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (w : ℕ → ℝ) :
    (∑ u ∈ retainedPrimeDivisors S, (∏ p ∈ u.primeFactors, w p) / (u : ℝ)) =
      ∏ p ∈ S, (1 + w p / (p : ℝ)) := by
  unfold retainedPrimeDivisors
  rw [sum_image (primeSubset_product_injective S hS)]
  calc
    _ = ∑ U ∈ S.powerset, ∏ p ∈ U, (w p / (p : ℝ)) := by
      apply sum_congr rfl
      intro U hU
      have hUS : U ⊆ S := mem_powerset.mp hU
      rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp)), Nat.cast_prod,
        prod_div_distrib]
    _ = _ := (prod_one_add S).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenterBandExpansion
namespace OAI

/-! Exact expansion of the center-band factors. Each nonempty choice of
constant factors leaves an ordinary divisibility condition for the retained
prime product, and carries precisely one reciprocal removed-prime product. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma primeProduct_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : S ⊆ n.primeFactors := fun p hp => (hS p hp).mem_primeFactors (h p hp) hn
      exact (prod_dvd_prod_of_subset S n.primeFactors (fun p : ℕ => p) hsub).trans
        (Nat.prod_primeFactors_dvd n)

lemma natDivisibilityIndicator_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ S, natDivisibilityIndicator p n) =
      natDivisibilityIndicator (∏ p ∈ S, p) n := by
  by_cases hd : (∏ p ∈ S, p) ∣ n
  · have hp := (primeProduct_dvd_iff S hS n).mp hd
    unfold natDivisibilityIndicator
    simp only [hd, ite_true]
    exact prod_eq_one (fun p hpS => if_pos (hp p hpS))
  · have hn : ¬∀ p ∈ S, p ∣ n := fun h => hd ((primeProduct_dvd_iff S hS n).mpr h)
    push Not at hn
    obtain ⟨p, hp, hpn⟩ := hn
    have hz : (∏ p ∈ S, natDivisibilityIndicator p n) = 0 :=
      prod_eq_zero hp (by simp [natDivisibilityIndicator, hpn])
    rw [hz]
    simp only [natDivisibilityIndicator, hd, ite_false]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LiouvilleDivisorExtraction
namespace OAI

/-! The exact partial-centering substitution n=u*v. Only u must be a
unit modulo l; the progression class and the removed product may be nonunits. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma unit_progression_cancel (l : ℕ) (b : ZMod l) (u z v : ℕ)
    (hu : IsUnit (u : ZMod l)) :
    ((u * v : ℕ) : ZMod l) = b * ((u * z : ℕ) : ZMod l) ↔
      (v : ZMod l) = b * (z : ZMod l) := by
  simp only [Nat.cast_mul]
  rw [show b * ((u : ZMod l) * z) = (u : ZMod l) * (b * z) by ring,
    hu.mul_right_inj]

lemma liouville_pair_dilate (u v z h : ℕ) (hu : 0 < u) :
    liouville (u * v) * liouville (u * v + h * (u * z)) =
      liouville v * liouville (v + h * z) := by
  rw [show u * v + h * (u * z) = u * (v + h * z) by ring]
  simp only [liouville_mul]
  calc
    _ = liouville u ^ 2 * (liouville v * liouville (v + h * z)) := by ring
    _ = _ := by rw [liouville_sq hu.ne', one_mul]

lemma liouville_progression_dilate (l : ℕ) [NeZero l] (b : ZMod l)
    (u v z h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) :
    progressionSequence liouville l (b * ((u * z : ℕ) : ZMod l)) (u * v) *
        liouville (u * v + h * (u * z)) =
      progressionSequence liouville l (b * (z : ZMod l)) v * liouville (v + h * z) := by
  simp only [progressionSequence, unit_progression_cancel l b u z v hunit]
  split_ifs
  · exact liouville_pair_dilate u v z h hu
  · simp only [zero_mul]



lemma natDivisibilityIndicator_mul (a b n : ℕ) (hab : a.Coprime b) :
    natDivisibilityIndicator a n * natDivisibilityIndicator b n =
      natDivisibilityIndicator (a * b) n := by
  have he : a * b ∣ n ↔ a ∣ n ∧ b ∣ n :=
    ⟨fun h => ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩,
      fun h => hab.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [natDivisibilityIndicator, he]
  split_ifs <;> simp_all

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FullDivisibility
namespace OAI

/-! The full-divisibility term extracts the original progression
correlation at a cutoff in the same logarithmic bin. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma fullLiouvilleProfile_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u h N : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) :
    positivePrefix (fullLiouvilleProfile l b u h) N =
      positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h)) (N / u) := by
  unfold fullLiouvilleProfile
  rw [divisibility_positivePrefix _ u N hu]
  congr 1
  funext v
  simpa only [Nat.cast_one, mul_one] using liouville_progression_dilate l b u v 1 h hu hunit

lemma progressionLiouvilleProfile_oneBounded (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) :
    OneBounded (fun n => progressionSequence liouville l b n * liouville (n + h)) := by
  intro n hn
  dsimp only [progressionSequence]
  split_ifs
  · rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (liouville_oneBounded n hn)
        (liouville_oneBounded (n + h) (by omega)) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · simp only [zero_mul, norm_zero, zero_le_one]

lemma fullLiouvilleProfile_real_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) (T : ℝ) (hT : 0 < T) :
    positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ) =
      (1 / (u : ℂ)) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊T / u⌋₊ / ((T / u : ℝ) : ℂ)) := by
  rw [fullLiouvilleProfile_prefix l b u h _ hu hunit, Nat.floor_div_natCast]
  push_cast
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

lemma fullLiouvilleProfile_bin_error (l : ℕ) [NeZero l] (b : ZMod l)
    (u h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l))
    (X T η : ℝ) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : X * Real.exp (-η) ≤ T / u) (hhi : T / u ≤ X) :
    ‖positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ) -
      (1 / (u : ℂ)) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤ (1 / (u : ℝ)) * (2 * η + 1 / X) := by
  have hY : 0 < T / u := (mul_pos hX (Real.exp_pos _)).trans_le hlo
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hT : 0 < T := by
    rcases div_pos_iff.mp hY with hp | hn
    · exact hp.1
    · linarith [hn.2]
  rw [fullLiouvilleProfile_real_prefix l b u h hu hunit T hT, ← mul_sub, norm_mul]
  have hc := real_prefix_log_bin _ (progressionLiouvilleProfile_oneBounded l b h)
    X (T / u) η hX hη hlo hhi
  simpa only [norm_div, norm_one, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 1 / (u : ℝ))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FullDivisibilityFamily
namespace OAI

/-! Finite weighted summation of the full-divisibility cutoff errors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma full_divisibility_family_error {ι : Type*} (l : ℕ) [NeZero l] (b : ZMod l)
    (h : ℕ) (U : Finset ι) (u : ι → ℕ) (weight : ι → ℝ)
    (hweight : ∀ i ∈ U, 0 ≤ weight i) (hu : ∀ i ∈ U, 0 < u i)
    (hunit : ∀ i ∈ U, IsUnit (u i : ZMod l)) (X T η : ℝ)
    (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ i ∈ U, X * Real.exp (-η) ≤ T / u i)
    (hhi : ∀ i ∈ U, T / u i ≤ X) :
    ‖(∑ i ∈ U, (weight i : ℂ) *
        (positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ i ∈ U, weight i / (u i : ℝ) : ℝ) : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      (∑ i ∈ U, weight i / (u i : ℝ)) * (2 * η + 1 / X) := by
  let F := positivePrefix
    (fun n => progressionSequence liouville l b n * liouville (n + h)) ⌊X⌋₊ / (X : ℂ)
  have he : (∑ i ∈ U, (weight i : ℂ) *
      (positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ i ∈ U, weight i / (u i : ℝ) : ℝ) : ℂ) * F =
      ∑ i ∈ U, (weight i : ℂ) *
        ((positivePrefix (fullLiouvilleProfile l b (u i) h) ⌊T⌋₊ / (T : ℂ)) -
          (1 / (u i : ℂ)) * F) := by
    push_cast
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change ‖_ - _ * F‖ ≤ _
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ U, weight i * ((1 / (u i : ℝ)) * (2 * η + 1 / X)) := by
      apply sum_le_sum
      intro i hiU
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight i hiU)]
      exact mul_le_mul_of_nonneg_left
        (fullLiouvilleProfile_bin_error l b (u i) h (hu i hiU) (hunit i hiU) X T η hX hη
          (hlo i hiU) (hhi i hiU)) (hweight i hiU)
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical














lemma paddingTiltNormalizer_eq_divisor_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    paddingTiltNormalizer Q =
      ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) := by
  unfold paddingTiltNormalizer
  rw [prod_coe_sort Q (fun p : ℕ => 1 + 4 / (p : ℝ))]
  simpa only [prod_const] using
    (retainedPrimeDivisors_weighted_mass Q hQ (fun _ => (4 : ℝ))).symm


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NonrawPrefix
namespace OAI

/-! Exact finite-prefix assembly of the nonraw expansion at the retained
divisor scale. No endpoint terms are discarded. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma positivePrefix_const_mul (c : ℂ) (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => c * F n) X = c * positivePrefix F X := by
  simp only [positivePrefix, mul_sum]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage
namespace OAI

/-! The literal finite bin family covers every padding divisor surviving
the degree and logarithmic-size cuts. This includes the last bin whose
left endpoint, rather than its right endpoint, is at most `100 L`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma mem_paddingBinIndices_iff (L η : ℝ) (j : ℤ) (hη : 0 < η) :
    j ∈ paddingBinIndices L η ↔ 0 ≤ j ∧ (j : ℝ) * η ≤ 100 * L := by
  rw [paddingBinIndices, mem_Icc, Int.le_floor, le_div_iff₀ hη]


lemma paddingBinIndices_card (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    ((paddingBinIndices L η).card : ℝ) ≤ 100 * L / η + 1 := by
  have hf : 0 ≤ ⌊100 * L / η⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : ((paddingBinIndices L η).card : ℝ) = (⌊100 * L / η⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le 0 ⌊100 * L / η⌋
      (show (0 : ℤ) ≤ ⌊100 * L / η⌋ + 1 by omega)
    simp only [sub_zero] at hh
    change ((Icc (0 : ℤ) ⌊100 * L / η⌋).card : ℝ) = _
    exact_mod_cast hh
  rw [hc]
  linarith [Int.floor_le (100 * L / η)]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma centeredPrimeTuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j)) :
    0 < d ∧ Real.log d ≤ 2 * L := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  constructor
  · exact prod_pos fun j _ => (centeredPrimeSupply_mem (x j).property).1.pos
  · exact (centeredPrimeSupply_tuple_log_bound hA hW hL
      (fun j => (x j).val) (fun j => (x j).property)).le




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily
namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








lemma centeredPrimeBand_subset_pool (E : Finset ℕ) (A W : ℝ) (J : ℕ) (j : Fin J) :
    centeredPrimeBands E A W J j ⊆ centeredPrimePool E A W J := by
  intro p hp
  exact mem_primeTuplePool.mpr ⟨j, hp⟩


lemma paddingPrimeSupply_bounds (E : Finset ℕ) (L : ℝ) {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : (p : ℝ) ≤ Real.exp L :=
  modFivePrimesUpTo_le (Real.exp_pos _).le (Finset.mem_sdiff.mp hp).1




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale
namespace OAI

/-! Harmonic masses and integer endpoints for the literal prime family.
These derive the trace theorem's prime-pool hypotheses from the single
fixed-modulus published input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical






lemma centeredPrimeTuple_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (centeredPrimeBands E A W J)) :
    d ≤ ⌊Real.exp (2 * L)⌋₊ := by
  have hb := centeredPrimeTuple_log_bound hA hW hL hd
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hb.1
  simpa only [Real.exp_log hdpos] using Real.exp_le_exp.mpr hb.2




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize
namespace OAI

/-! The full forced-step alphabet includes all bounded padding divisors.
Its size still fits the polynomial exponential budget of finite-law
comparison; no eligibility restriction is needed for this count. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma boundedPaddingDivisor_real_upper (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (q : ℝ) ≤ Real.exp (100 * L ^ 2) := by
  have hr := (mem_filter.mp hq).1
  have hsq := retainedPrimeDivisor_squarefree (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hpool := retainedPrimeDivisor_factors (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hdeg : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    (show (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) by
      exact_mod_cast (mem_filter.mp hq).2).trans
        (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg hL)))
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    _ ≤ ∏ _p ∈ q.primeFactors, Real.exp L :=
      Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
        (fun p hp => paddingPrimeSupply_bounds E L (hpool hp))
    _ = Real.exp ((q.primeFactors.card : ℝ) * L) := by
      rw [prod_const, Real.exp_nat_mul]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ExtractedWindowScale
namespace OAI

/-! An absolute long-interval scale survives extraction of every bounded
padding divisor and every partial tuple product, including both floor operations. -/

namespace TwoPointCorrelations

lemma extracted_window_lower (L T : ℝ) (u : ℕ) (hL : 1000 ≤ L)
    (hu : 0 < u) (hT : Real.exp (L ^ (1000 : ℝ)) ≤ T)
    (hupper : (u : ℝ) ≤ Real.exp (100 * L ^ 2 + 2 * L)) :
    Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ ((⌊T⌋₊ / u : ℕ) : ℝ) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hp : L ^ (4 : ℕ) ≤ L ^ (1000 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hLone (show (4 : ℝ) ≤ 1000 by norm_num)
  have hsq : (1000 : ℝ) ≤ L ^ 2 := by nlinarith
  have hfour : 1000 * L ^ 2 ≤ L ^ (4 : ℕ) := by
    calc
      _ ≤ (L ^ 2) * (L ^ 2) := mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
      _ = _ := by ring
  have hgap : 3 ≤ (1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L) := by
    nlinarith
  have he : 4 ≤ Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L)) := by
    linarith [Real.add_one_le_exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L))]
  let E := Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ))
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have huone : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hEu : 1 ≤ E * u := one_le_mul_of_one_le_of_one_le hE huone
  have hsmall : 4 * (E * u) ≤ T := by
    apply le_trans _ hT
    calc
      _ ≤ 4 * (E * Real.exp (100 * L ^ 2 + 2 * L)) := by gcongr
      _ = 4 * Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) + (100 * L ^ 2 + 2 * L)) := by
        congr 1
        exact (Real.exp_add _ _).symm
      _ ≤ Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L)) *
          Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) + (100 * L ^ 2 + 2 * L)) := by
        exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfloor : 2 * (E * u) ≤ (⌊T⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one T
    nlinarith
  have hdiv : (⌊T⌋₊ : ℝ) < (u : ℝ) * (((⌊T⌋₊ / u : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ ⌊T⌋₊ hu
  have hratio : 2 * E < ((⌊T⌋₊ / u : ℕ) : ℝ) + 1 := by
    apply (mul_lt_mul_iff_right₀ hup).mp
    nlinarith
  change E ≤ _
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount
namespace OAI

/-! Bounds for the actual finite bin set at eta = exp(-J). -/

namespace TwoPointCorrelations

open _root_.Filter

lemma paddingBinIndices_card_linear (L η : ℝ) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1) :
    ((paddingBinIndices L η).card : ℝ) ≤ 101 * L / η := by
  have hb := paddingBinIndices_card L η (by linarith) hη
  have hratio : 1 ≤ L / η := (one_le_div hη).mpr (by linarith)
  have he : 101 * L / η = 100 * L / η + L / η := by ring
  rw [he]
  linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleSlice
namespace OAI

/-! Exact splitting of a prime tuple into the removed and retained
supplies in the quantitative centering expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma primeTupleSlice_pos {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) {z : ℕ} (hz : z ∈ primeTupleSlice P I) :
    0 < z := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  exact prod_pos (fun i _ => (hprime i _ (x i).property).pos)

lemma primeTupleSlice_lower {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) (H : ℝ)
    (hlarge : ∀ i, ∀ p ∈ P i, H ≤ (p : ℝ)) (hne : I.Nonempty)
    {z : ℕ} (hz : z ∈ primeTupleSlice P I) : H ≤ (z : ℝ) := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  obtain ⟨i, hi⟩ := hne
  have hp : (x ⟨i, hi⟩).val ≤ ∏ j, (x j).val :=
    Nat.le_of_dvd (prod_pos (fun j _ => (hprime j _ (x j).property).pos))
      (dvd_prod_of_mem (fun j : I => (x j).val) (mem_univ (⟨i, hi⟩ : I)))
  exact (hlarge i _ (x ⟨i, hi⟩).property).trans (by exact_mod_cast hp)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleCenterExpansion
namespace OAI

/-! The exact expansion indexed by the set of prime supplies replaced by
reciprocal constants. The original tuple and all progression tests are retained. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma indexed_indicator_product {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (I : Finset (Fin J)) (n : ℕ) :
    (∏ i ∈ I, natDivisibilityIndicator (p i) n) =
      natDivisibilityIndicator (∏ i ∈ I, p i) n := by
  have hi : ∀ i ∈ I, ∀ j ∈ I, p i = p j → i = j := fun _ _ _ _ he => hinj he
  have hp : ∀ r ∈ I.image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    exact hprime i
  calc
    _ = ∏ r ∈ I.image p, natDivisibilityIndicator r n := (prod_image hi).symm
    _ = natDivisibilityIndicator (∏ r ∈ I.image p, r) n :=
      natDivisibilityIndicator_product _ hp n
    _ = _ := by rw [prod_image hi]

lemma tupleCenter_expansion {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p) (n : ℕ) :
    (∏ j, (natDivisibilityIndicator (p j) n - 1 / (p j : ℂ))) =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ j : {j // j ∉ I}, p j) n := by
  rw [prod_sub]
  apply sum_congr rfl
  intro I _
  rw [indexed_indicator_product p hprime hinj (univ \ I) n]
  have hI : (∏ i ∈ I, p i) = ∏ i : I, p i := prod_subtype I (by simp) p
  have hc : (∏ j ∈ univ \ I, p j) = ∏ j : {j // j ∉ I}, p j :=
    prod_subtype (univ \ I) (by simp) p
  rw [hc, prod_div_distrib]
  simp only [prod_const_one, ← Nat.cast_prod, hI]
  ring



lemma centeredTuple_nat_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (x : (j : Fin J) → P j) (n : ℕ) :
    (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) =
      ∏ j, (natDivisibilityIndicator (x j).val n - 1 / ((x j).val : ℂ)) := by
  have he : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) x (n : ℤ) =
      centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) := by
    simpa only [familyTuple] using familyCenter_zero_eq_centeredTuple
      (fun j (p : P j) => p.val) (fun j p => hprime j _ p.property) x
      (selectedPrimeValues_injective x hdisjoint) (n : ℤ)
  rw [← he]
  simp only [familyCenter, zero_add, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_inv, Complex.ofReal_natCast, natDivisibilityIndicator, one_div,
    Int.natCast_dvd_natCast]
  apply prod_congr rfl
  intro j _
  split_ifs <;> simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.PartialTupleProfiles
namespace OAI

/-! Reindex the actual partial-centering tuple sum by its retained and
removed supply products. Each removed numerical product occurs once. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma tuplePartialProfile_empty {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l]
    (b : ZMod l) (h n : ℕ) :
    tuplePartialProfile P ∅ q eligible l b h n =
      ∑ x : (j : Fin J) → P j,
        if eligible (∏ j, (x j).val) q then
          natDivisibilityIndicator (q * ∏ j, (x j).val) n *
            (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
              liouville (n + h * (q * ∏ j, (x j).val)))
        else 0 := by
  unfold tuplePartialProfile
  apply sum_congr rfl
  intro x _
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, (x j).val) =
      ∏ j, (x j).val := (prod_subtype univ (by simp) (fun j => (x j).val)).symm
  simp only [Fintype.prod_empty, Nat.cast_one, inv_one, one_mul, he]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredTupleProfiles
namespace OAI

/-! The actual centered tuple average is the signed sum of the supply
subsets. The empty subset is precisely the full-divisibility term. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tuple_center_padding_expansion {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (q n : ℕ) (hcop : ∀ j, q.Coprime (p j)) (F : ℂ) :
    natDivisibilityIndicator q n *
        (∏ j, (natDivisibilityIndicator (p j) n - 1 / (p j : ℂ))) * F =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
          natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, p j) n * F := by
  rw [tupleCenter_expansion p hprime hinj n, mul_sum, sum_mul]
  apply sum_congr rfl
  intro I _
  have hc : q.Coprime (∏ j : {j // j ∉ I}, p j) :=
    Nat.coprime_prod_right_iff.mpr (fun j _ => hcop j)
  rw [← natDivisibilityIndicator_mul q _ n hc]
  ring


lemma tupleCenteredProfile_expansion {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tupleCenteredProfile P q eligible l b h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n := by
  simp only [tupleCenteredProfile, tuplePartialProfile, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    rw [centeredTuple_nat_eq P hprime hdisjoint]
    have hx := tuple_center_padding_expansion (fun j => (x j).val)
      (fun j => hprime j _ (x j).property) (selectedPrimeValues_injective x hdisjoint)
      q n (fun j => hcop j _ (x j).property)
      (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
        liouville (n + h * (q * ∏ j, (x j).val)))
    apply hx.trans
    apply sum_congr rfl
    intro I _
    ring
  · simp only [he, ite_false, mul_zero, sum_const_zero]

lemma tupleCenteredProfile_nonraw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tupleCenteredProfile P q eligible l b h n - tuplePartialProfile P ∅ q eligible l b h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n := by
  rw [tupleCenteredProfile_expansion P hprime hdisjoint q hcop eligible l b h n]
  let F : Finset (Fin J) → ℂ := fun I =>
    (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n
  have he : (univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [he]
  change (∑ I ∈ (univ : Finset (Fin J)).powerset, F I) - _ =
    ∑ I ∈ (univ : Finset (Fin J)).powerset.erase ∅, F I
  rw [← sum_erase_add _ F (empty_mem_powerset _)]
  simp only [F, card_empty, pow_zero, one_mul, add_sub_cancel_right]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleSliceSupport
namespace OAI

/-! Arithmetic support and mass of the removed and retained tuple supplies. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma prime_dvd_primeTupleSlice {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) {z p : ℕ}
    (hz : z ∈ primeTupleSlice P I) (hp : p.Prime) (hd : p ∣ z) :
    ∃ i ∈ I, p ∈ P i := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i : I => (x i).val)).mp hd
  have he : p = (x i).val := (Nat.prime_dvd_prime_iff_eq hp
    (hprime i _ (x i).property)).mp hi
  exact ⟨i, i.property, he.symm ▸ (x i).property⟩

lemma primeTupleSlice_avoids {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) (y : ℝ) (hy : 0 ≤ y)
    (hlarge : ∀ i, ∀ p ∈ P i, y < (p : ℝ)) {z : ℕ}
    (hz : z ∈ primeTupleSlice P I) : avoidsPrimeSet (sievePrimesUpTo y) z := by
  intro p hp hd
  obtain ⟨i, _, hi⟩ := prime_dvd_primeTupleSlice P I hprime hz
    (sievePrimesUpTo_prime y p hp) hd
  exact (not_lt_of_ge (sievePrimesUpTo_le y hy p hp)) (hlarge i p hi)

lemma primeTupleSlice_le_full_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hne : ∀ i, (P i).Nonempty) (B : ℝ)
    (hB : ∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ B)
    {z : ℕ} (hz : z ∈ primeTupleSlice P I) : (z : ℝ) ≤ B := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  let x' : (j : Fin J) → P j := fun j =>
    if hj : j ∈ I then x ⟨j, hj⟩ else ⟨(hne j).choose, (hne j).choose_spec⟩
  have he : (∏ i : I, (x i).val) = ∏ i : I, (x' i).val := by
    apply prod_congr rfl
    intro i _
    simp only [x', dif_pos i.property]
  have hd : (∏ i : I, (x i).val) ∣ ∏ j, (x' j).val := by
    rw [he, prod_coe_sort I (fun j : Fin J => (x' j).val)]
    exact prod_dvd_prod_of_subset I univ (fun j => (x' j).val) (subset_univ I)
  have hpos : 0 < ∏ j, (x' j).val := prod_pos fun j _ => (hprime j _ (x' j).property).pos
  have hle : (∏ i : I, (x i).val) ≤ ∏ j, (x' j).val := Nat.le_of_dvd hpos hd
  exact (show ((∏ i : I, (x i).val : ℕ) : ℝ) ≤ (∏ j, (x' j).val : ℕ) by
    exact_mod_cast hle).trans (hB _ (mem_image.mpr ⟨x', mem_univ _, rfl⟩))


lemma retainedTuple_le_full_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hne : ∀ i, (P i).Nonempty) (B : ℝ)
    (hB : ∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ B)
    (y : (j : {j // j ∉ I}) → P j) : (∏ j, (y j).val : ℕ) ≤ B := by
  let x : (j : Fin J) → P j := fun j =>
    if hj : j ∉ I then y ⟨j, hj⟩ else ⟨(hne j).choose, (hne j).choose_spec⟩
  have he : (∏ j, (y j).val) = ∏ j : {j // j ∉ I}, (x j).val := by
    apply prod_congr rfl
    intro j _
    simp only [x, dif_pos j.property]
  have hs := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
  have hd : (∏ j, (y j).val) ∣ ∏ j, (x j).val := by
    rw [he, hs]
    exact prod_dvd_prod_of_subset (univ \ I) univ (fun j => (x j).val) (subset_univ _)
  have hpos : 0 < ∏ j, (x j).val := prod_pos fun j _ => (hprime j _ (x j).property).pos
  have hle := Nat.le_of_dvd hpos hd
  exact (show ((∏ j, (y j).val : ℕ) : ℝ) ≤ (∏ j, (x j).val : ℕ) by
    exact_mod_cast hle).trans (hB _ (mem_image.mpr ⟨x, mem_univ _, rfl⟩))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PartialCenteringSum
namespace OAI

/-! Exact finite summation of partial-centering errors. Each removed
supply subset costs its retained reciprocal mass, never its number of primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_sum_finite {α : Type*} (S : Finset α) (F : α → ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => ∑ a ∈ S, F a n) X =
      ∑ a ∈ S, positivePrefix (F a) X := by
  unfold positivePrefix
  exact sum_comm

lemma tupleCenteredProfile_nonraw_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ) :
    (positivePrefix (tupleCenteredProfile P q eligible l b h) X -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ) =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card *
          (positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)) := by
  have hp : positivePrefix (fun n => tupleCenteredProfile P q eligible l b h n -
      tuplePartialProfile P ∅ q eligible l b h n) X =
      positivePrefix (tupleCenteredProfile P q eligible l b h) X -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [← hp]
  simp_rw [tupleCenteredProfile_nonraw P hprime hdisjoint q hcop eligible l b h]
  rw [positivePrefix_sum_finite, sum_div]
  apply sum_congr rfl
  intro I _
  rw [positivePrefix_const_mul]
  ring

lemma complement_product_le {J : ℕ} (V : Fin J → ℝ) (hV : ∀ j, 1 ≤ V j)
    (I : Finset (Fin J)) : (∏ j : {j // j ∉ I}, V j) ≤ ∏ j, V j := by
  rw [← prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) V]
  exact Finset.prod_le_prod_of_subset_of_one_le (subset_univ _)
    (fun j _ => zero_le_one.trans (hV j)) (fun j _ _ => hV j)

lemma partial_centering_sum_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hmass : ∀ j, 1 ≤ primeHarmonicMass (P j))
    (Q : Finset ℕ) (weight : ℕ → ℝ) (hweight : ∀ q ∈ Q, 0 ≤ weight q)
    (hcop : ∀ q ∈ Q, ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ)
    (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ q ∈ Q, ∀ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)‖ ≤
        E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j))) :
    ‖∑ q ∈ Q, (weight q : ℂ) *
      ((positivePrefix (tupleCenteredProfile P q eligible l b h) X -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ))‖ ≤
      E * (2 : ℝ) ^ J * (∑ q ∈ Q, weight q / (q : ℝ)) *
        ∏ j, primeHarmonicMass (P j) := by
  let V := ∏ j, primeHarmonicMass (P j)
  have hV : 0 ≤ V := prod_nonneg fun j _ => zero_le_one.trans (hmass j)
  have hc : (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
      (2 : ℝ) ^ J := by
    have hn := card_le_card (filter_subset (s := (univ : Finset (Fin J)).powerset)
      (p := Finset.Nonempty))
    simpa only [card_powerset, card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      (show (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
        ((univ : Finset (Fin J)).powerset.card : ℝ) by exact_mod_cast hn)
  calc
    _ ≤ ∑ q ∈ Q, ‖(weight q : ℂ) *
        ((positivePrefix (tupleCenteredProfile P q eligible l b h) X -
          positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, weight q * ((2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V)) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight q hq),
        tupleCenteredProfile_nonraw_prefix P hprime hdisjoint q (hcop q hq)]
      apply mul_le_mul_of_nonneg_left _ (hweight q hq)
      calc
        _ ≤ ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            ‖(-1 : ℂ) ^ I.card *
              (positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            E * (1 / (q : ℝ)) * V := by
          apply sum_le_sum
          intro I hI
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          apply (hbound q hq I hI).trans
          have hv := complement_product_le (fun j => primeHarmonicMass (P j)) hmass I
          dsimp only [V]
          calc
            _ = (E * (1 / (q : ℝ))) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
        _ ≤ (2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V) := by
          simp only [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro q _
      dsimp only [V]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalTupleSlices
namespace OAI

/-! The actual centered bands satisfy every arithmetic support condition
used by quantitative partial centering, including nonunit progression classes. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma retainedPrimeDivisor_coprime_of_primes (S : Finset ℕ) (l : ℕ)
    (hcop : ∀ p ∈ S, p.Coprime l) {q : ℕ} (hq : q ∈ retainedPrimeDivisors S) :
    q.Coprime l := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hq
  exact Nat.coprime_prod_left_iff.mpr (fun p hp => hcop p ((mem_powerset.mp hU) hp))

lemma centeredPrimeBands_coprime (E : Finset ℕ) (A W : ℝ) (J l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (j : Fin J) {p : ℕ} (hp : p ∈ centeredPrimeBands E A W J j) : p.Coprime l := by
  have hs := centeredPrimeSupply_mem hp
  exact hs.1.coprime_iff_not_dvd.mpr (fun hd => hs.2.2.1 (hE p hs.1 hd))

lemma paddingPrimeDivisor_coprime (E : Finset ℕ) (L : ℝ) (l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L)) : q.Coprime l := by
  apply retainedPrimeDivisor_coprime_of_primes _ l _ hq
  intro p hp
  exact (paddingPrimeSupply_prime hp).coprime_iff_not_dvd.mpr
    (fun hd => (mem_sdiff.mp hp).2 (hE p (paddingPrimeSupply_prime hp) hd))

lemma paddingPrimeDivisor_coprime_centered (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L))
    (j : Fin J) {p : ℕ} (hp : p ∈ centeredPrimeBands E A W J j) : q.Coprime p := by
  apply retainedPrimeDivisor_coprime_of_primes _ p _ hq
  intro r hr
  apply (Nat.coprime_primes (paddingPrimeSupply_prime hr)
    (centeredPrimeBands_prime E A W J j p hp)).mpr
  intro he
  subst r
  exact (disjoint_left.mp (centeredPrimePool_disjoint_padding E A W L J))
    (centeredPrimeBand_subset_pool E A W J j hp) hr

lemma partial_tuple_unit (E : Finset ℕ) (A W L : ℝ) (J l : ℕ)
    (hE : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (I : Finset (Fin J)) {q : ℕ} (hq : q ∈ retainedPrimeDivisors (paddingPrimeSupply E L))
    (y : (j : {j // j ∉ I}) → centeredPrimeBands E A W J j) :
    IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l) := by
  apply (ZMod.isUnit_iff_coprime _ l).mpr
  exact Nat.coprime_mul_iff_left.mpr
    ⟨paddingPrimeDivisor_coprime E L l hE hq,
      Nat.coprime_prod_left_iff.mpr (fun j _ =>
        centeredPrimeBands_coprime E A W J l hE j (y j).property)⟩

theorem ModFiveThetaInput.eventually_canonical_tuple_slices (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      (∀ j, (P j).Nonempty) ∧
      (∀ I : Finset (Fin J), I.Nonempty → ∀ z ∈ primeTupleSlice P I,
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ Real.exp (2 * L) ∧
          avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) := by
  filter_upwards [hP.eventually_actual_prime_supplies E W hW,
    eventually_ge_atTop (2 : ℝ)] with L hs hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hLp : 0 < L := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos hLp _
  have hendpoint := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime E A W J
  have hlarge (j : Fin J) (p : ℕ) (hp : p ∈ P j) : Real.exp A < (p : ℝ) :=
    (centeredPrimeSupply_global_bounds hA.le (by linarith) j.isLt hendpoint hp).1
  have hne (j : Fin J) : (P j).Nonempty := by
    by_contra hn
    have he : P j = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hm : W ≤ primeHarmonicMass (P j) := by
      simpa only [primeHarmonicMass_eq_sum, P, A, centeredPrimeBands] using (hs.2.2 j.val).2.1
    rw [he] at hm
    norm_num [primeHarmonicMass] at hm
    linarith
  refine ⟨hne, ?_⟩
  intro I hI z hz
  have hy : Real.exp (L ^ (99 / 100 : ℝ)) < Real.exp A := by
    apply Real.exp_lt_exp.mpr
    exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
  refine ⟨primeTupleSlice_lower P I hp (Real.exp A) (fun j p hp => (hlarge j p hp).le) hI hz,
    primeTupleSlice_le_full_bound P I hp hne _ (fun d hd => ?_) hz,
    primeTupleSlice_avoids P I hp _ (Real.exp_pos _).le
      (fun j p hp => hy.trans (hlarge j p hp)) hz⟩
  exact (show (d : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
    exact_mod_cast centeredPrimeTuple_upper E A W L J hA hW hendpoint hd).trans
      (Nat.floor_le (Real.exp_pos _).le)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity





















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry
namespace OAI

/-! The literal logarithmic bin places T/(dq) between X exp(-eta)
and X. Floor normalization introduces a scalar of norm at most one. -/

namespace TwoPointCorrelations

lemma actualPaddingBin_cutoff (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (η X : ℝ) (hX : 0 < X) (j : ℤ)
    (hb : actualPaddingBin η (Real.log d) j q) :
    X * Real.exp (-η) ≤ (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ∧
      (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ≤ X := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hu : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']
    ring
  have hl : Real.exp ((j : ℝ) * η) ≤ (d * q : ℕ) := by
    calc
      _ ≤ Real.exp (Real.log (d * q : ℕ)) := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.1)
      _ = _ := Real.exp_log hu
  have hh : (d * q : ℕ) ≤ Real.exp (((j : ℝ) + 1) * η) := by
    calc
      _ = Real.exp (Real.log (d * q : ℕ)) := (Real.exp_log hu).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.2.le)
  constructor
  · apply (le_div_iff₀ hu).mpr
    have he : Real.exp (-η) * Real.exp (((j : ℝ) + 1) * η) =
        Real.exp ((j : ℝ) * η) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (X * Real.exp (-η)) * Real.exp (((j : ℝ) + 1) * η) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [mul_assoc, he]
  · apply (div_le_iff₀ hu).mpr
    exact mul_le_mul_of_nonneg_left hl hX.le


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalBins
namespace OAI

/-! One common eligibility predicate for the literal manuscript bins.
Positivity makes the log-product identity valid even outside the prime pools. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma numericalBinEligible_bin (L η : ℝ) (j : ℤ) (d q : ℕ)
    (he : numericalBinEligible L η j d q) : actualPaddingBin η (Real.log d) j q := he.2.2.2


lemma numericalBin_mass (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (hQ : ∀ p ∈ Q, p.Prime) (L η : ℝ) (hL : 1 ≤ L) :
    (∑ j ∈ paddingBinIndices L η, ∑ d ∈ D,
      ∑ q ∈ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊,
        if numericalBinEligible L η j d q then
          actualPaddingCoefficient q / (d * q : ℕ) else 0) =
      totalPaddingBinMass D Q L η := by
  unfold totalPaddingBinMass boundedPaddingDivisors
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro d hd
  rw [sum_filter]
  apply sum_congr rfl
  intro q hq
  have hqp := retainedPrimeDivisor_pos Q hQ hq
  have hr : q.primeFactors.card ≤ ⌊100 * Real.log L⌋₊ ↔
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (hD d hd).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.ne'
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hd0 hq0]
    ring
  simp only [hr, numericalBinEligible, hD d hd, hqp, true_and, actualPaddingBin,
    actualPaddingCoefficient, hlog]
  split_ifs <;> simp_all

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FullNumericalBins
namespace OAI

/-! The full-divisibility main term on the exact retained numerical pairs,
with its original harmonic mass and real bin endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma fullNumericalBin_error (D R : Finset ℕ) (L η X : ℝ)
    (hX : 0 < X) (hη : 0 ≤ η) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ)
    (hunit : ∀ d ∈ D, ∀ q ∈ R, IsUnit ((q * d : ℕ) : ZMod l)) :
    ‖fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
      (numericalBinHarmonicMass D R L η j : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      numericalBinHarmonicMass D R L η j * (2 * η + 1 / X) := by
  have he (e : ℕ × ℕ) (he : e ∈ numericalBinPairs D R L η j) :
      e.1 ∈ D ∧ e.2 ∈ R ∧ numericalBinEligible L η j e.1 e.2 := by
    simpa only [numericalBinPairs, mem_filter, mem_product, and_assoc] using he
  have hb := full_divisibility_family_error l b h (numericalBinPairs D R L η j)
    (fun e => e.2 * e.1) (fun e => actualPaddingCoefficient e.2)
    (fun e _ => actualPaddingCoefficient_nonneg e.2)
    (fun e he' => Nat.mul_pos (he e he').2.2.2.1 (he e he').2.2.1)
    (fun e he' => hunit e.1 (he e he').1 e.2 (he e he').2.1)
    X (X * Real.exp ((j : ℝ) * η)) η hX hη
    (fun e he' => by
      simpa only [Nat.mul_comm] using (actualPaddingBin_cutoff e.1 e.2
        (he e he').2.2.1 (he e he').2.2.2.1 η X hX j (he e he').2.2.2.2.2).1)
    (fun e he' => by
      simpa only [Nat.mul_comm] using (actualPaddingBin_cutoff e.1 e.2
        (he e he').2.2.1 (he e he').2.2.2.1 η X hX j (he e he').2.2.2.2.2).2)
  simpa only [fullNumericalBin, numericalBinHarmonicMass, Nat.mul_comm] using hb

lemma numericalBinHarmonicMass_total (D Q : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η : ℝ) (hL : 1 ≤ L) :
    (∑ j ∈ paddingBinIndices L η,
      numericalBinHarmonicMass D (boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊) L η j) =
      totalPaddingBinMass D Q L η := by
  simp only [numericalBinHarmonicMass, numericalBinPairs, sum_filter, sum_product]
  exact numericalBin_mass D Q hD hQ L η hL

theorem fullNumericalBins_error (D Q : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η X : ℝ) (hL : 1 ≤ L) (hX : 0 < X) (hη : 0 ≤ η)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ)
    (hunit : ∀ d ∈ D, ∀ q ∈ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊,
      IsUnit ((q * d : ℕ) : ZMod l)) :
    ‖(∑ j ∈ paddingBinIndices L η,
        fullNumericalBin D (boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊) L η j l b h
          (X * Real.exp ((j : ℝ) * η))) -
      (totalPaddingBinMass D Q L η : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      totalPaddingBinMass D Q L η * (2 * η + 1 / X) := by
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let F := positivePrefix
    (fun n => progressionSequence liouville l b n * liouville (n + h)) ⌊X⌋₊ / (X : ℂ)
  have hm := numericalBinHarmonicMass_total D Q hD hQ L η hL
  have he : (∑ j ∈ paddingBinIndices L η,
      fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η))) -
      (totalPaddingBinMass D Q L η : ℂ) * F =
      ∑ j ∈ paddingBinIndices L η,
        (fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
          (numericalBinHarmonicMass D R L η j : ℂ) * F) := by
    rw [← hm]
    push_cast
    rw [sum_sub_distrib, sum_mul]
  change ‖_ - _ * F‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ j ∈ paddingBinIndices L η,
        ‖fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
          (numericalBinHarmonicMass D R L η j : ℂ) * F‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ paddingBinIndices L η,
        numericalBinHarmonicMass D R L η j * (2 * η + 1 / X) :=
      sum_le_sum (fun j _ => fullNumericalBin_error D R L η X hX hη j l b h hunit)
    _ = _ := by rw [← sum_mul, hm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialWindows
namespace OAI

/-! Actual logarithmic bins and bounded padding provide the window and
length hypotheses in the quantitative partial-centering estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma partial_bin_window (q t z : ℕ) (hq : 0 < q) (ht : 0 < t) (hz : 0 < z)
    (η : ℝ) (j : ℤ) (hbin : actualPaddingBin η (Real.log (t * z : ℕ)) j q) :
    Real.exp ((j : ℝ) * η) / (q * t : ℕ) ≤ (z : ℝ) ∧
      (z : ℝ) ≤ Real.exp η * (Real.exp ((j : ℝ) * η) / (q * t : ℕ)) := by
  have hd := Nat.mul_pos ht hz
  have hc := actualPaddingBin_cutoff (t * z) q hd hq η 1 (by norm_num) j hbin
  have hu : (0 : ℝ) < (q * t : ℕ) := by exact_mod_cast Nat.mul_pos hq ht
  have hv : (0 : ℝ) < (t * z * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  simp only [one_mul] at hc
  constructor
  · apply (div_le_iff₀ hu).mpr
    have hh := (div_le_iff₀ hv).mp hc.2
    push_cast at hh ⊢
    nlinarith
  · have hh := (le_div_iff₀ hv).mp hc.1
    have he : Real.exp η * Real.exp (-η) = 1 := by
      rw [← Real.exp_add]; simp
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos η).le
    have heq : Real.exp η * (Real.exp (-η) * (t * z * q : ℕ)) = (t * z * q : ℕ) := by
      rw [← mul_assoc, he, one_mul]
    rw [heq] at hm
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hu).mpr
    push_cast at hm ⊢
    nlinarith

theorem ModFiveThetaInput.eventually_partial_extracted_windows (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ∀ (I : Finset (Fin J)) (q : ℕ),
      q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊ →
      ∀ (y : (j : {j // j ∉ I}) → P j) (T : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ T →
        Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤
          ((⌊T⌋₊ / (q * ∏ j, (y j).val) : ℕ) : ℝ) := by
  filter_upwards [hP.eventually_canonical_tuple_slices E W hW,
    eventually_ge_atTop (1000 : ℝ)] with L hs hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hp := centeredPrimeBands_prime E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hend := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  intro I q hq y T hT
  have hqp : 0 < q := retainedPrimeDivisor_pos _ (fun _ hp => paddingPrimeSupply_prime hp)
    (mem_filter.mp hq).1
  have htp : 0 < ∏ j, (y j).val := prod_pos fun j _ => (hp j _ (y j).property).pos
  have ht : ((∏ j, (y j).val : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
    apply retainedTuple_le_full_bound P I hp hs.1 _ _ y
    intro d hd
    exact (show (d : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by
      exact_mod_cast centeredPrimeTuple_upper E A W L J hA hW hend hd).trans
        (Nat.floor_le (Real.exp_pos _).le)
  have hqbound := boundedPaddingDivisor_real_upper E L (by linarith) q hq
  apply extracted_window_lower L T _ hL (Nat.mul_pos hqp htp) hT
  calc
    _ = (q : ℝ) * ((∏ j, (y j).val : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (100 * L ^ 2) * Real.exp (2 * L) :=
      mul_le_mul hqbound ht (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialCentering
namespace OAI

/-! Quantitative nonraw centering for one actual logarithmic bin. The
only analytic inputs are the stated prime-reciprocal and MRT inputs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma tupleNonrawBin_real_denominator {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (weight : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ‖tupleNonrawBin P R weight eligible l b h T‖ ≤
      ‖∑ q ∈ R, (weight q : ℂ) *
        ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
          positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / (⌊T⌋₊ : ℂ))‖ := by
  let F : ℕ → ℂ := fun q => (weight q : ℂ) *
    (positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊)
  have hN : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hT
  have he (c : ℂ) : (∑ q ∈ R, (weight q : ℂ) *
      ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / c)) =
        (∑ q ∈ R, F q) / c := by simp only [F, mul_div_assoc, sum_div]
  rw [tupleNonrawBin, he, he, norm_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T), Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hN (Nat.floor_le (by linarith))

theorem quantitative_canonical_nonraw_bin (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
      ∀ (T : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ T →
      ∀ (η : ℝ), 0 < η → η < Real.log 2 →
      ∀ (j : ℤ) (eligible : ℕ → ℕ → Prop),
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ∀ b : ZMod l,
      ‖tupleNonrawBin P R actualPaddingCoefficient eligible l b h T‖ ≤
        C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * paddingTiltNormalizer Q *
          ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hquant⟩ := quantitative_partial_tuple_bin hM hMRT h hh
  have hl : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  refine ⟨(l : ℝ) * C, mul_pos hl hC, ?_⟩
  filter_upwards [hquant, hP.eventually_canonical_tuple_slices E W hW,
    hP.eventually_partial_extracted_windows E W hW,
    hP.eventually_actual_pool_masses E W hW, eventually_ge_atTop (1000 : ℝ)]
      with L hquant hs hw hm hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  have hLp : 0 < L := by linarith
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg hLp.le _) (by linarith)
  have hmass : ∀ i, 1 ≤ primeHarmonicMass (P i) := fun i => (hm.2.1 i).1
  intro T hT η hη hηlog j eligible helig b
  have hTone : 1 ≤ T := (Real.one_le_exp (by positivity)).trans hT
  have hN : 0 < ⌊T⌋₊ := Nat.floor_pos.mpr hTone
  have hqprime (q : ℕ) (hq : q ∈ R) : q ∈ retainedPrimeDivisors Q := (mem_filter.mp hq).1
  have hqb (q : ℕ) (hq : q ∈ R) : 0 < q :=
    retainedPrimeDivisor_pos Q (fun _ hp => paddingPrimeSupply_prime hp) (hqprime q hq)
  have hbound (q : ℕ) (hq : q ∈ R)
      (I : Finset (Fin J)) (hI : I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty) :
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) ⌊T⌋₊ / (⌊T⌋₊ : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) *
          ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
    apply hquant J P hp hd I q ⌊T⌋₊ l (hqb q hq) hN eligible b
      (Real.exp ((j : ℝ) * η)) (Real.exp η) (Real.exp_pos _)
      (by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_lt_exp.mpr hηlog)
      (fun y => partial_tuple_unit E _ W L J l hEl I (hqprime q hq) y)
      (fun y => hw I q hq y T hT)
    intro y z hz he
    have htp : 0 < ∏ i, (y i).val := prod_pos fun i _ => (hp i _ (y i).property).pos
    have hzp := primeTupleSlice_pos P I hp hz
    have hwin := partial_bin_window q _ z (hqb q hq) htp hzp η j (helig _ _ he)
    have hr := hs.2 I (mem_filter.mp hI).2 z hz
    exact ⟨by simpa only [Nat.cast_mul, Nat.cast_prod] using hwin.1,
      by simpa only [Nat.cast_mul, Nat.cast_prod] using hwin.2, hr.1, hr.2.1, hr.2.2⟩
  have hb := partial_centering_sum_bound P hp hd hmass R actualPaddingCoefficient
    (fun _ _ => by unfold actualPaddingCoefficient; positivity)
    (fun q hq i p hp => paddingPrimeDivisor_coprime_centered E _ W L J (hqprime q hq) i hp)
    eligible l b h ⌊T⌋₊ ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) (by positivity) hbound
  have hS : (∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
    rw [paddingTiltNormalizer_eq_divisor_sum Q (fun _ hp => paddingPrimeSupply_prime hp)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by
      unfold actualPaddingCoefficient; positivity)
  apply (tupleNonrawBin_real_denominator P R actualPaddingCoefficient eligible l b h T hTone).trans
  apply hb.trans
  gcongr
  exact prod_nonneg fun i _ => zero_le_one.trans (hmass i)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalCenteringBins
namespace OAI

/-! Sum the actual partial-centering errors over the logarithmic bins.
The interval exponent remains the absolute value 1000. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma bin_cutoff_ge (L η X : ℝ) (hη : 0 < η) (hX : 0 ≤ X)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    X ≤ X * Real.exp ((j : ℝ) * η) := by
  have hj0 : (0 : ℝ) ≤ j := by
    exact_mod_cast ((mem_paddingBinIndices_iff L η j hη).mp hj).1
  have he : 1 ≤ Real.exp ((j : ℝ) * η) := Real.one_le_exp (mul_nonneg hj0 hη.le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hX

lemma bin_partial_error_sum_bound (L η C S V : ℝ) (J : ℕ)
    (hL : 1 ≤ L) (hη : 0 < η) (hηone : η ≤ 1)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (F : ℤ → ℂ)
    (hF : ∀ j ∈ paddingBinIndices L η,
      ‖F j‖ ≤ C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) :
    ∑ j ∈ paddingBinIndices L η, ‖F j‖ ≤
      (101 * C) * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * S * V := by
  have hLp : 0 < L := by linarith
  calc
    _ ≤ ∑ _j ∈ paddingBinIndices L η,
        C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V :=
      sum_le_sum hF
    _ = ((paddingBinIndices L η).card : ℝ) *
        (C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (101 * L / η) *
        (C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) :=
      mul_le_mul_of_nonneg_right (paddingBinIndices_card_linear L η hL hη hηone)
        (by positivity)
    _ = _ := by
      have hp : L * L ^ (-21 / 20 : ℝ) = L ^ (-1 / 20 : ℝ) := by
        calc
          _ = L ^ (1 : ℝ) * L ^ (-21 / 20 : ℝ) := by rw [Real.rpow_one]
          _ = L ^ ((1 : ℝ) + (-21 / 20)) := (Real.rpow_add hLp _ _).symm
          _ = _ := by norm_num
      calc
        _ = (101 * C) * η⁻¹ * (2 : ℝ) ^ J *
            (L * L ^ (-21 / 20 : ℝ)) * S * V := by ring
        _ = _ := by rw [hp]

theorem quantitative_canonical_centering_bins (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
      ∀ (X : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ X →
      ∀ (η : ℝ), 0 < η → η < Real.log 2 →
      ∀ (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ b : ZMod l,
      ∑ j ∈ paddingBinIndices L η,
        ‖tupleNonrawBin P R actualPaddingCoefficient (eligible j) l b h
          (X * Real.exp ((j : ℝ) * η))‖ ≤
        C * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * paddingTiltNormalizer Q *
          ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hb⟩ := quantitative_canonical_nonraw_bin hP hM hMRT h hh l E hEl W hW
  refine ⟨101 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  dsimp only
  intro X hX η hη hηlog eligible helig b
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hlog : Real.log 2 < 1 := by
    linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hηone : η ≤ 1 := hηlog.le.trans hlog.le
  apply bin_partial_error_sum_bound L η C _ _ _ hL hη hηone hC.le
    (paddingTiltNormalizer_pos _).le (prod_nonneg fun i _ => by unfold primeHarmonicMass; positivity)
  intro j hj
  exact hb (X * Real.exp ((j : ℝ) * η))
    (hX.trans (bin_cutoff_ge L η X hη hXp.le j hj)) η hη hηlog j
      (eligible j) (helig j) b

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UncutCenteredProfile
namespace OAI

/-! Identify the uncut graph sum with the literal centered-divisor
correlation, including the original (possibly nonunit) progression class. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma uncutNumericalEdge_progression (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h l b d q n : ℕ) [NeZero l] (hh : 0 < h) (hd : 0 < d) (hq : 0 < q)
    (hqR : q ∈ R) :
    uncutNumericalEdge R eligible h (progressionEdgeGate h l b) d q n
      ((n : ℤ) + (h * q * d : ℕ)) =
      if eligible d q then
        (actualPaddingCoefficient q : ℂ) * natDivisibilityIndicator q n *
          (centeredTuple d.primeFactors (n : ℤ) : ℂ) *
          (progressionSequence liouville l ((b : ZMod l) * ((q * d : ℕ) : ZMod l)) n *
            liouville (n + h * (q * d)))
      else 0 := by
  have hg : progressionEdgeGate h l b d (n : ℤ) ((n : ℤ) + (h * q * d : ℕ)) ↔
      (n : ZMod l) = (b : ZMod l) * ((q * d : ℕ) : ZMod l) := by
    rw [progressionEdgeGate_on_edge h l b d q hh hd hq]
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, mul_assoc]
  have hm : (n : ℤ) + (h * q * d : ℕ) = ((n + h * (q * d) : ℕ) : ℤ) := by
    push_cast
    ring
  simp only [uncutNumericalEdge, hqR, and_true, hm, integerLiouville_natCast,
    Int.natCast_dvd_natCast, Complex.ofReal_mul]
  unfold natDivisibilityIndicator progressionSequence
  split_ifs <;> simp_all
  ring

lemma uncutPrimePrefix_centered {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q) (eligible : ℕ → ℕ → Prop)
    (h l b N : ℕ) [NeZero l] (hh : 0 < h) :
    uncutPrimePrefix P R eligible h (progressionEdgeGate h l b) N =
      positivePrefix (fun n => ∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        tupleCenteredProfile P q eligible l (b : ZMod l) h n) N / (N : ℂ) := by
  unfold uncutPrimePrefix
  congr 2
  funext n
  rw [primeTupleDivisors, sum_image]
  · rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    simp only [tupleCenteredProfile, mul_sum]
    apply sum_congr rfl
    intro x _
    have hd : 0 < ∏ j, (x j).val := prod_pos (fun j _ => (hprime j _ (x j).property).pos)
    rw [uncutNumericalEdge_progression R eligible h l b _ q n hh hd (hR q hq) hq]
    by_cases he : eligible (∏ j, (x j).val) q
    · simp only [he, ite_true]
      ring
    · simp only [he, ite_false, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FullTupleBinIdentity
namespace OAI

/-! The empty supply subset is exactly the full numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_ite_const (p : Prop) (f : ℕ → ℂ) (N : ℕ) :
    positivePrefix (fun n => if p then f n else 0) N =
      if p then positivePrefix f N else 0 := by
  by_cases hp : p <;> simp only [hp, ite_true, ite_false, positivePrefix, sum_const_zero]

lemma fullNumericalBin_tuple {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (L η : ℝ) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) :
    fullNumericalBin (primeTupleDivisors P) R L η j l b h T =
      ∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        (positivePrefix (tuplePartialProfile P ∅ q (numericalBinEligible L η j) l b h) ⌊T⌋₊ /
          (T : ℂ)) := by
  simp only [fullNumericalBin, numericalBinPairs, sum_filter, sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [primeTupleDivisors, sum_image]
  · have hf : tuplePartialProfile P ∅ q (numericalBinEligible L η j) l b h =
        fun n => ∑ x : (i : Fin J) → P i,
          if numericalBinEligible L η j (∏ i, (x i).val) q then
            fullLiouvilleProfile l b (q * ∏ i, (x i).val) h n else 0 := by
      funext n
      exact tuplePartialProfile_empty P q (numericalBinEligible L η j) l b h n
    rw [hf, positivePrefix_sum_finite, sum_div, mul_sum]
    simp_rw [positivePrefix_ite_const]
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp_all only [zero_div, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredBinIdentity
namespace OAI

/-! The graph bin and the analytic centering bin are the same finite sum,
with the literal real denominator and no floor-normalization error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma prefix_scalar_real_denominator (f : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ((N : ℂ) / (T : ℂ)) * (positivePrefix f N / (N : ℂ)) =
      positivePrefix f N / (T : ℂ) := by
  by_cases hN : N = 0
  · subst N
    simp only [positivePrefix, range_zero, sum_empty, Nat.cast_zero, zero_div, mul_zero]
  · have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

lemma weighted_uncut_sub_full_bin {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q) (L η : ℝ) (j : ℤ)
    (h l b : ℕ) [NeZero l] (hh : 0 < h) (T : ℝ) :
    ((⌊T⌋₊ : ℂ) / (T : ℂ)) *
        uncutPrimePrefix P R (numericalBinEligible L η j) h (progressionEdgeGate h l b) ⌊T⌋₊ -
      fullNumericalBin (primeTupleDivisors P) R L η j l (b : ZMod l) h T =
        tupleNonrawBin P R actualPaddingCoefficient (numericalBinEligible L η j)
          l (b : ZMod l) h T := by
  rw [uncutPrimePrefix_centered P hprime hdisjoint R hR _ h l b _ hh,
    prefix_scalar_real_denominator, fullNumericalBin_tuple P hprime hdisjoint]
  rw [positivePrefix_sum_finite, sum_div]
  simp only [positivePrefix_const_mul, tupleNonrawBin, mul_div_assoc]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeCenteringAssembly
namespace OAI

/-! The quantitative centering estimate for the same numerical bins
used by the spectral and deletion bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



theorem quantitative_centering_assembly_oai (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L,
      ∀ X : ℝ, Real.exp (L ^ (1000 : ℝ)) ≤ X →
      ∀ η : ℝ, 0 < η → η < Real.log 2 → ∀ b : ℕ,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      ‖(∑ j ∈ paddingBinIndices L η, canonicalRawBin h l b E W L η X j) -
          (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤
        C * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * paddingTiltNormalizer Q *
          (∏ i, primeHarmonicMass (P i)) + S₀ * (2 * η + 1 / X) := by
  obtain ⟨C, hC, hb⟩ := quantitative_canonical_centering_bins hP hM hMRT h hh l E hEl W hW
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro hL X hX η hη hηlog b
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let S₀ := totalPaddingBinMass D Q L η
  let bins := paddingBinIndices L η
  let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
  let F := progressionLiouvilleMean h l b X
  let raw := fun j => canonicalRawBin h l b E W L η X j
  let full := fun j => fullNumericalBin D R L η j l (b : ZMod l) h (T j)
  let err := fun j => tupleNonrawBin P R actualPaddingCoefficient (numericalBinEligible L η j)
    l (b : ZMod l) h (T j)
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  have hR : ∀ q ∈ R, 0 < q := fun q hq' =>
    retainedPrimeDivisor_pos Q hq (mem_filter.mp hq').1
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd'
    obtain ⟨x, _, rfl⟩ := mem_image.mp hd'
    exact prod_pos fun i _ => (hp i _ (x i).property).pos
  have hunit : ∀ d ∈ D, ∀ q ∈ R, IsUnit ((q * d : ℕ) : ZMod l) := by
    intro d hd' q hq'
    obtain ⟨x, _, rfl⟩ := mem_image.mp hd'
    apply (ZMod.isUnit_iff_coprime _ l).mpr
    exact Nat.coprime_mul_iff_left.mpr
      ⟨paddingPrimeDivisor_coprime E L l hEl (mem_filter.mp hq').1,
        Nat.coprime_prod_left_iff.mpr (fun i _ =>
          centeredPrimeBands_coprime E _ W J l hEl i (x i).property)⟩
  have hident (j : ℤ) : raw j - full j = err j :=
    weighted_uncut_sub_full_bin P hp hd R hR L η j h l b hh (T j)
  have hsum : (∑ j ∈ bins, raw j) - (∑ j ∈ bins, full j) = ∑ j ∈ bins, err j := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun j _ => hident j)
  have he := hb X hX η hη hηlog (numericalBinEligible L η)
    (fun j d q he => numericalBinEligible_bin L η j d q he) (b : ZMod l)
  have hf := fullNumericalBins_error D Q hD hq L η X hL
    ((Real.exp_pos _).trans_le hX) hη.le l (b : ZMod l) h hunit
  change ‖(∑ j ∈ bins, raw j) - (S₀ : ℂ) * F‖ ≤ _
  have ht := norm_add_le ((∑ j ∈ bins, raw j) - (∑ j ∈ bins, full j))
    ((∑ j ∈ bins, full j) - (S₀ : ℂ) * F)
  rw [sub_add_sub_cancel, hsum] at ht
  exact ht.trans (add_le_add ((norm_sum_le _ _).trans he) hf)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.quantitative_centering_assembly_oai := @OAI.TwoPointCorrelations.quantitative_centering_assembly_oai
