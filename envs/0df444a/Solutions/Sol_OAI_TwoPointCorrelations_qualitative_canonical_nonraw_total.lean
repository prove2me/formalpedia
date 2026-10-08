-- Prove2me | solution 1 for OAI.TwoPointCorrelations.qualitative_canonical_nonraw_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:58:47.36097+00:00
-- url     : https://prove2.me/submissions/7ada4d5b-53bc-4bc6-a8b4-d4d3ed267391

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
import Theorems.Thm_OAI_TwoPointCorrelations_qualitative_dilated_fixed_factors

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





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]















lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm




end FiniteLaw

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums
namespace OAI

/-! Finite weighted assembly at the actual divisor scale `Y = X/u`.
The factor `1/u` is retained exactly, including floor cutoffs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma tendsto_nat_div_atTop (u : ℕ) (hu : 0 < u) :
    Tendsto (fun X : ℕ => X / u) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * u)] with X hX
  exact (Nat.le_div_iff_mul_le hu).mpr hX

lemma prefix_norm_of_average_bound (F : ℕ → ℂ) (N : ℕ) (E : ℝ)
    (hF : ‖positivePrefix F N / (N : ℂ)‖ ≤ E) :
    ‖positivePrefix F N‖ ≤ (N : ℝ) * E := by
  by_cases hN : N = 0
  · simp [hN, positivePrefix]
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [norm_div, Complex.norm_natCast] at hF
  have ht := (div_le_iff₀ hNp).mp hF
  nlinarith only [ht]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothReciprocalMass
namespace OAI

/-! Finite-prime smooth reciprocal sums. The exact Euler factors make
averaging the dilation cost against the padding law possible. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma smoothReciprocalProduct_hasSum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun a : Nat.factoredNumbers P => (a.val : ℝ) ^ (-s))
      (smoothReciprocalProduct P s) := by
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := natNegativePower s) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-s)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)) P
  have he : P.filter Nat.Prime = P := filter_eq_self.mpr hP
  simpa [natNegativePower, smoothReciprocalProduct, he] using h.2

lemma smoothReciprocalProduct_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    0 ≤ smoothReciprocalProduct P s := by
  apply (smoothReciprocalProduct_hasSum P hP s hs).nonneg
  intro a
  exact Real.rpow_nonneg (Nat.cast_nonneg a.val) _



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothProductBounds
namespace OAI

/-! Elementary bounds for the Euler cost of adjoining retained tuple primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma one_le_smoothReciprocalProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    1 ≤ smoothReciprocalProduct P s := by
  apply Finset.one_le_prod
  intro p hp
  have hr : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  exact (one_le_inv₀ (sub_pos.mpr hr)).mpr (by
    have hh := Real.rpow_nonneg (Nat.cast_nonneg p) (-s)
    linarith)

lemma smoothReciprocalProduct_union_le (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (s : ℝ) (hs : 0 < s) :
    smoothReciprocalProduct (P ∪ Q) s ≤
      smoothReciprocalProduct P s * smoothReciprocalProduct Q s := by
  have he : smoothReciprocalProduct (P ∪ Q) s * smoothReciprocalProduct (P ∩ Q) s =
      smoothReciprocalProduct P s * smoothReciprocalProduct Q s := by
    exact prod_union_inter
  have hnonneg := smoothReciprocalProduct_nonneg (P ∪ Q)
    (fun p hp => (mem_union.mp hp).elim (hP p) (hQ p)) s hs
  have hone := one_le_smoothReciprocalProduct (P ∩ Q)
    (fun p hp => hP p (mem_inter.mp hp).1) s hs
  exact (le_mul_of_one_le_right hnonneg hone).trans_eq he

lemma smoothReciprocalProduct_mul_le (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (s : ℝ) (hs : 0 < s) :
    smoothReciprocalProduct (q * t).primeFactors s ≤
      smoothReciprocalProduct q.primeFactors s * smoothReciprocalProduct t.primeFactors s := by
  rw [Nat.primeFactors_mul hq.ne' ht.ne']
  exact smoothReciprocalProduct_union_le _ _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) s hs

lemma reciprocal_one_sub_le_exp (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    (1 - r)⁻¹ ≤ Real.exp (2 * r) := by
  have hd : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 1 + 2 * r := by
    have hh : 1 / (1 - r) ≤ 1 + 2 * r := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg hr (show 0 ≤ 1 - 2 * r by linarith)])
    simpa only [one_div] using hh
  exact hinv.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * r))

lemma smooth_half_product_exp_bound (P : Finset ℕ)
    (hsmall : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤
      Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp (2 * (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have hh := hsmall p hp
        linarith
      · intro p hp
        exact reciprocal_one_sub_le_exp _ (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hsmall p hp)
    _ = _ := by rw [← Real.exp_sum, mul_sum]

lemma smooth_half_product_le_two (P : Finset ℕ)
    (hsmall : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2)
    (hsum : 2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ Real.log 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  exact (smooth_half_product_exp_bound P hsmall).trans
    ((Real.exp_le_exp.mpr hsum).trans_eq (Real.exp_log (by norm_num)))

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalRoughScale
namespace OAI

/-! Reparametrizing the stronger qualitative estimate at the actual
quantitative prime-band endpoint exp(L^.995). The gain survives the
finite tuple expansion and the final reciprocal L normalizer. -/

namespace TwoPointCorrelations

open _root_.Filter


lemma canonicalRoughParameter_prime_endpoint (L : ℝ) (hL : 0 ≤ L) :
    canonicalRoughParameter L ^ (9999 / 10000 : ℝ) = L ^ (199 / 200 : ℝ) := by
  unfold canonicalRoughParameter
  rw [← Real.rpow_mul hL]
  norm_num

lemma canonicalRoughParameter_square_ge (L : ℝ) (hL : 1 ≤ L) :
    L ≤ canonicalRoughParameter L ^ (2 : ℕ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
    _ ≤ L ^ (19900 / 9999 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ = _ := by
      unfold canonicalRoughParameter
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
      norm_num

lemma canonicalRoughParameter_error (L : ℝ) (hL : 0 ≤ L) :
    canonicalRoughParameter L ^ (-11 / 10 : ℝ) = L ^ (-10945 / 9999 : ℝ) := by
  unfold canonicalRoughParameter
  rw [← Real.rpow_mul hL]
  norm_num

lemma canonicalRoughParameter_tendsto : Tendsto canonicalRoughParameter atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9950 / 9999)

lemma tuple_expansion_small_power (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    (2 : ℝ) ^ J ≤ L ^ (1 / 100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : Real.log 2 ≤ 1 := by
    convert (preTransparency := .instances) Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

lemma canonical_centering_rate_bound (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    (2 : ℝ) ^ J * L * canonicalRoughParameter L ^ (-11 / 10 : ℝ) ≤
      L ^ (-2 / 25 : ℝ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  rw [canonicalRoughParameter_error L hL0]
  calc
    _ ≤ L ^ (1 / 100 : ℝ) * L * L ^ (-10945 / 9999 : ℝ) := by
      gcongr
      exact tuple_expansion_small_power L hL J hJ
    _ = L ^ ((1 / 100 : ℝ) + 1 - 10945 / 9999) := by
      rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans_le hL),
        Real.rpow_add (zero_lt_one.trans_le hL), Real.rpow_one]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

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



lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLiteralBins
namespace OAI

/-! The bin mass is the literal normalized sum of padding-divisor weights.
Boolean selections are finite subsets, so no extra multiplicity is present. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma paddingDivisorCoefficient_eq_four_pow (Q : Finset ℕ) (b : Q → Bool) :
    paddingDivisorCoefficient Q b = (4 : ℝ) ^ (selectedCoordinates Q b).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingDivisorCoefficient]





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






lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)










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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma reciprocal_padding_atom (p : ℕ) (hp : 0 < p) (b : Bool) :
    (reciprocalPaddingPrimeLaw p).weight b * (1 + 4 / (p : ℝ)) =
      if b then 4 / (p : ℝ) else 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases b <;> simp only [reciprocalPaddingPrimeLaw, booleanLaw, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma paddingSelectedDivisor_cast (Q : Finset ℕ) (b : Q → Bool) :
    (paddingSelectedDivisor Q b : ℝ) = ∏ p : Q, if b p then (p.val : ℝ) else 1 := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  simp only [selectedCoordinates, prod_filter]

lemma reciprocal_padding_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) :
    (reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q =
      paddingDivisorCoefficient Q b / (paddingSelectedDivisor Q b : ℝ) := by
  simp only [reciprocalPaddingLaw, FiniteLaw.independent, paddingTiltNormalizer,
    ← prod_mul_distrib]
  rw [paddingDivisorCoefficient, paddingSelectedDivisor_cast, ← prod_div_distrib]
  apply prod_congr rfl
  intro p _
  rw [reciprocal_padding_atom p (hQ p p.property).pos]
  cases b p <;> simp

lemma reciprocal_padding_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average (fun b => F (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q := by
  have hS := paddingTiltNormalizer_pos Q
  let G (q : retainedPrimeDivisors Q) : ℝ :=
    ((4 : ℝ) ^ q.val.primeFactors.card / (q.val : ℝ)) * F q.val
  have hatom (b : Q → Bool) :
      (reciprocalPaddingLaw Q).weight b * F (paddingSelectedDivisor Q b) =
        (paddingTiltNormalizer Q)⁻¹ * G (paddingDivisorEquiv Q hQ b) := by
    have hw := reciprocal_padding_weight Q hQ b
    change _ = (paddingTiltNormalizer Q)⁻¹ *
      ((4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card /
        (paddingSelectedDivisor Q b : ℝ) * F (paddingSelectedDivisor Q b))
    rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      ← paddingDivisorCoefficient_eq_four_pow]
    calc
      _ = (paddingTiltNormalizer Q)⁻¹ *
          (((reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q) *
            F (paddingSelectedDivisor Q b)) := by field_simp [hS.ne']
      _ = _ := by rw [hw]
  unfold FiniteLaw.average
  simp_rw [hatom]
  rw [← mul_sum, (paddingDivisorEquiv Q hQ).sum_comp G]
  congr 1
  exact sum_coe_sort (retainedPrimeDivisors Q)
    (fun q : ℕ => ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingSmoothMass
namespace OAI

/-! Averaging smooth-dilation costs under the actual padding divisor law.
Only one factor is paid at each selected prime. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma smoothReciprocalProduct_selected (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) (s : ℝ) :
    smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors s =
      ∏ p : Q, if b p then (1 - (p.val : ℝ) ^ (-s))⁻¹ else 1 := by
  rw [paddingSelectedDivisor_primeFactors Q hQ, smoothReciprocalProduct,
    paddingAvailablePrimes, prod_image]
  · simp only [selectedCoordinates, prod_filter]
  · intro p _ r _ hpr
    exact Subtype.ext hpr

lemma padding_smooth_reciprocal_average (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (s : ℝ) :
    (reciprocalPaddingLaw Q).average
      (fun b => smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors s) =
      ∏ p : Q, (1 + 4 / ((p.val : ℝ) + 4) *
        ((1 - (p.val : ℝ) ^ (-s))⁻¹ - 1)) := by
  simp only [smoothReciprocalProduct_selected Q hQ]
  rw [reciprocalPaddingLaw,
    FiniteLaw.independent_average_product (fun p : Q => reciprocalPaddingPrimeLaw p.val)
      (fun (p : Q) (b : Bool) => if b then (1 - (p.val : ℝ) ^ (-s))⁻¹ else 1)]
  apply prod_congr rfl
  intro p _
  simp only [FiniteLaw.average, reciprocalPaddingPrimeLaw, booleanLaw, Fintype.sum_bool,
    Bool.false_eq_true, ite_false, ite_true, mul_one]
  ring

lemma padding_smooth_reciprocal_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (s : ℝ) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      smoothReciprocalProduct q.primeFactors s) =
      paddingTiltNormalizer Q *
        ∏ p : Q, (1 + 4 / ((p.val : ℝ) + 4) *
          ((1 - (p.val : ℝ) ^ (-s))⁻¹ - 1)) := by
  have he := reciprocal_padding_average Q hQ
    (fun q => smoothReciprocalProduct q.primeFactors s)
  rw [padding_smooth_reciprocal_average Q hQ] at he
  have hpos := paddingTiltNormalizer_pos Q
  calc
    _ = paddingTiltNormalizer Q *
        ((paddingTiltNormalizer Q)⁻¹ *
          ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
            smoothReciprocalProduct q.primeFactors s) := by
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ = _ := by rw [← he]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingSmoothBound
namespace OAI

/-! The smooth-dilation cost averaged over the actual reciprocal padding
law is bounded by an absolute convergent product, uniformly in the pool. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma paddingSmoothConstant_pos : 0 < paddingSmoothConstant := Real.exp_pos _

lemma smooth_half_local_bound (p : ℕ) (hp : 2 ≤ p) :
    0 ≤ 4 / ((p : ℝ) + 4) * ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1) ∧
    4 / ((p : ℝ) + 4) * ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1) ≤
      (4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 < (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hr1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have h20 : 0 < (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (-(1 / 2) : ℝ) < 0)
    linarith
  have hrle : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
  have hlocal : (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1 =
      (p : ℝ) ^ (-(1 / 2) : ℝ) / (1 - (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr hr1))).mpr
    rw [sub_mul, inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hr1)), one_mul]
    ring
  rw [hlocal]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (4 / (p : ℝ)) *
        ((p : ℝ) ^ (-(1 / 2) : ℝ) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (by norm_num) hp0 (by linarith)
      · exact div_le_div_of_nonneg_left hr0.le h20 (by linarith)
      · positivity
      · positivity
    _ = _ := by
      rw [show (-3 / 2 : ℝ) = -1 + (-1 / 2) by norm_num,
        Real.rpow_add hp0, Real.rpow_neg_one]
      ring_nf

lemma padding_smooth_half_average_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    (reciprocalPaddingLaw Q).average
      (fun b => smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors
        (1 / 2 : ℝ)) ≤ paddingSmoothConstant := by
  rw [padding_smooth_reciprocal_average Q hQ]
  let c := 4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))
  let e : ℕ → ℝ := fun p => 4 / ((p : ℝ) + 4) *
    ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hh := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (-(1 / 2) : ℝ) < 0)
    positivity
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsum : (∑ p : Q, e p.val) ≤ c * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ ∑ p : Q, c * (p.val : ℝ) ^ (-3 / 2 : ℝ) := by
        apply sum_le_sum
        intro p _
        exact (smooth_half_local_bound p.val (hQ p.val p.property).two_le).2
      _ = c * ∑ p ∈ Q, (p : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [← mul_sum, sum_coe_sort Q (fun p : ℕ => (p : ℝ) ^ (-3 / 2 : ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum Q (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)) hc
  calc
    _ ≤ ∏ p : Q, Real.exp (e p.val) := by
      apply Finset.prod_le_prod
      · intro p _
        have hh := (smooth_half_local_bound p.val (hQ p.val p.property).two_le).1
        change 0 ≤ 1 + e p.val
        linarith
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (e p.val)
    _ = Real.exp (∑ p : Q, e p.val) := (Real.exp_sum _ _).symm
    _ ≤ paddingSmoothConstant := Real.exp_le_exp.mpr hsum

lemma padding_smooth_half_sum_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) ≤
      paddingTiltNormalizer Q * paddingSmoothConstant := by
  have he := padding_smooth_reciprocal_sum Q hQ (1 / 2 : ℝ)
  rw [← padding_smooth_reciprocal_average Q hQ] at he
  rw [he]
  exact mul_le_mul_of_nonneg_left (padding_smooth_half_average_le Q hQ)
    (paddingTiltNormalizer_pos Q).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleSmoothCost
namespace OAI

/-! The retained tuple introduces at most a factor two into the smooth
Euler cost, because all its primes lie above the canonical lower endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Topology

lemma smooth_half_cost_of_large_factors (P : Finset ℕ) (L : ℝ)
    (hL : 2 ≤ L) (hcard : (P.card : ℝ) ≤ L)
    (hlarge : ∀ p ∈ P, L ^ (4 : ℕ) ≤ (p : ℝ))
    (hlog : 2 / L ≤ Real.log 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  have hLp : 0 < L := by linarith
  have hterm : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ L ^ (-2 : ℝ) := by
    intro p hp
    have hh := Real.rpow_le_rpow_of_nonpos (pow_pos hLp 4) (hlarge p hp)
      (show (-(1 / 2) : ℝ) ≤ 0 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le] at hh
    norm_num at hh ⊢
    exact hh
  have hs : L ^ (-2 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
    apply (inv_le_comm₀ (sq_pos_of_pos hLp) (by norm_num)).mpr
    nlinarith
  apply smooth_half_product_le_two P (fun p hp => (hterm p hp).trans hs)
  calc
    2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * ((P.card : ℝ) * L ^ (-2 : ℝ)) := by
      gcongr
      exact (sum_le_sum hterm).trans_eq (by simp)
    _ ≤ 2 * (L * L ^ (-2 : ℝ)) := by gcongr
    _ = 2 / L := by rw [Real.rpow_neg hLp.le, Real.rpow_two]; field_simp
    _ ≤ Real.log 2 := hlog

lemma eventually_canonical_smooth_half_cost :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (P.card : ℝ) ≤ L →
      (∀ p ∈ P, Real.exp (L ^ (199 / 200 : ℝ)) ≤ (p : ℝ)) →
      smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  have hs := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < (1 / 4 : ℝ) by norm_num)
  have hl : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 2
  filter_upwards [hs, hl.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    eventually_ge_atTop 2] with L hs hl hL
  intro P hcard hlarge
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hs
  apply smooth_half_cost_of_large_factors P L hL hcard _ hl.le
  intro p hp
  calc
    L ^ (4 : ℕ) = Real.exp (4 * Real.log L) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hLp]
      congr 1
      ring
    _ ≤ Real.exp (L ^ (199 / 200 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (p : ℝ) := hlarge p hp

lemma dilated_tuple_smooth_cost (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (htcost : smoothReciprocalProduct t.primeFactors (1 / 2 : ℝ) ≤ 2) :
    smoothReciprocalProduct (q * t).primeFactors (1 / 2 : ℝ) ≤
      2 * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  calc
    _ ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) *
        smoothReciprocalProduct t.primeFactors (1 / 2 : ℝ) :=
      smoothReciprocalProduct_mul_le q t hq ht _ (by norm_num)
    _ ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left htcost (smoothReciprocalProduct_nonneg _
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) _ (by norm_num))
    _ = _ := mul_comm _ _

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



lemma primeSupplyCount_mul_bound (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤
      ((1 / 200 : ℝ) * Real.log L) / (6 * W) := Nat.floor_le (by positivity)
  exact (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale
namespace OAI

/-! At a fixed W the retained row majorant grows polynomially in L;
it can therefore be absorbed into a small exponential boundary budget. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma primeSupplyCount_le_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg hL]




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

lemma indexed_prime_product_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : ι) → P i => ∏ i, (x i).val) := by
  intro x y he
  change (∏ i, (x i).val) = ∏ i, (y i).val at he
  funext i
  apply Subtype.ext
  have hp := hprime i _ (x i).property
  have hd : (x i).val ∣ ∏ j, (y j).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun j => (x j).val) (mem_univ i)
  obtain ⟨j, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun j => (y j).val)).mp hd
  have hv : (x i).val = (y j).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime j _ (y j).property)).mp hdiv
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (hdisjoint i j (Ne.symm hne)) (x i).property
      (hv.symm ▸ (y j).property)
  subst j
  exact hv


lemma primeTupleSlice_injective {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : I) → P i => ∏ i, (x i).val) :=
  indexed_prime_product_injective _ (fun i => hprime i)
    (fun i j hne => hdisjoint i j (fun he => hne (Subtype.ext he)))


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

lemma primeTupleSlice_split_sum {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) (F : ℕ → ℕ → ℂ) :
    (∑ x : (j : Fin J) → P j,
      F (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val)) =
      ∑ y : (j : {j // j ∉ I}) → P j, ∑ z ∈ primeTupleSlice P I,
        F (∏ j, (y j).val) z := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : Fin J => j ∈ I) (fun j => P j)
  calc
    _ = ∑ xy : ((i : I) → P i) × ((j : {j // j ∉ I}) → P j),
        F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val) := by
      simpa only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk] using
        (e.sum_comp (fun xy => F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val)))
    _ = ∑ y : (j : {j // j ∉ I}) → P j, ∑ x : (i : I) → P i,
        F (∏ j, (y j).val) (∏ i, (x i).val) := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro y _
      rw [primeTupleSlice, sum_image]
      exact fun x _ y _ he => primeTupleSlice_injective P I hprime hdisjoint he

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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexTupleProfiles
namespace OAI

/-! Exact centered tuple expansion for arbitrary complex sequences. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma tupleComplexCenteredProfile_expansion {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexCenteredProfile P q eligible F G h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n := by
  simp only [tupleComplexCenteredProfile, tupleComplexPartialProfile, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    rw [centeredTuple_nat_eq P hprime hdisjoint]
    have hx := tuple_center_padding_expansion (fun j => (x j).val)
      (fun j => hprime j _ (x j).property) (selectedPrimeValues_injective x hdisjoint)
      q n (fun j => hcop j _ (x j).property)
      (F n * G (n + h * (q * ∏ j, (x j).val)))
    apply hx.trans
    apply sum_congr rfl
    intro I _
    ring
  · simp only [he, ite_false, mul_zero, sum_const_zero]

lemma tupleComplexCenteredProfile_nonraw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexCenteredProfile P q eligible F G h n - tupleComplexPartialProfile P ∅ q eligible F G h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n := by
  rw [tupleComplexCenteredProfile_expansion P hprime hdisjoint q hcop eligible F G h n]
  let H : Finset (Fin J) → ℂ := fun I =>
    (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n
  have he : (univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [he]
  change (∑ I ∈ (univ : Finset (Fin J)).powerset, H I) - _ =
    ∑ I ∈ (univ : Finset (Fin J)).powerset.erase ∅, H I
  rw [← sum_erase_add _ H (empty_mem_powerset _)]
  simp only [H, card_empty, pow_zero, one_mul, add_sub_cancel_right]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialProfiles
namespace OAI

/-! Exact retained/removed tuple reindexing and divisibility extraction for complex tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma complexPartialProfile_prefix (F G : ℕ → ℂ) (u : ℕ) (Z : Finset ℕ)
    (h X : ℕ) (hu : 0 < u) :
    positivePrefix (complexPartialProfile F G u Z h) X =
      positivePrefix (complexRoughProfile (fun n => F (u * n)) (fun n => G (u * n)) Z h)
        (X / u) := by
  unfold complexPartialProfile
  rw [divisibility_positivePrefix _ u X hu]
  congr 1
  funext n
  unfold complexRoughProfile
  apply sum_congr rfl
  intro z _
  rw [show u * n + h * u * z = u * (n + h * z) by ring]

lemma tupleComplexPartialProfile_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexPartialProfile P I q eligible F G h n =
      ∑ y : (j : {j // j ∉ I}) → P j,
        complexPartialProfile F G (q * ∏ j, (y j).val)
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h n := by
  let H : ℕ → ℕ → ℂ := fun t z =>
    if eligible (t * z) q then (z : ℂ)⁻¹ *
      (natDivisibilityIndicator (q * t) n *
        (F n * G (n + h * (q * t * z)))) else 0
  have hs := primeTupleSlice_split_sum P I hprime hdisjoint H
  have hleft : tupleComplexPartialProfile P I q eligible F G h n =
      ∑ x : (j : Fin J) → P j,
        H (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val) := by
    apply sum_congr rfl
    intro x _
    have he : (∏ j : {j // j ∉ I}, (x j).val) * (∏ i : I, (x i).val) =
        ∏ j, (x j).val := by
      have hI := prod_coe_sort I (fun j : Fin J => (x j).val)
      have hIc := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
      rw [hI, hIc, ← prod_union sdiff_disjoint, sdiff_union_of_subset (subset_univ I)]
    dsimp only [H]
    simp only [mul_assoc, he]
  rw [hleft, hs]
  apply sum_congr rfl
  intro y _
  rw [complexPartialProfile, mul_sum, sum_filter]
  apply sum_congr rfl
  intro z _
  dsimp only [H]
  split_ifs
  · simp only [mul_assoc]
    ring
  · simp

lemma tupleComplexPartialProfile_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h X : ℕ)
    :
    positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X =
      ∑ y : (j : {j // j ∉ I}) → P j,
        positivePrefix (complexRoughProfile (fun m => F ((q * ∏ j, (y j).val) * m))
          (fun m => G ((q * ∏ j, (y j).val) * m))
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
          (X / (q * ∏ j, (y j).val)) := by
  simp only [positivePrefix, tupleComplexPartialProfile_reindex P hprime hdisjoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  exact complexPartialProfile_prefix F G _ _ h X
    (Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos))

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


lemma complement_product_le {J : ℕ} (V : Fin J → ℝ) (hV : ∀ j, 1 ≤ V j)
    (I : Finset (Fin J)) : (∏ j : {j // j ∉ I}, V j) ≤ ∏ j, V j := by
  rw [← prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) V]
  exact Finset.prod_le_prod_of_subset_of_one_le (subset_univ _)
    (fun j _ => zero_le_one.trans (hV j)) (fun j _ _ => hV j)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexCenteringSum
namespace OAI

/-! Average the exact complex partial-centering errors with their padding-dependent cost. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tupleComplexCenteredProfile_nonraw_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h X : ℕ) :
    (positivePrefix (tupleComplexCenteredProfile P q eligible F G h) X -
      positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) X) / (X : ℂ) =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card *
          (positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)) := by
  have hp : positivePrefix (fun n => tupleComplexCenteredProfile P q eligible F G h n -
      tupleComplexPartialProfile P ∅ q eligible F G h n) X =
      positivePrefix (tupleComplexCenteredProfile P q eligible F G h) X -
        positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) X := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [← hp]
  simp_rw [tupleComplexCenteredProfile_nonraw P hprime hdisjoint q hcop eligible F G h]
  rw [positivePrefix_sum_finite, sum_div]
  apply sum_congr rfl
  intro I _
  rw [positivePrefix_const_mul]
  ring

lemma complex_partial_centering_sum_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hmass : ∀ j, 1 ≤ primeHarmonicMass (P j))
    (Q : Finset ℕ) (weight : ℕ → ℝ) (hweight : ∀ q ∈ Q, 0 ≤ weight q)
    (hcop : ∀ q ∈ Q, ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h X : ℕ)
    (E : ℕ → ℝ) (hE : ∀ q ∈ Q, 0 ≤ E q)
    (hbound : ∀ q ∈ Q, ∀ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
      ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)‖ ≤
        E q * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j))) :
    ‖∑ q ∈ Q, (weight q : ℂ) *
      ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) X -
        positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) X) / (X : ℂ))‖ ≤
      (2 : ℝ) ^ J * (∑ q ∈ Q, weight q / (q : ℝ) * E q) *
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
        ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) X -
          positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) X) / (X : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, weight q * ((2 : ℝ) ^ J * (E q * (1 / (q : ℝ)) * V)) := by
      apply sum_le_sum
      intro q hq
      have hEq := hE q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight q hq),
        tupleComplexCenteredProfile_nonraw_prefix P hprime hdisjoint q (hcop q hq)]
      apply mul_le_mul_of_nonneg_left _ (hweight q hq)
      calc
        _ ≤ ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            ‖(-1 : ℂ) ^ I.card *
              (positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            E q * (1 / (q : ℝ)) * V := by
          apply sum_le_sum
          intro I hI
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          apply (hbound q hq I hI).trans
          have hv := complement_product_le (fun j => primeHarmonicMass (P j)) hmass I
          dsimp only [V]
          calc
            _ = (E q * (1 / (q : ℝ))) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
        _ ≤ (2 : ℝ) ^ J * (E q * (1 / (q : ℝ)) * V) := by
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeTupleBins
namespace OAI

/-! A partial-centering bin saves L^(-21/20) with exactly the reciprocal
mass of the retained supply products. The scale exponent is absolute. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma indexed_rescaled_prefix_bound {α : Type*} [Fintype α]
    (u : α → ℕ) (F : α → ℕ → ℂ) (X : ℕ) (E : ℝ)
    (hX : 0 < X) (hE : 0 ≤ E) (hu : ∀ a, 0 < u a)
    (hF : ∀ a, ‖positivePrefix (F a) (X / u a) / ((X / u a : ℕ) : ℂ)‖ ≤ E) :
    ‖(∑ a, positivePrefix (F a) (X / u a)) / (X : ℂ)‖ ≤
      E * ∑ a, 1 / (u a : ℝ) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  rw [sum_div]
  calc
    _ ≤ ∑ a, ‖positivePrefix (F a) (X / u a) / (X : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ a, E * (1 / (u a : ℝ)) := by
      apply sum_le_sum
      intro a _
      have hup : (0 : ℝ) < u a := by exact_mod_cast hu a
      have hb := prefix_norm_of_average_bound (F a) (X / u a) E (hF a)
      have hratio : ((X / u a : ℕ) : ℝ) ≤ (X : ℝ) / u a := Nat.cast_div_le
      have hp := hb.trans (mul_le_mul_of_nonneg_right hratio hE)
      rw [norm_div, Complex.norm_natCast]
      calc
        _ ≤ (((X : ℝ) / u a) * E) / X := div_le_div_of_nonneg_right hp hXp.le
        _ = _ := by field_simp
    _ = _ := by rw [mul_sum]

lemma retained_tuple_reciprocal_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) :
    (∑ y : (j : {j // j ∉ I}) → P j,
      1 / ((q : ℝ) * ∏ j, ((y j).val : ℝ))) =
      (1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by
  calc
    _ = (1 / (q : ℝ)) *
        ∑ y : (j : {j // j ∉ I}) → P j, ∏ j, ((y j).val : ℝ)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      simp only [one_div, mul_inv_rev, prod_inv_distrib]
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum (fun j : {j // j ∉ I} =>
        fun p : P j => (p.val : ℝ)⁻¹)).symm


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialBounds
namespace OAI

/-! Exact reciprocal normalization of the complex partial-tuple profiles. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma complexRoughProfile_average (F G : ℕ → ℂ) (Z : Finset ℕ) (h Y : ℕ) :
    positivePrefix (complexRoughProfile F G Z h) Y / (Y : ℂ) =
      weightedRoughShiftAverage F G Z (fun _ => 1) h Y := by
  have he : complexRoughProfile F G Z h = weightedRoughShiftProfile F G Z (fun _ => 1) h := by
    funext n
    simp only [weightedRoughShiftProfile, complexRoughProfile, one_div]
  rw [weightedRoughShiftAverage, he]

lemma complex_partial_tuple_prefix_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h X : ℕ)
    (hX : 0 < X) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ y : (j : {j // j ∉ I}) → P j,
      ‖weightedRoughShiftAverage
        (fun n => F ((q * ∏ j, (y j).val) * n))
        (fun n => G ((q * ∏ j, (y j).val) * n))
        ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q))
        (fun _ => 1) h (X / (q * ∏ j, (y j).val))‖ ≤ E) :
    ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)‖ ≤
      E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  rw [tupleComplexPartialProfile_prefix P hprime hdisjoint I q hq]
  have he := indexed_rescaled_prefix_bound
    (fun y : (j : {j // j ∉ I}) → P j => q * ∏ j, (y j).val)
    (fun y => complexRoughProfile
      (fun n => F ((q * ∏ j, (y j).val) * n))
      (fun n => G ((q * ∏ j, (y j).val) * n))
      ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
    X E hX hE
    (fun y => Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos))
    (fun y => by rw [complexRoughProfile_average]; exact hb y)
  simpa only [Nat.cast_mul, Nat.cast_prod, retained_tuple_reciprocal_sum] using he

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



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalTupleSmooth
namespace OAI

/-! Uniformly bounded smooth-dilation cost for every retained subtuple of
the actual canonical prime bands. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma retained_tuple_factor_subset {J : ℕ} (P : Fin J → Finset ℕ)
    (hp : ∀ i, ∀ p ∈ P i, p.Prime) (I : Finset (Fin J))
    (y : (i : {i // i ∉ I}) → P i) :
    (∏ i, (y i).val).primeFactors ⊆ univ.image (fun i => (y i).val) := by
  intro p hp'
  have hpprime := Nat.prime_of_mem_primeFactors hp'
  have hdiv := Nat.dvd_of_mem_primeFactors hp'
  obtain ⟨i, _, hi⟩ := (hpprime.prime.dvd_finsetProd_iff (fun i => (y i).val)).mp hdiv
  have he : p = (y i).val := (Nat.prime_dvd_prime_iff_eq hpprime
    (hp i _ (y i).property)).mp hi
  exact mem_image.mpr ⟨i, mem_univ _, he.symm⟩

lemma retained_tuple_factor_card {J : ℕ} (P : Fin J → Finset ℕ)
    (hp : ∀ i, ∀ p ∈ P i, p.Prime) (I : Finset (Fin J))
    (y : (i : {i // i ∉ I}) → P i) : (∏ i, (y i).val).primeFactors.card ≤ J := by
  calc
    _ ≤ (univ.image (fun i => (y i).val)).card := card_le_card (retained_tuple_factor_subset P hp I y)
    _ ≤ (univ : Finset {i : Fin J // i ∉ I}).card := card_image_le
    _ ≤ J := by simpa only [card_univ, Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin J => i ∉ I)

theorem eventually_canonical_retained_smooth_cost (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ∀ I : Finset (Fin J), ∀ y : (i : {i // i ∉ I}) → P i,
        smoothReciprocalProduct (∏ i, (y i).val).primeFactors (1 / 2 : ℝ) ≤ 2 := by
  filter_upwards [eventually_canonical_smooth_half_cost, eventually_ge_atTop (1 : ℝ)] with L hcost hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime E A W J
  intro I y
  apply hcost
  · exact (show ((∏ i, (y i).val).primeFactors.card : ℝ) ≤ J by
      exact_mod_cast retained_tuple_factor_card P hp I y).trans
        ((primeSupplyCount_le_log W L hW hL).trans
          ((Real.log_le_sub_one_of_pos hLp).trans (by linarith)))
  · intro p hpmem
    obtain ⟨i, _, hi⟩ := mem_image.mp (retained_tuple_factor_subset P hp I y hpmem)
    subst p
    exact (centeredPrimeSupply_global_bounds (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW) i.val.isLt
      (primeSupplyScale_endpoint W L (by linarith) hL) (y i).property).1.le

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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexBinWindows
namespace OAI

/-! Enlarging a closed-low logarithmic bin by one bin on its left gives
the strict-low convention in the rough-shift theorem. -/

namespace TwoPointCorrelations



lemma enlarged_partial_bin_window (q t z : ℕ) (hq : 0 < q) (ht : 0 < t) (hz : 0 < z)
    (η : ℝ) (hη : 0 < η) (j : ℤ)
    (hbin : actualPaddingBin η (Real.log (t * z : ℕ)) j q) :
    enlargedBinStart η j (q * t) < (z : ℝ) ∧
      (z : ℝ) ≤ Real.exp (2 * η) * enlargedBinStart η j (q * t) := by
  have hw := partial_bin_window q t z hq ht hz η j hbin
  have hup : (0 : ℝ) < (q * t : ℕ) := by exact_mod_cast Nat.mul_pos hq ht
  have hl : enlargedBinStart η j (q * t) <
      Real.exp ((j : ℝ) * η) / (q * t : ℕ) := by
    apply div_lt_div_of_pos_right _ hup
    exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨hl.trans_le hw.1, hw.2.trans_eq ?_⟩
  unfold enlargedBinStart
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma enlargedBinStart_upper (η : ℝ) (hη : 0 ≤ η) (j : ℤ) (u : ℕ) (hu : 0 < u)
    (U : ℝ) (hU : Real.exp ((j : ℝ) * η) ≤ U) : enlargedBinStart η j u ≤ U := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  calc
    _ ≤ Real.exp (((j : ℝ) - 1) * η) :=
      div_le_self (Real.exp_pos _).le hu1
    _ ≤ Real.exp ((j : ℝ) * η) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ U := hU

lemma rough_bin_forces_start_lower {H M τ z : ℝ} (hτ : 0 < τ)
    (hz : H ≤ z) (hupper : z ≤ τ * M) : H / τ ≤ M := by
  apply (div_le_iff₀ hτ).mpr
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativePartialCentering
namespace OAI

/-! Direct dilation gives qualitative centering for the actual complex
partial-tuple terms. The eventual cutoff is allowed to depend on the fixed
finite prime families, while the analytic constant is independent of them. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem qualitative_complex_partial_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {F G : ℕ → ℂ}
    (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (J : ℕ) (P : Fin J → Finset ℕ),
      (∀ i, ∀ p ∈ P i, p.Prime) →
      (∀ i j, j ≠ i → Disjoint (P i) (P j)) →
      (∀ i, ∀ p ∈ P i, Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ (p : ℝ)) →
      ∀ (I : Finset (Fin J)), I.Nonempty → ∀ q : ℕ, 0 < q →
      (∀ y : (i : {i // i ∉ I}) → P i,
        smoothReciprocalProduct (∏ i, (y i).val).primeFactors (1 / 2 : ℝ) ≤ 2) →
      ∀ (η : ℝ), 0 < η → Real.exp (2 * η) < 2 → ∀ j : ℤ,
      Real.exp ((j : ℝ) * η) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ X : ℕ in atTop, ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)‖ ≤
        (2 * C * B ^ (-11 / 10 : ℝ) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) *
        ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
  obtain ⟨C, hC, hb⟩ := qualitative_dilated_fixed_factors hM hMRT hFm hGm hF hG hnp h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with B hb hB
  intro J P hp hd hlarge I hI q hq hcost η hη hηtwo j hj
  let τ := Real.exp (2 * η)
  have hτ : 1 < τ := Real.one_lt_exp_iff.mpr (by positivity)
  have hτp : 0 < τ := Real.exp_pos _
  let E := 2 * C * B ^ (-11 / 10 : ℝ) *
    smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have hE : 0 ≤ E := mul_nonneg (by positivity)
    (smoothReciprocalProduct_nonneg _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
      _ (by norm_num))
  have hall : ∀ᶠ X : ℕ in atTop, ∀ y : (i : {i // i ∉ I}) → P i,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖weightedRoughShiftAverage
        (fun n => F ((q * ∏ i, (y i).val) * n))
        (fun n => G ((q * ∏ i, (y i).val) * n))
        ((primeTupleSlice P I).filter (fun z => eligible ((∏ i, (y i).val) * z) q))
        (fun _ => 1) h (X / (q * ∏ i, (y i).val))‖ ≤ E := by
    apply Filter.eventually_all.mpr
    intro y
    let t : ℕ := ∏ i, (y i).val
    let u := q * t
    let M := enlargedBinStart η j u
    have ht : 0 < t := prod_pos fun i _ => (hp i _ (y i).property).pos
    have hu : 0 < u := Nat.mul_pos hq ht
    have hMupper : M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) :=
      enlargedBinStart_upper η hη.le j u hu _ hj
    by_cases hMlower : Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M
    · have hwin := (tendsto_nat_div_atTop u hu).eventually
        (hb u hu M τ hτ hηtwo hMlower hMupper)
      filter_upwards [hwin] with X hX
      intro eligible hel
      have hZ : ∀ z ∈ (primeTupleSlice P I).filter (fun z => eligible (t * z) q),
          M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
          HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z := by
        intro z hz
        obtain ⟨hz, he⟩ := mem_filter.mp hz
        have hzpos := primeTupleSlice_pos P I hp hz
        have hw := enlarged_partial_bin_window q t z hq ht hzpos η hη j (hel _ _ he)
        refine ⟨hw.1, hw.2, ?_⟩
        intro p hprime hsmall hdiv
        obtain ⟨i, _, hi⟩ := prime_dvd_primeTupleSlice P I hp hz hprime hdiv
        exact (not_lt_of_ge (hlarge i p hi)) hsmall
      apply (hX _ hZ).trans
      have hc := mul_le_mul_of_nonneg_left (dilated_tuple_smooth_cost q t hq ht (hcost y))
        (show 0 ≤ C * B ^ (-11 / 10 : ℝ) by positivity)
      exact hc.trans_eq (by dsimp only [E]; ring)
    · refine Filter.Eventually.of_forall ?_
      intro X eligible hel
      have hempty : (primeTupleSlice P I).filter (fun z => eligible (t * z) q) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hz, he⟩ := mem_filter.mp hz
        have hw := enlarged_partial_bin_window q t z hq ht
          (primeTupleSlice_pos P I hp hz) η hη j (hel _ _ he)
        exact hMlower (rough_bin_forces_start_lower hτp
          (primeTupleSlice_lower P I hp _ hlarge hI hz) hw.2)
      change ‖weightedRoughShiftAverage (fun n => F (u * n)) (fun n => G (u * n))
        ((primeTupleSlice P I).filter (fun z => eligible (t * z) q)) (fun _ => 1) h (X / u)‖ ≤ E
      rw [hempty]
      simpa only [weightedRoughShiftAverage, weightedRoughShiftProfile, sum_empty,
        positivePrefix, sum_const_zero, zero_div, norm_zero] using hE
  filter_upwards [hall, eventually_ge_atTop 1] with X hX hXpos
  intro eligible hel
  exact complex_partial_tuple_prefix_bound P hp hd I q hq eligible F G h X
    (by omega) E hE (fun y => hX y eligible hel)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexFinalScale
namespace OAI

/-! The complex retained graph has an exponentially vanishing normalized contribution. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma exp_neg_nat_exp_lt_two (J : ℕ) (hJ : 1 ≤ J) :
    Real.exp (Real.exp (-(J : ℝ))) < 2 := by
  have hj : Real.exp (-(J : ℝ)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    exact_mod_cast (show -(J : ℤ) ≤ -1 by omega)
  have hlog : Real.exp (-(J : ℝ)) < Real.log 2 := by
    have := Real.log_two_gt_d9
    have := Real.exp_neg_one_lt_half
    linarith
  calc
    _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
    _ = _ := Real.exp_log (by norm_num)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeCenteringRate
namespace OAI

/-! The small loss from summing every logarithmic bin still leaves a
negative power in the canonical qualitative centering estimate. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma primeSupplyCount_small_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L / 200 := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg hJ (show 0 ≤ 6 * W - 1 by linarith)
  nlinarith

lemma exp_double_neg_nat_lt_two (J : ℕ) (hJ : 2 ≤ J) :
    Real.exp (2 * Real.exp (-(J : ℝ))) < 2 := by
  have hj : Real.exp (-(J : ℝ)) ≤ Real.exp (-2) :=
    Real.exp_le_exp.mpr (by exact_mod_cast (show -(J : ℤ) ≤ -2 by omega))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have harg : 2 * Real.exp (-(J : ℝ)) ≤ Real.exp (-1) := by
    calc
      _ ≤ 2 * Real.exp (-2) := mul_le_mul_of_nonneg_left hj (by norm_num)
      _ ≤ Real.exp 1 * Real.exp (-2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have hend : Real.exp (Real.exp (-1)) < 2 := by
    simpa only [Nat.cast_one] using exp_neg_nat_exp_lt_two 1 (by decide)
  exact (Real.exp_le_exp.mpr harg).trans_lt hend

lemma eventually_primeSupplyCount_two (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (2400 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 2400 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : 0 ≤ 2400 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

lemma canonical_centering_bin_count_rate (L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    ((paddingBinIndices L (Real.exp (-(J : ℝ)))).card : ℝ) *
      (2 : ℝ) ^ J * canonicalRoughParameter L ^ (-11 / 10 : ℝ) ≤
        101 * L ^ (-3 / 40 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hβ : 0 ≤ canonicalRoughParameter L ^ (-11 / 10 : ℝ) :=
    Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _
  have hη : Real.exp (-(J : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hc := paddingBinIndices_card_linear L (Real.exp (-(J : ℝ))) hL (Real.exp_pos _) hη
  have he : Real.exp (J : ℝ) ≤ L ^ (1 / 200 : ℝ) := by
    rw [Real.rpow_def_of_pos hLp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hrate := canonical_centering_rate_bound L hL J hJ
  calc
    _ ≤ (101 * L * Real.exp (J : ℝ)) * (2 : ℝ) ^ J *
        canonicalRoughParameter L ^ (-11 / 10 : ℝ) := by
      have hc' : ((paddingBinIndices L (Real.exp (-(J : ℝ)))).card : ℝ) ≤
          101 * L * Real.exp (J : ℝ) := by
        simpa only [Real.exp_neg, div_eq_mul_inv, inv_inv] using hc
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (by positivity))
        hβ
    _ = 101 * Real.exp (J : ℝ) *
        ((2 : ℝ) ^ J * L * canonicalRoughParameter L ^ (-11 / 10 : ℝ)) := by ring
    _ ≤ 101 * L ^ (1 / 200 : ℝ) * L ^ (-2 / 25 : ℝ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hrate
        (mul_nonneg (mul_nonneg (by positivity) hLp.le) hβ) (by positivity)
    _ = 101 * L ^ (-3 / 40 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hLp]
      norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeCanonicalCentering
namespace OAI

/-! The actual canonical nonraw complex bins: the cost of every padding
dilation is summed against its exact reciprocal law. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma nonrawComplexBin_real_denominator {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ)
    (T : ℝ) (hT : 1 ≤ T) :
    ‖nonrawComplexBin P R eligible F G h T‖ ≤
      ‖∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
          positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) /
          (⌊T⌋₊ : ℂ))‖ := by
  let A : ℕ → ℂ := fun q => (actualPaddingCoefficient q : ℂ) *
    (positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
      positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊)
  have he (c : ℂ) : (∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
      ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
        positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) / c)) =
      (∑ q ∈ R, A q) / c := by simp only [A, mul_div_assoc, sum_div]
  have hN : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hT
  rw [nonrawComplexBin, he, he, norm_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T), Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hN (Nat.floor_le (by linarith))

theorem qualitative_canonical_nonraw_bin (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTShortExponentialInput)
    {F G : ℕ → ℂ} (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      ∀ R : Finset ℕ, R ⊆ retainedPrimeDivisors Q →
      ∀ η : ℝ, 0 < η → Real.exp (2 * η) < 2 →
      ∀ᶠ T : ℝ in atTop, ∀ j ∈ paddingBinIndices L η,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖nonrawComplexBin P R eligible F G h T‖ ≤
        C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J *
          paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_complex_partial_bin hM hMRT hFm hGm hF hG hnp
    h hh 100 (by norm_num)
  refine ⟨2 * C * paddingSmoothConstant,
    mul_pos (mul_pos (by norm_num) hC) paddingSmoothConstant_pos, ?_⟩
  filter_upwards [canonicalRoughParameter_tendsto.eventually hrough,
    eventually_canonical_retained_smooth_cost E W hW,
    hP.eventually_actual_pool_masses E W hW, eventually_ge_atTop (1 : ℝ)] with
    L hrough hcost hmass hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let B := canonicalRoughParameter L
  let Is := (univ : Finset (Fin J)).powerset.filter Finset.Nonempty
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 < B := Real.rpow_pos_of_pos hLp _
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i j, j ≠ i → Disjoint (P i) (P j) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW)
  have hlarge : ∀ i, ∀ p ∈ P i, Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ (p : ℝ) := by
    intro i p hip
    rw [canonicalRoughParameter_prime_endpoint L hLp.le]
    exact (centeredPrimeSupply_global_bounds (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW)
      i.isLt (primeSupplyScale_endpoint W L (by linarith) hL) hip).1.le
  have hQ : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  intro R hR
  have hRpos : ∀ q ∈ R, 0 < q := fun q hq => retainedPrimeDivisor_pos Q hQ (hR hq)
  have hcop : ∀ q ∈ R, ∀ i, ∀ p ∈ P i, q.Coprime p := by
    intro q hq i p hip
    exact paddingPrimeDivisor_coprime_centered E _ W L J (hR hq) i hip
  have hm : ∀ i, 1 ≤ primeHarmonicMass (P i) := fun i => (hmass.2.1 i).1
  intro η hη hηtwo
  let bins := paddingBinIndices L η
  let e : ℕ → ℝ := fun q => 2 * C * B ^ (-11 / 10 : ℝ) *
    smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have he : ∀ q ∈ R, 0 ≤ e q := by
    intro q _
    exact mul_nonneg (by positivity) (smoothReciprocalProduct_nonneg _
      (fun _ hp => Nat.prime_of_mem_primeFactors hp) _ (by norm_num))
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j ∈ bins, ∀ q ∈ R, ∀ I ∈ Is,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) N / (N : ℂ)‖ ≤
        e q * ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
    apply (eventually_all_finset bins).mpr
    intro j hj
    apply (eventually_all_finset R).mpr
    intro q hq
    apply (eventually_all_finset Is).mpr
    intro I hI
    have hjbound := (mem_paddingBinIndices_iff L η j hη).mp hj
    have hupper : Real.exp ((j : ℝ) * η) ≤ Real.exp (100 * B ^ (2 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      exact hjbound.2.trans (mul_le_mul_of_nonneg_left (canonicalRoughParameter_square_ge L hL)
        (by norm_num))
    exact hrough J P hp hd hlarge I (mem_filter.mp hI).2 q (hRpos q hq)
      (hcost I) η hη hηtwo j hupper
  have hsum : (∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ) * e q) ≤
      (2 * C * B ^ (-11 / 10 : ℝ)) *
        (paddingTiltNormalizer Q * paddingSmoothConstant) := by
    calc
      _ = (2 * C * B ^ (-11 / 10 : ℝ)) *
          ∑ q ∈ R, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
            smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        dsimp only [e, actualPaddingCoefficient]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply le_trans _ (padding_smooth_half_sum_le Q hQ)
        exact sum_le_sum_of_subset_of_nonneg hR (fun q _ _ => mul_nonneg (by positivity)
          (smoothReciprocalProduct_nonneg _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
            _ (by norm_num)))
  have hnat : ∀ᶠ N : ℕ in atTop, ∀ j ∈ bins, ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) N -
          positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) N) / (N : ℂ))‖ ≤
        (2 * C * paddingSmoothConstant) * B ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J *
          paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
    filter_upwards [hall] with N hN
    intro j hj eligible hel
    have hb := complex_partial_centering_sum_bound P hp hd hm R actualPaddingCoefficient
      (fun q _ => by unfold actualPaddingCoefficient; positivity) hcop eligible F G h N e he
      (fun q hq I hI => hN j hj q hq I hI eligible hel)
    apply hb.trans
    calc
      _ ≤ (2 : ℝ) ^ J * ((2 * C * B ^ (-11 / 10 : ℝ)) *
          (paddingTiltNormalizer Q * paddingSmoothConstant)) * ∏ i, primeHarmonicMass (P i) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
          (prod_nonneg (fun i _ => zero_le_one.trans (hm i)))
      _ = _ := by ring
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually hnat,
    eventually_ge_atTop (1 : ℝ)] with T hT hTone
  intro j hj eligible hel
  exact (nonrawComplexBin_real_denominator P R eligible F G h T hTone).trans
    (hT j hj eligible hel)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeCenteringTotal
namespace OAI

/-! Sum every actual logarithmic bin, retaining arbitrary unit-disk phase
weights and the exact padding and tuple normalizers. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem qualitative_canonical_nonraw_total_oai (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTShortExponentialInput)
    {F G : ℕ → ℂ} (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      ∀ R : Finset ℕ, R ⊆ retainedPrimeDivisors Q →
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ᶠ X : ℝ in atTop, ∀ (eligible : ℤ → ℕ → ℕ → Prop) (v : ℤ → ℂ),
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      ‖∑ j ∈ bins, v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ ≤
        C * L ^ (-3 / 40 : ℝ) * paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hb⟩ := qualitative_canonical_nonraw_bin hP hM hMRT hFm hGm hF hG hnp
    h hh E W hW
  refine ⟨101 * C, by positivity, ?_⟩
  filter_upwards [hb, eventually_primeSupplyCount_two W (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L hb hJ hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  intro R hR
  let η := Real.exp (-(J : ℝ))
  let bins := paddingBinIndices L η
  let V := paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i)
  have hη : 0 < η := Real.exp_pos _
  have hV : 0 ≤ V := mul_nonneg (paddingTiltNormalizer_pos Q).le
    (prod_nonneg (fun i _ => by unfold primeHarmonicMass; positivity))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hb R hR η hη (exp_double_neg_nat_lt_two J hJ))
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with X hX
  intro eligible v hel hv
  have hXp : 0 ≤ X := by linarith [le_max_right T₀ (1 : ℝ)]
  have hterm (j : ℤ) (hj : j ∈ bins) :
      ‖v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ ≤
      C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J * V := by
    have hgeom := (mem_paddingBinIndices_iff L η j hη).mp hj
    have ht : X ≤ X * Real.exp ((j : ℝ) * η) := by
      have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast hgeom.1
      exact le_mul_of_one_le_right hXp (Real.one_le_exp (mul_nonneg hj0 hη.le))
    have hb' := hT₀ (X * Real.exp ((j : ℝ) * η))
      ((le_max_left T₀ (1 : ℝ)).trans (hX.trans ht)) j hj (eligible j) (hel j hj)
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖nonrawComplexBin P R (eligible j) F G h
          (X * Real.exp ((j : ℝ) * η))‖ :=
        mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul, V, mul_assoc] using hb'
  have hcount := canonical_centering_bin_count_rate L J hL (primeSupplyCount_small_log W L hW hL)
  calc
    _ ≤ ∑ j ∈ bins, ‖v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ bins, C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J * V :=
      sum_le_sum hterm
    _ = C * (((bins.card : ℝ) * (2 : ℝ) ^ J *
        canonicalRoughParameter L ^ (-11 / 10 : ℝ))) * V := by
      rw [sum_const, nsmul_eq_mul]
      ring
    _ ≤ C * (101 * L ^ (-3 / 40 : ℝ)) * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hC.le) hV
    _ = _ := by dsimp only [V]; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.qualitative_canonical_nonraw_total_oai := @OAI.TwoPointCorrelations.qualitative_canonical_nonraw_total_oai
