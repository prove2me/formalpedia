-- Prove2me | solution 1 for OAI.OrdinaryTwoPointCorrelations.affine_corrected_elliott
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:54:50.048105+00:00
-- url     : https://prove2.me/submissions/a904157a-a803-4578-8fcc-07dcba46f31d

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_sparse_kernel
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_short_exponential
import Theorems.Thm_OAI_TwoPointCorrelations_affineCorrectedElliott_of_mrt
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_weak_hurwitz_growth

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
namespace OAI

/-! Partial assignments and the consistent terms used in the canonical
decision tree of a DNF. Each term contains at most one literal per variable. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PartialAssignment





@[simp] lemma assign_empty {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) :
    ρ.assign ∅ x = ρ := by funext i; simp [assign]





end PartialAssignment


namespace CubeTerm










end CubeTerm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPacking
namespace OAI

/-! Elementary interval packing for separated phase representatives. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_interval_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ x i ∧ x i < b + δ)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS, hix⟩ := mem_filter.mp hi
  obtain ⟨hjS, hjx⟩ := mem_filter.mp hj
  by_contra hij
  have hh := hsep i hiS j hjS hij
  have habs : |x i - x j| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma minor_arc_absolute_band_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b + δ)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b + δ)
  have hP : P.card ≤ 1 := minor_arc_interval_packing S x δ b hsep
  have hQ : Q.card ≤ 1 := by
    apply minor_arc_interval_packing S (fun i => -x i) δ b
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS, hix⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · apply mem_union_left
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hix⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hix⟩
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareRows
namespace OAI

/-! Summable quadratic-gap bounds for the MRT Dirichlet mean-value estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators


lemma mrt_quadratic_gap_sum {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ 2 * R + 1 := by
  let K := Nat.ceil R
  let M := max K N
  have hK : 0 < K := Nat.ceil_pos.mpr hR
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKR : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKM : K ≤ M := le_max_left _ _
  have hsplit : Ioc 0 M = Ioc 0 K ∪ Ioc K M := by
    ext k
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 K) (Ioc K M) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hnear : (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Ioc 0 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((k : ℝ) / R)])
      _ = _ := by simp
  have hfar : (∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ R := by
    calc
      _ ≤ ∑ k ∈ Ioc K M, R ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (hK.trans (mem_Ioc.mp hk).1)
        calc
          _ ≤ (((k : ℝ) / R) ^ 2)⁻¹ := by
            apply inv_anti₀ (sq_pos_of_pos (div_pos hk0 hR))
            linarith
          _ = _ := by field_simp
      _ = R ^ 2 * ∑ k ∈ Ioc K M, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ R ^ 2 * ((K : ℝ)⁻¹ - (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' hKM)
          (sq_nonneg R)
      _ ≤ R ^ 2 * (K : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg M))
      _ ≤ R := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]
        nlinarith
  calc
    _ ≤ ∑ k ∈ Ioc 0 M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (le_max_right _ _)⟩
      · intro k _ _
        positivity
    _ = (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) +
        ∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by rw [hsplit, sum_union hd]
    _ ≤ (K : ℝ) + R := add_le_add hnear hfar
    _ ≤ 2 * R + 1 := by linarith




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.BigOperators _root_.ComplexConjugate


lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedMeanSquare
namespace OAI

/-! Weighted Schur estimates for the prime-supported polynomials in Halász's
mean-value argument.  The weight occurs only once in the squared coefficient
sum, so a bound for the weighted frequency rows saves the extra logarithm
that an unrestricted integer mean-value theorem would lose. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators _root_.Classical

lemma halasz_weighted_symmetric_row_bound {ι : Type*} (S : Finset ι)
    (K : ι → ι → ℝ) (w v : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, w j * K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, (v i * w i) * (v j * w j) * K i j) ≤
      C * ∑ i ∈ S, (v i) ^ 2 * w i := by
  have he : (∑ i ∈ S, ∑ j ∈ S,
      ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j)) =
      ∑ i ∈ S, (v i) ^ 2 * w i * ∑ j ∈ S, w j * K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S)
      (f := fun i j => (v j) ^ 2 / 2 * (w i * w j * K i j))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsymm j hj i hi]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hv : v i * v j ≤ ((v i) ^ 2 + (v j) ^ 2) / 2 := by
        nlinarith [sq_nonneg (v i - v j)]
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hv
        (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hK i hi j hj)) using 1; ring
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * w i * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (mul_nonneg (sq_nonneg _) (hw i hi))
    _ = _ := by rw [← sum_mul, mul_comm]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseGram
namespace OAI

/-! Finite duality for sparse Dirichlet-polynomial samples.  The analytic
input is an explicit Gram-row sum, with no density-to-energy substitution. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_gram_synthesis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    {B : ℝ} (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    ‖∑ i ∈ S, a i • v i‖^2 ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
  calc
    _ = (inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)‖ := re_le_norm _
    _ = ‖∑ i ∈ S, ∑ j ∈ S, conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (‖a i‖ * 1) * (‖a j‖ * 1) * ‖inner ℂ (v i) (v j)‖ := by
      simp only [norm_mul, norm_conj, mul_one]
    _ ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
      simpa only [mul_one] using halasz_weighted_symmetric_row_bound S
        (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ => 1) (fun i => ‖a i‖) B
        (fun _ _ => by norm_num) (fun _ _ _ _ => norm_nonneg _)
        (fun i _ j _ => norm_inner_symm _ _) (by simpa only [one_mul] using hrow)

/-- Finite Bessel inequality with an absolute Gram-row bound. -/
theorem mrt_gram_analysis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (u : E)
    {B : ℝ} (hB : 0 ≤ B) (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    (∑ i ∈ S, ‖inner ℂ (v i) u‖^2) ≤ B * ‖u‖^2 := by
  let b := fun i => inner ℂ (v i) u
  let z := ∑ i ∈ S, b i • v i
  let A := ∑ i ∈ S, ‖b i‖^2
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : inner ℂ z u = (A : ℂ) := by
    dsimp only [z, A]
    rw [sum_inner]
    push_cast
    apply sum_congr rfl
    intro i _
    rw [inner_smul_left]
    exact conj_mul' (b i)
  have hc : A ≤ ‖z‖ * ‖u‖ := by
    calc
      A = ‖inner ℂ z u‖ := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
      _ ≤ _ := norm_inner_le_norm _ _
  have hz2 : ‖z‖^2 ≤ B*A := mrt_gram_synthesis S v b hrow
  have hc2 : A^2 ≤ ‖z‖^2 * ‖u‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hc 2
  have hprod := mul_le_mul_of_nonneg_right hz2 (sq_nonneg ‖u‖)
  by_cases hAz : A = 0
  · change A ≤ B * ‖u‖^2
    rw [hAz]
    exact mul_nonneg hB (sq_nonneg _)
  · change A ≤ B * ‖u‖^2
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    apply (mul_le_mul_iff_right₀ hApos).mp
    calc
      A * A = A^2 := by ring
      _ ≤ B * A * ‖u‖^2 := hc2.trans hprod
      _ = A * (B * ‖u‖^2) := by ring

/-- The Gram kernel is evaluated on the actual coefficient matrix. -/
theorem mrt_finite_matrix_gram {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (A : ι → κ → ℂ) (a : κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ K, A i n * conj (A j n)‖ ≤ B) :
    (∑ i ∈ S, ‖∑ n ∈ K, A i n * a n‖^2) ≤ B * ∑ n ∈ K, ‖a n‖^2 := by
  let v : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 (fun n => conj (A i n))
  let u : EuclideanSpace ℂ K := WithLp.toLp 2 (fun n => a n)
  have hinner (i j : ι) : inner ℂ (v i) (v j) = ∑ n ∈ K, A i n * conj (A j n) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * conj (A j n)) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * conj (A j n))
  have heval (i : ι) : inner ℂ (v i) u = ∑ n ∈ K, A i n * a n := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * a n) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * a n)
  have hnorm : ‖u‖^2 = ∑ n ∈ K, ‖a n‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ n : K, ‖a n‖^2) = _
    exact sum_coe_sort K (fun n => ‖a n‖^2)
  have hr : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B := by
    simpa only [hinner] using hrow
  simpa only [heval, hnorm] using mrt_gram_analysis S v u hB hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparsePolynomial
namespace OAI

/-! The sparse Gram bound for the actual finite exponential polynomial.
The optional nonnegative weight permits a smooth integer majorant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate


theorem mrt_sparse_weighted_polynomial_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ S, ∑ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤ B) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      B * ∑ n ∈ K, w n*‖a n‖^2 := by
  let A := fun t n => (Real.sqrt (w n):ℂ)*Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I)
  let b := fun n => (Real.sqrt (w n):ℂ)*a n
  have hs (n : ι) (hn : n ∈ K) : (Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ) = w n := by
    exact_mod_cast Real.mul_self_sqrt (hw n hn)
  have hp (t s : ℝ) : (∑ n ∈ K, A t n * conj (A s n)) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s) := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, mrtExponentialPolynomial]
    rw [map_mul, conj_ofReal]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ)) *
          (Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) *
            conj (Complex.exp (((freq n*s:ℝ):ℂ)*Complex.I))) := by ring
      _ = _ := by
        rw [hs n hn, mrt_phase_pair]
        rw [show freq n*t-freq n*s = freq n*(t-s) by ring]
  have he (t : ℝ) : (∑ n ∈ K, A t n*b n) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, b, mrtExponentialPolynomial]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ))*a n*
          Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) := by ring
      _ = _ := by rw [hs n hn]
  have hm : (∑ n ∈ K, ‖b n‖^2) = ∑ n ∈ K, w n*‖a n‖^2 := by
    apply sum_congr rfl
    intro n hn
    simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n hn)]
  have hr : ∀ t ∈ S, ∑ s ∈ S, ‖∑ n ∈ K, A t n*conj (A s n)‖ ≤ B := by
    simpa only [hp] using hrow
  simpa only [he, hm] using mrt_finite_matrix_gram S K A b hB hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseRows
namespace OAI

/-! Summable Gram rows on one-separated heights.  A square-root frequency
remainder costs only the number of sampled heights, not the full interval. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_separated_cauchy_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) :
    (∑ i ∈ S, 1/(1+(x i)^2)) ≤ 8 := by
  let b := fun i => ⌊|x i|⌋₊
  let L := S.sup b
  let F := fun j => S.filter (fun i => b i = j)
  have hindex (i : ι) (hi : i ∈ S) : b i ≤ L := le_sup hi
  have hband (j : ℕ) (i : ι) (hi : i ∈ F j) :
      (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1 := by
    have he := (mem_filter.mp hi).2
    have hl := Nat.floor_le (abs_nonneg (x i))
    have hu := Nat.lt_floor_add_one |x i|
    change (b i:ℝ) ≤ |x i| at hl
    change |x i| < (b i:ℝ)+1 at hu
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  have hcard (j : ℕ) : (F j).card ≤ 2 := by
    apply (card_le_card (s := F j) (t := S.filter
      (fun i => (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1)) ?_).trans
      (minor_arc_absolute_band_packing S x 1 j hsep)
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hband j i hi⟩
  have hpiece (j : ℕ) : (∑ i ∈ F j, 1/(1+(x i)^2)) ≤ 2/(1+(j:ℝ)^2) := by
    calc
      _ ≤ ∑ _i ∈ F j, 1/(1+(j:ℝ)^2) := by
        apply sum_le_sum
        intro i hi
        have hs := pow_le_pow_left₀ (Nat.cast_nonneg j) (hband j i hi).1 2
        rw [sq_abs] at hs
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = ((F j).card:ℝ)/(1+(j:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
  have hpartition : (∑ i ∈ S, 1/(1+(x i)^2)) =
      ∑ j ∈ Icc 0 L, ∑ i ∈ F j, 1/(1+(x i)^2) := by
    symm
    exact sum_fiberwise_of_maps_to
      (fun i hi => mem_Icc.mpr ⟨Nat.zero_le _, hindex i hi⟩) _
  have hI : Icc 0 L = insert 0 (Ioc 0 L) := by
    ext j
    simp only [mem_Icc, mem_insert, mem_Ioc]
    omega
  have htail := mrt_quadratic_gap_sum (by norm_num : (0:ℝ)<1) L
  simp only [div_one] at htail
  rw [hpartition]
  apply (sum_le_sum (fun j _ => hpiece j)).trans
  rw [hI, sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_pow (by omega : 2≠0), add_zero, div_one]
  have he : (∑ j ∈ Ioc 0 L, 2/(1+(j:ℝ)^2)) =
      2 * ∑ j ∈ Ioc 0 L, (1+(j:ℝ)^2)⁻¹ := by
    simp only [div_eq_mul_inv, mul_sum]
  rw [he]
  linarith

theorem mrt_sparse_weighted_row_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ K, w n*‖a n‖^2 := by
  apply mrt_sparse_weighted_polynomial_energy K w freq a hw S (by positivity)
  intro t ht
  have hc : (∑ s ∈ S, 1/(1+(t-s)^2)) ≤ 8 := by
    apply mrt_separated_cauchy_sum S (fun s => t-s)
    intro s hs u hu hsu
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep s hs u hu hsu
  calc
    _ ≤ ∑ s ∈ S, (A/(1+(t-s)^2)+D) := sum_le_sum (fun s hs => hkernel t ht s hs)
    _ = A*(∑ s ∈ S, 1/(1+(t-s)^2))+(S.card:ℝ)*D := by
      simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_const, nsmul_eq_mul,
        one_mul]
    _ ≤ A*8+(S.card:ℝ)*D := add_le_add (mul_le_mul_of_nonneg_left hc hA) le_rfl
    _ = _ := by ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionDNF
namespace OAI

/-! A decision tree of depth r is a DNF of width at most r. Both Boolean
polarities have such a representation, so gates can be switched without
counting the number of clauses produced by earlier switches. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] lemma negate_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    T.negate.eval x = !(T.eval x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hx : x i <;> simp [negate, eval, hx, hl, hh]

@[simp] lemma negate_depth {n : ℕ} (T : BooleanDecisionTree n) : T.negate.depth = T.depth := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh => simp [negate, depth, hl, hh]

end BooleanDecisionTree







namespace BooleanDecisionTree




end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionRestriction
namespace OAI

/-! Decision-tree certificates are preserved by fixing additional coordinates.
We also package the two Boolean polarities of a certificate. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] theorem restrict_eval {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (T.restrict ρ).eval x = T.eval (ρ.apply x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none =>
      cases hx : x i <;> simp [restrict, eval, PartialAssignment.apply, hρ, hx, hl, hh]
    | some b =>
      cases b <;> simp [restrict, eval, PartialAssignment.apply, hρ, hl, hh]


end BooleanDecisionTree






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells
namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset


@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSparseGram
namespace OAI

/-! The prime-supported sparse mean square keeps the reciprocal logarithmic
weight of the coefficient norm. The Mangoldt kernel estimate is an explicit
local hypothesis; its analytic proof is separate from this finite duality. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

/-- The full reciprocal weight in finite weighted Gram duality. -/
theorem mrt_sparse_divided_weight_energy {ι : Type*}
    (K P : Finset ι) (hPK : P ⊆ K) (w freq : ι → ℝ) (a : ι → ℂ)
    (hw : ∀ n ∈ K, 0 ≤ w n) (hwP : ∀ n ∈ P, 0 < w n)
    (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ P, ‖a n‖^2/w n := by
  let b := fun n => if n ∈ P then a n/(w n:ℂ) else 0
  have hb (n : ι) (hn : n ∈ P) : (w n:ℂ)*b n = a n := by
    have hnz : (w n:ℂ) ≠ 0 := by exact_mod_cast (hwP n hn).ne'
    dsimp only [b]
    rw [if_pos hn]
    field_simp
  have he (t : ℝ) : mrtExponentialPolynomial K (fun n => (w n:ℂ)*b n) freq t =
      mrtExponentialPolynomial P a freq t := by
    unfold mrtExponentialPolynomial
    calc
      _ = ∑ n ∈ P, (w n:ℂ)*b n*Complex.exp (((freq n*t:ℝ):ℂ)*I) := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := sum_congr rfl (fun n hn => by rw [hb n hn])
  have hmass : (∑ n ∈ K, w n*‖b n‖^2) = ∑ n ∈ P, ‖a n‖^2/w n := by
    calc
      _ = ∑ n ∈ P, w n*‖b n‖^2 := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        dsimp only [b]
        rw [if_pos hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hwP n hn)]
        field_simp
  have h := mrt_sparse_weighted_row_energy K w freq b hw S hsep hA hD hkernel
  simpa only [he, hmass] using h

/-- A nonnegative smooth Mangoldt majorant supplies the exact logarithmic
coefficient gain in the prime-supported sparse mean square. -/
theorem mrt_sparse_prime_gram (K P : Finset ℕ) (hPK : P ⊆ K)
    (hP : ∀ p ∈ P, p.Prime) (ψ : ℕ → ℝ)
    (hψ : ∀ n ∈ K, 0 ≤ ψ n) (hψP : ∀ p ∈ P, 1 ≤ ψ p)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K
        (fun n => (ψ n * ArithmeticFunction.vonMangoldt n:ℝ))
        (fun n => -Real.log (n:ℝ)) (t-s)‖ ≤ A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := by
  let w := fun n => ψ n * ArithmeticFunction.vonMangoldt n
  have hlog (p : ℕ) (hp : p ∈ P) : 0 < Real.log (p:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (hP p hp).one_lt
  have hlow (p : ℕ) (hp : p ∈ P) : Real.log (p:ℝ) ≤ w p := by
    dsimp only [w]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hψP p hp) (hlog p hp).le
  have hwP (p : ℕ) (hp : p ∈ P) : 0 < w p := (hlog p hp).trans_le (hlow p hp)
  have hh := mrt_sparse_divided_weight_energy K P hPK w
    (fun n => -Real.log (n:ℝ)) a
    (fun n hn => mul_nonneg (hψ n hn) ArithmeticFunction.vonMangoldt_nonneg)
    hwP S hsep hA hD hkernel
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum (fun p hp =>
    div_le_div_of_nonneg_left (sq_nonneg _) (hlog p hp) (hlow p hp))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseSmallPrimes
namespace OAI

/-! The small-prime range of the published sparse estimate follows from
Chebyshev and finite weighted Gram duality. Only larger log Y requires
the oscillatory prime estimate. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_dyadic_prime_log_mass {Y : ℝ} (hY : 2 ≤ Y)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) :
    (∑ p ∈ P, Real.log (p:ℝ)) ≤ (2*Real.log 4)*Y := by
  have hsub : P ⊆ (Icc 0 ⌊2*Y⌋₊).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.le_floor_iff (by linarith : 0 ≤ 2*Y)).mpr (hP p hp).2.2⟩,(hP p hp).1⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p:ℝ)) hsub
    (fun p hp _ => Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
  have ht := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ 2*Y)
  rw [Chebyshev.theta_eq_sum_Icc] at ht
  exact hs.trans (by convert (preTransparency := .instances) ht using 1; ring)

theorem halasz_sparse_prime_card_bound {Y : ℝ} (hY : 2 ≤ Y)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      (2*Real.log 4)*(S.card:ℝ)*Y*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) := by
  let D := ∑ p ∈ P, Real.log (p:ℝ)
  have hlog (p : ℕ) (hp : p ∈ P) : 0 < Real.log (p:ℝ) :=
    Real.log_pos (by exact_mod_cast (hP p hp).1.one_lt)
  have hD : 0 ≤ D := sum_nonneg (fun p hp => (hlog p hp).le)
  have hkernel (t s : ℝ) :
      ‖mrtExponentialPolynomial P (fun p => (Real.log (p:ℝ):ℂ))
        (fun p => -Real.log (p:ℝ)) (t-s)‖ ≤ D := by
    unfold mrtExponentialPolynomial
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro p hp
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hlog p hp),
      Complex.norm_exp_ofReal_mul_I,mul_one,le_refl]
  have hh := mrt_sparse_divided_weight_energy P P (Subset.refl _) (fun p => Real.log (p:ℝ))
    (fun p => -Real.log (p:ℝ)) a (fun p hp => (hlog p hp).le) hlog S hsep
    (show (0:ℝ) ≤ 0 by rfl) hD (fun t _ s _ => by simpa using hkernel t s)
  simp only [mul_zero,zero_add] at hh
  have hm : 0 ≤ ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) :=
    sum_nonneg (fun p hp => div_nonneg (sq_nonneg _) (hlog p hp).le)
  calc
    _ ≤ ((S.card:ℝ)*D)*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) := hh
    _ ≤ ((S.card:ℝ)*((2*Real.log 4)*Y))*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (halasz_dyadic_prime_log_mass hY P hP) (Nat.cast_nonneg _)) hm
    _ = _ := by ring

lemma halasz_sparse_small_scale {L Y : ℝ} (hL : 1 ≤ L)
    (hY : Real.log Y ≤ 2*L^(3/4:ℝ)*Real.log L) :
    1 ≤ Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 := by
  have hL0 : 0 < L := by linarith
  have hp : 0 < L^(3/4:ℝ) := Real.rpow_pos_of_pos hL0 _
  have hy : Real.log Y/L^(3/4:ℝ) ≤ 2*Real.log L := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hY]
  have he : 1 ≤ Real.exp (-Real.log Y/L^(3/4:ℝ)+2*Real.log L) :=
    Real.one_le_exp_iff.mpr (by rw [neg_div]; linarith only [hy])
  have hs : Real.exp (2*Real.log L) = L^2 := by
    rw [show 2*Real.log L=Real.log L+Real.log L by ring,Real.exp_add,Real.exp_log hL0]
    ring
  rwa [Real.exp_add,hs] at he

/-- This is the exact sparse-input inequality in the small log Y range. -/
theorem halasz_sparse_small_primes {L Y : ℝ} (hL : 1 ≤ L) (hY : 2 ≤ Y)
    (hscale : Real.log Y ≤ 2*L^(3/4:ℝ)*Real.log L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      (2*Real.log 4)*(Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2)*
        ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := by
  apply (halasz_sparse_prime_card_bound hY P hP a S hsep).trans
  have hm : 0 ≤ ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := sum_nonneg (fun p hp =>
    div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)))
  have hfactor := mul_le_mul_of_nonneg_left (halasz_sparse_small_scale hL hscale)
    (show 0 ≤ (S.card:ℝ)*Y by positivity)
  apply mul_le_mul_of_nonneg_right _ hm
  have hlog : 0 ≤ 2*Real.log 4 := by positivity
  have hy0 : 0 ≤ Y := by linarith
  nlinarith only [hfactor,hlog,hy0]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszPrimeGram
namespace OAI

/-! The exact sparse-prime input follows from the quadratic Riesz-Mangoldt
kernel. This finite bridge retains the published error and arbitrary Y. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma mrt_riesz_prime_weight_nonneg (Y : ℝ) (n : ℕ) : 0 ≤ mrtRieszPrimeWeight Y n := by
  unfold mrtRieszPrimeWeight
  positivity

lemma mrt_riesz_prime_support {Y : ℝ} (hY : 2 ≤ Y) {p : ℕ}
    (hp : p.Prime) (hpY : (p : ℝ) ≤ 2 * Y) : p ∈ mrtRieszPrimeSupport Y := by
  apply mem_Icc.mpr
  refine ⟨hp.one_le, (Nat.le_floor_iff (by linarith : 0 ≤ 4 * Y)).mpr ?_⟩
  linarith

lemma mrt_riesz_prime_weight_ge_one {Y : ℝ} (hY : 2 ≤ Y) {p : ℕ}
    (hpY : (p : ℝ) ≤ 2 * Y) : 1 ≤ mrtRieszPrimeWeight Y p := by
  have hY0 : 0 < Y := by linarith
  have hr : (p : ℝ) / (4 * Y) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Y)).mpr
    linarith
  have hm : 1 / 2 ≤ max (1 - (p : ℝ) / (4 * Y)) 0 :=
    le_trans (by linarith) (le_max_left _ _)
  unfold mrtRieszPrimeWeight
  nlinarith [sq_nonneg (max (1 - (p : ℝ) / (4 * Y)) 0 - 1 / 2)]

/-- Only the smoothed arithmetic kernel is left by the finite duality step.
The small-logY range has already been proved from Chebyshev. -/
theorem mrt_sparse_prime_of_riesz_kernel
    (hkernel : ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
      2 * L ^ (3 / 4 : ℝ) * Real.log L < Real.log Y →
      ∀ u : ℝ, |u| ≤ 2 * Real.exp L →
      ‖mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
        (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => -Real.log (n : ℝ)) u‖ ≤
          C * Y / (1 + u ^ 2) + C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2) :
    HalaszPrimeSparseInput := by
  obtain ⟨C, L₀, hC, hk⟩ := hkernel
  let D := 2 * Real.log 4 + 8 * C
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, L₀, hD, ?_⟩
  intro L Y hL₀ hL hY P hP a S hheight hsep
  have hmass : 0 ≤ ∑ p ∈ P, ‖a p‖ ^ 2 / Real.log (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    apply div_nonneg (sq_nonneg _)
    exact Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)
  have hE : 0 ≤ Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by positivity
  have hY0 : 0 ≤ Y := by linarith
  have hfactor : 0 ≤ Y + (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by
    positivity
  by_cases hs : Real.log Y ≤ 2 * L ^ (3 / 4 : ℝ) * Real.log L
  · apply (halasz_sparse_small_primes hL hY hs P hP a S hsep).trans
    apply mul_le_mul_of_nonneg_right _ hmass
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hfactor
  · have hPK : P ⊆ mrtRieszPrimeSupport Y := by
      intro p hp
      exact mrt_riesz_prime_support hY (hP p hp).1 (hP p hp).2.2
    have hh := mrt_sparse_prime_gram (mrtRieszPrimeSupport Y) P hPK
      (fun p hp => (hP p hp).1) (mrtRieszPrimeWeight Y)
      (fun n _ => mrt_riesz_prime_weight_nonneg Y n)
      (fun p hp => mrt_riesz_prime_weight_ge_one hY (hP p hp).2.2)
      a S hsep (A := C * Y)
      (D := C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2)
      (by positivity) (by positivity) (fun t ht s hs' => hk L Y hL₀ hL hY
        (lt_of_not_ge hs) (t - s) (by
          have hr := abs_sub t s
          linarith [hheight t ht, hheight s hs']))
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hmass
    calc
      _ ≤ (8 * C) * (Y + (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2) := by
        nlinarith [mul_nonneg (show 0 ≤ 7 * C by positivity)
          (show 0 ≤ (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) hfactor

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszEstimate
namespace OAI

/-! The sparse-prime Riesz kernel estimate, with no upper restriction on
the prime cutoff. Far tails are charged to the pole term. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter _root_.Set _root_.Erdos970 _root_.OAI.Erdos970
open scoped _root_.Topology



theorem MRTWeakHurwitzGrowthInput.prime_sparse (h : MRTWeakHurwitzGrowthInput) :
    HalaszPrimeSparseInput := by
  obtain ⟨C, L₀, hC, hb⟩ := h.riesz_sparse_kernel
  exact mrt_sparse_prime_of_riesz_kernel ⟨C, L₀, hC, fun L Y hL₀ hL hY _ u hu =>
    hb L Y hL₀ hL hY u hu⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTInputsTheorem
namespace OAI

/-! The corrected short exponential-sum estimates of Matomäki, Radziwiłł,
and Tao in the specializations used for ordinary two-point correlations. -/
namespace TwoPointCorrelations

/-- Corrected MRT (2015), Theorem 1.7, in the application specialization. -/
theorem mrtShortExponentialInput : MRTShortExponentialInput :=
  mrt_weak_hurwitz_growth.short_exponential mrt_weak_hurwitz_growth.prime_sparse


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Main
namespace OAI

/-! Paper 009-01: the three original main results, unconditionally. -/
namespace TwoPointCorrelations



/-- Corollary 1.3: the corrected Elliott theorem for nonproportional affine forms. -/
theorem affineCorrectedElliott : AffineCorrectedElliott :=
  affineCorrectedElliott_of_mrt mrtShortExponentialInput

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPointCorrelations.FinalMain
namespace OAI

namespace OrdinaryTwoPointCorrelations

open _root_.OAI.TwoPointCorrelations
open _root_.Filter



theorem affine_corrected_elliott_oai :
    ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
      OneBounded f₁ → OneBounded f₂ →
      (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
      ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
        Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0) :=
  TwoPointCorrelations.affineCorrectedElliott

end OrdinaryTwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.OrdinaryTwoPointCorrelations.affine_corrected_elliott_oai := @OAI.OrdinaryTwoPointCorrelations.affine_corrected_elliott_oai
