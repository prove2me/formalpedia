-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_bounded_prime_triple_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:27:03.145013+00:00
-- url     : https://prove2.me/submissions/23b72a45-1255-4aa9-ad4c-08519a4a3cc4

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_window_middle

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

/-- Backport (Mathlib d13f23b), proved from `Real.le_tan`. -/
theorem Real.arctan_le_self {x : ℝ} (h : 0 ≤ x) : Real.arctan x ≤ x := by
  have h0 : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr h
  simpa [Real.tan_arctan] using Real.le_tan h0 (Real.arctan_lt_pi_div_two x)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate



lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma mrtPrimeEulerTerm_norm_le (b : ℕ → ℂ) (t : ℝ) {p : ℕ}
    (_hp : 0 < p) (hb : ‖b p‖ ≤ 1) :
    ‖mrtPrimeEulerTerm b t p‖ ≤ (1 : ℝ) / p := by
  rw [mrtPrimeEulerTerm, norm_div, norm_mul, norm_conj,
    mrtArchimedeanTwist_norm, mul_one, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators



lemma mrt_line_one_term (b : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term b (1 + (t : ℂ) * Complex.I) n =
      b n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  push_cast
  ring_nf



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare
namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators






lemma mrt_LSeries_term_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  rw [LSeries.term_of_ne_zero (Nat.mul_pos hm hn).ne', LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', hF m n hm hn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, div_mul_div_comm]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothEuler
namespace OAI

/-! The finite-prime smooth Euler product on Re(s)=1.  Finite prime
support makes the series absolutely convergent even on this line; the
geometric local factors therefore give the actual analytic series to
which the pretentious-distance estimate applies. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_line_one_euler_term (F : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term F (1 + (t : ℂ) * Complex.I) n = mrtPrimeEulerTerm F t n := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [mrt_line_one_term F hn t, mrtPrimeEulerTerm, he]
  ring

lemma mrt_LSeries_term_pow (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    LSeries.term F s (p ^ k) = (LSeries.term F s p) ^ k := by
  induction k with
  | zero => simp [LSeries.term, hF1]
  | succ k ih =>
    calc
      _ = LSeries.term F s (p ^ k * p) := by rw [pow_succ]
      _ = LSeries.term F s (p ^ k) * LSeries.term F s p :=
        mrt_LSeries_term_mul F hF s (pow_pos hp k) hp
      _ = _ := by rw [ih, pow_succ]

lemma mrt_LSeries_term_coprime_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (_h : m.Coprime n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  exact mrt_LSeries_term_mul F hF s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma mrt_prime_euler_norm_lt_one (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {p : ℕ} (hp : p.Prime) : ‖mrtPrimeEulerTerm F t p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (1 : ℝ) / p := mrtPrimeEulerTerm_norm_le F t hp.pos (hF p hp.pos)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    _ < 1 := by norm_num

/-- The actual smooth L-series is absolutely summable and equals its
finite Euler product on the boundary line `Re(s)=1`. -/
theorem mrt_smooth_euler_product (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    Summable (fun n : Nat.smoothNumbers (N + 1) =>
      ‖LSeries.term F (1 + (t : ℂ) * Complex.I) n‖) ∧
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term F (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have h1 : LSeries.term F s 1 = 1 := by simp [LSeries.term, hF1]
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      LSeries.term F s (p ^ k) = (mrtPrimeEulerTerm F t p) ^ k := by
    rw [mrt_LSeries_term_pow F hF1 hF s hp.pos k,
      mrt_line_one_euler_term F hp.ne_zero t]
  have hnorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖LSeries.term F s (p ^ k)‖) := by
    intro p hp
    simpa only [hlocal p hp, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _)
        (mrt_prime_euler_norm_lt_one F hFb t hp))
  obtain ⟨hs, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {_ _} h => mrt_LSeries_term_coprime_mul F hF s h) hnorm (N + 1)
  have hprod : (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, LSeries.term F s (p ^ k)) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    change (∏ p ∈ primesUpTo N, ∑' k : ℕ, LSeries.term F s (p ^ k)) = _
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ = ∑' k : ℕ, (mrtPrimeEulerTerm F t p) ^ k := tsum_congr (hlocal p hprime)
      _ = _ := (hasSum_geometric_of_norm_lt_one
        (mrt_prime_euler_norm_lt_one F hFb t hprime)).tsum_eq
  rw [hprod] at he
  exact ⟨hs, he⟩


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


open _root_.Complex _root_.Topology _root_.Filter _root_.MeasureTheory _root_.Set _root_.Function
open _root_.Real hiding arctan_le_self



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

open _root_.Filter _root_.Asymptotics
open _root_.Real hiding arctan_le_self



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.Real hiding arctan_le_self
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel
namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open _root_.Complex


lemma modFive_perron_denominator_vertical {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (1 + t ^ 2) / 4 ≤
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 4 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t, sq_nonneg (σ - 1 / 2)]


lemma modFive_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * x ^ σ / (1 + t ^ 2) := by
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  have hd := modFive_perron_denominator_vertical hσ t
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hp hd).trans_eq (by
    field_simp)


lemma modFivePerronKernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h0 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have h1 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have hcont : Continuous (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    unfold modFivePerronKernel
    apply Continuous.div
    · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
        fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    · fun_prop
    · intro t
      exact mul_ne_zero (h0 t) (h1 t)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  apply hmaj.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (modFive_perron_kernel_vertical hx hσ)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronInversion
namespace OAI

/-! Triangular Perron inversion from Mellin inversion. The triangular
function is a difference of two elementary Mellin transforms. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory
open scoped _root_.Classical


lemma modFiveTriangle_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin modFiveTriangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have hd := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hd
  have he : ∀ t ∈ Ioi (0 : ℝ), modFiveTriangle t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [modFiveTriangle, indicator_of_mem hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [modFiveTriangle, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent modFiveTriangle s := by
    exact hd.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin modFiveTriangle s = mellin
        (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
          (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - 1 / (s + 1) := hd.2
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma modFiveTriangle_continuous : Continuous modFiveTriangle := by
  unfold modFiveTriangle
  fun_prop

lemma modFiveTriangle_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin modFiveTriangle) σ := by
  have hi := modFivePerronKernel_integrable (by norm_num : (0 : ℝ) < 1) hσ
  apply hi.congr
  filter_upwards [] with t
  have hs : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using (show 0 < σ by linarith)
  rw [(modFiveTriangle_hasMellin hs).2]
  simp [modFivePerronKernel]

theorem modFivePerron_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = modFiveTriangle (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ modFiveTriangle (one_div_pos.mpr hx)
    (modFiveTriangle_hasMellin (by simpa using hsp)).1
    (modFiveTriangle_verticalIntegrable hσ) (modFiveTriangle_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin modFiveTriangle ((σ : ℂ) + (t : ℂ) * Complex.I) =
          modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (modFiveTriangle_hasMellin (by simpa using hsp)).2]
    unfold modFivePerronKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm

lemma modFivePerron_gt_one {x σ : ℝ} (hx : 1 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 1 - 1 / (x : ℂ) := by
  rw [modFivePerron_inversion (zero_lt_one.trans hx) hσ]
  have hi : (1 : ℝ) / x ≤ 1 := (div_le_one (zero_lt_one.trans hx)).mpr hx.le
  rw [modFiveTriangle, max_eq_left (sub_nonneg.mpr hi)]
  push_cast
  rfl

lemma modFivePerron_lt_one {x σ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 0 := by
  rw [modFivePerron_inversion hx hσ]
  have hi : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa using hx1.le)
  rw [modFiveTriangle, max_eq_right (sub_nonpos.mpr hi)]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronSeries
namespace OAI

/-! Absolute interchange for the triangular Perron kernel. The estimate is
proved for any absolutely convergent Dirichlet series and then specialized
to the actual twisted von Mangoldt series.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators

lemma modFivePerron_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * modFivePerronKernel x s =
      a n * modFivePerronKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold modFivePerronKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma modFivePerron_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [modFivePerron_term_kernel a hn hx]
    exact (modFivePerronKernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma modFivePerron_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem modFivePerron_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑' n : ℕ, VerticalIntegral'
        (fun s => LSeries.term a s n * modFivePerronKernel x s) σ := by
  have hi := modFivePerronKernel_integrable hx hσ
  have hterms := fun n => modFivePerron_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [modFivePerron_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma modFivePerron_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hxn : x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ =
      if (n : ℝ) < x then a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * modFivePerronKernel x s) =
      fun s => a n * modFivePerronKernel (x / (n : ℝ)) s := by
    funext s
    exact modFivePerron_term_kernel a hn hx s
  rw [hk]
  have hconst : VerticalIntegral' (fun s => a n * modFivePerronKernel (x / (n : ℝ)) s) σ =
      a n * VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst]
  by_cases hnlt : (n : ℝ) < x
  · rw [if_pos hnlt]
    have hp := modFivePerron_gt_one ((one_lt_div hn').mpr hnlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = _ at hp
    rw [hp]
    congr 1
    push_cast
    field_simp
  · rw [if_neg hnlt]
    have hlt : x < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hnlt) hxn
    have hp := modFivePerron_lt_one (div_pos hx hn') ((div_lt_one hn').mpr hlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = 0 at hp
    rw [hp, mul_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedPsi
namespace OAI

/-! The exact triangular Perron formula for the twisted von Mangoldt sums.
Nonintegral real cutoffs avoid the irrelevant boundary value of the scalar
kernel; later we use half-integral cutoffs to recover every integer sum.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators _root_.Classical


theorem modFivePerron_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ))
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  rw [modFivePerron_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlarge
      exact if_neg (not_lt.mpr hxn.le)
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx.le)
  have hnlt : (n : ℝ) < x := lt_of_le_of_ne hnle (hxnat n).symm
  rw [if_pos hnlt]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPerronWindowKernel
namespace OAI

/-! A short multiplicative smoothing of Perron's kernel. The difference
has both the first-order bound and an integrable inverse-square tail. -/

namespace TwoPointCorrelations

open _root_.Complex





theorem halasz_perron_window_tail {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (δ * (1 + t ^ 2)) := by
  have hy : 0 < 1 + δ := by linarith
  have hk1 := modFive_perron_kernel_vertical (mul_pos hy hx) (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  have hk0 := modFive_perron_kernel_vertical hx (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  simp only [Real.rpow_one] at hk1 hk0
  unfold halaszPerronWindowKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_div_of_nonneg_right (norm_sub_le _ _) hδ.le).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have htop : (1 + δ) * ‖modFivePerronKernel ((1 + δ) * x)
      (1 + (t : ℂ) * Complex.I)‖ + ‖modFivePerronKernel x (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (1 + t ^ 2) := by
    calc
      _ ≤ (1 + δ) * (4 * ((1 + δ) * x) / (1 + t ^ 2)) + 4 * x / (1 + t ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hk1 hy.le) hk0
      _ ≤ _ := by
        have hδ2 : (1 + δ) ^ 2 ≤ 4 := by nlinarith
        have hnum : (1 + δ) * (4 * ((1 + δ) * x)) + 4 * x ≤ 20 * x := by
          nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hδ2)]
        calc
          _ = ((1 + δ) * (4 * ((1 + δ) * x)) + 4 * x) / (1 + t ^ 2) := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
  exact (div_le_div_of_nonneg_right htop hδ.le).trans_eq (by
    field_simp [ne_of_gt hδ, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity])

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.Classical _root_.LSeries.notation



lemma halasz_smooth_term (f : ℕ → ℂ) (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszSmoothFunction f N) s n =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) n := by
  by_cases hn : n ∈ Nat.smoothNumbers (N + 1) <;>
    simp [LSeries.term, halaszSmoothFunction, hn]


lemma halasz_smooth_LSeries_summable (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hbound : OneBounded f) (N : ℕ) (t : ℝ) :
    LSeriesSummable (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs : Summable (fun n : Nat.smoothNumbers (N + 1) => LSeries.term f s n) :=
    (mrt_smooth_euler_product f hf1 hf hbound N t).1.of_norm
  have hi : Summable ((Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s)) :=
    (summable_subtype_iff_indicator (s := Nat.smoothNumbers (N + 1))).mp hs
  change Summable (LSeries.term (halaszSmoothFunction f N) s)
  have he : LSeries.term (halaszSmoothFunction f N) s =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) :=
    funext (halasz_smooth_term f N s)
  rw [he]
  exact hi


lemma halasz_finite_term (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszFiniteCoefficient P a) s n =
      if n ∈ P then LSeries.term a s n else 0 := by
  by_cases hn : n ∈ P <;> simp [halaszFiniteCoefficient, LSeries.term, hn]

lemma halasz_finite_LSeries_summable (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (halaszFiniteCoefficient P a) s := by
  apply summable_of_ne_finset_zero (s := P)
  intro n hn
  simp only [halasz_finite_term, hn, ite_false]

lemma halasz_finite_LSeries (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeries (halaszFiniteCoefficient P a) s = ∑ n ∈ P, LSeries.term a s n := by
  unfold LSeries
  rw [tsum_eq_sum (s := P) (fun n hn => by simp [halasz_finite_term, hn])]
  exact sum_congr rfl (fun n hn => by simp [halasz_finite_term, hn])


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCoefficientBound
namespace OAI

/-! The triple-convolution coefficients have a logarithm-squared majorant.
This bounds the short boundary interval in the Perron unsmoothing step. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.LSeries.notation

lemma halasz_mangoldt_convolution_bound (a f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ f) n‖ ≤ c * Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, c * ArithmeticFunction.vonMangoldt p.1 := by
      apply sum_le_sum
      intro p hp
      have hp0 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hf p.2 (Nat.pos_of_ne_zero hp0)) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans_eq (mul_one _)
    _ = c * Real.log (n : ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => c * ArithmeticFunction.vonMangoldt a),
        ← mul_sum, ArithmeticFunction.vonMangoldt_sum]

lemma halasz_triple_coefficient_bound (a b f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n)
    (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ (b ⍟ f)) n‖ ≤ c * (Real.log (n : ℝ)) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnpos)
  have hinner (m : ℕ) : ‖(b ⍟ f) m‖ ≤ Real.log (m : ℝ) := by
    simpa only [one_mul] using halasz_mangoldt_convolution_bound b f (c := 1)
      (by norm_num) (fun n => by simpa using hb n) hf m
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        c * ArithmeticFunction.vonMangoldt p.1 * Real.log (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
      have hp2pos := Nat.pos_of_ne_zero hp0.2
      have hp2le : p.2 ≤ n := by
        rw [← hpmul]
        exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp0.1)
      have hlog : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hinner p.2) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg))
    _ = c * Real.log (n : ℝ) ^ 2 := by
      rw [Nat.sum_divisorsAntidiagonal
        (fun a _ => c * ArithmeticFunction.vonMangoldt a * Real.log (n : ℝ)),
        ← sum_mul, ← mul_sum, ArithmeticFunction.vonMangoldt_sum]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriplePrefix
namespace OAI

/-! Identify a grouped piece of the adaptive double convolution with the
actual coefficients to which narrow Perron inversion is applied. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.LSeries.notation





lemma halasz_smooth_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    OneBounded (halaszSmoothFunction f N) := by
  intro n hn
  unfold halaszSmoothFunction
  split_ifs
  · exact hf n hn
  · simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedSmooth
namespace OAI

/-! The smooth-series step needs only a bounded coefficient. In particular
it applies to the actual typical coefficient, whose value at one may vanish. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_bounded_smooth_summable (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (t : ℝ) :
    LSeriesSummable (halaszSmoothFunction f N) (1+(t:ℂ)*Complex.I) := by
  have hs := halasz_smooth_LSeries_summable (fun _ => (1:ℂ)) rfl
    (by intros; simp) (by intro n hn; simp) N t
  apply hs.norm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  by_cases hsm : n ∈ Nat.smoothNumbers (N+1)
  · simp only [LSeries.term, hn, ite_false, halaszSmoothFunction, hsm, ite_true,
      norm_div, norm_one]
    exact div_le_div_of_nonneg_right (hf n (Nat.pos_of_ne_zero hn)) (norm_nonneg _)
  · simp [LSeries.term, hn, halaszSmoothFunction, hsm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnsmoothing
namespace OAI

/-! Unsmoothing the triple convolution by a finite difference. Only the
coefficients in the short boundary interval contribute to the error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex


lemma halasz_triangle_scale (a : ℕ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * halaszTriangularSum a x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ) := by
  rw [halaszTriangularSum, mul_sum]
  apply sum_congr rfl
  intro n _
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp

lemma halasz_triangle_difference (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      (x : ℂ) * halaszTriangularSum a x) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, a n) +
        ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
  rw [halasz_triangle_scale a (by positivity), halasz_triangle_scale a hx.ne',
    Nat.floor_add_natCast hx.le]
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 (⌊x⌋₊ + m), f n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, f n) + ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), f n := by
    simpa only [Ico_add_one_right_eq_Icc] using
      (sum_Ico_consecutive f (by omega : 1 ≤ ⌊x⌋₊ + 1)
        (by omega : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ + m) + 1)).symm
  rw [hsplit]
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x + m - (n : ℝ) : ℝ) : ℂ)) -
      (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ)) =
      (m : ℂ) * ∑ n ∈ Icc 1 ⌊x⌋₊, a n := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  linear_combination he

lemma halasz_triangle_remainder (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x) (m : ℕ)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
      B * (m : ℝ) ^ 2 := by
  have hp (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤ B * m := by
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hnx : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hnlo)
    have hny : (n : ℝ) ≤ x + m := by
      have hf := Nat.floor_le hx.le
      have hn' : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast hnhi
      linarith
    have hw0 : 0 ≤ x + m - (n : ℝ) := by linarith
    have hwm : x + m - (n : ℝ) ≤ (m : ℝ) := by linarith
    have hBn := hB n (mem_Icc.mpr ⟨hnlo, hnhi⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul hBn hwm hw0 ((norm_nonneg _).trans hBn)
  have hc : #(Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) = m := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), B * m := sum_le_sum hp
    _ = _ := by rw [sum_const, hc, nsmul_eq_mul]; ring

theorem halasz_unsmoothing_error (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x)
    (m : ℕ) (hm : 0 < m)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖(((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [halasz_triangle_difference a hx m, add_div, mul_div_cancel_left₀ _ hmC,
    add_sub_cancel_left, norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (halasz_triangle_remainder a hx m hB) hmR.le).trans_eq
    (by field_simp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowPerron
namespace OAI

/-! Exact inversion for the narrow Perron window. Absolute convergence on
the line is enough, including the smooth Euler series at real part one. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum

lemma halasz_LSeries_line_continuous (a : ℕ → ℂ) (ha : LSeriesSummable a 1) :
    Continuous (fun t : ℝ => LSeries a (1 + (t : ℂ) * I)) := by
  change Continuous (fun t : ℝ => ∑' n, LSeries.term a (1 + (t : ℂ) * I) n)
  refine continuous_tsum (u := fun n => ‖LSeries.term a 1 n‖) ?_ ha.norm ?_
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero]
      exact continuous_const
    · simp_rw [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) by
          fun_prop).const_cpow (Or.inl (by exact_mod_cast hn))
      · intro t
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  · intro n t
    simp [LSeries.norm_term_eq]

lemma halasz_LSeries_line_bound (a : ℕ → ℂ) (ha : LSeriesSummable a 1) (t : ℝ) :
    ‖LSeries a (1 + (t : ℂ) * I)‖ ≤ ∑' n, ‖LSeries.term a 1 n‖ := by
  apply tsum_of_norm_bounded ha.norm.hasSum
  intro n
  simp [LSeries.norm_term_eq]

lemma halasz_LSeries_perron_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * I) *
      modFivePerronKernel x (1 + (t : ℂ) * I)) := by
  have hk := modFivePerronKernel_integrable hx (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simp only [Complex.ofReal_one] at hk
  apply (hk.norm.const_mul (∑' n, ‖LSeries.term a 1 n‖)).mono'
    ((halasz_LSeries_line_continuous a ha).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (halasz_LSeries_line_bound a ha t) (norm_nonneg _)

lemma halasz_LSeries_window_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hi := (((halasz_LSeries_perron_integrable a ha hy).const_mul
    ((1 + δ : ℝ) : ℂ)).sub (halasz_LSeries_perron_integrable a ha hx)).div_const (δ : ℂ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.sub_apply]
  unfold halaszPerronWindowKernel
  ring

theorem halasz_window_perron (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hynat : ∀ n : ℕ, (1 + δ) * x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x δ s) 1 =
      (((1 + δ : ℝ) : ℂ) * halaszTriangularSum a ((1 + δ) * x) -
        halaszTriangularSum a x) / (δ : ℂ) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hxI := halasz_LSeries_perron_integrable a ha hx
  have hyI := halasz_LSeries_perron_integrable a ha hy
  have hxP := modFivePerron_finite_sum a hx (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hxnat
  have hyP := modFivePerron_finite_sum a hy (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hynat
  change _ = (((1 + δ : ℝ) : ℂ) * _ - _) / (δ : ℂ)
  rw [halaszTriangularSum, halaszTriangularSum, ← hxP, ← hyP]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, Complex.ofReal_one]
  have he (t : ℝ) : LSeries a (1 + (t : ℂ) * I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I) =
      (((1 + δ : ℝ) : ℂ) * (LSeries a (1 + (t : ℂ) * I) *
        modFivePerronKernel ((1 + δ) * x) (1 + (t : ℂ) * I)) -
        LSeries a (1 + (t : ℂ) * I) * modFivePerronKernel x (1 + (t : ℂ) * I)) /
          (δ : ℂ) := by unfold halaszPerronWindowKernel; ring
  simp_rw [he]
  rw [integral_div, integral_sub (hyI.const_mul _) hxI, integral_const_mul]
  ring

theorem halasz_window_unsmoothing (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x B : ℝ} (hx : 0 < x) (m : ℕ) (hm : 0 < m)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x (m / x) s) 1 -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (1 + (m : ℝ) / x) * x = x + m := by field_simp
  have hynat (n : ℕ) : (1 + (m : ℝ) / x) * x ≠ (n : ℝ) := by
    rw [he]
    intro h
    by_cases hmn : m ≤ n
    · apply hxnat (n - m)
      rw [Nat.cast_sub hmn]
      linarith
    · have hnm : (n : ℝ) < m := by exact_mod_cast (Nat.lt_of_not_ge hmn)
      linarith
  rw [halasz_window_perron a ha hx (div_pos hmR hx) hxnat hynat, he]
  have hscale : (((1 + (m : ℝ) / x : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      halaszTriangularSum a x) / ((m : ℝ) / x : ℝ) =
      (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) := by
    push_cast
    field_simp [hx.ne', Nat.ne_of_gt hm]
  rw [hscale]
  exact halasz_unsmoothing_error a hx m hm hB

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open _root_.Real hiding arctan_le_self
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

open _root_.FourierTransform _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators
open _root_.Real hiding arctan_le_self

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCauchyMeanSquare
namespace OAI

/-! Summing the translated unit-window estimates against the Cauchy
weight gives the global weighted mean square used in the Perron argument. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_polynomial_norm_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    ‖mrtExponentialPolynomial S a freq t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  unfold mrtExponentialPolynomial
  exact (norm_sum_le _ _).trans (by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl])





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePolynomial
namespace OAI

/-! The finite prime factors in the Perron integrand, with the same
normalization as the prime mean-square theorem. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical


lemma halasz_prime_polynomial_series (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (∑ p ∈ P, LSeries.term (fun p => (Real.log (p : ℝ) : ℂ) * a p)
      (1 + (t : ℂ) * I) p) = halaszPrimePolynomial P a t := by
  unfold halaszPrimePolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro p hp
  rw [mrt_line_one_term _ (hP p hp).ne_zero t]
  push_cast
  ring


lemma halasz_prime_polynomial_norm (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ ∑ p ∈ P, ‖a p‖ * (Real.log (p : ℝ) / p) := by
  apply (halasz_polynomial_norm_le P _ _ t).trans_eq
  apply sum_congr rfl
  intro p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)

lemma halasz_prime_polynomial_bounded (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (t : ℝ) :
    ‖halaszPrimePolynomial P a t‖ ≤ R * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (halasz_prime_polynomial_norm P a hP t).trans
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (ha p hp)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))



lemma halasz_finite_prime_mangoldt_bound (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (hR : 0 ≤ R) (ha : ∀ p ∈ P, ‖a p‖ ≤ R) (n : ℕ) :
    ‖halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) n‖ ≤
      R * ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n ∈ P
  · rw [halaszFiniteCoefficient, if_pos hn, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le)),
      ArithmeticFunction.vonMangoldt_apply_prime (hP n hn)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ha n hn)
      (Real.log_nonneg (by exact_mod_cast (hP n hn).one_le))
  · rw [halaszFiniteCoefficient, if_neg hn, norm_zero]
    exact mul_nonneg hR ArithmeticFunction.vonMangoldt_nonneg

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowTail
namespace OAI

/-! Absolute truncation of the narrow Perron integral. The inverse-square
tail gives an explicit error, independently of the central mean squares. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_cauchy_tail_right {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Ioi_inv_one_add_sq, ← Real.arctan_inv_of_pos hT]
  exact Real.arctan_le_self (by positivity)

lemma halasz_cauchy_tail_left {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Iic_inv_one_add_sq, Real.arctan_neg]
  have h := halasz_cauchy_tail_right hT
  rw [integral_Ioi_inv_one_add_sq] at h
  linarith

theorem halasz_integral_truncate (f : ℝ → ℂ) (hf : Integrable f)
    {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hbound : ∀ t, ‖f t‖ ≤ D * (1 + t ^ 2)⁻¹) :
    ‖∫ t : ℝ, f t‖ ≤ ‖∫ t in -T..T, f t‖ + 2 * D / T := by
  have hmajor := integrable_inv_one_add_sq.const_mul D
  have hleft : ‖∫ t in Set.Iic (-T), f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Iic (-T), D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_left hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hright : ‖∫ t in Set.Ioi T, f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Ioi T, D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_right hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hsplit : (∫ t : ℝ, f t) = (∫ t in Set.Iic (-T), f t) +
      (∫ t in -T..T, f t) + ∫ t in Set.Ioi T, f t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict,
      add_sub_cancel, intervalIntegral.integral_Iic_add_Ioi hf.restrict hf.restrict]
  rw [hsplit]
  have hn := (norm_add_le ((∫ t in Set.Iic (-T), f t) + ∫ t in -T..T, f t)
    (∫ t in Set.Ioi T, f t)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [mul_div_assoc]
  linarith

theorem halasz_window_integral_truncate (P Q F : ℝ → ℂ)
    {x δ T U V W : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hT : 0 < T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hP : ∀ t, ‖P t‖ ≤ U) (hQ : ∀ t, ‖Q t‖ ≤ V) (hF : ∀ t, ‖F t‖ ≤ W)
    (hint : Integrable (fun t : ℝ => P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I))) :
    ‖∫ t : ℝ, P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      ‖∫ t in -T..T, P t * Q t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ +
        40 * x * U * V * W / (δ * T) := by
  refine (halasz_integral_truncate _ hint hT
    (show 0 ≤ U * V * W * (20 * x / δ) by positivity) ?_).trans_eq ?_
  · intro t
    rw [norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ U * V * W * (20 * x / (δ * (1 + t ^ 2))) := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul (hP t) (hQ t) (norm_nonneg _) hU)
            (hF t) (norm_nonneg _) (mul_nonneg hU hV))
          (halasz_perron_window_tail hx hδ hδ1 t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hU hV) hW)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  · congr 1
    ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTripleEstimate
namespace OAI

/-! A complete finite estimate for each grouped triple convolution.
The main term, contour tail, and unsmoothing error are all explicit. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped _root_.Classical _root_.LSeries.notation

lemma halasz_vertical_integral_norm (G : ℂ → ℂ) :
    ‖VerticalIntegral' G 1‖ ≤ ‖∫ t : ℝ, G (1 + (t : ℂ) * I)‖ := by
  have hnorm : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    simp only [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
    exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hp
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, norm_mul, norm_I,
    one_mul, Complex.ofReal_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedTriple
namespace OAI

/-! The triple-convolution estimate for the typical coefficient. Only
one-boundedness is needed by Perron inversion; multiplicativity belongs
to the separate finite convolution identity. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped _root_.Classical _root_.LSeries.notation

theorem halasz_bounded_prime_triple_estimate_oai : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), OneBounded f →
    ∀ (N : ℕ) (x T A W R : ℝ) (m : ℕ), 0 < x → 0 < m → (m : ℝ) ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) → B ≤ T → 0 ≤ A → 0 ≤ W → 0 ≤ R →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ a b : ℕ → ℂ,
      (∀ p ∈ P, ‖a p‖ ≤ R) → (∀ q ∈ Q, ‖b q‖ ≤ 1) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊,
      (halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟
          halaszSmoothFunction f N)) n‖ ≤
      (C * x * A) *
        (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) +
      40 * x * (R * ∑ p ∈ P, Real.log (p : ℝ) / p) *
        (∑ q ∈ Q, Real.log (q : ℝ) / q) * W / ((m / x) * T) +
      R * Real.log (x + m) ^ 2 * m := by
  obtain ⟨C, B, hC, hB, hmid⟩ := halasz_prime_window_middle
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hbound N x T A W R m hx hm hmx hxnat hBT hA hW hR P Q hP hQ a b ha hb hFA hFW
  let c : ℕ → ℂ := halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
    (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟ halaszSmoothFunction f N)
  let D := halaszPrimePolynomial P a
  let E := halaszPrimePolynomial Q b
  let F := fun t : ℝ => LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hsum (t : ℝ) : LSeriesSummable c (1 + (t : ℂ) * I) :=
    (halasz_finite_LSeries_summable P _ _).convolution
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_bounded_smooth_summable f hbound N t))
  have hc : LSeriesSummable c 1 := by simpa using hsum 0
  have hline (t : ℝ) : LSeries c (1 + (t : ℂ) * I) = D t * E t * F t := by
    dsimp only [c]
    rw [LSeries_convolution' (halasz_finite_LSeries_summable P _ _)
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_bounded_smooth_summable f hbound N t)),
      LSeries_convolution' (halasz_finite_LSeries_summable Q _ _)
        (halasz_bounded_smooth_summable f hbound N t),
      halasz_finite_LSeries, halasz_finite_LSeries,
      halasz_prime_polynomial_series P a hPl t, halasz_prime_polynomial_series Q b hQ t]
    dsimp [D, E, F]
    ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < (m : ℝ) / x := div_pos hmR hx
  have hδ1 : (m : ℝ) / x ≤ 1 := (div_le_one hx).mpr hmx
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hpMass : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hqMass : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQ q hq).one_le)) (Nat.cast_nonneg _))
  have hint : Integrable (fun t : ℝ => D t * E t * F t *
      halaszPerronWindowKernel x (m / x) (1 + (t : ℂ) * I)) := by
    simpa only [hline] using halasz_LSeries_window_integrable c hc hx hδ
  have htail := halasz_window_integral_truncate D E F hx hδ hδ1 hT
    (mul_nonneg hR hpMass) hqMass hW
    (halasz_prime_polynomial_bounded P a hPl ha)
    (fun t => by simpa only [one_mul] using halasz_prime_polynomial_bounded Q b hQ hb t)
    hFW hint
  have hmiddle := hmid x (m / x) T A hx hδ hδ1 hBT hA P Q hP hQ a b F hFA
  have hcoeff (n : ℕ) : ‖c n‖ ≤ R * Real.log (n : ℝ) ^ 2 :=
    halasz_triple_coefficient_bound _ _ _ hR
      (halasz_finite_prime_mangoldt_bound P a hPl hR ha)
      (fun n : ℕ => by simpa only [one_mul] using
        halasz_finite_prime_mangoldt_bound Q b hQ (R := 1) (by norm_num) hb n)
      (halasz_smooth_oneBounded f hbound N) n
  have hboundary (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖c n‖ ≤ R * Real.log (x + m) ^ 2 := by
    have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnle : (n : ℝ) ≤ x + m := by
      have hh : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast (mem_Icc.mp hn).2
      linarith [Nat.floor_le hx.le]
    exact (hcoeff n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg hn1)
        (Real.log_le_log (by positivity) hnle) 2) hR)
  have hunsmooth := halasz_window_unsmoothing c hc hx m hm hxnat hboundary
  have hnorm := halasz_vertical_integral_norm
    (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s)
  simp_rw [hline] at hnorm
  have hcompare := norm_add_le
    (VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
    ((∑ n ∈ Icc 1 ⌊x⌋₊, c n) -
      VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
  rw [add_sub_cancel, norm_sub_rev] at hcompare
  change ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ _
  dsimp only [D, E, halaszPrimePolynomial] at htail hnorm
  linarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_bounded_prime_triple_estimate_oai := @OAI.TwoPointCorrelations.halasz_bounded_prime_triple_estimate_oai
