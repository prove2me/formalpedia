-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_actual_bin_moment_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:40:07.632247+00:00
-- url     : https://prove2.me/submissions/6bf15829-484c-4a34-be86-5caa146cf69b

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_mixed_real_bin_separation

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical







lemma mrt_band_index_le_log_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hlogQ : 1 ≤ Real.log Q) : (j : ℝ) ≤ Real.log (mrtBandUpper Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  simp only [mrtBandUpper, Real.log_exp]
  calc
    (j : ℝ) ≤ (j : ℝ) ^ (4 * j + 2) := by
      simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 4 * j + 2 by omega)
    _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by
      have hh := one_le_pow₀ (n := j) hlogQ
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ j) (4 * j + 2)]


end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeometricBins
namespace OAI

/-! The exponential sum over the first MRT prime band. Its constant is
independent of the number of coarse bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_exp_geometric_sum {β H : ℝ} (hβ : 0 < β) (hH : 0 < H) (m n : ℕ) :
    (∑ k ∈ Icc m n, Real.exp (-β * (k : ℝ) / H)) ≤
      Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) := by
  let q := Real.exp (-β / H)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by linarith : -β < 0) hH
  have he (k : ℕ) : Real.exp (-β * (k : ℝ) / H) = q ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Icc m n = Ico m (n + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  simp_rw [he]
  rw [hs]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

lemma mrt_geometric_denominator_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 / (1 - Real.exp (-x)) ≤ 2 / x := by
  have hex : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hex
  have hgap : x / 2 ≤ 1 - Real.exp (-x) := by
    calc
      _ ≤ x / (1 + x) := div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      _ = 1 - 1 / (1 + x) := by
        field_simp [show (1 : ℝ) + x ≠ 0 by positivity]
        ring
      _ ≤ _ := sub_le_sub_left hinv 1
  calc
    _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hgap
    _ = _ := by ring

theorem mrt_first_band_exponential_sum {β H P : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H) (hP : 1 ≤ P) (n : ℕ) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ n, Real.exp (-β * (k : ℝ) / H)) ≤
      (2 * Real.exp 1 * H / β) * P ^ (-β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  let m : ℕ := ⌊H * Real.log P⌋₊
  have hfloor : H * Real.log P < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase : -β * (m : ℝ) / H ≤ -β * Real.log P + β / H := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hfloor.le hβ.le
    field_simp [hH.ne']
    nlinarith
  have hpower : Real.exp (-β * (m : ℝ) / H) ≤ Real.exp 1 * P ^ (-β) := by
    calc
      _ ≤ Real.exp (-β * Real.log P + β / H) := Real.exp_le_exp.mpr hbase
      _ = Real.exp (β / H) * P ^ (-β) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hP0]
        rw [show -β * Real.log P = Real.log P * (-β) by ring, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((div_le_one hH).mpr hβH)) (Real.rpow_nonneg hP0.le _)
  have hgap : 0 < 1 - Real.exp (-β / H) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith : -β < 0) hH))
  have hden : 1 / (1 - Real.exp (-β / H)) ≤ 2 / (β / H) := by
    simpa only [neg_div] using mrt_geometric_denominator_bound (div_pos hβ hH)
      ((div_le_one hH).mpr hβH)
  calc
    _ ≤ Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) :=
      mrt_exp_geometric_sum hβ hH m n
    _ ≤ (Real.exp 1 * P ^ (-β)) * (2 / (β / H)) := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul hpower hden (le_of_lt (one_div_pos.mpr hgap)) (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPrimeBins
namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical







lemma mrt_prime_log_lower_le_upper {H Q : ℝ} (hH : 0 < H) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ≤ ⌊H * Real.log Q⌋₊) : mrtPrimeLogLower H k ≤ Q := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hQ))
  have hkR : (k : ℝ) ≤ ⌊H * Real.log Q⌋₊ := by exact_mod_cast hk
  calc
    _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr
      ((div_le_iff₀ hH).mpr (by nlinarith))
    _ = _ := Real.exp_log hQ0


lemma mrt_log_bin_card {H Q P : ℝ} (hH : 0 ≤ H) (hQ : 1 ≤ Q) :
    ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ H * Real.log Q + 1 := by
  have hc : (Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card ≤ ⌊H * Real.log Q⌋₊ + 1 := by
    rw [Nat.card_Icc]
    omega
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH (Real.log_nonneg hQ))
  have hcR : ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤
      (⌊H * Real.log Q⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogBinEndpoints
namespace OAI

/-! Endpoint control for every logarithmic bin, including the first
partially filled bin below the original lower endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma mrt_log_bin_lower_endpoint {H P : ℝ} (hH : 1 ≤ H) (hP : 0 < P)
    {k : ℕ} (hk : ⌊H * Real.log P⌋₊ ≤ k) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k := by
  have hH0 : 0 < H := by linarith
  have hkR : (⌊H * Real.log P⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  have hf : H * Real.log P < (k : ℝ) + 1 :=
    (Nat.lt_floor_add_one (H * Real.log P)).trans_le (by linarith)
  have hi : (1 : ℝ) / H ≤ 1 := (div_le_one hH0).mpr hH
  have hl : Real.log P - 1 ≤ (k : ℝ) / H := by
    have hh : Real.log P < ((k : ℝ) + 1) / H :=
      (lt_div_iff₀ hH0).mpr (by nlinarith)
    rw [add_div] at hh
    linarith
  calc
    _ = Real.exp (Real.log P - 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mrt_log_bin_endpoints {H P Q : ℝ} (hH : 1 ≤ H) (hP : 0 < P) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ Q :=
  ⟨mrt_log_bin_lower_endpoint hH hP (mem_Icc.mp hk).1,
    mrt_prime_log_lower_le_upper (by linarith) hQ (mem_Icc.mp hk).2⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRealPrimeBins
namespace OAI

/-! Real short-prime bins, as used in the Ramaré decomposition, fit the
integer endpoint mixed-moment theorem without moving any prime. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_real_prime_bin_ceil {Y : ℝ} (hY : 1 < Y) :
    1 < ⌈Y⌉₊ ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ 2 * Y ∧
      Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log Y + Real.log 2 := by
  have hY0 : 0 < Y := by linarith
  have hlo : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hhi : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have hh := Nat.ceil_lt_add_one hY0.le
    linarith
  refine ⟨Nat.lt_ceil.mpr (by simpa using hY), hlo, hhi, ?_⟩
  calc
    _ ≤ Real.log (2 * Y) := Real.log_le_log (hY0.trans_le hlo) hhi
    _ = _ := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY0.ne']; ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandLogGrowth
namespace OAI

/-! Uniform scalar growth estimates for the actual MRT band endpoints.
These estimates bound the mixed-moment factorial cost for every band. -/

namespace TwoPointCorrelations

lemma mrt_log_log_band_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hQ : 1 ≤ Real.log Q) :
    Real.log (Real.log (mrtBandUpper Q j)) + 1 ≤
      8 * (j : ℝ) ^ 2 * (Real.log (Real.log Q) + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hq0 : 0 < Real.log Q := by linarith
  have hl0 : 0 ≤ Real.log (Real.log Q) := Real.log_nonneg hQ
  have hlj : Real.log (j : ℝ) ≤ j :=
    (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hlj
    (show 0 ≤ 4 * (j : ℝ) + 2 by positivity)
  have hq := mul_le_mul_of_nonneg_right hj2 hl0
  simp only [mrtBandUpper, Real.log_exp]
  rw [Real.log_mul (pow_ne_zero _ hj0.ne') (pow_ne_zero _ hq0.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

lemma mrt_log_band_lower_fourth (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (j : ℝ) ^ 4 * Real.log P ≤ Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : (j : ℝ) ^ 4 ≤ (j : ℝ) ^ (4 * j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q ^ (j - 1) := one_le_pow₀ hQ
  simp only [mrtBandLower, Real.log_exp]
  apply mul_le_mul_of_nonneg_right _ hP
  exact hp.trans (le_mul_of_one_le_right (by positivity) hq)

lemma mrt_band_adjacent_log_product (P Q : ℝ) (j : ℕ)
    (hP : 0 ≤ Real.log P) (hQ : 0 ≤ Real.log Q) :
    ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P ≤
      Real.log (mrtBandLower P Q (j + 1)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
    pow_le_pow_left₀ hj0 (by linarith) _
  have he : ((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ (4 * j + 2) ≤
      ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (4 * j + 2) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (pow_nonneg hQ j)) hP
  simpa only [mrtBandUpper, mrtBandLower, Real.log_exp,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc] using hh

theorem mrt_band_factorial_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 4096 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    32 * ((j : ℝ) + 1) ^ 2 *
        (Real.log (Real.log (mrtBandUpper Q (j + 1))) + 1) ≤
      η * Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl : 0 ≤ Real.log (Real.log Q) + 1 := by
    linarith [Real.log_nonneg hQ]
  have hu := mrt_log_log_band_upper Q (j + 1) (by omega) hQ
  simp only [Nat.cast_add, Nat.cast_one] at hu
  have hp : ((j : ℝ) + 1) ^ 4 ≤ 16 * (j : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * (j : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  calc
    _ ≤ 32 * ((j : ℝ) + 1) ^ 2 *
        (8 * ((j : ℝ) + 1) ^ 2 * (Real.log (Real.log Q) + 1)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 256 * ((j : ℝ) + 1) ^ 4 * (Real.log (Real.log Q) + 1) := by ring
    _ ≤ 4096 * (j : ℝ) ^ 4 * (Real.log (Real.log Q) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hp hl]
    _ = (j : ℝ) ^ 4 * (4096 * (Real.log (Real.log Q) + 1)) := by ring
    _ ≤ (j : ℝ) ^ 4 * (η * Real.log P) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = η * ((j : ℝ) ^ 4 * Real.log P) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_log_band_lower_fourth P Q j hj hP hQ) hη

theorem mrt_band_support_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 16 ≤ η * Real.log P) :
    8 * ((j : ℝ) + 1) ^ 2 * (Real.log (mrtBandUpper Q j) + Real.log 2) ≤
      η * Real.log (mrtBandLower P Q (j + 1)) := by
  have hy : 1 ≤ Real.log (mrtBandUpper Q j) := by
    have hh := mrt_band_index_le_log_upper Q j hj hQ
    exact (show (1 : ℝ) ≤ j by exact_mod_cast hj).trans hh
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) by positivity)
  calc
    _ ≤ 16 * ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) := by
      nlinarith [mul_le_mul_of_nonneg_left (show Real.log 2 ≤
        Real.log (mrtBandUpper Q j) by linarith)
        (show 0 ≤ 8 * ((j : ℝ) + 1) ^ 2 by positivity)]
    _ ≤ η * (((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P) := by
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_band_adjacent_log_product P Q j hP (by linarith)) hη

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandMixedBound
namespace OAI

/-! The numerical mixed-moment coefficient on two successive actual
MRT bands. The only initial scale condition is stated on P and Q. -/

namespace TwoPointCorrelations

theorem mrt_actual_band_mixed_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hP0 : 0 ≤ Real.log P := by linarith
  have hbase (k : ℕ) (hk : 1 ≤ k) :
      2 ≤ Real.log (mrtBandLower P Q k) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hh := mrt_log_band_lower_fourth P Q k hk hP0 hQ
    have hp : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
    have hp2 : (2 : ℝ) ≤ (k : ℝ) ^ 4 * Real.log P := by
      have hmul := mul_le_mul hp hP (by norm_num : (0 : ℝ) ≤ 2) (by positivity)
      norm_num at hmul
      exact hmul
    exact hp2.trans hh
  have hY0 : 0 < Y := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hYlo
  have hu0 : 0 < u := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hulo
  have hlogYlo : Real.log (mrtBandLower P Q (j + 1)) - 1 ≤ Real.log Y := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hYlo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 1)) ≤ Real.log Y at hh
    linarith
  have hlogulo : Real.log (mrtBandLower P Q (j + 2)) - 1 ≤ Real.log u := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hulo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 2)) ≤ Real.log u at hh
    linarith
  have hybase := hbase (j + 1) (by omega)
  have hubase := hbase (j + 2) (by omega)
  have hlogY : 1 ≤ Real.log Y := by linarith
  have hlogu : 1 ≤ Real.log u := by linarith
  have hYhalf : Real.log (mrtBandLower P Q (j + 1)) / 2 ≤ Real.log Y := by linarith
  have huhalf : Real.log (mrtBandLower P Q (j + 2)) / 2 ≤ Real.log u := by linarith
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hlogYhi : Real.log Y ≤ Real.log (mrtBandUpper Q (j + 1)) :=
    Real.log_le_log hY0 hYhi
  have hloguhi : Real.log u ≤ Real.log (mrtBandUpper Q (j + 2)) :=
    Real.log_le_log hu0 huhi
  have hhalfBudget : 4096 * (Real.log (Real.log Q) + 1) ≤ (η / 2) * Real.log P := by
    linarith
  have hsep0 := mrt_band_factorial_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ hhalfBudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, show 1 + 1 = 2 by decide] at hsep0
  have hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y := by
    calc
      _ ≤ 32 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (Real.log (mrtBandUpper Q (j + 2))) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (Real.log_le_log (by linarith) hloguhi) le_rfl
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 1)) := by
        convert (preTransparency := .instances) hsep0 using 1
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hYhalf hη]
  have h16 : 16 ≤ (η / 2) * Real.log P := by
    have hl := Real.log_nonneg hQ
    linarith
  have hsize0 := mrt_band_support_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ h16
  simp only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by decide,
    Nat.cast_add, Nat.cast_one] at hsize0
  have hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u := by
    calc
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (mrtBandUpper Q (j + 1)) + Real.log 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlogYhi le_rfl) (by positivity)
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 2)) := by
        convert (preTransparency := .instances) hsize0 using 1
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left huhalf hη]
  have hc := mrt_real_prime_bin_ceil hY1
  have hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u := by
    have hmult : 1 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith [sq_nonneg (j : ℝ)]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hh := le_mul_of_one_le_left
      (show 0 ≤ Real.log Y + Real.log 2 by linarith) hmult
    have he : η * Real.log u ≤ Real.log u :=
      mul_le_of_le_one_left (by linarith) (by linarith)
    exact hc.2.2.2.trans (hh.trans (hsize.trans he))
  exact mrt_mixed_real_bin_separation hη hη' j hY1 hlogY hYu hu0 hτ hsep hsize

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandCostSum
namespace OAI

/-! Summing the actual amplified cofactor cost over the preceding
witness bins and current small-polynomial bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_mixed_bin_cost_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    mrtMixedBinCost η j τ Y u ≤ 16 * Real.exp 10 * (τ + 1) *
      Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have he : Real.exp (-mrtFrequencyExponent η (j + 1) * Real.log u) ^ 2 =
      Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hb := mul_le_mul_of_nonneg_left
    (mrt_actual_band_mixed_bound hη hη' j hP hQ hbudget hYlo hYhi hulo huhi hτ)
    (show 0 ≤ 16 * Real.exp 10 by positivity)
  unfold mrtMixedBinCost
  rw [he]
  convert (preTransparency := .instances) hb using 1 <;> ring

theorem mrt_mixed_bin_cost_sum {β κ : Type*} (B : Finset β) (K : Finset κ)
    (Y : β → ℝ) (u : κ → ℝ) {η P Q τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hY : ∀ b ∈ B, Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y b ∧
      Y b ≤ mrtBandUpper Q (j + 1))
    (hu : ∀ k ∈ K, Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u k ∧
      u k ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      32 * Real.exp 10 * (τ + 1) * B.card * K.card *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hb (b : β) (hmem : b ∈ B) :
      (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact mrt_mixed_bin_cost_bound hη hη' j hP hQ hbudget
      (hY b hmem).1 (hY b hmem).2 (hu k hk).1 (hu k hk).2 hτ
  calc
    _ ≤ 2 * ∑ b ∈ B, (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by norm_num)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBinMomentSum
namespace OAI

/-! The complete finite witness-bin sum. Both bin cardinalities and the
remaining exponential sum are bounded using their actual endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem mrt_actual_bin_moment_sum_oai {η P Q τ H₀ H₁ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH₀ : 2 ≤ H₀) (hH₁ : 2 ≤ H₁) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
        ∑ k ∈ mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
          mrtMixedBinCost η j τ (mrtPrimeLogLower H₀ b) (mrtPrimeLogLower H₁ k) ≤
      64 * Real.exp 11 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        (H₁ / (η / (2 * ((j : ℝ) + 2) ^ 2))) *
        (mrtBandLower P Q (j + 2)) ^ (-(η / (2 * ((j : ℝ) + 2) ^ 2))) := by
  let B := mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1))
  let K := mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))
  let β : ℝ := η / (2 * ((j : ℝ) + 2) ^ 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβH : β ≤ H₁ := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : 1 ≤ 2 * ((j : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (j : ℝ)]
    have hh := div_le_self hη.le hd
    dsimp [β]
    linarith
  have hUpper (k : ℕ) : 1 ≤ mrtBandUpper Q (k + 1) := by
    apply Real.one_le_exp
    have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
    exact mul_nonneg (pow_nonneg hk _) (pow_nonneg (by linarith : 0 ≤ Real.log Q) _)
  have hLower (k : ℕ) : 1 ≤ mrtBandLower P Q (k + 1) := by
    apply Real.one_le_exp
    positivity
  have hU₂ : 1 ≤ mrtBandUpper Q (j + 2) := by
    simpa only [Nat.add_assoc] using hUpper (j + 1)
  have hL₂ : 1 ≤ mrtBandLower P Q (j + 2) := by
    simpa only [Nat.add_assoc] using hLower (j + 1)
  have hcB := mrt_log_bin_card (P := mrtBandLower P Q (j + 1))
    (by linarith : 0 ≤ H₀) (hUpper j)
  have hcK := mrt_log_bin_card (P := mrtBandLower P Q (j + 2))
    (by linarith : 0 ≤ H₁) hU₂
  have hh := mrt_mixed_bin_cost_sum B K (mrtPrimeLogLower H₀) (mrtPrimeLogLower H₁)
    hη.le hη' j hP hQ hbudget
    (fun b hb => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) (hUpper j) hb)
    (fun k hk => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) hU₂ hk) hτ
  have hs := mrt_first_band_exponential_sum hβ (by linarith : 0 < H₁)
    hβH hL₂ ⌊H₁ * Real.log (mrtBandUpper Q (j + 2))⌋₊
  have he (k : ℕ) :
      -η * Real.log (mrtPrimeLogLower H₁ k) / (2 * ((j : ℝ) + 2) ^ 2) =
        -β * (k : ℝ) / H₁ := by
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    ring
  simp_rw [he] at hh
  apply hh.trans
  have hnB : 0 ≤ H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1 :=
    (Nat.cast_nonneg B.card).trans hcB
  have hnK : 0 ≤ H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1 :=
    (Nat.cast_nonneg K.card).trans hcK
  calc
    _ ≤ 32 * Real.exp 10 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        ((2 * Real.exp 1 * H₁ / β) * (mrtBandLower P Q (j + 2)) ^ (-β)) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcB (by positivity)
        · exact hcK
        · exact Nat.cast_nonneg K.card
        · positivity
      · exact hs
      · exact sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · positivity
    _ = _ := by
      rw [show Real.exp 11 = Real.exp 10 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      dsimp [β]
      ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_actual_bin_moment_sum_oai := @OAI.TwoPointCorrelations.mrt_actual_bin_moment_sum_oai
